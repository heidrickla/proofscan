//! Question 7 over shell a check runs in: a test or lint runner piped into another command
//! exits with the last command's status, so a failure is reported as a pass.

use super::Analysis;
use crate::facts::*;
use crate::report::Verdict;
use regex::Regex;

impl<'a> Analysis<'a> {
    pub(super) fn pipe_masks_exit(&mut self) {
        let f = self.f;
        let runner = Regex::new(
            r"^(pytest|py\.test|tox|nox|ruff|mypy|pyright|flake8|pylint|black|eslint|tsc|jest|vitest|mocha|cargo(nextest|test|clippy|build|check|fmt|deny|nextest)|npm(test|runtest|run\w*test|run\w*lint|run\w*check|ci)|pnpm(test|run\w*test)|yarn(test)?|gotest|govet|make\w*|ctest|\S*check\S*\.sh|\S*test\S*\.sh|python3?-m(pytest|unittest|mypy|ruff)|uv(run)?(pytest|ruff|mypy)|(\S*/)?(pytest|ruff|mypy))",
        )
        .expect("runner");
        for c in &f.calls {
            if c.pipe_to.is_empty() {
                continue;
            }
            let s = &f.sites[c.site as usize];
            if f.files[s.file as usize].lang != Lang::Bash {
                continue;
            }
            let cmd: String = std::iter::once(c.full.as_str())
                .chain(c.str_args.iter().map(|a| a.as_str()))
                .collect::<Vec<_>>()
                .join("");
            if !runner.is_match(&cmd) {
                continue;
            }
            // The shell this command runs in starts at the last block marker before it (a run step,
            // a recipe line), or at the top of a script.
            let same_file = |x: &&Call| f.sites[x.site as usize].file == s.file;
            let block_start = f
                .calls
                .iter()
                .filter(same_file)
                .filter(|x| {
                    x.str_args.iter().any(|a| a == crate::lang::SHELL_BLOCK)
                        && f.sites[x.site as usize].line <= s.line
                })
                .map(|x| f.sites[x.site as usize].line)
                .max()
                .unwrap_or(0);
            let next_block = f
                .calls
                .iter()
                .filter(same_file)
                .filter(|x| {
                    x.str_args.iter().any(|a| a == crate::lang::SHELL_BLOCK)
                        && f.sites[x.site as usize].line > s.line
                })
                .map(|x| f.sites[x.site as usize].line)
                .min()
                .unwrap_or(u32::MAX);
            let in_block = |x: &&Call, lo: u32, hi: u32| {
                let l = f.sites[x.site as usize].line;
                l >= lo && l <= hi
            };
            let pipefail = f.calls.iter().filter(same_file).any(|x| {
                in_block(&x, block_start, s.line)
                    && x.full == "set"
                    && x.str_args.iter().any(|a| a.contains("pipefail"))
            });
            let pipestatus = f.calls.iter().filter(same_file).any(|x| {
                in_block(&x, s.line, next_block.saturating_sub(1))
                    && (x.str_args.iter().any(|a| a.contains("PIPESTATUS"))
                        || x.args.iter().any(|a| a.text.contains("PIPESTATUS")))
            });
            let into = c.pipe_to.join(" | ");
            if pipefail || pipestatus {
                self.push(
                    7,
                    "pipe-masks-exit",
                    Verdict::Proven,
                    c.site,
                    format!(
                        "`{}` is piped into `{into}` under {}: its failure fails the step",
                        c.full,
                        if pipefail {
                            "pipefail"
                        } else {
                            "a PIPESTATUS check"
                        }
                    ),
                    vec![],
                    vec![],
                );
            } else {
                self.push(
                    7,
                    "pipe-masks-exit",
                    Verdict::Violated,
                    c.site,
                    format!(
                        "`{}` is piped into `{into}` with no `set -o pipefail` or PIPESTATUS check: the pipeline exits with `{}`'s status, so a failing run reads as a pass",
                        c.full,
                        c.pipe_to.last().map_or("", |p| p.as_str())
                    ),
                    vec![],
                    vec![],
                );
            }
        }
    }

    /// Question 7: a Hypothesis property test told to draw new examples on every run
    /// (`settings(derandomize=False)`). Its pass, or its kill of a mutant, can change from one
    /// run to the next. Under `CI` Hypothesis derandomizes unless a setting says otherwise, so
    /// only an explicit `False` stays random there.
    pub(super) fn random_property(&mut self) {
        let f = self.f;
        let settings = Regex::new(r"(^|\.)(settings|register_profile)$").expect("settings");
        for c in &f.calls {
            if !settings.is_match(&c.full) {
                continue;
            }
            let Some((_, v)) = c.kwargs.iter().find(|(k, _)| k == "derandomize") else {
                continue;
            };
            match v.text.trim() {
                "False" => self.push(
                    7,
                    "random-property",
                    Verdict::Violated,
                    c.site,
                    format!(
                        "`{}` sets `derandomize=False`: the property draws new examples on every run, CI included, so whether it passes, or kills a mutant, can change between runs",
                        c.full
                    ),
                    vec![],
                    vec![],
                ),
                "True" => self.push(
                    7,
                    "random-property",
                    Verdict::Proven,
                    c.site,
                    format!("`{}` sets `derandomize=True`: each run draws the same examples", c.full),
                    vec![],
                    vec![],
                ),
                _ => {}
            }
        }
    }

    /// Question 7: a crate replaced through `[patch]` with a path, in a repository whose advisory
    /// check (`cargo deny check`, `cargo audit`) passes. Both match advisories by a registry
    /// crate's name and version; a path crate has no registry source, so the patched copy, the
    /// code that is built, is never checked and its absence reads as a clean pass.
    pub(super) fn path_patch_advisories(&mut self) {
        let f = self.f;
        let repo_of = |site: Id| f.files[f.sites[site as usize].file as usize].repo;
        let advisory = |c: &Call| -> bool {
            let words: Vec<&str> = c.str_args.iter().map(|a| a.as_str()).collect();
            let marker = words.first() == Some(&crate::lang::ADVISORY_CHECK);
            let words: Vec<&str> = if marker { words[1..].to_vec() } else { words };
            let tool = match c.full.as_str() {
                ":" if marker => words.first().copied(),
                "cargo" => words.iter().find(|w| !w.starts_with('-')).copied(),
                "cargo-deny" => Some("deny"),
                "cargo-audit" => Some("audit"),
                _ => None,
            };
            match tool {
                Some("audit") => true,
                Some("deny") => match words.iter().position(|w| *w == "check") {
                    Some(i) => {
                        let checks: Vec<&&str> = words[i + 1..]
                            .iter()
                            .filter(|w| !w.starts_with('-'))
                            .collect();
                        checks.is_empty() || checks.iter().any(|w| **w == "advisories")
                    }
                    None => false,
                },
                _ => false,
            }
        };
        let checks: Vec<&Call> = f
            .calls
            .iter()
            .filter(|c| f.files[f.sites[c.site as usize].file as usize].lang == Lang::Bash)
            .filter(|c| advisory(c))
            .collect();
        // A crate whose code hands cargo deny a graph of its own (`--metadata-path`) with
        // `check advisories`, and a shell step that runs it (`cargo run -p <crate>`): the graph
        // can present path and git crates as their crates.io releases. (repo, (step, crate))
        let crate_dir = |path: &str| -> String {
            path.rfind("/src/")
                .map(|i| path[..i].to_string())
                .unwrap_or_default()
        };
        let mut graph_tools: Vec<(Id, String)> = vec![];
        for x in &f.calls {
            let file = &f.files[f.sites[x.site as usize].file as usize];
            if file.lang != Lang::Rust
                || file.test
                || !x.str_args.iter().any(|a| a == "--metadata-path")
            {
                continue;
            }
            let advisories = f.calls.iter().any(|y| {
                f.sites[y.site as usize].file == f.sites[x.site as usize].file
                    && y.str_args.iter().any(|a| a == "advisories")
            });
            let dir = crate_dir(&file.path);
            if advisories && !dir.is_empty() {
                let name = dir.rsplit('/').next().unwrap_or(&dir).to_string();
                graph_tools.push((file.repo, name));
            }
        }
        let mut graph_checks: Vec<(Id, (String, String))> = vec![];
        for x in &f.calls {
            let file = &f.files[f.sites[x.site as usize].file as usize];
            if file.lang != Lang::Bash
                || x.full != "cargo"
                || x.str_args.first().map(|a| a.as_str()) != Some("run")
            {
                continue;
            }
            let pkg = x
                .str_args
                .windows(2)
                .find(|w| w[0] == "-p" || w[0] == "--package")
                .map(|w| w[1].clone());
            if let Some(pkg) = pkg
                && graph_tools
                    .iter()
                    .any(|(r, n)| *r == file.repo && *n == pkg)
            {
                let at = format!("{}:{}", file.path, f.sites[x.site as usize].line);
                graph_checks.push((file.repo, (at, pkg)));
            }
        }
        for c in &f.calls {
            if c.full != ":"
                || c.str_args.first().map(|a| a.as_str()) != Some(crate::lang::PATH_PATCH)
            {
                continue;
            }
            let (Some(name), Some(path)) = (c.str_args.get(1), c.str_args.get(2)) else {
                continue;
            };
            let repo = repo_of(c.site);
            let here: Vec<String> = checks
                .iter()
                .filter(|x| repo_of(x.site) == repo)
                .map(|x| {
                    let s = &f.sites[x.site as usize];
                    let words = match x.str_args.first().map(|a| a.as_str()) {
                        Some(crate::lang::ADVISORY_CHECK) => &x.str_args[1..],
                        _ => &x.str_args[..],
                    };
                    format!(
                        "{}:{} `cargo {}` checks advisories by registry name and version",
                        f.files[s.file as usize].path,
                        s.line,
                        words.join(" ")
                    )
                })
                .collect();
            if here.is_empty() {
                continue;
            }
            let what = match path.strip_prefix("git:") {
                Some(url) => format!("`{name}` is built from git (`{url}`)"),
                None => format!("`{name}` is patched to the path `{path}`"),
            };
            if let Some(step) = graph_checks.iter().find(|(r, _)| *r == repo) {
                self.push(
                    7,
                    "path-patch-advisories",
                    Verdict::Proven,
                    c.site,
                    format!(
                        "{what}, and {} runs `{}`, which gives cargo deny a rewritten graph (`--metadata-path`) to check advisories over",
                        step.1 .0, step.1 .1
                    ),
                    here,
                    vec![format!(
                        "`{}` presents every path and git crate as its crates.io release of the same name and version",
                        step.1 .1
                    )],
                );
                continue;
            }
            self.push(
                7,
                "path-patch-advisories",
                Verdict::Violated,
                c.site,
                format!(
                    "{what}: the advisory check matches registry crates, so the copy that is built is never checked and the check passes without it"
                ),
                here,
                vec![],
            );
        }
    }
}
