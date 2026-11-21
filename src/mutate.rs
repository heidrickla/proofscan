//! Question 8, tests that can fail. Each condition, guard exit or raise that a diff adds is
//! mutated in a pristine copy of the commit (negated, or the exit removed), and the test command
//! runs. A mutant the tests kill is proven; one they let live is a violation, a rule no test
//! checks; a mutant that cannot build or a test run that cannot start is unknown.

use crate::diff;
use crate::lang::{lang_of, line, named_children, text};
use crate::report::{Finding, Report, Verdict, summarize};
use anyhow::{Context, Result, bail};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use tree_sitter::{Node, Parser};

#[derive(Debug, Clone)]
pub struct Mutant {
    pub file: String,
    pub line: u32,
    pub start: usize,
    pub end: usize,
    pub replacement: String,
    pub what: String,
}

/// Mutants for the changed lines of one file.
pub fn mutants(path: &str, src: &str, lines: &std::collections::HashSet<u32>) -> Vec<Mutant> {
    let Some(lang) = lang_of(Path::new(path)) else {
        return vec![];
    };
    let mut parser = Parser::new();
    let ok = match lang {
        crate::facts::Lang::Python => parser
            .set_language(&tree_sitter_python::LANGUAGE.into())
            .is_ok(),
        crate::facts::Lang::Rust => parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .is_ok(),
        _ => false,
    };
    if !ok {
        return vec![];
    }
    let Some(tree) = parser.parse(src, None) else {
        return vec![];
    };
    let mut out = vec![];
    visit(tree.root_node(), src, path, lines, &mut out);
    out
}

fn visit(
    n: Node,
    src: &str,
    path: &str,
    lines: &std::collections::HashSet<u32>,
    out: &mut Vec<Mutant>,
) {
    let on = lines.contains(&line(n));
    match n.kind() {
        "if_statement" | "elif_clause" | "while_statement" | "if_expression"
        | "while_expression"
            if on =>
        {
            if let Some(c) = n.child_by_field_name("condition") {
                let t = text(c, src);
                out.push(Mutant {
                    file: path.into(),
                    line: line(c),
                    start: c.start_byte(),
                    end: c.end_byte(),
                    replacement: format!("not ({t})"),
                    what: format!("`{t}` is negated"),
                });
                if n.kind().ends_with("expression") {
                    out.last_mut().unwrap().replacement = format!("!({t})");
                }
                // The guard taken every time: a check that only skips a duplicate (append unless
                // the last row is this one) is killed by negation, yet no test may need it at all.
                // Not for a loop, which would never end.
                if !n.kind().starts_with("while") {
                    out.push(Mutant {
                        file: path.into(),
                        line: line(c),
                        start: c.start_byte(),
                        end: c.end_byte(),
                        replacement: if n.kind() == "if_expression" {
                            "true"
                        } else {
                            "True"
                        }
                        .into(),
                        what: format!("`{t}` always holds"),
                    });
                }
                // Each half of `a or b` / `a and b` on its own: a test of one half kills the
                // negation of the whole, while the other half goes unchecked.
                operands(c, src, path, out);
            }
        }
        "raise_statement" | "assert_statement" | "return_statement" | "continue_statement"
        | "break_statement"
            if on && in_guard_branch(n) =>
        {
            let indent_ok = matches!(
                n.kind(),
                "raise_statement"
                    | "assert_statement"
                    | "return_statement"
                    | "continue_statement"
                    | "break_statement"
            );
            if indent_ok {
                out.push(Mutant {
                    file: path.into(),
                    line: line(n),
                    start: n.start_byte(),
                    end: n.end_byte(),
                    replacement: "pass".into(),
                    what: format!("`{}` is removed", first_line(text(n, src))),
                });
            }
        }
        "macro_invocation" if on => {
            let t = text(n, src);
            if t.starts_with("bail!") || t.starts_with("ensure!") || t.starts_with("assert!") {
                out.push(Mutant {
                    file: path.into(),
                    line: line(n),
                    start: n.start_byte(),
                    end: n.end_byte(),
                    replacement: "()".into(),
                    what: format!("`{}` is removed", first_line(t)),
                });
            }
        }
        _ => {}
    }
    for c in named_children(n) {
        visit(c, src, path, lines, out);
    }
}

/// An exit inside an `if` body: the shape of a guard.
fn in_guard_branch(n: Node) -> bool {
    let mut cur = n.parent();
    while let Some(p) = cur {
        match p.kind() {
            "if_statement" | "elif_clause" | "else_clause" => return true,
            "function_definition" | "class_definition" | "module" => return false,
            _ => cur = p.parent(),
        }
    }
    false
}

/// For a boolean condition, a mutant per operand: a disjunct replaced by `False`, a conjunct by
/// `True` (Python), so the rule that operand adds is removed and the rest stands.
fn operands(c: Node, src: &str, path: &str, out: &mut Vec<Mutant>) {
    let c = if c.kind() == "parenthesized_expression" {
        named_children(c).into_iter().next().unwrap_or(c)
    } else {
        c
    };
    if c.kind() != "boolean_operator" {
        return;
    }
    let op = c
        .child_by_field_name("operator")
        .map(|o| text(o, src))
        .unwrap_or("");
    let neutral = match op {
        "or" => "False",
        "and" => "True",
        _ => return,
    };
    for side in ["left", "right"] {
        let Some(x) = c.child_by_field_name(side) else {
            continue;
        };
        if x.kind() == "boolean_operator"
            && x.child_by_field_name("operator").map(|o| text(o, src)) == Some(op)
        {
            operands(x, src, path, out);
            continue;
        }
        let t = text(x, src);
        out.push(Mutant {
            file: path.into(),
            line: line(x),
            start: x.start_byte(),
            end: x.end_byte(),
            replacement: neutral.into(),
            what: format!("`{}` is dropped from its `{op}`", first_line(t)),
        });
        // An operand that is itself a condition of the other operator: each of its operands too.
        operands(x, src, path, out);
    }
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(80).collect()
}

/// Run the tests on the mutated tree. A failure that only property tests drawing new examples
/// each run (`derandomize=False`) report is not a stable kill: with pytest, those tests are set
/// aside (`--deselect`) and the rest run again, up to three times. Returns the outcome and the
/// random tests set aside.
fn judge(test: &str, dir: &Path, timeout: u64) -> (Result<Option<bool>>, Vec<String>) {
    let mut cmd = test.to_string();
    let mut aside: Vec<String> = vec![];
    loop {
        let (res, out) = match sh(&cmd, dir, timeout) {
            Ok(r) => r,
            Err(e) => return (Err(e), aside),
        };
        if res != Some(false) {
            return (Ok(res), aside);
        }
        let failed = failed_tests(&out);
        let random = !failed.is_empty()
            && failed
                .iter()
                .all(|(_, file, func)| random_test(dir, file, func));
        if !random {
            return (Ok(res), aside);
        }
        if !test.contains("pytest") || aside.len() >= 3 {
            // Only random draws kill it and they cannot be set aside: no stable kill.
            aside.extend(failed.into_iter().map(|(id, _, _)| id));
            return (Ok(Some(true)), aside);
        }
        for (id, _, _) in failed {
            let q = if cfg!(windows) { '"' } else { '\'' };
            cmd.push_str(&format!(" --deselect {q}{id}{q}"));
            aside.push(id);
        }
    }
}

/// pytest's `FAILED <file>::[<class>::]<test>[<params>]` lines: (id, file, test function).
fn failed_tests(out: &str) -> Vec<(String, String, String)> {
    let re = regex::Regex::new(r"(?m)^FAILED (\S+?\.py::\S+?)(?: - .*)?$").expect("failed");
    re.captures_iter(out)
        .filter_map(|c| {
            let id = c.get(1)?.as_str().to_string();
            let (file, rest) = id.split_once("::")?;
            let func = rest.rsplit("::").next()?.split('[').next()?.to_string();
            Some((id.clone(), file.to_string(), func))
        })
        .collect()
}

/// Whether the decorators above `def <func>` in `file` set `derandomize=False`.
fn random_test(dir: &Path, file: &str, func: &str) -> bool {
    let Ok(text) = std::fs::read_to_string(dir.join(file)) else {
        return false;
    };
    let lines: Vec<&str> = text.lines().collect();
    let def = [format!("def {func}("), format!("async def {func}(")];
    let Some(at) = lines.iter().position(|l| {
        let t = l.trim_start();
        def.iter().any(|d| t.starts_with(d.as_str()))
    }) else {
        return false;
    };
    let above: String = lines[..at]
        .iter()
        .rev()
        .take_while(|l| !l.trim().is_empty())
        .map(|l| l.split_whitespace().collect::<String>())
        .collect();
    above.contains("derandomize=False")
}

/// One run of the test command with `CI` set, as CI runs it (Hypothesis then draws the same
/// examples unless a test says otherwise): passed, failed or timed out (`None`), and its output.
fn sh(cmd: &str, dir: &Path, timeout: u64) -> Result<(Option<bool>, String)> {
    let log = dir.with_extension("log");
    let out = std::fs::File::create(&log)?;
    let mut c = if cfg!(windows) {
        let mut c = Command::new("cmd");
        c.args(["/C", cmd]);
        c
    } else {
        let mut c = Command::new("sh");
        c.args(["-c", cmd]);
        c
    };
    let mut child = c
        .current_dir(dir)
        .env("CI", "true")
        .stdin(Stdio::null())
        .stdout(Stdio::from(out.try_clone()?))
        .stderr(Stdio::from(out))
        .spawn()?;
    let t0 = Instant::now();
    let res = loop {
        if let Some(s) = child.try_wait()? {
            break Some(s.success());
        }
        if t0.elapsed() > Duration::from_secs(timeout) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(200));
    };
    let text = std::fs::read_to_string(&log).unwrap_or_default();
    Ok((res, text))
}

fn extract(root: &Path, rev: &str, into: &Path) -> Result<()> {
    std::fs::create_dir_all(into)?;
    let archive = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["archive", "--format=tar", rev])
        .output()?;
    if !archive.status.success() {
        bail!(
            "git archive {rev}: {}",
            String::from_utf8_lossy(&archive.stderr).trim()
        );
    }
    let mut tar = Command::new("tar")
        .args(["-x", "-f", "-", "-C"])
        .arg(into)
        .stdin(Stdio::piped())
        .spawn()
        .context("tar")?;
    use std::io::Write;
    tar.stdin
        .take()
        .context("tar stdin")?
        .write_all(&archive.stdout)?;
    if !tar.wait()?.success() {
        bail!("tar -x into {}", into.display());
    }
    Ok(())
}

/// The mutants a diff gives, read from the commit's objects.
pub fn list(root: &Path, base: &str, rev: Option<&str>, at: &[String]) -> Result<Vec<Mutant>> {
    let rev = rev.unwrap_or("HEAD");
    let changed = diff::changed_lines(root, base, Some(rev))?;
    let mut files: Vec<&String> = changed.keys().collect();
    files.sort();
    let mut out = vec![];
    for file in files {
        let shown = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["show", &format!("{rev}:{file}")])
            .output()?;
        if !shown.status.success() {
            continue;
        }
        let src = String::from_utf8_lossy(&shown.stdout).into_owned();
        out.extend(mutants(file, &src, &changed[file]));
    }
    out.retain(|m| picked(m, at));
    Ok(out)
}

/// With `--at`, only the mutants on the named lines.
fn picked(m: &Mutant, at: &[String]) -> bool {
    at.is_empty() || at.iter().any(|a| *a == format!("{}:{}", m.file, m.line))
}

pub fn run(
    root: &Path,
    base: &str,
    rev: Option<&str>,
    test: &str,
    timeout: u64,
    at: &[String],
) -> Result<Report> {
    if test.is_empty() {
        bail!("--test is required to run the mutants (or --list to list them)");
    }
    let t0 = Instant::now();
    let rev = rev.unwrap_or("HEAD");
    let changed = diff::changed_lines(root, base, Some(rev))?;
    let scratch = tempdir()?;
    let pristine = scratch.join("tree");
    extract(root, rev, &pristine)?;
    let baseline = sh(test, &pristine, timeout)?.0;
    let repo = root
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    let mut findings = vec![];
    let mut all = vec![];
    for (file, lines) in &changed {
        let Ok(src) = std::fs::read_to_string(pristine.join(file)) else {
            continue;
        };
        all.extend(
            mutants(file, &src, lines)
                .into_iter()
                .filter(|m| picked(m, at))
                .map(|m| (m, src.clone())),
        );
    }
    if baseline != Some(true) {
        let why = if baseline.is_none() {
            "timed out"
        } else {
            "fails"
        };
        findings.push(Finding {
            question: 8,
            rule: "mutant",
            verdict: Verdict::Unknown,
            repo: repo.clone(),
            site: rev.to_string(),
            message: format!("the test command {why} on the unmutated commit, so no mutant can be judged ({} mutants)", all.len()),
            witness: vec![test.to_string()],
            assumptions: vec![],
        });
    } else {
        for (m, src) in all {
            let mut mutated = String::with_capacity(src.len());
            mutated.push_str(&src[..m.start]);
            mutated.push_str(&m.replacement);
            mutated.push_str(&src[m.end..]);
            let path = pristine.join(&m.file);
            std::fs::write(&path, &mutated)?;
            let (res, random) = judge(test, &pristine, timeout);
            std::fs::write(&path, &src)?;
            let aside = random.join(", ");
            let (verdict, msg) = match res {
                Ok(Some(false)) if random.is_empty() => {
                    (Verdict::Proven, format!("the tests fail when {}", m.what))
                }
                Ok(Some(false)) => (
                    Verdict::Proven,
                    format!(
                        "the tests fail when {}, with the random property tests set aside ({aside})",
                        m.what
                    ),
                ),
                Ok(Some(true)) if !random.is_empty() => (
                    Verdict::Violated,
                    format!(
                        "only {aside} fails when {}, a property test that draws new examples each run (`derandomize=False`): another run may let the mutant through, and no test that draws the same examples checks this rule",
                        m.what
                    ),
                ),
                Ok(Some(true)) => (
                    Verdict::Violated,
                    format!(
                        "the tests still pass when {}: no test checks this rule",
                        m.what
                    ),
                ),
                Ok(None) => (
                    Verdict::Unknown,
                    format!("the tests time out when {}", m.what),
                ),
                Err(e) => (Verdict::Unknown, format!("tests could not run: {e}")),
            };
            findings.push(Finding {
                question: 8,
                rule: "mutant",
                verdict,
                repo: repo.clone(),
                site: format!("{}:{}", m.file, m.line),
                message: msg,
                witness: vec![],
                assumptions: vec![],
            });
        }
    }
    let _ = std::fs::remove_dir_all(&scratch);
    let mut qs = summarize(&findings, &Default::default());
    qs.retain(|q| q.question == 8);
    Ok(Report {
        build: crate::report::BUILD,
        repos: vec![format!("{}@{rev}", root.display())],
        profiles: vec![],
        files: changed.len(),
        functions: 0,
        unparsed: vec![],
        diff: Some(base.to_string()),
        questions: qs,
        findings,
        millis: t0.elapsed().as_millis(),
    })
}

fn tempdir() -> Result<std::path::PathBuf> {
    let base = std::env::temp_dir().join(format!(
        "proofscan-mutate-{}-{}",
        std::process::id(),
        Instant::now().elapsed().as_nanos()
    ));
    std::fs::create_dir_all(&base)?;
    Ok(base)
}

#[cfg(test)]
mod random_tests {
    use super::*;

    #[test]
    fn failed_lines_give_file_and_function() {
        let out = "....F\nFAILED tests/test_loops.py::test_the_scheduler_keeps_to_its_reference_model - AssertionError: x\nFAILED tests/t.py::TestA::test_b[UTC-03:30] - ValueError\n1 failed\n";
        let got = failed_tests(out);
        assert_eq!(got.len(), 2);
        assert_eq!(
            got[0],
            (
                "tests/test_loops.py::test_the_scheduler_keeps_to_its_reference_model".into(),
                "tests/test_loops.py".into(),
                "test_the_scheduler_keeps_to_its_reference_model".into()
            )
        );
        assert_eq!(got[1].1, "tests/t.py");
        assert_eq!(got[1].2, "test_b");
    }

    #[test]
    fn a_test_is_random_only_by_its_own_decorators() {
        let dir = std::env::temp_dir().join(format!("ps-random-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("tests")).unwrap();
        std::fs::write(
            dir.join("tests/t.py"),
            "@settings(max_examples=5, derandomize=True)\n@given(st.integers())\ndef test_fixed(x):\n    pass\n\n\n@settings(\n    max_examples=1200, database=None,\n    derandomize = False,\n)\n@given(st.integers())\n# a pinned case\n@example(1)\ndef test_drawn(x):\n    pass\n",
        )
        .unwrap();
        assert!(random_test(&dir, "tests/t.py", "test_drawn"));
        assert!(!random_test(&dir, "tests/t.py", "test_fixed"));
        assert!(!random_test(&dir, "tests/t.py", "test_missing"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
