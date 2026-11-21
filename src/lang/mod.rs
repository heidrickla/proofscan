//! Source files to facts. One extractor per language; all fill the same `Facts`.

pub mod python;
mod retry;
pub mod rust;
pub mod script;

use crate::facts::{Facts, File, Lang};
use std::path::Path;
use tree_sitter::Node;

pub fn lang_of(path: &Path) -> Option<Lang> {
    if shell_host(&path.to_string_lossy()).is_some() {
        return Some(Lang::Bash);
    }
    match path.extension()?.to_str()? {
        "py" => Some(Lang::Python),
        "rs" => Some(Lang::Rust),
        "js" | "mjs" | "cjs" => Some(Lang::JavaScript),
        "sh" | "bash" => Some(Lang::Bash),
        "ps1" | "psm1" => Some(Lang::PowerShell),
        _ => None,
    }
}

/// Test code: under a tests directory, a `test_*`/`*_test` file, conftest, or a Rust `tests.rs`,
/// `*_tests.rs` or `*_test.rs`.
pub fn is_test_path(rel: &str) -> bool {
    let rel = rel.replace('\\', "/");
    let name = rel.rsplit('/').next().unwrap_or(&rel);
    rel.split('/')
        .any(|p| p == "tests" || p == "test" || p == "testing")
        || name.starts_with("test_")
        || name.ends_with("_test.py")
        || name == "conftest.py"
        || name == "tests.rs"
        || name.ends_with("_tests.rs")
        || name.ends_with("_test.rs")
        || name.ends_with(".test.js")
}

pub fn module_of(rel: &str, lang: Lang) -> String {
    let rel = rel.replace('\\', "/");
    let stem = rel.rsplit_once('.').map(|(s, _)| s).unwrap_or(&rel);
    let sep = if lang == Lang::Rust { "::" } else { "." };
    let parts: Vec<&str> = stem
        .split('/')
        .filter(|p| *p != "__init__" && *p != "mod")
        .collect();
    parts.join(sep)
}

/// Files read as shell without being scripts: CI workflows and Makefiles hold shell; a Cargo
/// manifest, or a diff that edits one, holds `[patch]` entries, given as marker commands.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShellHost {
    Workflow,
    Makefile,
    Manifest,
    Diff,
}

pub fn shell_host(rel: &str) -> Option<ShellHost> {
    let rel = rel.replace('\\', "/");
    let name = rel.rsplit('/').next().unwrap_or(&rel);
    let in_workflows = [
        ".github/workflows/",
        ".gitea/workflows/",
        ".forgejo/workflows/",
    ]
    .iter()
    .any(|d| rel.starts_with(d) || rel.contains(&format!("/{d}")));
    if in_workflows && (name.ends_with(".yml") || name.ends_with(".yaml")) {
        Some(ShellHost::Workflow)
    } else if name == "Makefile" || name == "GNUmakefile" || name.ends_with(".mk") {
        Some(ShellHost::Makefile)
    } else if name == "Cargo.toml" {
        Some(ShellHost::Manifest)
    } else if name.ends_with(".patch") || name.ends_with(".diff") {
        Some(ShellHost::Diff)
    } else {
        None
    }
}

/// The marker a block of host shell starts with: each `run:` step and each recipe line is its
/// own shell, so `set -o pipefail` holds only inside its block.
pub const SHELL_BLOCK: &str = "proofscan-shell-block";

/// The marker for a `[patch]` entry that replaces a crate with a path:
/// `: proofscan-path-patch <crate> <path>` on the entry's line.
pub const PATH_PATCH: &str = "proofscan-path-patch";

/// The marker for an advisory check in a workflow line that bash cannot read as one (a pwsh step
/// running a downloaded `cargo-deny.exe`): `: proofscan-advisory-check deny|audit <checks>`.
pub const ADVISORY_CHECK: &str = "proofscan-advisory-check";

/// A workflow `run:` line that runs cargo-deny's `check` or cargo-audit other than as a plain
/// `cargo ...` command, as its marker; `None` for every other line.
fn advisory_marker(line: &str) -> Option<String> {
    let t = line.trim();
    if t.is_empty() || t.starts_with('#') || t.starts_with("cargo ") || t.contains("install") {
        return None;
    }
    let deny = regex::Regex::new(r"cargo[- ]deny\b.*?\bcheck\b(.*)$").expect("deny");
    let audit = regex::Regex::new(r#"cargo[- ]audit(\.exe)?["')]*(\s|$)"#).expect("audit");
    if let Some(c) = deny.captures(t) {
        let checks: Vec<&str> = c[1]
            .split_whitespace()
            .take_while(|w| w.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '-'))
            .filter(|w| !w.starts_with('-'))
            .collect();
        return Some(format!(
            ": {ADVISORY_CHECK} deny check {}",
            checks.join(" ")
        ));
    }
    audit
        .is_match(t)
        .then(|| format!(": {ADVISORY_CHECK} audit"))
}

/// The `[patch]` entries with a path or git source, and the dependencies from git, in manifest
/// lines, as (line index, crate, path or `git:url`). A line is `None` where it is not in the
/// manifest (a removed or header line of a diff); a diff hunk that starts inside a table without
/// its header is not seen.
fn path_patches(lines: &[Option<&str>]) -> Vec<(usize, String, String)> {
    let header = regex::Regex::new(
        r#"^\[\s*patch\.(?:"[^"]*"|'[^']*'|[A-Za-z0-9_-]+)(?:\.([A-Za-z0-9_-]+))?\s*\]"#,
    )
    .expect("header");
    // A dependency table that ships: not dev-dependencies.
    let deps =
        regex::Regex::new(r#"^\[\s*(?:workspace\.|target\.[^\]]*\.)?(?:build-)?dependencies\s*\]"#)
            .expect("deps");
    let inline =
        regex::Regex::new(r#"^([A-Za-z0-9_-]+)\s*=\s*\{[^}]*\b(path|git)\s*=\s*"([^"]+)""#)
            .expect("inline");
    let dotted =
        regex::Regex::new(r#"^([A-Za-z0-9_-]+)\.(path|git)\s*=\s*"([^"]+)""#).expect("dotted");
    let table = regex::Regex::new(r#"^(path|git)\s*=\s*"([^"]+)""#).expect("table");
    let mut out = vec![];
    // (a `[patch]` table, the crate a `[patch.x.name]` table names)
    let mut section: Option<(bool, Option<String>)> = None;
    for (i, l) in lines.iter().enumerate() {
        let Some(l) = l else { continue };
        let t = l.trim();
        if t.starts_with('[') {
            section = header
                .captures(t)
                .map(|c| (true, c.get(1).map(|m| m.as_str().to_string())))
                .or_else(|| deps.is_match(t).then_some((false, None)));
            continue;
        }
        let Some((patch, crate_table)) = &section else {
            continue;
        };
        let hit = match crate_table {
            Some(name) => table
                .captures(t)
                .map(|c| (name.clone(), c[1].to_string(), c[2].to_string())),
            None => inline
                .captures(t)
                .or_else(|| dotted.captures(t))
                .map(|c| (c[1].to_string(), c[2].to_string(), c[3].to_string())),
        };
        // A `[patch]` entry counts with either source; a dependency only from git (a path
        // dependency is the workspace's own crate).
        if let Some((name, kind, value)) = hit
            && (*patch || kind == "git")
        {
            let source = if kind == "git" {
                format!("git:{value}")
            } else {
                value
            };
            out.push((i, name, source));
        }
    }
    out
}

/// The shell of a workflow or Makefile as bash, on its own lines; every other line is blank.
/// A block opens with `: proofscan-shell-block`, and with `set -o pipefail` when the host runs it
/// that way (`shell: bash` in a workflow, `.SHELLFLAGS` holding pipefail in a Makefile).
pub fn host_shell(src: &str, host: ShellHost) -> String {
    let lines: Vec<&str> = src.lines().collect();
    let mut out: Vec<String> = vec![String::new(); lines.len()];
    match host {
        ShellHost::Workflow => {
            let pipefail = lines.iter().any(|l| {
                let t = l.trim();
                t == "shell: bash" || t == "shell: bash -eo pipefail {0}"
            });
            let open = format!(
                ": {SHELL_BLOCK}{}",
                if pipefail { "; set -o pipefail" } else { "" }
            );
            let mut i = 0;
            while i < lines.len() {
                let l = lines[i];
                let t = l.trim_start();
                let t = t.strip_prefix("- ").map(str::trim_start).unwrap_or(t);
                let Some(rest) = t.strip_prefix("run:") else {
                    i += 1;
                    continue;
                };
                let indent = l.len() - l.trim_start().len();
                let rest = rest.trim();
                if rest.starts_with('|') || rest.starts_with('>') {
                    out[i] = open.clone();
                    let mut j = i + 1;
                    let mut block_indent = None;
                    while j < lines.len() {
                        let b = lines[j];
                        if b.trim().is_empty() {
                            j += 1;
                            continue;
                        }
                        let bi = b.len() - b.trim_start().len();
                        if bi <= indent {
                            break;
                        }
                        let bi = *block_indent.get_or_insert(bi);
                        let text = b.get(bi.min(b.len())..).unwrap_or("");
                        out[j] = advisory_marker(text).unwrap_or_else(|| text.to_string());
                        j += 1;
                    }
                    i = j;
                } else {
                    let cmd = rest.trim_matches(|c| c == '"' || c == '\'');
                    let cmd = advisory_marker(cmd).unwrap_or_else(|| cmd.to_string());
                    out[i] = format!("{open}; {cmd}");
                    i += 1;
                }
            }
        }
        ShellHost::Makefile => {
            let pipefail = lines
                .iter()
                .any(|l| l.contains(".SHELLFLAGS") && l.contains("pipefail"));
            let open = format!(
                ": {SHELL_BLOCK}{}",
                if pipefail { "; set -o pipefail" } else { "" }
            );
            for (i, l) in lines.iter().enumerate() {
                if let Some(r) = l.strip_prefix('\t') {
                    let cmd = r.trim_start_matches(['@', '-', '+']).replace("$$", "$");
                    out[i] = format!("{open}; {cmd}");
                }
            }
        }
        ShellHost::Manifest => {
            let manifest: Vec<Option<&str>> = lines.iter().map(|l| Some(*l)).collect();
            for (i, name, path) in path_patches(&manifest) {
                out[i] = format!(": {PATH_PATCH} '{name}' '{path}'");
            }
        }
        ShellHost::Diff => {
            // The new side of each hunk of a Cargo.toml: context and added lines.
            let mut manifest: Vec<Option<&str>> = vec![None; lines.len()];
            let mut in_manifest = false;
            let mut in_hunk = false;
            for (i, l) in lines.iter().enumerate() {
                if l.starts_with("diff ") {
                    in_manifest = false;
                    in_hunk = false;
                } else if let Some(p) = l.strip_prefix("+++ ") {
                    in_manifest = p.trim_end().ends_with("Cargo.toml");
                    in_hunk = false;
                } else if l.starts_with("@@") {
                    // A hunk starts in an unknown table until its own context names one.
                    in_hunk = true;
                    if in_manifest {
                        manifest[i] = Some("[");
                    }
                } else if in_manifest && in_hunk {
                    manifest[i] = l.strip_prefix('+').or_else(|| l.strip_prefix(' '));
                }
            }
            for (i, name, path) in path_patches(&manifest) {
                out[i] = format!(": {PATH_PATCH} '{name}' '{path}'");
            }
        }
    }
    out.join("\n")
}

pub fn extract(rel: &str, src: &str, lang: Lang) -> Facts {
    let hosted;
    let src = match shell_host(rel) {
        Some(h) => {
            hosted = host_shell(src, h);
            hosted.as_str()
        }
        None => src,
    };
    let mut facts = Facts::default();
    facts.files.push(File {
        path: rel.replace('\\', "/"),
        lang,
        test: is_test_path(rel),
        module: module_of(rel, lang),
        repo: 0,
    });
    let res = match lang {
        Lang::Python => python::extract(src, &mut facts),
        Lang::Rust => rust::extract(src, &mut facts),
        Lang::JavaScript | Lang::Bash | Lang::PowerShell => script::extract(src, lang, &mut facts),
    };
    if let Err(e) = res {
        facts.unparsed.push((rel.to_string(), e.to_string()));
    }
    facts
}

pub fn text<'a>(n: Node, src: &'a str) -> &'a str {
    &src[n.byte_range()]
}

pub fn line(n: Node) -> u32 {
    n.start_position().row as u32 + 1
}

/// Collapses whitespace so a callee split over lines matches a pattern.
pub fn squash(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join("")
}

pub fn children(n: Node) -> Vec<Node> {
    let mut c = n.walk();
    n.children(&mut c).collect()
}

pub fn named_children(n: Node) -> Vec<Node> {
    let mut c = n.walk();
    n.named_children(&mut c).collect()
}

/// Strips quotes and prefixes from a string literal's text.
pub fn unquote(s: &str) -> String {
    let s = s.trim_start_matches(|c: char| c.is_ascii_alphabetic());
    for q in ["\"\"\"", "'''", "\"", "'"] {
        if s.len() >= 2 * q.len() && s.starts_with(q) && s.ends_with(q) {
            return s[q.len()..s.len() - q.len()].to_string();
        }
    }
    s.to_string()
}
