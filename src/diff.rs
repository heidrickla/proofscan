//! Lines a diff adds or changes, for gate mode: a finding counts when its site or a witness step
//! lies on one of them.

use crate::report::Finding;
use anyhow::{Result, bail};
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::process::Command;

pub type Changed = HashMap<String, HashSet<u32>>;

pub fn changed_lines(root: &Path, base: &str, rev: Option<&str>) -> Result<Changed> {
    let mut cmd = Command::new("git");
    cmd.arg("-C")
        .arg(root)
        .args(["diff", "-U0", "--no-color", "--no-ext-diff"]);
    match rev {
        Some(r) => cmd.arg(format!("{base}..{r}")),
        None => cmd.arg(base),
    };
    let out = cmd.output()?;
    if !out.status.success() {
        bail!(
            "git diff {base}: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(parse(&String::from_utf8_lossy(&out.stdout)))
}

pub fn parse(text: &str) -> Changed {
    let mut out: Changed = HashMap::new();
    let mut file: Option<String> = None;
    for l in text.lines() {
        if let Some(p) = l.strip_prefix("+++ ") {
            file = p.strip_prefix("b/").map(str::to_string);
        } else if let Some(h) = l.strip_prefix("@@ ")
            && let Some(f) = &file
        {
            let plus = h
                .split_whitespace()
                .find(|t| t.starts_with('+'))
                .unwrap_or("+0");
            let mut it = plus[1..].split(',');
            let start: u32 = it.next().and_then(|x| x.parse().ok()).unwrap_or(0);
            let count: u32 = it.next().and_then(|x| x.parse().ok()).unwrap_or(1);
            let set = out.entry(f.clone()).or_default();
            for n in start..start + count {
                set.insert(n);
            }
        }
    }
    out
}

fn on(changed: &Changed, loc: &str) -> bool {
    let Some((path, rest)) = loc.rsplit_once(':') else {
        return false;
    };
    let line: u32 = rest
        .split_whitespace()
        .next()
        .and_then(|x| x.parse().ok())
        .unwrap_or(0);
    changed.get(path).is_some_and(|s| s.contains(&line))
}

/// The finding's own site is on a changed line.
pub fn on_site(changed: &Changed, f: &Finding) -> bool {
    on(changed, &f.site)
}

/// A finding's identity across commits, where lines move: question, rule, file and message.
pub fn key(f: &Finding) -> (u8, &'static str, String, String) {
    let file = f.site.rsplit_once(':').map_or(f.site.as_str(), |(p, _)| p);
    (f.question, f.rule, file.to_string(), f.message.clone())
}

pub fn touches(changed: &Changed, f: &Finding) -> bool {
    on(changed, &f.site)
        || f.witness.iter().any(|w| {
            w.split_whitespace()
                .next()
                .is_some_and(|loc| on(changed, loc))
        })
}

/// The commit the current branch's upstream points at (`@{upstream}`), as a full id.
pub fn upstream(root: &Path) -> Result<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "--verify", "-q", "@{upstream}"])
        .output()?;
    let id = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if !out.status.success() || id.is_empty() {
        bail!("{} has no upstream branch", root.display());
    }
    Ok(id)
}

/// Whether `name` appears anywhere in the tree at `base` (a fixed-string `git grep`). An error
/// reads as present, so a failed look never makes a store new.
pub fn in_base(root: &Path, base: &str, name: &str) -> bool {
    Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["grep", "-q", "-F", "-e", name, base, "--"])
        .status()
        .map(|s| s.success())
        .unwrap_or(true)
}

/// Keys a change starts reading: a `["key"]` or `.get("key")` on a changed line whose quoted
/// literal appears nowhere in the base, with the value it is read from. A stored file the previous
/// release wrote lacks them.
pub fn new_keys(
    root: &Path,
    base: &str,
    changed: &Changed,
    texts: &[(String, String)],
) -> Vec<(String, u32, String, String, bool)> {
    let re = regex::Regex::new(
        r#"([A-Za-z_][\w.]*)(?:\[\s*["']([A-Za-z_][\w-]*)["']\s*\]|\.get\(\s*["']([A-Za-z_][\w-]*)["'])"#,
    )
    .expect("key");
    let mut at_base: HashMap<String, bool> = HashMap::new();
    let mut out = vec![];
    for (path, text) in texts {
        let Some(lines) = changed.get(path) else {
            continue;
        };
        if crate::lang::is_test_path(path) || !path.ends_with(".py") {
            continue;
        }
        let all: Vec<&str> = text.lines().collect();
        let mut ns: Vec<&u32> = lines.iter().collect();
        ns.sort();
        for &n in ns {
            let Some(l) = all.get(n as usize - 1) else {
                continue;
            };
            for m in re.captures_iter(l) {
                let Some(k) = m.get(2).or(m.get(3)).map(|x| x.as_str().to_string()) else {
                    continue;
                };
                // `doc["k"] = v` and `doc["k"] += v` write the key; only a read counts.
                let after = l[m.get(0).map_or(0, |x| x.end())..].trim_start();
                let assigned = after.starts_with('=') && !after.starts_with("==")
                    || after.starts_with(['+', '-', '*', '/', '|', '&', '%'])
                        && after[1..].starts_with('=');
                if assigned {
                    continue;
                }
                let base_var = m.get(1).map_or("", |x| x.as_str()).to_string();
                let seen = *at_base.entry(k.clone()).or_insert_with(|| {
                    Command::new("git")
                        .arg("-C")
                        .arg(root)
                        .args([
                            "grep",
                            "-q",
                            "-F",
                            "-e",
                            &format!("\"{k}\""),
                            "-e",
                            &format!("'{k}'"),
                            base,
                            "--",
                        ])
                        .status()
                        .map(|s| s.success())
                        .unwrap_or(true)
                });
                if !seen {
                    out.push((path.clone(), n, k, base_var, m.get(2).is_some()));
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hunks_give_new_lines() {
        let d = "+++ b/a.py\n@@ -1,0 +2,3 @@\n+x\n@@ -9 +12 @@\n+y\n+++ b/b.py\n@@ -3,2 +3,0 @@\n";
        let c = parse(d);
        assert_eq!(c["a.py"], HashSet::from([2, 3, 4, 12]));
        assert!(c["b.py"].is_empty());
    }
}
