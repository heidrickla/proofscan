//! Review focus. For a change, the unknowns become the reviewer's scope (the constructs no proof
//! covers), the violations are handed over as found, and the proven sites are listed with what
//! each proof rests on. Given a reviewer's findings, each is checked against the verdicts at its
//! line: a finding is rejected on proof only where a proven verdict covers that line, and only for
//! that question; everywhere else it stands on its own evidence.

use crate::report::{Finding, Report, TITLES, Verdict};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::Path;

/// One reviewer finding: its `file`, `line` and `title`, read from either
/// its whole output (`{"findings": [...]}`) or a bare array.
#[derive(Deserialize)]
pub struct ReviewerFinding {
    #[serde(default)]
    pub id: String,
    #[serde(default)]
    pub title: String,
    pub file: String,
    pub line: u32,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum FindingsFile {
    Wrapped { findings: Vec<ReviewerFinding> },
    Bare(Vec<ReviewerFinding>),
}

pub fn load_findings(path: &Path) -> Result<Vec<ReviewerFinding>> {
    let text = std::fs::read_to_string(path).with_context(|| format!("{}", path.display()))?;
    Ok(
        match serde_json::from_str(&text).context("reviewer findings")? {
            FindingsFile::Wrapped { findings } | FindingsFile::Bare(findings) => findings,
        },
    )
}

#[derive(Serialize)]
pub struct Item {
    pub question: u8,
    pub title: &'static str,
    pub rule: &'static str,
    pub site: String,
    pub message: String,
    pub assumptions: Vec<String>,
}

#[derive(Serialize)]
pub struct Check {
    pub id: String,
    pub title: String,
    pub at: String,
    /// "contradicted-by-proof", "confirmed-by-violation", "no-proof" or "unknown-here".
    pub outcome: &'static str,
    pub detail: String,
}

#[derive(Serialize)]
pub struct Scope {
    pub diff: Option<String>,
    /// Constructs no proof covers: the reviewer reads these.
    pub review: Vec<Item>,
    pub violated: Vec<Item>,
    /// Settled by proof: re-raise only by naming the assumption that fails.
    pub proven: Vec<Item>,
    pub checks: Vec<Check>,
}

fn item(f: &Finding) -> Item {
    Item {
        question: f.question,
        title: TITLES[f.question as usize - 1],
        rule: f.rule,
        site: f.site.clone(),
        message: f.message.clone(),
        assumptions: f.assumptions.clone(),
    }
}

/// `path:line` and `path:line what` locations, split.
fn loc(s: &str) -> Option<(&str, u32)> {
    let head = s.split_whitespace().next()?;
    let (p, n) = head.rsplit_once(':')?;
    Some((p, n.parse().ok()?))
}

/// The verdict's site, or one of its witness steps, is on the finding's line (two lines either
/// way, since a reviewer and the scanner may name different lines of one statement).
fn near(f: &Finding, file: &str, line: u32) -> bool {
    let file = file.replace('\\', "/");
    std::iter::once(&f.site)
        .chain(f.witness.iter())
        .filter_map(|s| loc(s))
        .any(|(p, n)| p == file && n.abs_diff(line) <= 2)
}

fn check(r: &Report, rf: &ReviewerFinding) -> Check {
    let here: Vec<&Finding> = r
        .findings
        .iter()
        .filter(|f| near(f, &rf.file, rf.line))
        .collect();
    let of = |v: Verdict| -> Vec<&&Finding> { here.iter().filter(|f| f.verdict == v).collect() };
    let name = |f: &Finding| format!("Q{} {} {}", f.question, f.rule, f.site);
    let (outcome, detail) = if let Some(v) = of(Verdict::Violated).first() {
        (
            "confirmed-by-violation",
            format!("{}: {}", name(v), v.message),
        )
    } else if !of(Verdict::Proven).is_empty() {
        let p = of(Verdict::Proven);
        (
            "contradicted-by-proof",
            p.iter()
                .map(|f| {
                    format!(
                        "{} proves {} resting on: {}; reject only if the finding is a Q{} claim and its scenario breaks none of these",
                        name(f),
                        TITLES[f.question as usize - 1].to_lowercase(),
                        f.assumptions.join("; "),
                        f.question
                    )
                })
                .collect::<Vec<_>>()
                .join(" | "),
        )
    } else if let Some(u) = of(Verdict::Unknown).first() {
        (
            "unknown-here",
            format!(
                "{}: {}; no proof either way, the finding stands on its evidence",
                name(u),
                u.message
            ),
        )
    } else {
        (
            "no-proof",
            "no verdict at this line; the finding stands on its evidence".into(),
        )
    };
    Check {
        id: rf.id.clone(),
        title: rf.title.clone(),
        at: format!("{}:{}", rf.file, rf.line),
        outcome,
        detail,
    }
}

pub fn scope(r: &Report, findings: &[ReviewerFinding]) -> Scope {
    let pick = |v: Verdict| -> Vec<Item> {
        r.findings
            .iter()
            .filter(|f| f.verdict == v)
            .map(item)
            .collect()
    };
    Scope {
        diff: r.diff.clone(),
        review: pick(Verdict::Unknown),
        violated: pick(Verdict::Violated),
        proven: pick(Verdict::Proven),
        checks: findings.iter().map(|f| check(r, f)).collect(),
    }
}

impl Scope {
    pub fn human(&self) -> String {
        let mut out = String::new();
        let list = |out: &mut String, head: &str, items: &[Item], why: bool| {
            out.push_str(&format!("{head} ({})\n", items.len()));
            for i in items {
                out.push_str(&format!(
                    "- {} Q{} {}: {}\n",
                    i.site, i.question, i.rule, i.message
                ));
                if why && !i.assumptions.is_empty() {
                    out.push_str(&format!("  rests on: {}\n", i.assumptions.join("; ")));
                }
            }
        };
        list(
            &mut out,
            "Review these: no proof covers them",
            &self.review,
            false,
        );
        list(&mut out, "Violations", &self.violated, false);
        list(
            &mut out,
            "Settled by proof: re-raise only by naming the assumption that fails",
            &self.proven,
            true,
        );
        if !self.checks.is_empty() {
            out.push_str(&format!("Reviewer findings ({})\n", self.checks.len()));
            for c in &self.checks {
                out.push_str(&format!(
                    "- {} {} [{}]: {}\n",
                    c.at, c.title, c.outcome, c.detail
                ));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(question: u8, verdict: Verdict, site: &str) -> Finding {
        Finding {
            question,
            rule: "r",
            verdict,
            repo: "x".into(),
            site: site.into(),
            message: "m".into(),
            witness: vec![],
            assumptions: vec!["a".into()],
        }
    }

    fn report(findings: Vec<Finding>) -> Report {
        Report {
            build: crate::report::BUILD,
            repos: vec![],
            profiles: vec![],
            files: 0,
            functions: 0,
            unparsed: vec![],
            diff: Some("base".into()),
            questions: vec![],
            findings,
            millis: 0,
        }
    }

    fn rf(file: &str, line: u32) -> ReviewerFinding {
        ReviewerFinding {
            id: "F1".into(),
            title: "t".into(),
            file: file.into(),
            line,
        }
    }

    #[test]
    fn each_outcome_follows_the_verdict_on_the_line() {
        let r = report(vec![
            f(4, Verdict::Proven, "a.py:10 handler"),
            f(1, Verdict::Violated, "b.py:20"),
            f(6, Verdict::Unknown, "c.py:30"),
        ]);
        let out = scope(
            &r,
            &[
                rf("a.py", 11),
                rf("b.py", 20),
                rf("c.py", 30),
                rf("a.py", 40),
            ],
        );
        let got: Vec<&str> = out.checks.iter().map(|c| c.outcome).collect();
        assert_eq!(
            got,
            [
                "contradicted-by-proof",
                "confirmed-by-violation",
                "unknown-here",
                "no-proof"
            ]
        );
        assert_eq!(out.review.len(), 1);
        assert_eq!(out.violated.len(), 1);
        assert_eq!(out.proven.len(), 1);
    }

    #[test]
    fn a_violation_outranks_a_proof_on_the_same_line() {
        let r = report(vec![
            f(4, Verdict::Proven, "a.py:10"),
            f(9, Verdict::Violated, "a.py:10"),
        ]);
        assert_eq!(
            scope(&r, &[rf("a.py", 10)]).checks[0].outcome,
            "confirmed-by-violation"
        );
    }

    #[test]
    fn both_findings_file_shapes_load() {
        let d = std::env::temp_dir().join(format!("ps-review-{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        let a = d.join("a.json");
        let b = d.join("b.json");
        std::fs::write(&a, r#"{"summary":"s","findings":[{"id":"F1","title":"t","file":"x.py","line":3,"severity":"high"}]}"#).unwrap();
        std::fs::write(&b, r#"[{"file":"x.py","line":3}]"#).unwrap();
        assert_eq!(load_findings(&a).unwrap()[0].line, 3);
        assert_eq!(load_findings(&b).unwrap()[0].file, "x.py");
        let _ = std::fs::remove_dir_all(&d);
    }
}
