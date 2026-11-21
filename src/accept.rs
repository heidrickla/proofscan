//! Acceptance: each known defect is flagged at its pre-fix commit by the question it was classed
//! under; each control's own change draws no violation; and each defect pattern, inserted into a
//! clean control, turns that control's verdict into a violation (a proof that cannot fail is a
//! defect of the scanner).

use crate::config::Config;
use crate::report::{Finding, Verdict};
use crate::scan::Source;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Deserialize)]
struct Cases {
    case: Vec<Case>,
}

#[derive(Deserialize, Clone)]
struct Case {
    id: String,
    /// defect, control or inject
    kind: String,
    /// The repository path; in the review-eval format `repo` is a name and `clone` the path.
    repo: String,
    #[serde(default)]
    clone: Option<String>,
    #[serde(alias = "review_at")]
    rev: String,
    /// The defect's files, from the review-eval format: an unclassed defect's candidates lie here.
    #[serde(default)]
    files: Vec<String>,
    #[serde(default)]
    scope: Vec<String>,
    /// Scan only what the change from this base touched, as `scan --diff` does: the rules that
    /// judge a change (a key new in it) need one. A control diffs against its parent regardless.
    #[serde(default)]
    diff: Option<String>,
    /// Configuration relative to the cases file.
    #[serde(default)]
    config: Option<String>,
    /// For a defect or an inject: what must be flagged.
    #[serde(default)]
    expect: Vec<Expect>,
    /// For an inject: (repo-relative file, snippet file relative to the cases file) appended in memory.
    #[serde(default)]
    inject: Option<(String, String)>,
    #[serde(default)]
    note: String,
    /// For a defect: the commit that fixed it, and whether its rule should still fire there.
    #[serde(default)]
    fix: Option<FixField>,
}

/// A fix is a table here and a bare commit in the review-eval format.
#[derive(Deserialize, Clone)]
#[serde(untagged)]
enum FixField {
    Rev(String),
    Full(Fix),
}

impl FixField {
    fn get(&self) -> Fix {
        match self {
            FixField::Rev(rev) => Fix {
                rev: rev.clone(),
                lines: None,
                expect: cleared(),
                note: String::new(),
            },
            FixField::Full(f) => f.clone(),
        }
    }
}

#[derive(Deserialize, Clone)]
struct Fix {
    rev: String,
    /// Lines at the fix the check is kept to; the whole file when absent.
    #[serde(default)]
    lines: Option<[u32; 2]>,
    /// "cleared" (the default) or "flagged" (the fix kept the construct the question flags).
    #[serde(default = "cleared")]
    expect: String,
    #[serde(default)]
    note: String,
}

fn cleared() -> String {
    "cleared".into()
}

#[derive(Deserialize, Serialize, Clone)]
struct Expect {
    question: u8,
    rule: String,
    /// The site or a witness step must lie in this file.
    file: String,
    /// And, when given, on a line in this inclusive range (the answer key's lines).
    #[serde(default)]
    lines: Option<[u32; 2]>,
    /// "violated" (the default); "proven": the construct is reported proven (a config's reason,
    /// or a closed domain); "unknown": reported unknown (a question the rule cannot settle must
    /// still be asked); "absent": no finding of the rule on these lines at all (a false
    /// positive that must stay gone).
    #[serde(default = "violated")]
    verdict: String,
}

fn violated() -> String {
    "violated".into()
}

#[derive(Serialize)]
struct Row {
    id: String,
    kind: String,
    pass: bool,
    /// An unclassed defect: reported for triage, not counted as a pass or a failure.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    open: bool,
    expected: String,
    got: String,
    note: String,
    /// The rules this row scores: a case's expected rules, or the rules a control flagged.
    #[serde(skip)]
    rules: Vec<String>,
}

fn hit(f: &Finding, e: &Expect) -> bool {
    (match e.verdict.as_str() {
        "proven" => f.verdict == Verdict::Proven,
        "unknown" => f.verdict == Verdict::Unknown,
        "absent" => true,
        _ => f.verdict == Verdict::Violated,
    }) && f.question == e.question
        && f.rule == e.rule
        && std::iter::once(&f.site)
            .chain(f.witness.iter())
            .any(|loc| at(loc, e))
}

/// A location `path:line ...` lies in the expected file and, when given, its line range.
fn at(loc: &str, e: &Expect) -> bool {
    if !loc.starts_with(&e.file) {
        return false;
    }
    let Some([lo, hi]) = e.lines else { return true };
    let head = loc.split_whitespace().next().unwrap_or("");
    head.rsplit_once(':')
        .and_then(|(_, n)| n.parse::<u32>().ok())
        .is_some_and(|n| (lo..=hi).contains(&n))
}

fn describe(expect: &[Expect]) -> String {
    expect
        .iter()
        .map(|e| {
            let v = match e.verdict.as_str() {
                "proven" => " proven",
                "unknown" => " unknown",
                "absent" => " absent",
                _ => "",
            };
            match e.lines {
                Some([lo, hi]) => format!("Q{} {}{v} in {}:{lo}-{hi}", e.question, e.rule, e.file),
                None => format!("Q{} {}{v} in {}", e.question, e.rule, e.file),
            }
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// The defect's rule at its fix commit: cleared from the answer key's lines, or still there
/// where the fix kept the construct the question flags.
fn fix_row(c: &Case, fx: &Fix, root: &Path, cfg: &Config) -> Result<Row> {
    let r = crate::scan_repo_overlay(
        &Source::Rev(root.to_path_buf(), fx.rev.clone()),
        cfg,
        &c.scope,
        None,
        &[],
    )?;
    let expect: Vec<Expect> = c
        .expect
        .iter()
        .map(|e| Expect {
            lines: fx.lines,
            ..e.clone()
        })
        .collect();
    let still: Vec<String> = expect
        .iter()
        .filter_map(|e| {
            r.findings
                .iter()
                .find(|f| hit(f, e))
                .map(|f| format!("Q{} {} {}", f.question, f.rule, f.site))
        })
        .collect();
    let want_cleared = fx.expect == "cleared";
    let pass = if want_cleared {
        still.is_empty()
    } else {
        still.len() == expect.len()
    };
    let short = &fx.rev[..fx.rev.len().min(8)];
    Ok(Row {
        open: false,
        id: format!("{}@fix", c.id),
        kind: "fix".into(),
        pass,
        expected: format!(
            "{} at {short}: {}",
            if want_cleared {
                "cleared"
            } else {
                "still flagged"
            },
            describe(&expect)
        ),
        got: if still.is_empty() {
            "cleared".into()
        } else {
            still.join("; ")
        },
        note: fx.note.clone(),
        rules: c.expect.iter().map(|e| e.rule.clone()).collect(),
    })
}

/// A defect nobody has classed yet (the escaped-defect loop): the candidates are the violations
/// in its files that its fix cleared or whose lines it changed; none means it escapes the questions.
fn open_row(c: &Case, at: &[Finding], root: &Path, cfg: &Config) -> Result<Row> {
    let in_files = |f: &&Finding| {
        f.verdict == Verdict::Violated
            && (c.files.is_empty() || c.files.iter().any(|p| f.site.starts_with(p.as_str())))
    };
    // A violation the fix cleared (matched by rule and message, since lines move), or one on a
    // line the fix changed. Either alone misses cases: a fix often edits a registration line
    // rather than the flagged effect, or leaves a same-worded violation elsewhere in the file.
    let key = |f: &Finding| {
        let file = f.site.rsplit_once(':').map_or(f.site.as_str(), |(p, _)| p);
        (f.question, f.rule, file.to_string(), f.message.clone())
    };
    let mut cands: Vec<String> = vec![];
    if let Some(fx) = &c.fix {
        let fix = fx.get().rev;
        let scan = |rev: &str, diff: Option<&str>| {
            crate::scan_repo_overlay(
                &Source::Rev(root.to_path_buf(), rev.to_string()),
                cfg,
                &c.scope,
                diff,
                &[],
            )
        };
        let after: Vec<_> = scan(&fix, None)?
            .findings
            .iter()
            .filter(in_files)
            .map(key)
            .collect();
        let changed = scan(&c.rev, Some(&fix))?.findings;
        for f in at.iter().filter(in_files) {
            if !after.contains(&key(f))
                || changed.iter().any(|g| g.site == f.site && g.rule == f.rule)
            {
                cands.push(format!("Q{} {} {}", f.question, f.rule, f.site));
            }
        }
    } else {
        cands = at
            .iter()
            .filter(in_files)
            .map(|f| format!("Q{} {} {}", f.question, f.rule, f.site))
            .collect();
    }
    Ok(Row {
        open: true,
        id: c.id.clone(),
        kind: "defect".into(),
        pass: false,
        expected:
            "unclassed: candidates are violations in its files that the fix cleared or touched"
                .into(),
        got: if cands.is_empty() {
            "none: escapes the questions".into()
        } else {
            cands.join("; ")
        },
        note: c.note.clone(),
        rules: vec![],
    })
}

pub fn run(cases_path: &Path, json: bool) -> Result<i32> {
    let rows = rows(cases_path)?;
    let pass = rows.iter().all(|r| r.pass || r.open);
    if json {
        println!("{}", serde_json::to_string_pretty(&rows)?);
    } else {
        print_rows(&rows);
    }
    Ok(if pass { 0 } else { 1 })
}

pub fn selfcheck() -> Result<i32> {
    use crate::facts::{Lang, RetryBound};

    let cases = [
        (
            true,
            "fresh",
            include_str!("../acceptance/inject/q6_counter_fresh.rs"),
        ),
        (
            true,
            "local",
            include_str!("../acceptance/inject/q6_counter_local.rs"),
        ),
        (
            false,
            "disconnected",
            include_str!("../acceptance/inject/q6_counter_disconnected.rs"),
        ),
        (
            false,
            "bypass",
            include_str!("../acceptance/inject/q6_counter_bypass.rs"),
        ),
        (
            false,
            "any_error",
            include_str!("../acceptance/inject/q6_counter_any_error.rs"),
        ),
        (
            false,
            "reset",
            include_str!("../acceptance/inject/q6_counter_reset.rs"),
        ),
        (
            false,
            "same_key",
            include_str!("../acceptance/inject/q6_counter_same_key.rs"),
        ),
        (
            false,
            "unrelated",
            include_str!("../acceptance/inject/q6_counter_unrelated.rs"),
        ),
    ];
    let mut passed = 0;
    for (fresh, name, src) in cases {
        let facts = crate::lang::extract(&format!("q6_counter_{name}.rs"), src, Lang::Rust);
        let ok = facts.unparsed.is_empty()
            && match facts.retries.as_slice() {
                [] => fresh,
                [retry] => !fresh && matches!(retry.bound, RetryBound::None),
                _ => false,
            };
        if ok {
            passed += 1;
        } else {
            eprintln!(
                "counter probe {name}: unexpected retry facts {:?}",
                facts.retries
            );
        }
    }
    println!("Rust counter probes: {passed}/{} passed", cases.len());
    Ok(i32::from(passed != cases.len()))
}

fn rows(cases_path: &Path) -> Result<Vec<Row>> {
    let dir = cases_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let cases: Cases =
        toml::from_str(&std::fs::read_to_string(cases_path)?).context("cases file")?;
    let mut rows = vec![];
    for c in &cases.case {
        let root = PathBuf::from(c.clone.as_ref().unwrap_or(&c.repo));
        let cfg_path = c.config.as_ref().map(|p| dir.join(p));
        let cfg = Config::load(&root, cfg_path.as_deref())?;
        let src = Source::Rev(root.clone(), c.rev.clone());
        let overlay: Vec<(String, String)> = match &c.inject {
            Some((file, snippet)) => vec![(
                file.clone(),
                std::fs::read_to_string(dir.join(snippet))
                    .with_context(|| format!("snippet {snippet}"))?,
            )],
            None => vec![],
        };
        let diff = c
            .diff
            .clone()
            .or_else(|| (c.kind == "control").then(|| format!("{}^", c.rev)));
        let r = crate::scan_repo_overlay(&src, &cfg, &c.scope, diff.as_deref(), &overlay);
        let row = match r {
            Err(e) => Row {
                open: false,
                id: c.id.clone(),
                kind: c.kind.clone(),
                pass: false,
                expected: String::new(),
                got: format!("could not run: {e:#}"),
                note: c.note.clone(),
                rules: c.expect.iter().map(|e| e.rule.clone()).collect(),
            },
            Ok(r) => {
                let violated: Vec<&Finding> = r
                    .findings
                    .iter()
                    .filter(|f| f.verdict == Verdict::Violated)
                    .collect();
                let got: Vec<String> = violated
                    .iter()
                    .map(|f| format!("Q{} {} {}", f.question, f.rule, f.site))
                    .collect();
                match c.kind.as_str() {
                    "defect" if c.expect.is_empty() => open_row(c, &r.findings, &root, &cfg)?,
                    "control" => Row {
                        open: false,
                        id: c.id.clone(),
                        kind: c.kind.clone(),
                        pass: violated.is_empty(),
                        expected: "no violation in the change".into(),
                        got: if got.is_empty() {
                            "none".into()
                        } else {
                            got.join("; ")
                        },
                        note: c.note.clone(),
                        rules: violated.iter().map(|f| f.rule.to_string()).collect(),
                    },
                    _ => {
                        // An inject must add the violation: a site the clean control already has does not count.
                        let base: Vec<String> = if c.kind == "inject" {
                            crate::scan_repo_overlay(&src, &cfg, &c.scope, None, &[])?
                                .findings
                                .iter()
                                .filter(|f| f.verdict == Verdict::Violated)
                                .map(|f| f.site.clone())
                                .collect()
                        } else {
                            vec![]
                        };
                        let found = |e: &Expect| {
                            r.findings
                                .iter()
                                .find(|f| hit(f, e) && !base.contains(&f.site))
                        };
                        // An absent expectation is missed when a finding is there.
                        let missing: Vec<&Expect> = c
                            .expect
                            .iter()
                            .filter(|e| found(e).is_some() == (e.verdict == "absent"))
                            .collect();
                        let matched: Vec<String> = c
                            .expect
                            .iter()
                            .filter_map(|e| match (e.verdict.as_str(), found(e)) {
                                ("absent", None) => {
                                    Some(format!("Q{} {} absent", e.question, e.rule))
                                }
                                ("absent", Some(_)) | (_, None) => None,
                                (_, Some(f)) => {
                                    Some(format!("Q{} {} {}", f.question, f.rule, f.site))
                                }
                            })
                            .collect();
                        let gotline = if missing.is_empty() {
                            matched.join("; ")
                        } else {
                            format!(
                                "missing {}; flagged: {}",
                                missing
                                    .iter()
                                    .map(|e| format!("Q{} {}", e.question, e.rule))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                if got.is_empty() {
                                    "none".into()
                                } else {
                                    got.join("; ")
                                }
                            )
                        };
                        Row {
                            open: false,
                            id: c.id.clone(),
                            kind: c.kind.clone(),
                            pass: missing.is_empty(),
                            expected: describe(&c.expect),
                            got: gotline,
                            note: c.note.clone(),
                            rules: c.expect.iter().map(|e| e.rule.clone()).collect(),
                        }
                    }
                }
            }
        };
        let open = row.open;
        rows.push(row);
        if let Some(fx) = c.fix.as_ref().filter(|_| !open) {
            rows.push(fix_row(c, &fx.get(), &root, &cfg)?);
        }
    }
    Ok(rows)
}

fn print_rows(rows: &[Row]) {
    {
        println!("| case | kind | result | expected | flagged |");
        println!("|---|---|---|---|---|");
        for r in rows {
            println!(
                "| {} | {} | {} | {} | {} |",
                r.id,
                r.kind,
                if r.open {
                    "open"
                } else if r.pass {
                    "pass"
                } else {
                    "FAIL"
                },
                r.expected,
                r.got.replace('|', "/")
            );
        }
        let open = rows.iter().filter(|r| r.open).count();
        println!(
            "\n{} of {} cases pass{}",
            rows.iter().filter(|r| r.pass && !r.open).count(),
            rows.len() - open,
            if open > 0 {
                format!("; {open} open (unclassed defects, not counted)")
            } else {
                String::new()
            }
        );
    }
}

/// One review outcome for a violation: a reviewer or a fix confirmed it, or it was a false positive.
#[derive(Deserialize, Serialize)]
pub struct Outcome {
    pub date: String,
    pub rule: String,
    pub site: String,
    /// "confirmed" or "false".
    pub outcome: String,
    #[serde(default)]
    pub note: String,
}

#[derive(Default, Serialize)]
struct Score {
    rule: String,
    /// Defect and inject cases whose violation the rule reports.
    caught: usize,
    /// Defect and inject cases it misses.
    missed: usize,
    /// Precision cases it gets right (proven or silent where it should be) and fixes it clears.
    held: usize,
    /// Precision cases it gets wrong and violations on a clean control.
    false_cases: usize,
    /// Ledger outcomes: violations a review confirmed, and ones that were false.
    confirmed: usize,
    false_review: usize,
}

/// The ledger beside the cases file unless named: one JSON outcome per line.
pub fn ledger_path(cases: &Path, ledger: Option<&Path>) -> PathBuf {
    ledger.map(Path::to_path_buf).unwrap_or_else(|| {
        cases
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default()
            .join("outcomes.jsonl")
    })
}

pub fn record(ledger: &Path, o: &Outcome) -> Result<()> {
    if o.outcome != "confirmed" && o.outcome != "false" {
        anyhow::bail!("an outcome is confirmed or false, not {}", o.outcome);
    }
    use std::io::Write;
    let mut fh = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(ledger)
        .with_context(|| format!("ledger {}", ledger.display()))?;
    writeln!(fh, "{}", serde_json::to_string(o)?)?;
    Ok(())
}

/// Per rule: the acceptance cases it catches, misses, holds and gets wrong, and the review outcomes
/// in the ledger; the rule's precision is its hits over its hits and false positives.
pub fn tally(cases: &[PathBuf], ledger: Option<&Path>, json: bool) -> Result<i32> {
    let mut by: std::collections::BTreeMap<String, Score> = Default::default();
    fn entry<'m>(by: &'m mut std::collections::BTreeMap<String, Score>, r: &str) -> &'m mut Score {
        let s = by.entry(r.to_string()).or_default();
        s.rule = r.to_string();
        s
    }
    for path in cases {
        for row in rows(path)? {
            if row.open {
                continue;
            }
            let mut rules = row.rules.clone();
            rules.sort();
            rules.dedup();
            for r in &rules {
                let s = entry(&mut by, r);
                match (row.kind.as_str(), row.pass) {
                    ("defect" | "inject", true) => s.caught += 1,
                    ("defect" | "inject", false) => s.missed += 1,
                    ("precision" | "fix", true) => s.held += 1,
                    ("precision" | "fix", false) | ("control", _) => s.false_cases += 1,
                    _ => {}
                }
            }
        }
    }
    let lp = ledger_path(&cases[0], ledger);
    if let Ok(text) = std::fs::read_to_string(&lp) {
        for (i, line) in text
            .lines()
            .enumerate()
            .filter(|(_, l)| !l.trim().is_empty())
        {
            let o: Outcome = serde_json::from_str(line)
                .with_context(|| format!("{}:{}", lp.display(), i + 1))?;
            let s = entry(&mut by, &o.rule);
            if o.outcome == "confirmed" {
                s.confirmed += 1;
            } else {
                s.false_review += 1;
            }
        }
    }
    let scores: Vec<&Score> = by.values().collect();
    if json {
        println!("{}", serde_json::to_string_pretty(&scores)?);
        return Ok(0);
    }
    println!(
        "| rule | caught | missed | held | false (cases) | confirmed | false (reviews) | precision |"
    );
    println!("|---|---|---|---|---|---|---|---|");
    for s in &scores {
        let hits = s.caught + s.confirmed;
        let wrong = s.false_cases + s.false_review;
        let precision = if hits + wrong == 0 {
            "-".to_string()
        } else {
            format!("{:.0}%", 100.0 * hits as f64 / (hits + wrong) as f64)
        };
        println!(
            "| {} | {} | {} | {} | {} | {} | {} | {precision} |",
            s.rule, s.caught, s.missed, s.held, s.false_cases, s.confirmed, s.false_review
        );
    }
    println!("\nledger: {}", lp.display());
    Ok(0)
}

/// Today's date in UTC, `YYYY-MM-DD`, from the system clock (civil-from-days).
pub fn today() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0) as i64;
    let z = secs.div_euclid(86_400) + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}")
}
