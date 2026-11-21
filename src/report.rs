//! Findings, per-question summaries, JSON and the terse human report.

use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Verdict {
    Proven,
    Unknown,
    Violated,
}

impl Verdict {
    pub fn word(self) -> &'static str {
        match self {
            Verdict::Proven => "proven",
            Verdict::Unknown => "unknown",
            Verdict::Violated => "violated",
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub question: u8,
    pub rule: &'static str,
    pub verdict: Verdict,
    pub repo: String,
    /// `path:line` of the site the verdict is about.
    pub site: String,
    pub message: String,
    /// The path that shows it: each step `path:line what`.
    pub witness: Vec<String>,
    /// What the verdict rests on.
    pub assumptions: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Question {
    pub question: u8,
    pub title: &'static str,
    pub verdict: Verdict,
    pub proven: usize,
    pub violated: usize,
    pub unknown: usize,
    /// Why the whole question is unknown when nothing in the repo could be checked against it.
    pub not_checked: Vec<String>,
    pub assumptions: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Report {
    /// The proofscan version and the commit it was built from.
    pub build: &'static str,
    pub repos: Vec<String>,
    pub profiles: Vec<String>,
    pub files: usize,
    pub functions: usize,
    pub unparsed: Vec<(String, String)>,
    pub diff: Option<String>,
    pub questions: Vec<Question>,
    pub findings: Vec<Finding>,
    pub millis: u128,
}

/// The version and commit of this build, as `--version` gives them.
pub const BUILD: &str = concat!(env!("CARGO_PKG_VERSION"), " ", env!("PROOFSCAN_COMMIT"));

pub const TITLES: [&str; 10] = [
    "One source per fact",
    "Provenance of stand-ins",
    "Check and use together",
    "Guard at the effect",
    "Closed sets",
    "Bounds and exits",
    "Proof by effect",
    "Tests that can fail",
    "Release on every exit",
    "Secrets never reach a sink",
];

pub const ASSUMPTIONS: [&[&str]; 10] = [
    &[
        "provider patterns name every call that reads a provider",
        "a call with no in-repo target neither reads a provider nor calls back into the repository",
    ],
    &[
        "wire patterns name every literal that stands in for a reply",
        "a capture under a declared capture path came from the real thing",
    ],
    &[
        "a guard reads what it verifies through calls the model sees",
        "effect patterns name every effect",
    ],
    &[
        "entry, guard and effect patterns are complete",
        "a guard call raises, or decides an early exit, when the check fails",
    ],
    &[
        "a parameter of a public function is outside input",
        "closed-parse patterns accept only members of a closed set",
    ],
    &[
        "resource patterns name every durable resource",
        "retry loops are recognized by their shape",
    ],
    &["weak-probe patterns name the probes whose reply cannot show the state"],
    &[
        "the test command exercises the changed rule",
        "a mutant that does not compile is not counted",
    ],
    &[
        "resource patterns name every acquire and release",
        "any call can raise or, in async code, be cancelled",
    ],
    &[
        "source patterns name every credential read",
        "sink patterns name every log, argument, error text and child process",
    ],
];

pub fn summarize(findings: &[Finding], not_checked: &BTreeMap<u8, Vec<String>>) -> Vec<Question> {
    (1..=10u8)
        .map(|q| {
            let mine: Vec<&Finding> = findings.iter().filter(|f| f.question == q).collect();
            let count = |v: Verdict| mine.iter().filter(|f| f.verdict == v).count();
            let (proven, violated, unknown) = (
                count(Verdict::Proven),
                count(Verdict::Violated),
                count(Verdict::Unknown),
            );
            let nc = not_checked.get(&q).cloned().unwrap_or_default();
            let verdict = if violated > 0 {
                Verdict::Violated
            } else if unknown > 0 || !nc.is_empty() {
                Verdict::Unknown
            } else {
                Verdict::Proven
            };
            Question {
                question: q,
                title: TITLES[q as usize - 1],
                verdict,
                proven,
                violated,
                unknown,
                not_checked: nc,
                assumptions: ASSUMPTIONS[q as usize - 1].to_vec(),
            }
        })
        .collect()
}

/// Reports of one repository each, joined as one sweep: sites carry their repository, and a
/// question no repository could check carries every repository's reason.
pub fn join(parts: Vec<Report>, questions: &[u8], profiles: Vec<String>) -> Report {
    let mut out = Report {
        build: BUILD,
        repos: vec![],
        profiles,
        files: 0,
        functions: 0,
        unparsed: vec![],
        diff: None,
        questions: vec![],
        findings: vec![],
        millis: 0,
    };
    let mut not_checked: BTreeMap<u8, Vec<String>> = BTreeMap::new();
    for part in parts {
        let name = part.repos.first().cloned().unwrap_or_default();
        out.repos.extend(part.repos);
        out.files += part.files;
        out.functions += part.functions;
        out.unparsed.extend(part.unparsed);
        out.millis += part.millis;
        for q in part.questions {
            for why in q.not_checked {
                not_checked
                    .entry(q.question)
                    .or_default()
                    .push(format!("{name}: {why}"));
            }
        }
        out.findings.extend(part.findings.into_iter().map(|mut f| {
            f.site = format!("{}/{}", f.repo, f.site);
            f
        }));
    }
    out.findings.sort_by(|a, b| {
        (
            a.question, b.verdict, &a.site, &a.rule, &a.message, &a.witness,
        )
            .cmp(&(
                b.question, a.verdict, &b.site, &b.rule, &b.message, &b.witness,
            ))
    });
    let mut qs = summarize(&out.findings, &not_checked);
    if !questions.is_empty() {
        qs.retain(|q| questions.contains(&q.question));
    }
    if !questions.contains(&8) {
        qs.retain(|q| q.question != 8);
    }
    out.questions = qs;
    out
}

impl Report {
    pub fn exit_code(&self, unknown_fails: bool) -> i32 {
        if self.findings.iter().any(|f| f.verdict == Verdict::Violated) {
            1
        } else if unknown_fails && self.findings.iter().any(|f| f.verdict == Verdict::Unknown) {
            2
        } else {
            0
        }
    }

    pub fn human(&self, all: bool) -> String {
        let mut out = String::new();
        let scope = match &self.diff {
            Some(d) => format!(", findings in the diff {d}"),
            None => String::new(),
        };
        out.push_str(&format!(
            "proofscan {}: {} ({} files, {} functions, {} ms{}){}\n",
            self.build,
            self.repos.join(", "),
            self.files,
            self.functions,
            self.millis,
            scope,
            if self.profiles.is_empty() {
                String::new()
            } else {
                format!(", profiles {}", self.profiles.join(", "))
            }
        ));
        for q in &self.questions {
            let state = match q.verdict {
                Verdict::Proven => "proven",
                Verdict::Violated => "VIOLATED",
                Verdict::Unknown => "unknown",
            };
            out.push_str(&format!(
                "Q{} {:<24} {:<8} proven {} violated {} unknown {}",
                q.question, q.title, state, q.proven, q.violated, q.unknown
            ));
            if !q.not_checked.is_empty() {
                out.push_str(&format!("; not checked: {}", q.not_checked.join("; ")));
            }
            out.push('\n');
        }
        for f in &self.findings {
            if f.verdict == Verdict::Proven && !all {
                continue;
            }
            let v = match f.verdict {
                Verdict::Proven => "proven",
                Verdict::Violated => "violated",
                Verdict::Unknown => "unknown",
            };
            out.push_str(&format!(
                "\nQ{} {} {} {}: {}\n",
                f.question, v, f.rule, f.site, f.message
            ));
            for w in &f.witness {
                out.push_str(&format!("    {w}\n"));
            }
            for a in &f.assumptions {
                out.push_str(&format!("    assumes {a}\n"));
            }
        }
        for (p, why) in &self.unparsed {
            out.push_str(&format!("\nunparsed {p}: {why}\n"));
        }
        out
    }
}
