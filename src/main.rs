mod accept;
mod analysis;
mod config;
mod diff;
mod facts;
mod lang;
mod mutate;
#[cfg(feature = "smt")]
mod policy;
mod report;
mod resolve;
mod review;
mod scan;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use config::Config;
use report::Report;
use scan::Source;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Parser)]
#[command(
    name = "proofscan",
    version = report::BUILD,
    about = "Three-valued verdicts for classes of defect: proven, violated or unknown"
)]
struct Cli {
    /// Parse every file again instead of reusing facts cached by content.
    #[arg(long, global = true)]
    no_cache: bool,
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Scan one repository (working tree, or a commit with --rev).
    Scan {
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Read files from this commit instead of the working tree.
        #[arg(long)]
        rev: Option<String>,
        /// Keep only findings whose site or witness lies on a line changed since this commit.
        #[arg(long)]
        diff: Option<String>,
        /// Configuration file (default: <path>/proofscan.toml when present).
        #[arg(long)]
        config: Option<PathBuf>,
        /// Repo-relative paths to scan (default: all).
        #[arg(long)]
        scope: Vec<String>,
        /// Only these questions.
        #[arg(long, short)]
        question: Vec<u8>,
        #[arg(long)]
        json: bool,
        /// Also list proven sites.
        #[arg(long)]
        all: bool,
    },
    /// The RCA sweep: every site of the given questions across repositories, with its verdict.
    Sweep {
        /// Only these questions (default: all but 8, which needs a test command).
        #[arg(long, short)]
        question: Vec<u8>,
        /// Repositories as PATH or PATH@REV.
        #[arg(required = true)]
        repos: Vec<String>,
        #[arg(long)]
        json: bool,
        /// Also list proven sites.
        #[arg(long)]
        all: bool,
        /// Answer the repositories as one program, so calls resolve from one into another. Without
        /// it each repository is answered alone, which holds one repository in memory at a time.
        #[arg(long)]
        one_program: bool,
    },
    /// Question 8: mutate each rule a diff changed and run the tests; a surviving mutant is a test that cannot fail.
    Mutate {
        #[arg(default_value = ".")]
        path: PathBuf,
        #[arg(long)]
        diff: String,
        /// The test command, run in a pristine copy of the commit with the mutant applied.
        #[arg(long, default_value = "")]
        test: String,
        #[arg(long)]
        rev: Option<String>,
        /// Seconds per test run.
        #[arg(long, default_value_t = 600)]
        timeout: u64,
        #[arg(long)]
        json: bool,
        /// List the mutants the diff gives, without running the tests.
        #[arg(long)]
        list: bool,
        /// Only the mutants on these lines (`path:line`, repeated or comma separated).
        #[arg(long, value_delimiter = ',')]
        at: Vec<String>,
    },
    /// Compare a policy with a reference by SMT: proves it grants no more, or gives a counterexample.
    #[cfg(feature = "smt")]
    Policy {
        #[arg(long)]
        kind: String,
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        reference: PathBuf,
        #[arg(long)]
        json: bool,
    },
    /// Review focus for a change: unknowns as the reviewer's scope, violations, and proven sites
    /// with their assumptions; with --findings, each reviewer finding checked against them.
    Review {
        #[arg(default_value = ".")]
        path: PathBuf,
        /// The base the change is measured from.
        #[arg(long)]
        diff: String,
        #[arg(long)]
        rev: Option<String>,
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        scope: Vec<String>,
        /// A reviewer's findings: a `{"findings": [...]}` report, or an array of {file, line, title}.
        #[arg(long)]
        findings: Option<PathBuf>,
        #[arg(long)]
        json: bool,
    },
    /// Run the acceptance cases: known defects must be flagged, controls must not be.
    Accept {
        cases: PathBuf,
        #[arg(long)]
        json: bool,
    },
    /// Check the built-in Rust counter-probe fixtures with this binary.
    Selfcheck,
    /// The gate for an opted-in repository: with no `proofscan.toml` at its root it passes and
    /// says so; otherwise it scans what the change from BASE (default the upstream branch)
    /// touched and fails on a violation, or on an unknown with --strict.
    Gate {
        #[arg(default_value = ".")]
        path: PathBuf,
        #[arg(long)]
        base: Option<String>,
        #[arg(long)]
        strict: bool,
        #[arg(long)]
        json: bool,
    },
    /// A score per rule: the acceptance cases it catches, misses, holds and gets wrong, and the
    /// review outcomes in the ledger. With --record, append one outcome to the ledger instead.
    Tally {
        /// Cases files; the ledger defaults to `outcomes.jsonl` beside the first.
        #[arg(required = true)]
        cases: Vec<PathBuf>,
        #[arg(long)]
        ledger: Option<PathBuf>,
        /// Record a review outcome: RULE SITE confirmed|false.
        #[arg(long, num_args = 3, value_names = ["RULE", "SITE", "OUTCOME"])]
        record: Option<Vec<String>>,
        /// What the outcome rests on (the review, the commit that fixed it).
        #[arg(long, default_value = "")]
        note: String,
        #[arg(long)]
        json: bool,
    },
}

pub fn scan_repo(
    src: &Source,
    cfg: &Config,
    scope: &[String],
    diff: Option<&str>,
    questions: &[u8],
) -> Result<Report> {
    scan_repo_with(src, cfg, scope, diff, questions, &[])
}

pub fn scan_repo_overlay(
    src: &Source,
    cfg: &Config,
    scope: &[String],
    diff: Option<&str>,
    overlay: &[(String, String)],
) -> Result<Report> {
    scan_repo_with(src, cfg, scope, diff, &[], overlay)
}

fn scan_repo_with(
    src: &Source,
    cfg: &Config,
    scope: &[String],
    diff: Option<&str>,
    questions: &[u8],
    overlay: &[(String, String)],
) -> Result<Report> {
    scan_union(
        std::slice::from_ref(src),
        cfg,
        scope,
        diff,
        questions,
        overlay,
    )
}

/// Scan the union of the repositories' facts as one program: a rule whose parts lie in two
/// repositories is seen whole. A diff applies to a single repository only.
fn scan_union(
    srcs: &[Source],
    cfg: &Config,
    scope: &[String],
    diff: Option<&str>,
    questions: &[u8],
    overlay: &[(String, String)],
) -> Result<Report> {
    let t0 = Instant::now();
    let mut facts = facts::Facts::default();
    let mut texts = vec![];
    let mut repo_of_file = vec![];
    // Repositories load in parallel and join in order, so ids and output do not depend on timing.
    let loads: Vec<Result<scan::Loaded>> = {
        use rayon::prelude::*;
        srcs.par_iter()
            .map(|src| scan::load(src, cfg, scope, overlay))
            .collect()
    };
    for (ri, (src, loaded)) in srcs.iter().zip(loads).enumerate() {
        let mut loaded = loaded?;
        let name = src
            .root()
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        for f in &mut loaded.facts.files {
            f.repo = ri as facts::Id;
        }
        repo_of_file.extend(std::iter::repeat_n(name, loaded.facts.files.len()));
        facts.absorb(loaded.facts);
        texts.extend(loaded.texts);
    }
    analysis::timing("load", t0);
    let t = Instant::now();
    let graph = resolve::build(&facts);
    analysis::timing("resolve", t);
    let mut a = analysis::Analysis::new(&facts, &graph, cfg, &texts, repo_of_file);
    let early = match (diff, srcs) {
        (Some(base), [src]) => {
            let rev = match src {
                Source::Rev(_, r) => Some(r.as_str()),
                Source::Tree(_) => None,
            };
            let changed = diff::changed_lines(src.root(), base, rev)?;
            a.new_keys = diff::new_keys(src.root(), base, &changed, &texts);
            let (root, b) = (src.root().to_path_buf(), base.to_string());
            a.in_base = Some(Box::new(move |name: &str| diff::in_base(&root, &b, name)));
            Some(changed)
        }
        _ => None,
    };
    a.run();
    let mut findings = std::mem::take(&mut a.findings);
    let mut not_checked = std::mem::take(&mut a.not_checked);
    if let Some(base) = diff {
        let [src] = srcs else {
            anyhow::bail!("a diff applies to one repository")
        };
        let rev = match src {
            Source::Rev(_, r) => Some(r.as_str()),
            Source::Tree(_) => None,
        };
        let changed = match early {
            Some(c) => c,
            None => diff::changed_lines(src.root(), base, rev)?,
        };
        // A finding whose site the change touched is the change's. One that only passes through
        // a changed line (a witness step) is the change's only if the base does not have it.
        if findings
            .iter()
            .any(|f| !diff::on_site(&changed, f) && diff::touches(&changed, f))
        {
            let before = scan_union(
                &[Source::Rev(src.root().to_path_buf(), base.to_string())],
                cfg,
                scope,
                None,
                questions,
                &[],
            )?;
            let old: std::collections::HashSet<_> = before.findings.iter().map(diff::key).collect();
            findings.retain(|f| {
                diff::on_site(&changed, f)
                    || diff::touches(&changed, f) && !old.contains(&diff::key(f))
            });
        } else {
            findings.retain(|f| diff::on_site(&changed, f));
        }
        not_checked.clear();
    }
    if srcs.len() > 1 {
        for f in &mut findings {
            f.site = format!("{}/{}", f.repo, f.site);
        }
    }
    if !questions.is_empty() {
        findings.retain(|f| questions.contains(&f.question));
    }
    findings.sort_by(|a, b| {
        (
            a.question, b.verdict, &a.site, &a.rule, &a.message, &a.witness,
        )
            .cmp(&(
                b.question, a.verdict, &b.site, &b.rule, &b.message, &b.witness,
            ))
    });
    let mut qs = report::summarize(&findings, &not_checked);
    if !questions.is_empty() {
        qs.retain(|q| questions.contains(&q.question));
    }
    if !questions.contains(&8) {
        qs.retain(|q| q.question != 8);
    }
    Ok(Report {
        build: crate::report::BUILD,
        repos: srcs
            .iter()
            .map(|src| match src {
                Source::Tree(p) => p.display().to_string(),
                Source::Rev(p, r) => format!("{}@{r}", p.display()),
            })
            .collect(),
        profiles: cfg.applied.clone(),
        files: facts.files.len(),
        functions: facts
            .funcs
            .iter()
            .filter(|f| f.kind == facts::ScopeKind::Function)
            .count(),
        unparsed: facts.unparsed.clone(),
        diff: diff.map(str::to_string),
        questions: qs,
        findings,
        millis: t0.elapsed().as_millis(),
    })
}

fn emit(r: &Report, json: bool, all: bool) -> Result<()> {
    if json {
        println!("{}", serde_json::to_string_pretty(r)?);
    } else {
        print!("{}", r.human(all));
    }
    Ok(())
}

fn main() {
    let code = match run() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("proofscan: {e:#}");
            3
        }
    };
    std::process::exit(code);
}

fn split_spec(spec: &str) -> (PathBuf, Option<String>) {
    // `D:/x/repo@abc123`: the part after the last `@` is a revision when it holds no path separator.
    match spec.rsplit_once('@') {
        Some((p, r)) if !r.contains(['/', '\\']) && !p.is_empty() => {
            (PathBuf::from(p), Some(r.to_string()))
        }
        _ => (PathBuf::from(spec), None),
    }
}

fn run() -> Result<i32> {
    let cli = Cli::parse();
    scan::NO_CACHE.store(cli.no_cache, std::sync::atomic::Ordering::Relaxed);
    match cli.cmd {
        Cmd::Scan {
            path,
            rev,
            diff,
            config,
            scope,
            question,
            json,
            all,
        } => {
            let cfg = Config::load(&path, config.as_deref())?;
            let src = match rev {
                Some(r) => Source::Rev(path.clone(), r),
                None => Source::Tree(path.clone()),
            };
            let r = scan_repo(&src, &cfg, &scope, diff.as_deref(), &question)?;
            emit(&r, json, all)?;
            Ok(r.exit_code(cfg.report.unknown_fails))
        }
        Cmd::Sweep {
            question,
            repos,
            json,
            all,
            one_program,
        } => {
            let specs: Vec<(PathBuf, Option<String>)> =
                repos.iter().map(|s| split_spec(s)).collect();
            let roots: Vec<&Path> = specs.iter().map(|(p, _)| p.as_path()).collect();
            let cfg = Config::load_many(&roots).context("sweep configuration")?;
            let srcs: Vec<Source> = specs
                .into_iter()
                .map(|(path, rev)| match rev {
                    Some(r) => Source::Rev(path, r),
                    None => Source::Tree(path),
                })
                .collect();
            if one_program {
                let r = scan_union(&srcs, &cfg, &[], None, &question, &[])?;
                emit(&r, json, all)?;
                return Ok(r.exit_code(cfg.report.unknown_fails));
            }
            // One repository at a time: a union of all of them held every repository's facts and
            // source text at once (about 3 GB for 140), and a handler name that every copy of a
            // repository defines resolved to none of them. Each repository is answered on its
            // own and the reports are joined.
            let mut parts = Vec::with_capacity(srcs.len());
            for src in &srcs {
                parts.push(scan_union(
                    std::slice::from_ref(src),
                    &cfg,
                    &[],
                    None,
                    &question,
                    &[],
                )?);
            }
            let r = report::join(parts, &question, cfg.applied.clone());
            emit(&r, json, all)?;
            Ok(r.exit_code(cfg.report.unknown_fails))
        }
        Cmd::Mutate {
            path,
            diff,
            test,
            rev,
            timeout,
            json,
            list,
            at,
        } => {
            if list {
                for m in mutate::list(&path, &diff, rev.as_deref(), &at)? {
                    println!("{}:{} {}", m.file, m.line, m.what);
                }
                return Ok(0);
            }
            let r = mutate::run(&path, &diff, rev.as_deref(), &test, timeout, &at)?;
            emit(&r, json, true)?;
            Ok(r.exit_code(true))
        }
        #[cfg(feature = "smt")]
        Cmd::Policy {
            kind,
            candidate,
            reference,
            json,
        } => {
            let out = policy::compare(&kind, &candidate, &reference)?;
            if json {
                println!("{}", serde_json::to_string_pretty(&out)?);
            } else {
                println!("{}", out.human());
            }
            Ok(match out.verdict {
                report::Verdict::Proven => 0,
                report::Verdict::Violated => 1,
                report::Verdict::Unknown => 2,
            })
        }
        Cmd::Review {
            path,
            diff,
            rev,
            config,
            scope,
            findings,
            json,
        } => {
            let cfg = Config::load(&path, config.as_deref())?;
            let src = match rev {
                Some(r) => Source::Rev(path.clone(), r),
                None => Source::Tree(path.clone()),
            };
            let r = scan_repo(&src, &cfg, &scope, Some(&diff), &[])?;
            let fs = match findings {
                Some(p) => review::load_findings(&p)?,
                None => vec![],
            };
            let out = review::scope(&r, &fs);
            if json {
                println!("{}", serde_json::to_string_pretty(&out)?);
            } else {
                print!("{}", out.human());
            }
            // Exit as a scan would: a violation in the change, then an unknown left to the reviewer.
            Ok(if !out.violated.is_empty() {
                1
            } else if !out.review.is_empty() {
                2
            } else {
                0
            })
        }
        Cmd::Accept { cases, json } => accept::run(&cases, json),
        Cmd::Selfcheck => accept::selfcheck(),
        Cmd::Gate {
            path,
            base,
            strict,
            json,
        } => {
            if !path.join("proofscan.toml").is_file() {
                println!(
                    "proofscan gate: {} has no proofscan.toml, so it is not opted in; nothing scanned",
                    path.display()
                );
                return Ok(0);
            }
            let base = match base {
                Some(b) => b,
                None => diff::upstream(&path)
                    .context("no upstream branch to diff against; pass --base")?,
            };
            let cfg = Config::load(&path, None)?;
            let r = scan_repo(&Source::Tree(path.clone()), &cfg, &[], Some(&base), &[])?;
            emit(&r, json, false)?;
            let has = |v: report::Verdict| r.findings.iter().any(|f| f.verdict == v);
            Ok(if has(report::Verdict::Violated) {
                1
            } else if strict && has(report::Verdict::Unknown) {
                2
            } else {
                0
            })
        }
        Cmd::Tally {
            cases,
            ledger,
            record,
            note,
            json,
        } => match record {
            Some(r) => {
                let lp = accept::ledger_path(&cases[0], ledger.as_deref());
                accept::record(
                    &lp,
                    &accept::Outcome {
                        date: accept::today(),
                        rule: r[0].clone(),
                        site: r[1].clone(),
                        outcome: r[2].clone(),
                        note,
                    },
                )?;
                println!("recorded in {}", lp.display());
                Ok(0)
            }
            None => accept::tally(&cases, ledger.as_deref(), json),
        },
    }
}
