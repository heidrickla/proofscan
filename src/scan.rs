//! Reads a repository, from its working tree or from a commit, into facts.

use crate::config::Config;
use crate::facts::Facts;
use crate::lang;
use anyhow::{Context, Result, bail};
use globset::{Glob, GlobSet, GlobSetBuilder};
use rayon::prelude::*;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Where the files come from.
#[derive(Clone, Debug)]
pub enum Source {
    Tree(PathBuf),
    /// A repository and a commit; files are read from git objects, never checked out.
    Rev(PathBuf, String),
}

impl Source {
    pub fn root(&self) -> &Path {
        match self {
            Source::Tree(p) | Source::Rev(p, _) => p,
        }
    }
}

pub struct Loaded {
    pub facts: Facts,
    /// Every file read, for wire captures and provenance markers: (path, content).
    pub texts: Vec<(String, String)>,
}

fn globset(pats: &[String]) -> Result<GlobSet> {
    let mut b = GlobSetBuilder::new();
    for p in pats {
        b.add(Glob::new(p).with_context(|| format!("glob {p:?}"))?);
    }
    Ok(b.build()?)
}

/// Files under `scope` (repo-relative prefixes; empty means all), minus the excludes.
pub fn load(
    src: &Source,
    cfg: &Config,
    scope: &[String],
    overlay: &[(String, String)],
) -> Result<Loaded> {
    let exclude = globset(&cfg.scan.exclude)?;
    let kept = globset(&cfg.scan.keep)?;
    let include = if cfg.scan.include.is_empty() {
        None
    } else {
        Some(globset(&cfg.scan.include)?)
    };
    let keep = |rel: &str| {
        (!exclude.is_match(rel) || kept.is_match(rel))
            && include.as_ref().is_none_or(|i| i.is_match(rel))
            && (scope.is_empty()
                || scope
                    .iter()
                    .any(|s| rel == s || rel.starts_with(&format!("{}/", s.trim_end_matches('/')))))
    };
    let files: Vec<(String, String)> = match src {
        Source::Tree(root) => {
            let mut out = vec![];
            for e in ignore::WalkBuilder::new(root)
                .hidden(false)
                .build()
                .flatten()
            {
                if !e.file_type().is_some_and(|t| t.is_file()) {
                    continue;
                }
                let rel = e
                    .path()
                    .strip_prefix(root)
                    .unwrap_or(e.path())
                    .to_string_lossy()
                    .replace('\\', "/");
                if rel.starts_with(".git/") || !keep(&rel) {
                    continue;
                }
                out.push(rel);
            }
            out.par_iter()
                .filter_map(|rel| {
                    std::fs::read(root.join(rel))
                        .ok()
                        .map(|b| (rel.clone(), String::from_utf8_lossy(&b).into_owned()))
                })
                .collect()
        }
        Source::Rev(root, rev) => read_rev(root, rev, &keep)?,
    };
    let mut files = files;
    // An overlay appends text to a file (or adds it): the acceptance self-check inserts a defect this way.
    for (path, extra) in overlay {
        match files.iter_mut().find(|(p, _)| p == path) {
            Some((_, text)) => {
                text.push('\n');
                text.push_str(extra);
            }
            None => files.push((path.clone(), extra.clone())),
        }
    }
    let cache = cache_dir();
    let parsed: Vec<Facts> = files
        .par_iter()
        .filter_map(|(rel, text)| {
            lang::lang_of(Path::new(rel)).map(|l| cached_extract(cache.as_deref(), rel, text, l))
        })
        .collect();
    let mut facts = Facts::default();
    for f in parsed {
        facts.absorb(f);
    }
    Ok(Loaded {
        facts,
        texts: files,
    })
}

/// Set by `--no-cache`.
pub static NO_CACHE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Where per-file facts are kept between runs: `PROOFSCAN_CACHE`, else the user cache directory,
/// one subdirectory per build. `PROOFSCAN_CACHE=off` or `--no-cache` turns it off.
fn cache_dir() -> Option<std::path::PathBuf> {
    if NO_CACHE.load(std::sync::atomic::Ordering::Relaxed) {
        return None;
    }
    let base: std::path::PathBuf = match std::env::var_os("PROOFSCAN_CACHE") {
        Some(v) if v == "off" => return None,
        Some(v) => v.into(),
        None => std::env::var_os("LOCALAPPDATA")
            .map(|d| Path::new(&d).join("proofscan"))
            .or_else(|| std::env::var_os("XDG_CACHE_HOME").map(|d| Path::new(&d).join("proofscan")))
            .or_else(|| std::env::var_os("HOME").map(|d| Path::new(&d).join(".cache/proofscan")))?,
    };
    let build = format!("b-{}", &FACTS_BUILD[..16.min(FACTS_BUILD.len())]);
    let dir = base.join(&build);
    if std::fs::create_dir_all(&dir).is_ok() {
        let _ = std::fs::write(dir.join("used"), b"");
        prune_builds(&base, &build);
    }
    Some(dir)
}

/// Removes the facts of other builds not used for a week, so rebuilds do not pile up.
fn prune_builds(base: &Path, keep: &str) {
    let week = std::time::Duration::from_secs(7 * 24 * 3600);
    let Ok(entries) = std::fs::read_dir(base) else {
        return;
    };
    for e in entries.flatten() {
        let name = e.file_name();
        let name = name.to_string_lossy();
        if !name.starts_with("b-") || name == keep {
            continue;
        }
        let idle = std::fs::metadata(e.path().join("used"))
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| t.elapsed().ok())
            .is_none_or(|age| age > week);
        if idle {
            let _ = std::fs::remove_dir_all(e.path());
        }
    }
}

/// A file's facts, from the cache when the same tool version has parsed the same path and bytes.
/// The key covers the path because a file's module and test status come from it.
fn cached_extract(cache: Option<&Path>, rel: &str, text: &str, l: crate::facts::Lang) -> Facts {
    let Some(dir) = cache else {
        return lang::extract(rel, text, l);
    };
    let mut h = blake3::Hasher::new();
    h.update(env!("CARGO_PKG_VERSION").as_bytes());
    h.update(FACTS_BUILD.as_bytes());
    h.update(&[0]);
    h.update(rel.as_bytes());
    h.update(&[0]);
    h.update(text.as_bytes());
    let key = h.finalize().to_hex();
    let path = dir.join(&key[..2]).join(&key[2..]);
    if let Ok(bytes) = std::fs::read(&path)
        && let Ok(f) = postcard::from_bytes::<Facts>(&bytes)
    {
        return f;
    }
    let f = lang::extract(rel, text, l);
    if let Ok(bytes) = postcard::to_stdvec(&f) {
        // A write that fails leaves the cache cold for this file; the facts are already in hand.
        let tmp = path.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::create_dir_all(path.parent().unwrap_or(dir)).is_ok()
            && std::fs::write(&tmp, bytes).is_ok()
        {
            let _ = std::fs::rename(&tmp, &path);
        }
    }
    f
}

/// Changes whenever the extractors change, so a rebuilt binary does not reuse facts an older
/// extractor wrote: the build's own executable bytes stand in for it.
static FACTS_BUILD: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
    std::env::current_exe()
        .ok()
        .and_then(|p| std::fs::read(p).ok())
        .map(|b| blake3::hash(&b).to_hex().to_string())
        .unwrap_or_default()
});

/// Every blob at `rev` that `keep` accepts, through one `git cat-file --batch`.
fn read_rev(root: &Path, rev: &str, keep: &dyn Fn(&str) -> bool) -> Result<Vec<(String, String)>> {
    let ls = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-tree", "-r", "-z", "--full-tree", rev])
        .output()
        .context("git ls-tree")?;
    if !ls.status.success() {
        bail!(
            "git ls-tree {rev} in {}: {}",
            root.display(),
            String::from_utf8_lossy(&ls.stderr).trim()
        );
    }
    let mut wanted = vec![];
    for entry in ls.stdout.split(|b| *b == 0) {
        let entry = String::from_utf8_lossy(entry);
        let Some((meta, path)) = entry.split_once('\t') else {
            continue;
        };
        let mut m = meta.split_whitespace();
        let (_mode, kind, oid) = (m.next(), m.next(), m.next());
        if kind == Some("blob") && keep(path) {
            wanted.push((path.to_string(), oid.unwrap_or_default().to_string()));
        }
    }
    let mut child = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .context("git cat-file")?;
    let mut stdin = child.stdin.take().context("cat-file stdin")?;
    let oids: Vec<String> = wanted.iter().map(|(_, o)| o.clone()).collect();
    let writer = std::thread::spawn(move || -> std::io::Result<()> {
        for o in oids {
            writeln!(stdin, "{o}")?;
        }
        Ok(())
    });
    let mut out = BufReader::new(child.stdout.take().context("cat-file stdout")?);
    let mut files = Vec::with_capacity(wanted.len());
    for (path, _) in &wanted {
        let mut header = String::new();
        out.read_line(&mut header)?;
        let size: usize = header
            .split_whitespace()
            .nth(2)
            .and_then(|s| s.parse().ok())
            .with_context(|| format!("cat-file header {header:?}"))?;
        let mut buf = vec![0u8; size + 1];
        out.read_exact(&mut buf)?;
        buf.pop();
        files.push((path.clone(), String::from_utf8_lossy(&buf).into_owned()));
    }
    writer
        .join()
        .map_err(|_| anyhow::anyhow!("cat-file writer panicked"))??;
    child.wait()?;
    Ok(files)
}
