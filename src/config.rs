//! Configuration: built-in defaults, framework profiles, then the repository's `proofscan.toml`.

use anyhow::{Context, Result};
use regex::Regex;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::Path;

const DEFAULTS: &str = include_str!("defaults.toml");
const PROFILES: &str = include_str!("profiles.toml");

#[derive(Deserialize, Debug, Clone)]
pub struct Config {
    pub scan: Scan,
    pub providers: BTreeMap<String, Vec<String>>,
    pub q1: Q1,
    pub q2: Q2,
    pub q3: Q3,
    pub q4: Q4,
    pub effect: Vec<EffectSpec>,
    pub q5: Q5,
    pub q6: Q6,
    pub q7: Q7,
    pub q9: Q9,
    pub q10: Q10,
    pub report: Report,
    /// Profiles applied, for the report.
    #[serde(default)]
    pub applied: Vec<String>,
    /// The repository file merged in, if any.
    #[serde(default)]
    pub source: Option<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Scan {
    pub exclude: Vec<String>,
    /// Scanned although an exclude matches: vendored code that is the repository's own in effect
    /// (a patched parser of untrusted input).
    #[serde(default)]
    pub keep: Vec<String>,
    #[serde(default)]
    pub include: Vec<String>,
    pub profiles: Vec<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q1 {
    pub single_fact: Vec<String>,
    pub endpoint: String,
    pub closed_types: String,
    pub declared: BTreeMap<String, Vec<String>>,
    pub double_shared_tokens: usize,
    pub double_class: String,
    pub external_time: Vec<String>,
    /// Calls that bring a clock reading to an outside source's precision.
    #[serde(default)]
    pub normalize: Vec<String>,
    /// Calls that only report (log, print): a reading passed straight to one is no decision.
    #[serde(default)]
    pub report: Vec<String>,
    /// Provider calls that read only when called with no argument (`new Date(x)` converts `x`).
    #[serde(default)]
    pub argless: Vec<String>,
    /// Second readings kept on purpose: a function's readings of a provider, up to a count.
    #[serde(default)]
    pub accepted_reading: Vec<AcceptedReading>,
}

/// A function that reads one provider more than once on purpose (a cheap filter before a lock,
/// then the reading the decision uses). Keyed by function, not line, so it survives edits above it;
/// a reading beyond `readings` makes the sites violated again.
#[derive(Deserialize, Debug, Clone)]
pub struct AcceptedReading {
    /// The function label as findings print it: `path::Class.function`.
    pub function: String,
    /// The provider as findings print it (`clock`, `env:TOKEN`).
    pub provider: String,
    /// The most read sites the acceptance covers.
    pub readings: usize,
    pub reason: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q2 {
    pub guard_names: String,
    pub wire: Vec<Wire>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Wire {
    pub name: String,
    pub pattern: String,
    /// Globs of capture files inside the repository.
    #[serde(default)]
    pub captures: Vec<String>,
    /// Capture files outside the repository, relative to the configuration file.
    #[serde(default)]
    pub capture_files: Vec<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q3 {
    pub guards: Vec<String>,
    /// A literal argument that names a store's file (`state.json`); a path call's constant
    /// argument (`os.path.join(root, RUN_LOG)`) names one too.
    pub store_file: String,
    /// Calls that write: a function that names a store and makes one of these writes it.
    pub store_write: String,
    /// What a guard vouches for, by provider: a guard whose callee is named or reaches a call or
    /// literal matching the pattern checks that provider's readings (`clock_unsynced`,
    /// `dt_synchronized`), though it reads none of them itself.
    #[serde(default)]
    pub vouch: std::collections::BTreeMap<String, String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q4 {
    pub entry: Vec<EntrySpec>,
    pub guarded_entry: Vec<EntrySpec>,
    pub guard: Vec<GuardSpec>,
    /// A write before a guard kept on purpose (`path:line`, or a function label for every one in
    /// it), with its reason: reported proven with it.
    #[serde(default)]
    pub accepted_order: Vec<Accepted>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct EntrySpec {
    pub name: String,
    pub call: String,
    pub handler_arg: usize,
    #[serde(default)]
    pub handler_kw: Option<String>,
    /// Effect kinds the guard protects; every kind when empty.
    #[serde(default)]
    pub effects: Vec<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct GuardSpec {
    pub name: String,
    pub call: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct EffectSpec {
    pub kind: String,
    pub call: String,
    #[serde(default)]
    pub arg: Option<String>,
    #[serde(default)]
    pub receiver_from: Option<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q5 {
    pub closed_parse: Vec<String>,
    pub accepted_deny: Vec<Accepted>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Accepted {
    pub site: String,
    pub reason: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q6 {
    pub resource: Vec<Resource>,
    pub startup: Vec<String>,
    pub query_names: String,
    /// Where input from outside enters: a router call (`.route(path, post(handler))`) whose
    /// second argument holds method calls naming handlers, and functions whose `path:name`
    /// matches `untrusted_function`.
    #[serde(default)]
    pub untrusted_route: String,
    #[serde(default)]
    pub untrusted_method: String,
    #[serde(default)]
    pub untrusted_function: String,
    /// Check repeated output against a shared allowance, where the sink is modeled.
    #[serde(default)]
    pub emitted_bytes: bool,
    /// Check request prefix work at reviewed Rust consumers.
    #[serde(default)]
    pub prefix_work: bool,
    /// Rust calls that write their payload to durable storage.
    #[serde(default)]
    pub store_write: String,
    /// Required Rust request extractors that reject unauthenticated requests.
    #[serde(default)]
    pub authenticated_extractors: String,
    /// Header-authentication functions whose successful returns authenticate the path.
    #[serde(default)]
    pub authenticated_calls: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Resource {
    pub name: String,
    pub acquire: String,
    pub release: String,
    pub durable: bool,
    /// Functions that release what earlier runs left (a reconcile, a startup sweep). Without it,
    /// any function that can release the resource counts, including one that frees only its own.
    #[serde(default)]
    pub sweep: Option<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q10 {
    /// Calls that read a credential: a callee, or `arg:` a literal argument (a store's path).
    pub source: Vec<String>,
    /// Environment reads (`os.getenv`) whose literal key matches `secret_name` are sources too.
    pub env_read: String,
    pub secret_name: String,
    /// Keys that name where a credential is, not the credential (`TOKEN_FILE`, `API_KEY_PATH`).
    pub not_secret_name: String,
    /// Outside calls whose result carries their input (string methods, encoders, formatters);
    /// any other outside call's result is taken not to hold the credential it was given.
    pub carry: Vec<String>,
    /// Calls that make a path: a store's path given to one is not the credential. A reader
    /// (`read_text`, `open`) called on or with that path literal is a source.
    pub path_call: String,
    pub read_call: String,
    /// Keyword arguments of a sink that others do not read (`env=`, `input=` of a child process).
    pub not_sink_kwarg: String,
    /// Calls whose result no longer carries the value (a length, a hash, a redaction).
    pub sanitize: Vec<String>,
    /// Calls that put their arguments where others read them: logs, argv, error text.
    pub sink: Vec<String>,
    /// Commands after a shell pipe that print only a length or a digest.
    pub pipe_sanitize: String,
    /// Shell commands that print what they read; a wrapper (ssh, sudo) counts when its command does.
    pub print_cmd: String,
    pub wrapper_cmd: String,
    /// Flags that make grep or sed print nothing they read (`grep -q`, `sed -i`).
    pub quiet_arg: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q9 {
    pub resource: Vec<HeldResource>,
    /// Calls taken not to raise (pure path and type helpers).
    #[serde(default)]
    pub no_raise: Vec<String>,
}

/// A resource held in the process: each pattern matches a call's callee, `arg:` a literal argument,
/// `assign:` an assignment written `target = value`; any may carry a language prefix.
#[derive(Deserialize, Debug, Clone)]
pub struct HeldResource {
    pub name: String,
    pub acquire: Vec<String>,
    pub release: Vec<String>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Q7 {
    pub weak_probe: Vec<WeakProbe>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct WeakProbe {
    pub call: String,
    #[serde(default)]
    pub arg1: Option<String>,
    pub why: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Report {
    pub unknown_fails: bool,
}

/// Tables merge key by key, arrays append, anything else replaces.
fn merge(base: &mut toml::Value, over: toml::Value) {
    match (base, over) {
        (toml::Value::Table(b), toml::Value::Table(o)) => {
            for (k, v) in o {
                match b.get_mut(&k) {
                    Some(slot) => merge(slot, v),
                    None => {
                        b.insert(k, v);
                    }
                }
            }
        }
        (toml::Value::Array(b), toml::Value::Array(o)) => b.extend(o),
        (slot, v) => *slot = v,
    }
}

impl Config {
    /// Defaults, then each profile named or detected, then `config` (or `<root>/proofscan.toml`).
    pub fn load(root: &Path, config: Option<&Path>) -> Result<Config> {
        Self::build(&[(root, config)])
    }

    /// One configuration for a sweep over several repositories: each profile any of them names
    /// or matches, applied once, then each repository's own file in order.
    pub fn load_many(roots: &[&Path]) -> Result<Config> {
        Self::build(&roots.iter().map(|r| (*r, None)).collect::<Vec<_>>())
    }

    fn build(repos: &[(&Path, Option<&Path>)]) -> Result<Config> {
        let mut value: toml::Value = toml::from_str(DEFAULTS).context("built-in defaults")?;
        let mut files = vec![];
        for (root, config) in repos {
            let file = config
                .map(Path::to_path_buf)
                .or_else(|| Some(root.join("proofscan.toml")).filter(|p| p.is_file()));
            let repo: Option<toml::Value> = match &file {
                Some(p) => Some(
                    toml::from_str(
                        &std::fs::read_to_string(p)
                            .with_context(|| format!("reading {}", p.display()))?,
                    )
                    .with_context(|| format!("parsing {}", p.display()))?,
                ),
                None => None,
            };
            files.push((*root, file, repo));
        }
        let profiles: toml::Table = toml::from_str(PROFILES).context("built-in profiles")?;
        let mut applied = vec![];
        for (name, profile) in &profiles {
            let detect = profile.get("detect").and_then(|d| d.as_str()).unwrap_or("");
            let wanted = files.iter().any(|(root, _, repo)| {
                let named = repo
                    .as_ref()
                    .and_then(|r| r.get("scan")?.get("profiles")?.as_array().cloned())
                    .unwrap_or_default()
                    .iter()
                    .any(|v| v.as_str() == Some(name.as_str()));
                named || (!detect.is_empty() && glob_exists(root, detect))
            });
            if wanted {
                let mut p = profile.clone();
                if let Some(t) = p.as_table_mut() {
                    t.remove("detect");
                }
                merge(&mut value, p);
                applied.push(name.clone());
            }
        }
        // Wire captures named relative to their own configuration file.
        for (_, file, repo) in &mut files {
            if let (Some(dir), Some(r)) = (file.as_ref().and_then(|p| p.parent()), repo.as_mut())
                && let Some(wires) = r
                    .get_mut("q2")
                    .and_then(|q| q.get_mut("wire"))
                    .and_then(|w| w.as_array_mut())
            {
                for w in wires {
                    if let Some(cf) = w.get_mut("capture_files").and_then(|c| c.as_array_mut()) {
                        for c in cf.iter_mut() {
                            if let Some(s) = c.as_str() {
                                *c =
                                    toml::Value::String(dir.join(s).to_string_lossy().into_owned());
                            }
                        }
                    }
                }
            }
        }
        let sources: Vec<String> = files
            .iter()
            .filter_map(|(_, f, _)| f.as_ref().map(|p| p.display().to_string()))
            .collect();
        for (_, _, repo) in files {
            if let Some(r) = repo {
                merge(&mut value, r);
            }
        }
        let mut cfg: Config = value.try_into().context("configuration shape")?;
        cfg.applied = applied;
        cfg.source = (!sources.is_empty()).then(|| sources.join(", "));
        cfg.check()?;
        Ok(cfg)
    }

    /// Every pattern compiles, so a typo is an error and never a rule that matches nothing.
    fn check(&self) -> Result<()> {
        let mut pats: Vec<&str> = self
            .providers
            .values()
            .flatten()
            .map(|p| lang_scoped(p).1)
            .collect();
        pats.extend(
            self.q1
                .external_time
                .iter()
                .chain(&self.q1.normalize)
                .chain(&self.q1.report)
                .chain(&self.q1.argless)
                .map(String::as_str),
        );
        pats.extend(
            self.q9
                .resource
                .iter()
                .flat_map(|r| r.acquire.iter().chain(&r.release))
                .map(|p| lang_scoped(pattern_kind(p).1).1),
        );
        pats.extend(self.q9.no_raise.iter().map(String::as_str));
        pats.extend(
            self.q10
                .source
                .iter()
                .chain(&self.q10.sanitize)
                .chain(&self.q10.sink)
                .chain(&self.q10.carry)
                .map(|p| lang_scoped(pattern_kind(p).1).1),
        );
        pats.push(&self.q10.env_read);
        pats.push(&self.q10.secret_name);
        pats.push(&self.q10.not_secret_name);
        pats.push(&self.q10.path_call);
        pats.push(&self.q3.store_file);
        pats.push(&self.q3.store_write);
        pats.push(&self.q10.read_call);
        pats.push(&self.q10.not_sink_kwarg);
        pats.push(&self.q10.pipe_sanitize);
        pats.push(&self.q10.print_cmd);
        pats.push(&self.q10.wrapper_cmd);
        pats.push(&self.q10.quiet_arg);
        pats.push(&self.q1.double_class);
        pats.push(&self.q1.endpoint);
        pats.push(&self.q1.closed_types);
        pats.push(&self.q2.guard_names);
        pats.extend(self.q2.wire.iter().map(|w| w.pattern.as_str()));
        pats.extend(
            self.q4
                .entry
                .iter()
                .chain(&self.q4.guarded_entry)
                .map(|e| e.call.as_str()),
        );
        pats.extend(self.q4.guard.iter().map(|g| g.call.as_str()));
        for e in &self.effect {
            pats.push(&e.call);
            pats.extend(e.arg.as_deref());
            pats.extend(e.receiver_from.as_deref());
        }
        pats.extend(self.q5.closed_parse.iter().map(String::as_str));
        pats.extend(
            self.q6
                .resource
                .iter()
                .flat_map(|r| [r.acquire.as_str(), r.release.as_str()]),
        );
        pats.extend(self.q6.startup.iter().map(String::as_str));
        pats.push(&self.q6.query_names);
        for w in &self.q7.weak_probe {
            pats.push(&w.call);
            pats.extend(w.arg1.as_deref());
        }
        for p in pats {
            Regex::new(p).with_context(|| format!("pattern {p:?}"))?;
        }
        Ok(())
    }
}

fn glob_exists(root: &Path, pattern: &str) -> bool {
    let Ok(g) = globset::Glob::new(pattern) else {
        return false;
    };
    let m = g.compile_matcher();
    // Profiles detect by a shallow layout (`custom_components/*/manifest.json`), so walk three levels.
    walkdir3(root, root, 3, &m)
}

fn walkdir3(root: &Path, dir: &Path, depth: u32, m: &globset::GlobMatcher) -> bool {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return false;
    };
    for e in rd.flatten() {
        let p = e.path();
        if let Ok(rel) = p.strip_prefix(root)
            && m.is_match(rel)
        {
            return true;
        }
        if depth > 1 && p.is_dir() && walkdir3(root, &p, depth - 1, m) {
            return true;
        }
    }
    false
}

/// What a resource pattern matches: a call's callee (no prefix), a literal argument (`arg:`) or an
/// assignment written `target = value` (`assign:`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatternKind {
    Call,
    Arg,
    Assign,
}

pub fn pattern_kind(p: &str) -> (PatternKind, &str) {
    if let Some(r) = p.strip_prefix("assign:") {
        (PatternKind::Assign, r)
    } else if let Some(r) = p.strip_prefix("arg:") {
        (PatternKind::Arg, r)
    } else {
        (PatternKind::Call, p)
    }
}

/// A pattern limited to one language by a prefix: `sh:`, `ps:`, `js:`, `py:` or `rs:`.
pub fn lang_scoped(p: &str) -> (Option<crate::facts::Lang>, &str) {
    use crate::facts::Lang;
    for (pre, l) in [
        ("sh:", Lang::Bash),
        ("ps:", Lang::PowerShell),
        ("js:", Lang::JavaScript),
        ("py:", Lang::Python),
        ("rs:", Lang::Rust),
    ] {
        if let Some(rest) = p.strip_prefix(pre) {
            return (Some(l), rest);
        }
    }
    (None, p)
}

/// A compiled set of patterns.
#[derive(Clone)]
pub struct Pats(pub Vec<Regex>);

impl Pats {
    pub fn new(v: &[String]) -> Pats {
        Pats(v.iter().filter_map(|p| Regex::new(p).ok()).collect())
    }
    pub fn one(p: &str) -> Pats {
        Pats(Regex::new(p).ok().into_iter().collect())
    }
    pub fn is_match(&self, s: &str) -> bool {
        self.0.iter().any(|r| r.is_match(s))
    }
}
