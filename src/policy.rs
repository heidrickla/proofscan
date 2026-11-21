//! Policy comparison by SMT, in the manner of Zelkova: each policy becomes a formula over the
//! request (a path, a command line, an address and port), and Z3 is asked for a request the
//! candidate allows and the reference denies. Unsat proves the candidate grants no more; sat gives
//! that request as the witness; unknown names what defeated the solver.
//!
//! Kinds:
//!   brief    `Writable: <path>` and `Read only: <path>` lines; the deepest line decides, and a
//!            path no line covers is not writable.
//!   sudoers  `who host = (runas) [TAG:] cmd, !cmd` lines; the last matching entry decides.
//!   rules    TOML: `semantics` (first-match, last-match, deny-overrides), `default`, `[fields]`
//!            (string, int, ipv4) and `[[rule]]` with `effect` and a `match` table.

use crate::report::Verdict;
use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;
use z3::ast::{Bool, Int, Regexp, String as ZStr};
use z3::{Params, SatResult, Solver};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FieldKind {
    String,
    Int,
    Ipv4,
}

#[derive(Clone, Debug)]
enum Cond {
    /// `*` any characters (`/` included, as in sudoers), `?` one character.
    Glob(String),
    /// The path itself or anything under it.
    Under(String),
    Range(i64, i64),
}

#[derive(Clone, Debug)]
struct Rule {
    allow: bool,
    conds: Vec<(String, Cond)>,
    /// Where it came from, for the report.
    origin: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum Semantics {
    FirstMatch,
    LastMatch,
    DenyOverrides,
}

#[derive(Clone, Debug)]
pub struct Policy {
    fields: BTreeMap<String, FieldKind>,
    rules: Vec<Rule>,
    semantics: Semantics,
    default_allow: bool,
    /// Constructs read as written although their meaning may be wider (aliases, includes).
    assumptions: Vec<String>,
    /// Constructs not modeled; any makes a proof unknown.
    unmodeled: Vec<String>,
}

#[derive(Serialize)]
pub struct Outcome {
    pub verdict: Verdict,
    pub message: String,
    /// A request the candidate allows and the reference denies.
    pub witness: BTreeMap<String, String>,
    /// A request the reference allows and the candidate denies (the candidate is narrower there).
    pub narrower: BTreeMap<String, String>,
    /// The candidate's rule that allows the witness, and the reference's that denies it.
    pub decided_by: Vec<String>,
    pub assumptions: Vec<String>,
}

impl Outcome {
    pub fn human(&self) -> String {
        let mut s = format!("{}: {}", self.verdict.word(), self.message);
        if !self.witness.is_empty() {
            s.push_str(&format!(
                "\n  allowed only by the candidate: {}",
                show(&self.witness)
            ));
        }
        for d in &self.decided_by {
            s.push_str(&format!("\n  {d}"));
        }
        if !self.narrower.is_empty() {
            s.push_str(&format!(
                "\n  allowed only by the reference: {}",
                show(&self.narrower)
            ));
        }
        for a in &self.assumptions {
            s.push_str(&format!("\n  assumes: {a}"));
        }
        s
    }
}

fn show(m: &BTreeMap<String, String>) -> String {
    m.iter()
        .map(|(k, v)| format!("{k}={v:?}"))
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn load(kind: &str, path: &Path) -> Result<Policy> {
    let text =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    match kind {
        "brief" => Ok(brief(&text)),
        "sudoers" => Ok(sudoers(&text)),
        "rules" => rules(&text),
        _ => bail!("unknown policy kind {kind:?} (brief, sudoers, rules)"),
    }
}

fn norm_path(p: &str) -> String {
    let p = p.trim().replace('\\', "/");
    let p = p.trim_end_matches('/');
    if p.is_empty() {
        "/".into()
    } else {
        p.to_string()
    }
}

/// Brief scope lines. The deepest line decides, so rules are ordered deepest first.
pub fn brief(text: &str) -> Policy {
    let mut rules = vec![];
    let mut unmodeled = vec![];
    for (n, line) in text.lines().enumerate() {
        let (allow, rest) = if let Some(r) = line.strip_prefix("Writable:") {
            (true, r)
        } else if let Some(r) = line.strip_prefix("Read only:") {
            (false, r)
        } else {
            continue;
        };
        let p = norm_path(rest);
        if p.contains('*') || p.contains('?') {
            unmodeled.push(format!("line {}: a wildcard in a scope path ({p})", n + 1));
        }
        rules.push(Rule {
            allow,
            conds: vec![("path".into(), Cond::Under(p))],
            origin: format!("line {}: {}", n + 1, line.trim()),
        });
    }
    rules.sort_by_key(|r| match &r.conds[0].1 {
        Cond::Under(p) => std::cmp::Reverse(p.len()),
        _ => std::cmp::Reverse(0),
    });
    Policy {
        fields: [("path".to_string(), FieldKind::String)].into(),
        rules,
        semantics: Semantics::FirstMatch,
        default_allow: false,
        assumptions: vec!["paths compare case-sensitively, with `\\` read as `/`".into()],
        unmodeled,
    }
}

/// sudoers user specifications. Aliases, includes and Defaults are not expanded.
pub fn sudoers(text: &str) -> Policy {
    let mut rules = vec![];
    let mut unmodeled = vec![];
    let mut assumptions = vec![
        "a command named without arguments allows any arguments; `\"\"` allows none".to_string(),
    ];
    let mut joined = String::new();
    let mut lines = vec![];
    for (n, raw) in text.lines().enumerate() {
        let l = raw.split('#').next().unwrap_or("");
        if let Some(stripped) = l.strip_suffix('\\') {
            joined.push_str(stripped);
            joined.push(' ');
            continue;
        }
        joined.push_str(l);
        lines.push((n + 1, std::mem::take(&mut joined)));
    }
    for (n, line) in lines {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let first = line.split_whitespace().next().unwrap_or("");
        if first.ends_with("_Alias")
            || first.starts_with("Defaults")
            || first.starts_with("@include")
            || line.starts_with("#include")
        {
            if first.ends_with("_Alias") {
                unmodeled.push(format!("line {n}: alias definition {first}"));
            } else {
                assumptions.push(format!("line {n}: `{first}` is not modeled"));
            }
            continue;
        }
        let Some((lhs, rhs)) = line.split_once('=') else {
            unmodeled.push(format!("line {n}: not a user specification"));
            continue;
        };
        let mut lw = lhs.split_whitespace();
        let who = lw.next().unwrap_or("").to_string();
        let mut rhs = rhs.trim();
        if rhs.starts_with('(')
            && let Some(end) = rhs.find(')')
        {
            rhs = rhs[end + 1..].trim();
        }
        // Tags (NOPASSWD:, SETENV:) ahead of the command list.
        while let Some((tag, rest)) = rhs.split_once(':') {
            if tag
                .trim()
                .chars()
                .all(|c| c.is_ascii_uppercase() || c == '_')
                && !tag.trim().is_empty()
            {
                rhs = rest.trim();
            } else {
                break;
            }
        }
        let who_glob = if who == "ALL" {
            "*".to_string()
        } else {
            who.clone()
        };
        if who
            .chars()
            .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
            && who != "ALL"
        {
            unmodeled.push(format!("line {n}: user alias {who}"));
        }
        for cmd in rhs.split(',') {
            let cmd = cmd.trim();
            if cmd.is_empty() {
                continue;
            }
            let (allow, cmd) = match cmd.strip_prefix('!') {
                Some(c) => (false, c.trim()),
                None => (true, cmd),
            };
            let glob = if cmd == "ALL" {
                "*".to_string()
            } else if cmd
                .chars()
                .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
            {
                unmodeled.push(format!("line {n}: command alias {cmd}"));
                continue;
            } else if let Some(bin) = cmd.strip_suffix(" \"\"") {
                bin.trim().to_string()
            } else if !cmd.contains(' ') {
                format!("{cmd}\u{0}")
            } else {
                cmd.to_string()
            };
            rules.push(Rule {
                allow,
                conds: vec![
                    ("user".into(), Cond::Glob(who_glob.clone())),
                    ("command".into(), Cond::Glob(glob)),
                ],
                origin: format!("line {n}: {}", line),
            });
        }
    }
    Policy {
        fields: [
            ("user".to_string(), FieldKind::String),
            ("command".to_string(), FieldKind::String),
        ]
        .into(),
        rules,
        semantics: Semantics::LastMatch,
        default_allow: false,
        assumptions,
        unmodeled,
    }
}

#[derive(Deserialize)]
struct RulesFile {
    semantics: Semantics,
    #[serde(default = "deny")]
    default: String,
    fields: BTreeMap<String, FieldKind>,
    #[serde(default)]
    rule: Vec<RuleSpec>,
}

fn deny() -> String {
    "deny".into()
}

#[derive(Deserialize)]
struct RuleSpec {
    effect: String,
    #[serde(default, rename = "match")]
    matches: BTreeMap<String, toml::Value>,
}

pub fn rules(text: &str) -> Result<Policy> {
    let f: RulesFile = toml::from_str(text).context("rules file")?;
    let mut rules = vec![];
    for (i, r) in f.rule.iter().enumerate() {
        let allow = match r.effect.as_str() {
            "allow" => true,
            "deny" => false,
            e => bail!("rule {}: effect {e:?} is neither allow nor deny", i + 1),
        };
        let mut conds = vec![];
        for (field, v) in &r.matches {
            let Some(kind) = f.fields.get(field) else {
                bail!("rule {}: field {field} is not declared", i + 1)
            };
            let text = match v {
                toml::Value::String(s) => s.clone(),
                toml::Value::Integer(n) => n.to_string(),
                _ => bail!("rule {}: {field} must be a string or an integer", i + 1),
            };
            conds.push((
                field.clone(),
                parse_cond(*kind, &text).with_context(|| format!("rule {}: {field}", i + 1))?,
            ));
        }
        rules.push(Rule {
            allow,
            conds,
            origin: format!("rule {}", i + 1),
        });
    }
    Ok(Policy {
        fields: f.fields,
        rules,
        semantics: f.semantics,
        default_allow: f.default == "allow",
        assumptions: vec![],
        unmodeled: vec![],
    })
}

fn parse_cond(kind: FieldKind, text: &str) -> Result<Cond> {
    let text = text.trim();
    Ok(match kind {
        FieldKind::String => Cond::Glob(text.to_string()),
        FieldKind::Int => match text.split_once('-') {
            _ if text == "*" => Cond::Range(i64::MIN, i64::MAX),
            Some((a, b)) => Cond::Range(a.trim().parse()?, b.trim().parse()?),
            None => {
                let n = text.parse()?;
                Cond::Range(n, n)
            }
        },
        FieldKind::Ipv4 => {
            if text == "*" || text == "any" {
                return Ok(Cond::Range(0, u32::MAX as i64));
            }
            let (addr, bits) = text.split_once('/').unwrap_or((text, "32"));
            let a: std::net::Ipv4Addr = addr.parse()?;
            let bits: u32 = bits.parse()?;
            if bits > 32 {
                bail!("prefix length {bits}");
            }
            let base = u32::from(a) as i64;
            let size = 1i64 << (32 - bits);
            let lo = base & !(size - 1);
            Cond::Range(lo, lo + size - 1)
        }
    })
}

fn glob_re(g: &str) -> Regexp {
    let mut parts: Vec<Regexp> = vec![];
    let mut lit = String::new();
    let flush = |lit: &mut String, parts: &mut Vec<Regexp>| {
        if !lit.is_empty() {
            parts.push(Regexp::literal(lit));
            lit.clear();
        }
    };
    for ch in g.chars() {
        match ch {
            '*' => {
                flush(&mut lit, &mut parts);
                parts.push(Regexp::full());
            }
            '?' => {
                flush(&mut lit, &mut parts);
                parts.push(Regexp::allchar());
            }
            // A command named alone: itself, or itself followed by a space and arguments.
            '\u{0}' => {
                flush(&mut lit, &mut parts);
                parts.push(Regexp::concat(&[&Regexp::literal(" "), &Regexp::full()]).option());
            }
            c => lit.push(c),
        }
    }
    flush(&mut lit, &mut parts);
    match parts.len() {
        0 => Regexp::literal(""),
        1 => parts.pop().unwrap(),
        _ => Regexp::concat(&parts.iter().collect::<Vec<_>>()),
    }
}

struct Vars {
    s: BTreeMap<String, ZStr>,
    i: BTreeMap<String, Int>,
}

fn matches(r: &Rule, v: &Vars) -> Bool {
    let parts: Vec<Bool> = r
        .conds
        .iter()
        .map(|(field, c)| match c {
            Cond::Glob(g) => v.s[field].regex_matches(&glob_re(g)),
            Cond::Under(p) => {
                let p = p.as_str();
                let re = if p == "/" {
                    Regexp::full()
                } else {
                    Regexp::concat(&[
                        &Regexp::literal(p),
                        &Regexp::concat(&[&Regexp::literal("/"), &Regexp::full()]).option(),
                    ])
                };
                v.s[field].regex_matches(&re)
            }
            Cond::Range(lo, hi) => Bool::and(&[
                v.i[field].ge(Int::from_i64(*lo)),
                v.i[field].le(Int::from_i64(*hi)),
            ]),
        })
        .collect();
    if parts.is_empty() {
        Bool::from_bool(true)
    } else {
        Bool::and(&parts)
    }
}

fn allowed(p: &Policy, v: &Vars) -> Bool {
    match p.semantics {
        Semantics::DenyOverrides => {
            let allow: Vec<Bool> = p
                .rules
                .iter()
                .filter(|r| r.allow)
                .map(|r| matches(r, v))
                .collect();
            let deny: Vec<Bool> = p
                .rules
                .iter()
                .filter(|r| !r.allow)
                .map(|r| matches(r, v))
                .collect();
            let any_allow = if allow.is_empty() {
                Bool::from_bool(p.default_allow)
            } else {
                Bool::or(&allow)
            };
            let any_deny = if deny.is_empty() {
                Bool::from_bool(false)
            } else {
                Bool::or(&deny)
            };
            Bool::and(&[any_allow, any_deny.not()])
        }
        Semantics::FirstMatch | Semantics::LastMatch => {
            let mut ordered: Vec<&Rule> = p.rules.iter().collect();
            if p.semantics == Semantics::FirstMatch {
                ordered.reverse();
            }
            // Build from the rule that decides last outward: ite(m1, e1, ite(m2, e2, ... default)).
            let mut acc = Bool::from_bool(p.default_allow);
            for r in ordered {
                acc = matches(r, v).ite(&Bool::from_bool(r.allow), &acc);
            }
            acc
        }
    }
}

/// The rule that decides a concrete request, by the same semantics as `allowed`.
fn decider<'p>(p: &'p Policy, w: &BTreeMap<String, String>) -> Option<&'p Rule> {
    let hit = |r: &Rule| {
        r.conds.iter().all(|(field, c)| {
            let Some(val) = w.get(field) else {
                return false;
            };
            match c {
                Cond::Glob(g) => {
                    let mut re = String::from("^");
                    for ch in g.chars() {
                        match ch {
                            '*' => re.push_str("(?s:.*)"),
                            '?' => re.push_str("(?s:.)"),
                            '\u{0}' => re.push_str("(?s: .*)?"),
                            c => re.push_str(&regex::escape(&c.to_string())),
                        }
                    }
                    re.push('$');
                    regex::Regex::new(&re).is_ok_and(|r| r.is_match(val))
                }
                Cond::Under(base) => {
                    base == "/" || val == base || val.starts_with(&format!("{base}/"))
                }
                Cond::Range(lo, hi) => {
                    let n = val
                        .parse::<std::net::Ipv4Addr>()
                        .map(|a| u32::from(a) as i64)
                        .or_else(|_| val.parse::<i64>());
                    n.is_ok_and(|n| (*lo..=*hi).contains(&n))
                }
            }
        })
    };
    match p.semantics {
        Semantics::FirstMatch => p.rules.iter().find(|r| hit(r)),
        Semantics::LastMatch => p.rules.iter().rev().find(|r| hit(r)),
        Semantics::DenyOverrides => p
            .rules
            .iter()
            .find(|r| !r.allow && hit(r))
            .or_else(|| p.rules.iter().find(|r| r.allow && hit(r))),
    }
}

fn ipv4(n: i64) -> String {
    std::net::Ipv4Addr::from(n.clamp(0, u32::MAX as i64) as u32).to_string()
}

/// A request one policy allows and the other denies, or why there is no answer.
fn counterexample(
    yes: &Policy,
    no: &Policy,
    fields: &BTreeMap<String, FieldKind>,
    timeout_ms: u32,
) -> (SatResult, BTreeMap<String, String>, Option<String>) {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", timeout_ms);
    solver.set_params(&params);
    let mut v = Vars {
        s: BTreeMap::new(),
        i: BTreeMap::new(),
    };
    for (name, kind) in fields {
        match kind {
            FieldKind::String => {
                v.s.insert(name.clone(), ZStr::new_const(name.as_str()));
            }
            FieldKind::Int | FieldKind::Ipv4 => {
                let x = Int::new_const(name.as_str());
                if *kind == FieldKind::Ipv4 {
                    solver.assert(Bool::and(&[
                        x.ge(Int::from_i64(0)),
                        x.le(Int::from_i64(u32::MAX as i64)),
                    ]));
                }
                v.i.insert(name.clone(), x);
            }
        }
    }
    solver.assert(allowed(yes, &v));
    solver.assert(allowed(no, &v).not());
    let r = solver.check();
    let mut w = BTreeMap::new();
    if r == SatResult::Sat
        && let Some(m) = solver.get_model()
    {
        for (name, x) in &v.s {
            if let Some(s) = m.eval(x, true).and_then(|e| e.as_string()) {
                w.insert(name.clone(), s);
            }
        }
        for (name, x) in &v.i {
            if let Some(n) = m.eval(x, true).and_then(|e| e.as_i64()) {
                w.insert(
                    name.clone(),
                    if fields[name] == FieldKind::Ipv4 {
                        ipv4(n)
                    } else {
                        n.to_string()
                    },
                );
            }
        }
    }
    let why = (r == SatResult::Unknown).then(|| {
        solver
            .get_reason_unknown()
            .unwrap_or_else(|| "no reason given".into())
    });
    (r, w, why)
}

pub fn compare_policies(
    candidate: &Policy,
    reference: &Policy,
    timeout_ms: u32,
) -> Result<Outcome> {
    let mut fields = reference.fields.clone();
    for (k, v) in &candidate.fields {
        if let Some(old) = fields.insert(k.clone(), *v)
            && old != *v
        {
            bail!("field {k} is {old:?} in the reference and {v:?} in the candidate");
        }
    }
    let mut assumptions: Vec<String> = candidate
        .assumptions
        .iter()
        .chain(&reference.assumptions)
        .cloned()
        .collect();
    assumptions.dedup();
    let (r, witness, why) = counterexample(candidate, reference, &fields, timeout_ms);
    let (_, narrower, _) = counterexample(reference, candidate, &fields, timeout_ms);
    let unmodeled: Vec<String> = candidate
        .unmodeled
        .iter()
        .map(|u| format!("candidate {u}"))
        .chain(reference.unmodeled.iter().map(|u| format!("reference {u}")))
        .collect();
    let (verdict, message) = match r {
        SatResult::Sat => (
            Verdict::Violated,
            "the candidate allows a request the reference denies".to_string(),
        ),
        SatResult::Unknown => (
            Verdict::Unknown,
            format!("the solver gave no answer: {}", why.unwrap_or_default()),
        ),
        SatResult::Unsat if !unmodeled.is_empty() => (
            Verdict::Unknown,
            format!(
                "no request found, but these were not modeled: {}",
                unmodeled.join("; ")
            ),
        ),
        SatResult::Unsat => (
            Verdict::Proven,
            "the candidate allows nothing the reference denies".to_string(),
        ),
    };
    let mut decided_by = vec![];
    if !witness.is_empty() {
        decided_by.push(match decider(candidate, &witness) {
            Some(r) => format!("candidate allows it by {}", r.origin),
            None => "candidate allows it by its default".into(),
        });
        decided_by.push(match decider(reference, &witness) {
            Some(r) => format!("reference denies it by {}", r.origin),
            None => "reference denies it by its default".into(),
        });
    }
    Ok(Outcome {
        verdict,
        message,
        witness,
        narrower,
        decided_by,
        assumptions,
    })
}

pub fn compare(kind: &str, candidate: &Path, reference: &Path) -> Result<Outcome> {
    compare_policies(&load(kind, candidate)?, &load(kind, reference)?, 10_000)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmp(c: Policy, r: Policy) -> Outcome {
        compare_policies(&c, &r, 10_000).unwrap()
    }

    #[test]
    fn brief_deeper_read_only_line_narrows() {
        let wide = brief("Writable: D:\\repo\nLimits: no-push-github\n");
        let narrow = brief("Writable: D:\\repo\nRead only: D:\\repo\\records\n");
        let o = cmp(wide.clone(), narrow.clone());
        assert_eq!(o.verdict, Verdict::Violated);
        assert_eq!(
            o.decided_by,
            [
                "candidate allows it by line 1: Writable: D:\\repo",
                "reference denies it by line 2: Read only: D:\\repo\\records"
            ]
        );
        let p = &o.witness["path"];
        assert!(
            p == "D:/repo/records" || p.starts_with("D:/repo/records/"),
            "{p}"
        );
        assert_eq!(cmp(narrow, wide).verdict, Verdict::Proven);
    }

    #[test]
    fn brief_sibling_prefix_is_not_under() {
        // D:/repo2 is not under D:/repo.
        let a = brief("Writable: D:/repo\n");
        let b = brief("Writable: D:/repo2\n");
        let o = cmp(b, a);
        assert_eq!(o.verdict, Verdict::Violated);
        assert!(o.witness["path"].starts_with("D:/repo2"));
    }

    #[test]
    fn sudoers_bare_command_allows_arguments() {
        let bare = sudoers("deploy ALL=(root) NOPASSWD: /usr/bin/systemctl\n");
        let exact = sudoers("deploy ALL=(root) NOPASSWD: /usr/bin/systemctl restart app\n");
        let o = cmp(bare.clone(), exact.clone());
        assert_eq!(o.verdict, Verdict::Violated);
        assert_eq!(cmp(exact, bare).verdict, Verdict::Proven);
    }

    #[test]
    fn sudoers_negation_and_alias() {
        let all_but_su = sudoers("ops ALL=(ALL) ALL, !/usr/bin/su\n");
        let all = sudoers("ops ALL=(ALL) ALL\n");
        let o = cmp(all.clone(), all_but_su.clone());
        assert_eq!(o.verdict, Verdict::Violated);
        assert!(o.witness["command"].starts_with("/usr/bin/su"));
        let alias = sudoers("Cmnd_Alias SVC = /usr/bin/systemctl\nops ALL=(ALL) SVC\n");
        assert_eq!(cmp(alias, all).verdict, Verdict::Unknown);
    }

    #[test]
    fn firewall_rules_first_match() {
        let reference = rules(
            r#"
semantics = "first-match"
default = "deny"
[fields]
src = "ipv4"
port = "int"
[[rule]]
effect = "allow"
match = { src = "198.51.100.0/24", port = 22 }
"#,
        )
        .unwrap();
        let candidate = rules(
            r#"
semantics = "first-match"
default = "deny"
[fields]
src = "ipv4"
port = "int"
[[rule]]
effect = "deny"
match = { src = "198.51.100.66" }
[[rule]]
effect = "allow"
match = { src = "198.51.0.0/16", port = "22" }
"#,
        )
        .unwrap();
        let o = cmp(candidate.clone(), reference.clone());
        assert_eq!(o.verdict, Verdict::Violated);
        assert!(o.witness["src"].starts_with("198.51."), "{:?}", o.witness);
        assert!(
            !o.witness["src"].starts_with("198.51.100."),
            "{:?}",
            o.witness
        );
        assert_eq!(o.witness["port"], "22");
        // The reference allows 198.51.100.66, which the candidate's first rule denies.
        assert_eq!(o.narrower["src"], "198.51.100.66");
    }
}
