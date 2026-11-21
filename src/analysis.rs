//! Facts to verdicts. Classification turns calls into provider reads, effects, guards and value
//! sources; the Datalog program in `Prog` closes reachability and value flow to a fixed point; each
//! question's rules then read the derived relations and give each site a verdict.

use crate::config::{Config, Pats};
use crate::facts::*;
use crate::report::{Finding, Verdict};
use crate::resolve::{Graph, class_of, module_of_func};
use ascent::ascent;
use regex::Regex;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

mod blocking;
mod ci;
mod cost;
mod emitted_bytes;
mod guard_wait;
mod handle;
mod prefix_work;
mod state;
mod state_error;
mod store_size;
mod text_filter;

ascent! {
    pub struct Prog;
    relation edge(Id, Id, Id, bool);
    relation read(Id, Id, u32);
    relation effect(Id, Id, u32);
    relation guarded_site(Id);
    relation entry(Id);
    relation guarded_entry(Id);
    relation query_fn(Id);
    relation startup(Id);
    relation release(Id, Id, u32);
    relation src_site(Id, u32);
    relation cut_site(Id);
    relation assign_site(Id, u32, Id);
    relation assign_var(Id, u32, Id, u32);
    relation bind_site(Id, u32, Id);
    relation bind_var(Id, u32, Id, u32);
    relation ret_site(Id, Id);
    relation ret_var(Id, Id, u32);
    relation seed_var(Id, u32, u32);
    // A call with no in-repo target passes a credential in an argument on to its result.
    relation through_site(Id);
    relation arg_site(Id, Id);
    relation arg_var(Id, Id, u32);
    relation taint(u32);
    // The same flows over the variables an expression uses itself, for the credential kind.
    relation assign_var_d(Id, u32, Id, u32);
    relation ret_var_d(Id, Id, u32);
    relation bind_var_d(Id, u32, Id, u32);
    // And over an expression's outermost calls: a credential read inside a call's arguments
    // reaches the expression only if that call's result carries it.
    relation assign_site_d(Id, u32, Id);
    relation ret_site_d(Id, Id);
    relation bind_site_d(Id, u32, Id);

    // Provider reads reachable from each function; the flag is true when every edge is exact.
    relation reads(Id, Id, u32, bool);
    reads(f, s, p, true) <-- read(s, f, p);
    reads(f, s, p, *x && *y) <-- edge(f, g, _, x), reads(g, s, p, y);

    // Readings that arrive in a function as values: its own reads, and a callee's when the callee
    // returns a value derived from a source. A reading a callee consumes is that callee's decision.
    relation returns_kind(Id);
    returns_kind(g) <-- ret_kind(g, _);
    relation vreads(Id, Id, u32, bool);
    vreads(f, s, p, true) <-- read(s, f, p);
    vreads(f, s, p, *x && *y) <-- edge(f, g, _, x), returns_kind(g), vreads(g, s, p, y);

    relation eff_reach(Id, u32);
    eff_reach(f, k) <-- effect(_, f, k);
    eff_reach(f, k) <-- edge(f, g, _, _), eff_reach(g, k);

    // Functions an unguarded entry reaches without crossing a guarded call.
    relation open(Id, Id, bool);
    open(e, e, true) <-- entry(e), !guarded_entry(e);
    open(e, g, *x && *y) <-- open(e, f, x), edge(f, g, s, y), !guarded_site(s);

    relation qreach(Id, Id);
    qreach(q, q) <-- query_fn(q);
    qreach(f, q) <-- edge(f, g, _, _), qreach(g, q);

    relation rel_reach(Id, u32);
    rel_reach(f, r) <-- release(_, f, r);
    rel_reach(f, r) <-- edge(f, g, _, _), rel_reach(g, r);
    relation swept(u32);
    swept(r) <-- startup(f), rel_reach(f, r);

    // Value kinds: a value carries the kind of every source it may derive from.
    relation site_kind(Id, u32);
    relation var_kind(Id, u32, u32);
    relation ret_kind(Id, u32);
    site_kind(s, k) <-- src_site(s, k);
    site_kind(s, k) <-- edge(_, g, s, _), ret_kind(g, k), !cut_site(s);
    ret_kind(g, k) <-- ret_site(g, s), site_kind(s, k), !taint(k);
    ret_kind(g, k) <-- ret_site_d(g, s), site_kind(s, k), taint(k);
    ret_kind(g, k) <-- ret_var(g, sc, v), var_kind(sc, v, k), !taint(k);
    ret_kind(g, k) <-- ret_var_d(g, sc, v), var_kind(sc, v, k), taint(k);
    var_kind(sc, v, k) <-- seed_var(sc, v, k);
    var_kind(sc, v, k) <-- assign_site(sc, v, s), site_kind(s, k), !taint(k);
    var_kind(sc, v, k) <-- assign_site_d(sc, v, s), site_kind(s, k), taint(k);
    var_kind(sc, v, k) <-- assign_var(sc, v, sc2, v2), var_kind(sc2, v2, k), !taint(k);
    var_kind(sc, v, k) <-- assign_var_d(sc, v, sc2, v2), var_kind(sc2, v2, k), taint(k);
    var_kind(g, p, k) <-- bind_site(g, p, s2), site_kind(s2, k), !taint(k);
    var_kind(g, p, k) <-- bind_site_d(g, p, s2), site_kind(s2, k), taint(k);
    var_kind(g, p, k) <-- bind_var(g, p, sc, v), var_kind(sc, v, k), !taint(k);
    var_kind(g, p, k) <-- bind_var_d(g, p, sc, v), var_kind(sc, v, k), taint(k);
    site_kind(s, k) <-- through_site(s), arg_site(s, x), site_kind(x, k), taint(k), !cut_site(s);
    site_kind(s, k) <-- through_site(s), arg_var(s, sc, v), var_kind(sc, v, k), taint(k), !cut_site(s);
}

/// Whether a name appears in a diff's base tree.
pub type InBase<'a> = Box<dyn Fn(&str) -> bool + 'a>;

pub struct Analysis<'a> {
    pub f: &'a Facts,
    pub g: &'a Graph,
    pub cfg: &'a Config,
    pub texts: &'a [(String, String)],
    pub repo_of_file: Vec<String>,
    kinds: Vec<String>,
    vars: HashMap<String, u32>,
    locals: HashMap<Id, HashSet<String>>,
    /// site -> fact index (`clock`, `env:HOME`, `endpoint:/host/info`) for every read.
    reads_at: HashMap<Id, u32>,
    /// site -> value kind of the provider read there, for flows.
    read_kind: HashMap<Id, u32>,
    fact_names: Vec<String>,
    /// site -> effect kind index.
    effects_at: HashMap<Id, u32>,
    effect_kinds: Vec<String>,
    call_at: HashMap<Id, usize>,
    closed: Pats,
    prog: Prog,
    pub findings: Vec<Finding>,
    pub not_checked: BTreeMap<u8, Vec<String>>,
    /// On a diff: (file, line, key) for each key the change starts reading (`diff::new_keys`).
    /// The last field is true for a subscript read, which raises on a file without the key.
    pub new_keys: Vec<(String, u32, String, String, bool)>,
    /// On a diff: whether a name (a store's file name or constant) appears in the base, for a
    /// store the change itself introduces, which no previous release left.
    pub in_base: Option<InBase<'a>>,
    /// Call edges by caller, built once for witness searches.
    adj: std::cell::OnceCell<Adjacency>,
    /// The derived value kinds by site and by (scope, variable), built once after the fixed point.
    kinds_index: std::cell::OnceCell<KindsIndex>,
}

/// A handler registered by an entry: (handler, entry name, effect kinds its guard covers).
type EntrySpec = (Id, String, Vec<String>);

/// Phase times on stderr when PROOFSCAN_TIMING is set.
pub fn timing(phase: &str, t: std::time::Instant) {
    if std::env::var_os("PROOFSCAN_TIMING").is_some() {
        eprintln!("proofscan: {phase} {} ms", t.elapsed().as_millis());
    }
}

/// A resource pattern for calls: the callee, or with `arg:` a literal argument.
struct CallPat(
    crate::config::PatternKind,
    Option<Regex>,
    Option<crate::facts::Lang>,
);

impl CallPat {
    fn new(pattern: &str) -> CallPat {
        let (k, p) = crate::config::pattern_kind(pattern);
        let (l, p) = crate::config::lang_scoped(p);
        CallPat(k, Regex::new(p).ok(), l)
    }
    fn hit_in(&self, c: &crate::facts::Call, lang: crate::facts::Lang) -> bool {
        self.2.is_none_or(|l| l == lang) && self.hit(c)
    }
    fn hit(&self, c: &crate::facts::Call) -> bool {
        let Some(r) = &self.1 else { return false };
        match self.0 {
            crate::config::PatternKind::Call => r.is_match(&c.full),
            crate::config::PatternKind::Arg => c.str_args.iter().any(|a| r.is_match(a)),
            crate::config::PatternKind::Assign => false,
        }
    }
}

/// A finding held back until a borrow ends: verdict, site, message, witness, assumptions.
type Pending = (Verdict, Id, String, Vec<String>, Vec<String>);

/// Call edges by caller: (callee, call site, exact).
type Adjacency = HashMap<Id, Vec<(Id, Id, bool)>>;

#[derive(Default)]
struct KindsIndex {
    site: HashMap<Id, Vec<u32>>,
    var: HashMap<(Id, u32), Vec<u32>>,
}

const EXT_TIME: &str = "external time";
const EXTERNAL: &str = "outside input";
const PARAM: &str = "public parameter";
const CLOSED: &str = "closed";
const NORMALIZED: &str = "normalized time";
const SECRET: &str = "credential";

impl<'a> Analysis<'a> {
    pub fn new(
        f: &'a Facts,
        g: &'a Graph,
        cfg: &'a Config,
        texts: &'a [(String, String)],
        repo_of_file: Vec<String>,
    ) -> Self {
        let mut kinds: Vec<String> = cfg.providers.keys().cloned().collect();
        kinds.extend([EXT_TIME, EXTERNAL, PARAM, CLOSED, NORMALIZED, SECRET].map(String::from));
        let call_at = f
            .calls
            .iter()
            .enumerate()
            .map(|(i, c)| (c.site, i))
            .collect();
        let mut locals: HashMap<Id, HashSet<String>> = HashMap::new();
        for a in &f.assigns {
            locals
                .entry(f.sites[a.site as usize].func)
                .or_default()
                .insert(a.target.clone());
        }
        for (i, func) in f.funcs.iter().enumerate() {
            let set = locals.entry(i as Id).or_default();
            set.extend(func.params.iter().map(|p| p.name.clone()));
        }
        Analysis {
            f,
            g,
            cfg,
            texts,
            repo_of_file,
            kinds,
            vars: HashMap::new(),
            locals,
            reads_at: HashMap::new(),
            read_kind: HashMap::new(),
            fact_names: vec![],
            effects_at: HashMap::new(),
            effect_kinds: vec![],
            call_at,
            closed: Pats::new(&cfg.q5.closed_parse),
            prog: Prog::default(),
            findings: vec![],
            not_checked: BTreeMap::new(),
            new_keys: vec![],
            in_base: None,
            adj: std::cell::OnceCell::new(),
            kinds_index: std::cell::OnceCell::new(),
        }
    }

    fn kind(&self, k: &str) -> u32 {
        self.kinds.iter().position(|x| x == k).unwrap_or(0) as u32
    }

    fn fact(&mut self, name: &str) -> u32 {
        match self.fact_names.iter().position(|x| x == name) {
            Some(i) => i as u32,
            None => {
                self.fact_names.push(name.to_string());
                (self.fact_names.len() - 1) as u32
            }
        }
    }

    fn var(&mut self, v: &str) -> u32 {
        let n = self.vars.len() as u32;
        *self.vars.entry(v.to_string()).or_insert(n)
    }

    /// The scope a variable name belongs to when read in `func`.
    fn scope_of(&self, func: Id, v: &str) -> Id {
        if v.starts_with("self.") {
            return class_of(self.f, func).unwrap_or(func);
        }
        let mut cur = Some(func);
        while let Some(s) = cur {
            if self.locals.get(&s).is_some_and(|l| l.contains(v)) {
                return s;
            }
            cur = self.f.funcs[s as usize].parent;
        }
        func
    }

    fn call(&self, site: Id) -> Option<&'a Call> {
        self.call_at.get(&site).map(|&i| &self.f.calls[i])
    }

    fn loc(&self, site: Id) -> String {
        self.f.loc(site)
    }

    fn repo(&self, site: Id) -> String {
        self.repo_of_file[self.f.sites[site as usize].file as usize].clone()
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "a finding's fields, each set at every call"
    )]
    fn push(
        &mut self,
        q: u8,
        rule: &'static str,
        verdict: Verdict,
        site: Id,
        message: String,
        witness: Vec<String>,
        assumptions: Vec<String>,
    ) {
        let repo = self.repo(site);
        self.findings.push(Finding {
            question: q,
            rule,
            verdict,
            repo,
            site: self.loc(site),
            message,
            witness,
            assumptions,
        });
    }

    /// Whether site `a` runs before `b` on every path through their function.
    pub fn dominates(&self, a: Id, b: Id) -> bool {
        let (sa, sb) = (&self.f.sites[a as usize], &self.f.sites[b as usize]);
        if sa.func != sb.func || sa.ctx.cond || sa.ctx.in_lambda || a == b {
            return false;
        }
        let (pa, pb) = (&sa.ctx.path, &sb.ctx.path);
        let n = pa.len();
        if n == 0 || pb.len() < n || pa[..n - 1] != pb[..n - 1] {
            return false;
        }
        let (la, lb) = (pa[n - 1], pb[n - 1]);
        (la == lb && (pb.len() > n || a < b)) || (la.0 == lb.0 && la.1 < lb.1)
    }

    /// Classification, flow facts, and the fixed point.
    #[expect(
        clippy::field_reassign_with_default,
        reason = "Ascent's program is filled one relation at a time"
    )]
    pub fn run(&mut self) {
        let t_prep = std::time::Instant::now();
        let f = self.f;
        let provider_pats: Vec<(u32, Option<crate::facts::Lang>, Regex)> = self
            .cfg
            .providers
            .iter()
            .enumerate()
            .flat_map(|(i, (_, v))| {
                v.iter().filter_map(move |p| {
                    let (l, p) = crate::config::lang_scoped(p);
                    Regex::new(p).ok().map(|r| (i as u32, l, r))
                })
            })
            .collect();
        let provider_of = |full: &str, func: Id| {
            let lang = f.files[f.funcs[func as usize].file as usize].lang;
            provider_pats
                .iter()
                .find(|(_, l, p)| l.is_none_or(|l| l == lang) && p.is_match(full))
                .map(|(i, _, _)| *i)
        };

        // Aliases: names bound to a provider function (`self.now = lambda: datetime.now()`).
        let mut alias: HashMap<(Id, String), u32> = HashMap::new();
        for a in &f.assigns {
            let func = f.sites[a.site as usize].func;
            // An alias is a name bound to the provider itself: a reference, or a lambda whose outermost call is the provider.
            let p = a
                .refs
                .iter()
                .find_map(|r| provider_of(r, func))
                .or_else(|| a.lambda_calls.first().and_then(|r| provider_of(r, func)));
            if let Some(p) = p {
                alias.insert((self.scope_of(func, &a.target), a.target.clone()), p);
            }
        }
        for (i, func) in f.funcs.iter().enumerate() {
            for prm in &func.params {
                if let Some(p) = prm
                    .default_refs
                    .iter()
                    .find_map(|r| provider_of(r, i as Id))
                    .or_else(|| {
                        prm.default_lambda_calls
                            .first()
                            .and_then(|r| provider_of(r, i as Id))
                    })
                {
                    alias.insert((i as Id, prm.name.clone()), p);
                }
            }
        }
        // Effects, with receivers traced to the call that made them where a spec asks.
        let mut origin_call: HashMap<(Id, String), String> = HashMap::new();
        for a in &f.assigns {
            if let Some(&first) = a.value.calls.first()
                && let Some(c) = self.call(first)
            {
                let func = f.sites[a.site as usize].func;
                origin_call.insert(
                    (self.scope_of(func, &a.target), a.target.clone()),
                    c.full.clone(),
                );
            }
        }
        let specs: Vec<(String, Regex, Option<Regex>, Option<Regex>)> = self
            .cfg
            .effect
            .iter()
            .filter_map(|e| {
                Some((
                    e.kind.clone(),
                    Regex::new(&e.call).ok()?,
                    e.arg.as_deref().and_then(|a| Regex::new(a).ok()),
                    e.receiver_from.as_deref().and_then(|a| Regex::new(a).ok()),
                ))
            })
            .collect();
        for (k, ..) in &specs {
            if !self.effect_kinds.contains(k) {
                self.effect_kinds.push(k.clone());
            }
        }
        for c in &f.calls {
            let func = f.sites[c.site as usize].func;
            for (kind, call, arg, recv_from) in &specs {
                if !call.is_match(&c.full) {
                    continue;
                }
                if let Some(arg) = arg
                    && !c.str_args.iter().any(|s| arg.is_match(s))
                {
                    continue;
                }
                if let Some(rf) = recv_from {
                    let head = crate::lang::python::var_name(&c.recv);
                    let made = origin_call.get(&(self.scope_of(func, &head), head.clone()));
                    if !(made.is_some_and(|m| rf.is_match(m)) || rf.is_match(&c.recv)) {
                        continue;
                    }
                }
                let k = self
                    .effect_kinds
                    .iter()
                    .position(|x| x == kind)
                    .unwrap_or(0) as u32;
                self.effects_at.insert(c.site, k);
                break;
            }
        }

        // Reads: a provider call, a call through an alias of one, or a GET of a literal endpoint.
        // A provider call inside a lambda that defines an alias is no read: calls through the alias are.
        let alias_defs: HashSet<(Id, u32, String)> = f
            .assigns
            .iter()
            .flat_map(|a| {
                let st = &f.sites[a.site as usize];
                a.lambda_calls
                    .first()
                    .map(move |c| (st.func, st.line, c.clone()))
            })
            .collect();
        let endpoint = Regex::new(&self.cfg.q1.endpoint).ok();
        let names: Vec<String> = self.cfg.providers.keys().cloned().collect();
        let report: Vec<Regex> = self
            .cfg
            .q1
            .report
            .iter()
            .filter_map(|r| Regex::new(r).ok())
            .collect();
        let argless: Vec<Regex> = self
            .cfg
            .q1
            .argless
            .iter()
            .filter_map(|r| Regex::new(r).ok())
            .collect();
        let reported: HashSet<Id> = f
            .calls
            .iter()
            .filter(|c| report.iter().any(|r| r.is_match(&c.full)))
            .flat_map(|c| {
                c.args
                    .iter()
                    .chain(c.kwargs.iter().map(|(_, e)| e))
                    .flat_map(|e| e.calls.iter().copied())
            })
            .collect();
        for c in &f.calls {
            let st = &f.sites[c.site as usize];
            if st.ctx.in_lambda && alias_defs.contains(&(st.func, st.line, c.full.clone())) {
                continue;
            }
            if reported.contains(&c.site)
                || c.output_only
                || c.nargs > 0 && argless.iter().any(|r| r.is_match(&c.full))
            {
                continue;
            }
            let pv = provider_of(&c.full, st.func).or_else(|| {
                alias
                    .get(&(self.scope_of(st.func, &c.full), c.full.clone()))
                    .copied()
            });
            if let Some(pv) = pv {
                let name = &names[pv as usize];
                let fact = if name == "env" {
                    // A key that is not a literal is its own fact: two unknown keys are not one.
                    match c.str_args.first().filter(|k| !k.is_empty()) {
                        Some(k) => format!("env:{k}"),
                        None => format!("env:? at {}", self.loc(c.site)),
                    }
                } else {
                    name.clone()
                };
                let id = self.fact(&fact);
                self.reads_at.insert(c.site, id);
                self.read_kind.insert(c.site, pv);
            } else if !self.effects_at.contains_key(&c.site)
                && endpoint.as_ref().is_some_and(|e| e.is_match(&c.full))
                && let Some(path) = c.str_args.first().filter(|a| a.contains('/'))
            {
                let id = self.fact(&format!("endpoint:{path}"));
                self.reads_at.insert(c.site, id);
            }
        }

        let mut p = Prog::default();
        p.edge = self
            .g
            .edges
            .iter()
            .map(|&(a, b, s, x)| (a, b, s, x))
            .collect();
        p.read = self
            .reads_at
            .iter()
            .map(|(&s, &pv)| (s, f.sites[s as usize].func, pv))
            .collect();
        p.effect = self
            .effects_at
            .iter()
            .map(|(&s, &k)| (s, f.sites[s as usize].func, k))
            .collect();

        // Value sources and flows.
        let ext_time = Pats::new(&self.cfg.q1.external_time);
        let normalize = Pats::new(&self.cfg.q1.normalize);
        let k_norm = self.kind(NORMALIZED);
        let external = Pats::one(
            r"(^|\.)(json|loads|load|read_text|read_bytes|readline|readlines|recv|getenv|input)$|^(sys\.argv|request\.\w+)$|(^|\.)(get_json|text|content)$",
        );
        let (k_ext_time, k_external, k_param, k_closed) = (
            self.kind(EXT_TIME),
            self.kind(EXTERNAL),
            self.kind(PARAM),
            self.kind(CLOSED),
        );
        let kinds_of_provider: Vec<u32> = (0..self.cfg.providers.len() as u32).collect();
        // Question 10: credential sources, sanitizers, and flow through outside calls.
        let k_secret = self.kind(SECRET);
        p.taint.push((k_secret,));
        let q10_src: Vec<CallPat> = self
            .cfg
            .q10
            .source
            .iter()
            .map(|s| CallPat::new(s))
            .collect();
        let q10_san: Vec<CallPat> = self
            .cfg
            .q10
            .sanitize
            .iter()
            .map(|s| CallPat::new(s))
            .collect();
        let env_read = Regex::new(&self.cfg.q10.env_read).ok();
        let secret_name = Regex::new(&self.cfg.q10.secret_name).ok();
        let not_secret = Regex::new(&self.cfg.q10.not_secret_name).ok();
        let q10_carry: Vec<CallPat> = self.cfg.q10.carry.iter().map(|s| CallPat::new(s)).collect();
        let path_call = Regex::new(&self.cfg.q10.path_call).ok();
        let read_call = Regex::new(&self.cfg.q10.read_call).ok();
        let is = |r: &Option<Regex>, t: &str| r.as_ref().is_some_and(|r| r.is_match(t));
        // A store path literal in a reader's receiver or arguments (`Path(".storage/x").read_text()`).
        let store_in = |t: &str| {
            q10_src.iter().any(|x| {
                x.0 == crate::config::PatternKind::Arg
                    && x.1.as_ref().is_some_and(|r| {
                        t.split(['"', '\''])
                            .skip(1)
                            .step_by(2)
                            .any(|lit| r.is_match(lit))
                    })
            })
        };
        let in_repo: HashSet<Id> = self.g.edges.iter().map(|e| e.2).collect();
        for c in &f.calls {
            let lang = f.files[f.sites[c.site as usize].file as usize].lang;
            let reader = is(&read_call, &c.full)
                && (store_in(&c.recv) || c.args.iter().any(|a| store_in(&a.text)));
            let src = reader
                || !is(&path_call, &c.full) && q10_src.iter().any(|x| x.hit_in(c, lang))
                || env_read.as_ref().is_some_and(|r| r.is_match(&c.full))
                    && c.str_args.first().is_some_and(|k| {
                        secret_name.as_ref().is_some_and(|r| r.is_match(k))
                            && !not_secret.as_ref().is_some_and(|r| r.is_match(k))
                    });
            if src {
                p.src_site.push((c.site, k_secret));
            }
            if q10_san.iter().any(|x| x.hit_in(c, lang)) {
                p.cut_site.push((c.site,));
            }
            if !in_repo.contains(&c.site) && q10_carry.iter().any(|x| x.hit_in(c, lang)) {
                p.through_site.push((c.site,));
                let func = f.sites[c.site as usize].func;
                for e in c.args.iter().chain(c.kwargs.iter().map(|(_, e)| e)) {
                    for &x in &e.calls {
                        p.arg_site.push((c.site, x));
                    }
                    for w in self.direct_vars(e) {
                        let (sc, v) = (self.scope_of(func, w), self.var(w));
                        p.arg_var.push((c.site, sc, v));
                    }
                }
                if !c.recv.is_empty() && !c.recv.contains('(') {
                    let w = crate::lang::python::var_name(&c.recv);
                    let (sc, v) = (self.scope_of(func, &w), self.var(&w));
                    p.arg_var.push((c.site, sc, v));
                }
            }
        }
        for c in &f.calls {
            if let Some(&pv) = self.read_kind.get(&c.site) {
                p.src_site.push((c.site, kinds_of_provider[pv as usize]));
            }
            if ext_time.is_match(&c.full) {
                p.src_site.push((c.site, k_ext_time));
            } else if external.is_match(&c.full) {
                p.src_site.push((c.site, k_external));
            }
            if self.closed.is_match(&c.full) {
                p.src_site.push((c.site, k_closed));
                p.cut_site.push((c.site,));
            } else if normalize.is_match(&c.full) {
                p.src_site.push((c.site, k_norm));
                p.cut_site.push((c.site,));
            }
        }
        for a in &f.assigns {
            let func = f.sites[a.site as usize].func;
            let sc = self.scope_of(func, &a.target);
            let v = self.var(&a.target);
            let top = a.value.calls.first().copied().filter(|&s| {
                self.call(s)
                    .is_some_and(|c| a.value.text.starts_with(&format!("{}(", c.full)))
            });
            if let Some(t) = top
                && self
                    .call(t)
                    .is_some_and(|c| self.closed.is_match(&c.full) || normalize.is_match(&c.full))
            {
                p.assign_site.push((sc, v, t));
                p.assign_site_d.push((sc, v, t));
                continue;
            }
            for &s in &a.value.calls {
                p.assign_site.push((sc, v, s));
            }
            for s in self.top_calls(&a.value) {
                p.assign_site_d.push((sc, v, s));
            }
            for w in &a.value.vars {
                let (sc2, w2) = (self.scope_of(func, w), self.var(w));
                p.assign_var.push((sc, v, sc2, w2));
            }
            for w in self.direct_vars(&a.value) {
                let (sc2, w2) = (self.scope_of(func, w), self.var(w));
                p.assign_var_d.push((sc, v, sc2, w2));
            }
        }
        for r in &f.returns {
            let func = f.sites[r.site as usize].func;
            for &s in &r.value.calls {
                p.ret_site.push((func, s));
            }
            for s in self.top_calls(&r.value) {
                p.ret_site_d.push((func, s));
            }
            for w in &r.value.vars {
                let (sc, w2) = (self.scope_of(func, w), self.var(w));
                p.ret_var.push((func, sc, w2));
            }
            for w in self.direct_vars(&r.value) {
                let (sc, w2) = (self.scope_of(func, w), self.var(w));
                p.ret_var_d.push((func, sc, w2));
            }
        }
        for &(_, callee, site, _) in &self.g.edges {
            let Some(c) = self.call(site) else { continue };
            let caller = f.sites[site as usize].func;
            let off = self.g.offset.get(&(site, callee)).copied().unwrap_or(0) as usize;
            let params = &f.funcs[callee as usize].params;
            let bind = |pname: &str, e: &Expr, this: &mut Self, p: &mut Prog| {
                let pv = this.var(pname);
                for &s in &e.calls {
                    p.bind_site.push((callee, pv, s));
                }
                for s in this.top_calls(e) {
                    p.bind_site_d.push((callee, pv, s));
                }
                for w in &e.vars {
                    let (sc, w2) = (this.scope_of(caller, w), this.var(w));
                    p.bind_var.push((callee, pv, sc, w2));
                }
                let direct: Vec<String> = this.direct_vars(e).into_iter().cloned().collect();
                for w in &direct {
                    let (sc, w2) = (this.scope_of(caller, w), this.var(w));
                    p.bind_var_d.push((callee, pv, sc, w2));
                }
            };
            for (i, e) in c.args.iter().enumerate() {
                if let Some(prm) = params.get(i + off) {
                    let name = prm.name.clone();
                    bind(&name, e, self, &mut p);
                }
            }
            for (k, e) in &c.kwargs {
                if params.iter().any(|x| &x.name == k) {
                    bind(k, e, self, &mut p);
                }
            }
        }
        let closed_types = Regex::new(&self.cfg.q1.closed_types).ok();
        for (i, func) in f.funcs.iter().enumerate() {
            if func.kind == ScopeKind::Function && !func.name.starts_with('_') && !func.test {
                for prm in &func.params {
                    if matches!(prm.name.as_str(), "self" | "cls" | "hass") {
                        continue;
                    }
                    let v = self.var(&prm.name);
                    let closed_type = closed_types
                        .as_ref()
                        .is_some_and(|r| r.is_match(&prm.annotation));
                    p.seed_var
                        .push((i as Id, v, if closed_type { k_closed } else { k_param }));
                }
            }
        }

        // Question 4 entries and guards.
        let guard_pats = Pats::new(
            &self
                .cfg
                .q4
                .guard
                .iter()
                .map(|g| g.call.clone())
                .collect::<Vec<_>>(),
        );
        let guard_sites: Vec<Id> = f
            .calls
            .iter()
            .filter(|c| guard_pats.is_match(&c.full))
            .map(|c| c.site)
            .collect();
        let all_sites: Vec<Id> = f.calls.iter().map(|c| c.site).collect();
        for &s in &all_sites {
            if guard_sites.iter().any(|&g| self.dominates(g, s)) {
                p.guarded_site.push((s,));
            }
        }
        let (entries, guarded) = self.entries();
        p.entry = entries.iter().map(|(e, _, _)| (*e,)).collect();
        p.guarded_entry = guarded.iter().map(|e| (*e,)).collect();
        p.entry.extend(guarded.iter().map(|e| (*e,)));

        // Question 6 queries, startup functions and resource releases.
        let qn = Regex::new(&self.cfg.q6.query_names).ok();
        let startup = Pats::new(&self.cfg.q6.startup);
        for (i, func) in f.funcs.iter().enumerate() {
            if func.kind == ScopeKind::Function {
                if qn.as_ref().is_some_and(|r| r.is_match(&func.name)) {
                    p.query_fn.push((i as Id,));
                }
                if startup.is_match(&func.name) && func.class.is_none() && !func.test {
                    p.startup.push((i as Id,));
                }
            }
        }
        for (ri, r) in self.cfg.q6.resource.iter().enumerate() {
            let rel = CallPat::new(&r.release);
            for c in &f.calls {
                if rel.hit(c) {
                    p.release
                        .push((c.site, f.sites[c.site as usize].func, ri as u32));
                }
            }
        }

        timing("facts to relations", t_prep);
        let t = std::time::Instant::now();
        p.run();
        timing("datalog", t);
        if std::env::var_os("PROOFSCAN_TIMING").is_some() {
            eprintln!(
                "proofscan: sizes reads {} eff_reach {} open {} qreach {} rel_reach {} site_kind {} var_kind {} ret_kind {} edges {}",
                p.reads.len(),
                p.eff_reach.len(),
                p.open.len(),
                p.qreach.len(),
                p.rel_reach.len(),
                p.site_kind.len(),
                p.var_kind.len(),
                p.ret_kind.len(),
                p.edge.len()
            );
        }
        self.prog = p;
        let t = std::time::Instant::now();
        self.q1();
        timing("q1", t);
        let t = std::time::Instant::now();
        self.q2();
        timing("q2", t);
        let t = std::time::Instant::now();
        let stores = self.stores();
        timing("stores", t);
        let t = std::time::Instant::now();
        self.q3();
        self.stale_write_back(&stores);
        timing("q3", t);
        let t = std::time::Instant::now();
        self.q4(&entries);
        self.guard_order(&stores);
        self.guard_after_wait();
        timing("q4", t);
        let t = std::time::Instant::now();
        self.q5();
        self.name_table_guard();
        self.text_filter_pass();
        timing("q5", t);
        let t = std::time::Instant::now();
        self.q6();
        self.held_state(&stores);
        self.stale_status(&stores);
        self.upgrade_shape(&stores);
        self.fixed_day_span();
        self.pipe_masks_exit();
        self.path_patch_advisories();
        self.grow_and_search();
        self.blocking_unbounded();
        self.untrusted_store_size();
        self.emitted_bytes();
        self.prefix_work();
        self.release_on_panic();
        self.error_keeps_state();
        self.random_property();
        timing("q6", t);
        let t = std::time::Instant::now();
        self.q7();
        timing("q7", t);
        let t = std::time::Instant::now();
        self.q9();
        timing("q9", t);
        let t = std::time::Instant::now();
        self.q10();
        timing("q10", t);
        self.dyn_unknowns();
        if self.g.wide > 0 {
            for q in [1u8, 3, 4, 6] {
                self.not_checked.entry(q).or_default().push(format!(
                    "{} calls by a method name more than {} methods share were not followed",
                    self.g.wide,
                    crate::resolve::MAX_DISPATCH
                ));
            }
        }
    }

    /// Handlers registered by entry specs: (handler, spec name); and those registered guarded.
    fn entries(&mut self) -> (Vec<EntrySpec>, Vec<Id>) {
        let f = self.f;
        let mut open = vec![];
        let mut guarded = vec![];
        for (specs, is_guarded) in [
            (&self.cfg.q4.entry, false),
            (&self.cfg.q4.guarded_entry, true),
        ] {
            for spec in specs.iter() {
                let Ok(re) = Regex::new(&spec.call) else {
                    continue;
                };
                for c in &f.calls {
                    if !re.is_match(&c.full) {
                        continue;
                    }
                    let arg = c.args.get(spec.handler_arg).or_else(|| {
                        spec.handler_kw
                            .as_ref()
                            .and_then(|k| c.kwargs.iter().find(|(n, _)| n == k).map(|(_, e)| e))
                    });
                    let Some(arg) = arg else { continue };
                    let name = arg.text.trim_start_matches("self.");
                    let caller = f.sites[c.site as usize].func;
                    let file = f.sites[c.site as usize].file;
                    let simple = name.chars().all(|ch| ch.is_alphanumeric() || ch == '_');
                    let target = simple.then(|| {
                        f.funcs.iter().enumerate().find(|(_, x)| {
                            x.kind == ScopeKind::Function
                                && x.name == name
                                && x.file == file
                                && (x.parent == Some(caller)
                                    || x.parent == Some(module_of_func(f, caller))
                                    || x.class.is_some())
                        })
                    });
                    match target.flatten() {
                        Some((h, _)) if is_guarded => guarded.push(h as Id),
                        Some((h, _)) => {
                            open.push((h as Id, spec.name.clone(), spec.effects.clone()))
                        }
                        None => {
                            let site = c.site;
                            self.push(4, "entry-handler", Verdict::Unknown, site, format!("{} registers `{}`, which the model cannot resolve to a function", spec.name, arg.text), vec![], vec![]);
                        }
                    }
                }
            }
        }
        (open, guarded)
    }

    /// Kinds of an expression read in `func`.
    fn kinds_of(&self, func: Id, e: &Expr) -> HashSet<u32> {
        let mut out = HashSet::new();
        for &s in &e.calls {
            out.extend(self.kinds().site.get(&s).into_iter().flatten().copied());
        }
        for w in &e.vars {
            let sc = self.scope_of(func, w);
            if let Some(&v) = self.vars.get(w) {
                out.extend(self.var_kinds(sc, v));
            }
        }
        out
    }

    /// The variables an expression uses itself: those only inside a nested call's arguments
    /// reach it through that call's result, which a sanitizer may cut.
    /// A receiver (`self.api` in `self.api.get()`) reaches the expression only through the
    /// call's result as well.
    fn direct_vars<'e>(&self, e: &'e Expr) -> Vec<&'e String> {
        let mut inner: HashSet<String> = HashSet::new();
        for &x in &e.calls {
            if let Some(c) = self.call(x) {
                for a in c.args.iter().chain(c.kwargs.iter().map(|(_, a)| a)) {
                    inner.extend(a.vars.iter().cloned());
                }
                if !c.recv.is_empty() {
                    inner.insert(c.recv.clone());
                    inner.insert(crate::lang::python::var_name(&c.recv));
                }
            }
        }
        e.vars.iter().filter(|v| !inner.contains(*v)).collect()
    }

    /// An expression's outermost calls: those not inside another of its calls' arguments.
    fn top_calls(&self, e: &Expr) -> Vec<Id> {
        let mut inner: HashSet<Id> = HashSet::new();
        for &x in &e.calls {
            if let Some(c) = self.call(x) {
                for a in c.args.iter().chain(c.kwargs.iter().map(|(_, a)| a)) {
                    inner.extend(a.calls.iter().copied());
                }
            }
        }
        e.calls
            .iter()
            .copied()
            .filter(|s| !inner.contains(s))
            .collect()
    }

    /// Kinds an expression carries, counting nested calls by their results.
    fn kinds_direct(&self, func: Id, e: &Expr) -> HashSet<u32> {
        let mut out = HashSet::new();
        for s in self.top_calls(e) {
            out.extend(self.kinds().site.get(&s).into_iter().flatten().copied());
        }
        for w in self.direct_vars(e) {
            let sc = self.scope_of(func, w);
            if let Some(&v) = self.vars.get(w) {
                out.extend(self.var_kinds(sc, v));
            }
        }
        out
    }

    fn var_kinds(&self, sc: Id, v: u32) -> Vec<u32> {
        self.kinds().var.get(&(sc, v)).cloned().unwrap_or_default()
    }

    fn kinds(&self) -> &KindsIndex {
        self.kinds_index.get_or_init(|| {
            let mut ix = KindsIndex::default();
            for &(s, k) in &self.prog.site_kind {
                ix.site.entry(s).or_default().push(k);
            }
            for &(sc, v, k) in &self.prog.var_kind {
                ix.var.entry((sc, v)).or_default().push(k);
            }
            ix
        })
    }

    /// Shortest call path from `from` to `to` over all edges, as witness lines.
    fn path(&self, from: Id, to: Id, avoid: &dyn Fn(Id) -> bool) -> Option<Vec<String>> {
        let mut prev: HashMap<Id, (Id, Id, bool)> = HashMap::new();
        let mut q = VecDeque::from([from]);
        let mut seen = HashSet::from([from]);
        let adj = self.adj.get_or_init(|| {
            let mut adj: HashMap<Id, Vec<(Id, Id, bool)>> = HashMap::new();
            for &(a, b, s, x) in &self.g.edges {
                adj.entry(a).or_default().push((b, s, x));
            }
            adj
        });
        while let Some(n) = q.pop_front() {
            if n == to {
                let mut out = vec![];
                let mut cur = to;
                while let Some(&(p, s, x)) = prev.get(&cur) {
                    let how = if x {
                        "calls"
                    } else {
                        "may call (dispatch by name)"
                    };
                    out.push(format!(
                        "{} {} {}",
                        self.loc(s),
                        how,
                        self.f.func_label(cur)
                    ));
                    cur = p;
                }
                out.reverse();
                return Some(out);
            }
            for &(b, s, x) in adj.get(&n).map(Vec::as_slice).unwrap_or(&[]) {
                if !avoid(s) && seen.insert(b) {
                    prev.insert(b, (n, s, x));
                    q.push_back(b);
                }
            }
        }
        None
    }

    fn provider_name(&self, p: u32) -> String {
        self.fact_names.get(p as usize).cloned().unwrap_or_default()
    }

    /// The provider a fact comes from: `env:HOME` -> `env`.
    fn provider_of_fact(&self, p: u32) -> String {
        self.provider_name(p)
            .split(':')
            .next()
            .unwrap_or("")
            .to_string()
    }

    // ---------- Question 1: one source per fact ----------
    fn q1(&mut self) {
        let f = self.f;
        let declared = self.cfg.q1.declared.clone();
        // Declared providers: every read outside the declared functions is a second source.
        for (prov, funcs) in &declared {
            let allowed: Vec<Id> = (0..f.funcs.len() as Id)
                .filter(|&i| {
                    funcs
                        .iter()
                        .any(|d| self.f.func_label(i).ends_with(d.as_str()))
                })
                .collect();
            for (&s, &pv) in &self.reads_at.clone() {
                if self.provider_of_fact(pv) != *prov {
                    continue;
                }
                let func = f.sites[s as usize].func;
                if allowed.contains(&func) {
                    self.push(
                        1,
                        "declared-provider",
                        Verdict::Proven,
                        s,
                        format!("{prov} read inside its declared provider"),
                        vec![],
                        vec![],
                    );
                } else {
                    let msg = format!(
                        "{prov} read outside its declared provider ({})",
                        funcs.join(", ")
                    );
                    self.push(
                        1,
                        "declared-provider",
                        Verdict::Violated,
                        s,
                        msg,
                        vec![format!("{} reads {prov}", self.loc(s))],
                        vec![],
                    );
                }
            }
        }
        // Undeclared providers: the lowest function whose calls read one provider at two or more sites.
        let mut by_func: HashMap<(Id, u32), Vec<(Id, bool)>> = HashMap::new();
        for &(func, s, pv, x) in &self.prog.vreads {
            if f.funcs[func as usize].test {
                continue;
            }
            by_func.entry((func, pv)).or_default().push((s, x));
        }
        // Each read site: violated when a decision that reaches it reaches another read of the same
        // fact; the witness is the tightest such decision, exact paths first.
        let mut best: HashMap<(Id, u32), (bool, usize, Id)> = HashMap::new();
        let mut seen_sites: HashSet<(Id, u32)> = HashSet::new();
        for (&(func, pv), sites) in &by_func {
            let provider = self.provider_of_fact(pv);
            if declared.contains_key(&provider) || !self.cfg.q1.single_fact.contains(&provider) {
                continue;
            }
            let exact: HashSet<Id> = sites.iter().filter(|(_, x)| *x).map(|(s, _)| *s).collect();
            let any: HashSet<Id> = sites.iter().map(|(s, _)| *s).collect();
            for &s in &any {
                seen_sites.insert((s, pv));
                if any.len() < 2 {
                    continue;
                }
                let is_exact = exact.contains(&s) && exact.len() >= 2;
                let cand = (is_exact, any.len(), func);
                let better = match best.get(&(s, pv)) {
                    None => true,
                    // Exact first, then the fewest reads, then the lowest id, so the choice is stable.
                    Some(&(bx, bn, bf)) => {
                        (is_exact && !bx)
                            || (is_exact == bx && any.len() < bn)
                            || (is_exact == bx && any.len() == bn && func < bf)
                    }
                };
                if better {
                    best.insert((s, pv), cand);
                }
            }
        }
        let mut items: Vec<(Id, u32)> = seen_sites.into_iter().collect();
        items.sort();
        for (s, pv) in items {
            let prov = self.provider_name(pv);
            let Some(&(exact, n, func)) = best.get(&(s, pv)) else {
                self.push(
                    1,
                    "one-reading",
                    Verdict::Proven,
                    s,
                    format!("the only read of {prov} in every decision that reaches it"),
                    vec![],
                    vec![],
                );
                continue;
            };
            let mut others: Vec<Id> = by_func
                .get(&(func, pv))
                .map(|v| {
                    v.iter()
                        .map(|(x, _)| *x)
                        .filter(|x| *x != s)
                        .collect::<HashSet<_>>()
                        .into_iter()
                        .collect()
                })
                .unwrap_or_default();
            others.sort();
            let fd = &f.funcs[func as usize];
            let mut witness = vec![format!(
                "{}:{} {} reads {prov} at {n} sites",
                f.files[fd.file as usize].path,
                fd.line,
                f.func_label(func)
            )];
            witness.extend(
                others
                    .iter()
                    .take(6)
                    .map(|&o| format!("{} also reads {prov}", self.loc(o))),
            );
            if others.len() > 6 {
                witness.push(format!("... {} more", others.len() - 6));
            }
            let label = f.func_label(func);
            if let Some(a) = self
                .cfg
                .q1
                .accepted_reading
                .iter()
                .find(|a| a.function == label && a.provider == prov && n <= a.readings)
            {
                let msg = format!(
                    "{prov} read at {n} sites in {label}, accepted: {}",
                    a.reason
                );
                self.push(1, "one-reading", Verdict::Proven, s, msg, witness, vec![]);
                continue;
            }
            let verdict = if exact {
                Verdict::Violated
            } else {
                Verdict::Unknown
            };
            let assumptions = if exact {
                vec![]
            } else {
                vec!["the other reads are reached only through calls dispatched by name".into()]
            };
            let msg = format!(
                "{prov} is read here and again in one decision ({}): the readings can differ",
                f.func_label(func)
            );
            self.push(1, "one-reading", verdict, s, msg, witness, assumptions);
        }

        // A time from a clock compared with a time from outside: two sources for one fact.
        let clock_kinds: Vec<u32> = ["clock", "monotonic"]
            .iter()
            .filter_map(|k| self.kinds.iter().position(|x| x == k).map(|i| i as u32))
            .collect();
        let ext = self.kind(EXT_TIME);
        let norm = self.kind(NORMALIZED);
        for c in &f.compares {
            let func = f.sites[c.site as usize].func;
            if f.funcs[func as usize].test || !matches!(c.op.as_str(), "<" | ">" | "<=" | ">=") {
                continue;
            }
            let (l, r) = (self.kinds_of(func, &c.left), self.kinds_of(func, &c.right));
            let lc = clock_kinds.iter().any(|k| l.contains(k));
            let rc = clock_kinds.iter().any(|k| r.contains(k));
            if (lc && r.contains(&ext) && !rc) || (rc && l.contains(&ext) && !lc) {
                let (clock_side, ext_side) = if lc {
                    (&c.left, &c.right)
                } else {
                    (&c.right, &c.left)
                };
                let msg = format!(
                    "`{}` (a clock reading) is compared with `{}` (a time parsed from outside): one fact from two sources with their own precision and zone",
                    clock_side.text, ext_side.text
                );
                self.push(
                    1,
                    "mixed-time-sources",
                    Verdict::Violated,
                    c.site,
                    msg,
                    vec![],
                    vec![],
                );
            } else if (l.contains(&norm) && r.contains(&ext) && !rc)
                || (r.contains(&norm) && l.contains(&ext) && !lc)
            {
                let (n_side, ext_side) = if l.contains(&norm) {
                    (&c.left, &c.right)
                } else {
                    (&c.right, &c.left)
                };
                let msg = format!(
                    "`{}` is brought to the outside source's precision before it is compared with `{}`",
                    n_side.text, ext_side.text
                );
                let assume = vec!["the normalizer named by q1.normalize cuts the reading to the precision the outside source writes".to_string()];
                self.push(
                    1,
                    "mixed-time-sources",
                    Verdict::Proven,
                    c.site,
                    msg,
                    vec![],
                    assume,
                );
            }
        }

        // A test double that re-implements the production rules it stands in for.
        let dc = Regex::new(&self.cfg.q1.double_class).ok();
        let need = self.cfg.q1.double_shared_tokens;
        let mut prod: HashMap<&str, Vec<usize>> = HashMap::new();
        for (j, p) in f.funcs.iter().enumerate() {
            if !p.test && p.kind == ScopeKind::Function && p.branches > 0 {
                prod.entry(p.name.as_str()).or_default().push(j);
            }
        }
        for (i, d) in f.funcs.iter().enumerate() {
            let is_double = d.kind == ScopeKind::Function
                && d.class.as_ref().is_some_and(|c| {
                    dc.as_ref().is_some_and(|r| r.is_match(c)) || d.test && d.trait_name.is_some()
                })
                && d.branches > 0;
            if !is_double {
                continue;
            }
            for &j in prod.get(d.name.as_str()).into_iter().flatten() {
                let p = &f.funcs[j];
                if i == j {
                    continue;
                }
                if d.trait_name.is_some() && p.trait_name.is_some() && d.trait_name != p.trait_name
                {
                    continue;
                }
                let pt: HashSet<&String> = p.tokens.iter().collect();
                let shared: Vec<&String> = d
                    .tokens
                    .iter()
                    .filter(|t| pt.contains(t))
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                if shared.len() >= need {
                    let mut sh: Vec<String> = shared.iter().map(|s| s.to_string()).collect();
                    sh.sort();
                    let anchor = f
                        .sites
                        .iter()
                        .position(|s| s.func == i as Id)
                        .map(|x| x as Id);
                    // A double that branches only on its own state returns what it was set to: a
                    // canned answer, not the production rules applied to an input.
                    if let Some(anchor) = anchor
                        && d.param_decisions == 0
                    {
                        let msg = format!(
                            "test double {} answers from the state it was set to, not from its input: no second source for the rules of {}",
                            f.func_label(i as Id),
                            f.func_label(j as Id),
                        );
                        let witness = vec![
                            format!("{}:{} double", f.files[d.file as usize].path, d.line),
                            format!("{}:{} production", f.files[p.file as usize].path, p.line),
                            format!("shared outcomes: {}", sh.join(", ")),
                        ];
                        self.push(
                            1,
                            "double-reimplements",
                            Verdict::Proven,
                            anchor,
                            msg,
                            witness,
                            vec!["no branch of the double reads a parameter: what it returns is chosen by the test that built it".into()],
                        );
                    } else if let Some(anchor) = anchor {
                        let msg = format!(
                            "test double {} re-implements the rules of {} ({} shared decision tokens): a second source for what the code under test decides",
                            f.func_label(i as Id),
                            f.func_label(j as Id),
                            sh.len()
                        );
                        let witness = vec![
                            format!("{}:{} double", f.files[d.file as usize].path, d.line),
                            format!("{}:{} production", f.files[p.file as usize].path, p.line),
                            format!("shared: {}", sh.join(", ")),
                        ];
                        self.push(
                            1,
                            "double-reimplements",
                            Verdict::Violated,
                            anchor,
                            msg,
                            witness,
                            vec![],
                        );
                    }
                }
            }
        }
    }

    // ---------- Question 2: provenance of stand-ins ----------
    fn q2(&mut self) {
        let f = self.f;
        let guard = Regex::new(&self.cfg.q2.guard_names).ok();
        for p in &f.patches {
            let name = p.target.rsplit('.').next().unwrap_or(&p.target);
            if guard.as_ref().is_some_and(|g| g.is_match(name)) {
                let opt = if p.opt_out {
                    " (a test may opt out, so every other test runs without the guard)"
                } else {
                    ""
                };
                self.push(
                    2,
                    "suite-disables-guard",
                    Verdict::Violated,
                    p.site,
                    format!(
                        "an autouse fixture replaces `{}` for the whole suite{opt}",
                        p.target
                    ),
                    vec![],
                    vec![],
                );
            }
        }
        if self.cfg.q2.wire.is_empty() {
            self.not_checked
                .entry(2)
                .or_default()
                .push("no wire declared ([[q2.wire]]), so fixture literals are not traced".into());
        }
        for w in self.cfg.q2.wire.clone() {
            let Ok(re) = Regex::new(&w.pattern) else {
                continue;
            };
            let globs = w
                .captures
                .iter()
                .filter_map(|g| globset::Glob::new(g).ok())
                .fold(globset::GlobSetBuilder::new(), |mut b, g| {
                    b.add(g);
                    b
                });
            let Ok(set) = globs.build() else { continue };
            let mut captured: Vec<String> = vec![];
            for (path, text) in self.texts {
                if set.is_match(path) {
                    captured.extend(
                        text.lines()
                            .map(str::trim)
                            .filter(|l| re.is_match(l))
                            .map(str::to_string),
                    );
                    // Literals inside source captures (a test file of the real client) count too.
                    for part in text.split(['"', '\'']) {
                        if re.is_match(part) {
                            captured.push(part.to_string());
                        }
                    }
                }
            }
            for path in &w.capture_files {
                match std::fs::read_to_string(path) {
                    Ok(text) => captured.extend(
                        text.lines()
                            .map(str::trim)
                            .filter(|l| re.is_match(l))
                            .map(str::to_string),
                    ),
                    Err(e) => self
                        .not_checked
                        .entry(2)
                        .or_default()
                        .push(format!("capture file {path} could not be read: {e}")),
                }
            }
            let shapes: Vec<Vec<(char, usize)>> = captured.iter().map(|c| shape(c)).collect();
            for s in &f.strs {
                if !re.is_match(&s.text) {
                    continue;
                }
                let site = s.site;
                if captured.is_empty() {
                    self.push(
                        2,
                        "wire-provenance",
                        Verdict::Violated,
                        site,
                        format!(
                            "`{}` stands in for {} but no capture of {} exists under {}",
                            s.text,
                            w.name,
                            w.name,
                            w.captures
                                .iter()
                                .chain(&w.capture_files)
                                .cloned()
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        vec![],
                        vec![],
                    );
                    continue;
                }
                let mine = shape(&s.text);
                let same_code: Vec<&Vec<(char, usize)>> = shapes
                    .iter()
                    .filter(|c| c.first() == mine.first())
                    .collect();
                match field_mismatch(&mine, &same_code) {
                    None if captured.iter().any(|c| c == &s.text) || !same_code.is_empty() => {
                        self.push(
                            2,
                            "wire-provenance",
                            Verdict::Proven,
                            site,
                            format!("`{}` has the shape of a captured {} frame", s.text, w.name),
                            vec![],
                            vec![],
                        );
                    }
                    None => self.push(
                        2,
                        "wire-provenance",
                        Verdict::Violated,
                        site,
                        format!(
                            "`{}` matches no captured {} frame of its kind",
                            s.text, w.name
                        ),
                        vec![],
                        vec![],
                    ),
                    Some(why) => self.push(
                        2,
                        "wire-provenance",
                        Verdict::Violated,
                        site,
                        format!(
                            "`{}` differs from every captured {} frame: {why}",
                            s.text, w.name
                        ),
                        vec![],
                        vec![],
                    ),
                }
            }
        }
    }

    // ---------- Question 3: check and use together ----------
    fn q3(&mut self) {
        let f = self.f;
        let declared = Pats::new(
            &self
                .cfg
                .q3
                .guards
                .iter()
                .map(|g| format!(r"(^|\.){g}$"))
                .collect::<Vec<_>>(),
        );
        let reads_of: HashMap<Id, HashSet<u32>> =
            self.prog
                .reads
                .iter()
                .fold(HashMap::new(), |mut m, (func, _, p, _)| {
                    m.entry(*func).or_default().insert(*p);
                    m
                });
        let eff: HashSet<Id> = self.prog.eff_reach.iter().map(|(func, _)| *func).collect();
        let targets = |s: Id| -> Vec<Id> {
            self.g
                .targets
                .get(&s)
                .map(|v| v.iter().map(|(t, _)| *t).collect())
                .unwrap_or_default()
        };
        let mut calls_in: HashMap<Id, Vec<&crate::facts::Call>> = HashMap::new();
        for c in &f.calls {
            calls_in
                .entry(f.sites[c.site as usize].func)
                .or_default()
                .push(c);
        }
        let mut out = vec![];
        for gc in &f.calls {
            let is_guard = declared.is_match(&gc.full) || gc.predicate;
            if !is_guard || f.funcs[f.sites[gc.site as usize].func as usize].test {
                continue;
            }
            let verified: HashSet<u32> = targets(gc.site)
                .iter()
                .flat_map(|t| reads_of.get(t).cloned().unwrap_or_default())
                .collect();
            if verified.is_empty() {
                continue;
            }
            let func = f.sites[gc.site as usize].func;
            for ec in calls_in.get(&func).into_iter().flatten() {
                if f.sites[ec.site as usize].func != func || !self.dominates(gc.site, ec.site) {
                    continue;
                }
                let effectful = self.effects_at.contains_key(&ec.site)
                    || targets(ec.site).iter().any(|t| eff.contains(t));
                if !effectful {
                    continue;
                }
                let args: Vec<Id> = ec
                    .args
                    .iter()
                    .chain(ec.kwargs.iter().map(|(_, e)| e))
                    .flat_map(|e| e.calls.iter().copied())
                    .collect();
                for r in args {
                    let rp: HashSet<u32> = self
                        .reads_at
                        .get(&r)
                        .into_iter()
                        .copied()
                        .chain(
                            targets(r)
                                .iter()
                                .flat_map(|t| reads_of.get(t).cloned().unwrap_or_default()),
                        )
                        .collect();
                    if let Some(p) = rp.intersection(&verified).next() {
                        out.push((ec.site, gc.site, r, *p));
                    }
                }
            }
        }
        out.sort_by_key(|&(e, g, r, p)| (r, p, g, e));
        let mut grouped: BTreeMap<(Id, u32), (Vec<Id>, Id)> = BTreeMap::new();
        for (e, g, r, p) in out {
            let slot = grouped.entry((r, p)).or_insert((vec![], e));
            if !slot.0.contains(&g) {
                slot.0.push(g);
            }
        }
        for ((r, p), (guards, e)) in grouped {
            let prov = self.provider_name(p);
            let msg = format!("the {prov} verified by the guard is read again for the effect");
            let mut witness: Vec<String> = guards
                .iter()
                .map(|&g| format!("{} guard verifies {prov}", self.loc(g)))
                .collect();
            witness.push(format!("{} reads {prov} again", self.loc(r)));
            witness.push(format!("{} effect uses the second reading", self.loc(e)));
            self.push(
                3,
                "reread-after-check",
                Verdict::Violated,
                r,
                msg,
                witness,
                vec![],
            );
        }
    }

    // ---------- Question 4: guard at the effect ----------
    fn q4(&mut self, entries: &[EntrySpec]) {
        let f = self.f;
        if self.cfg.q4.entry.is_empty() && self.cfg.q4.guarded_entry.is_empty() {
            self.not_checked
                .entry(4)
                .or_default()
                .push("no entry points declared ([[q4.entry]] or a profile)".into());
            return;
        }
        let guarded: HashSet<Id> = self.prog.guarded_site.iter().map(|(s,)| *s).collect();
        let mut seen: HashSet<(Id, Id)> = HashSet::new();
        for &(e, ref spec, ref kinds) in entries {
            let mut hit = false;
            let opens: Vec<(Id, Id, bool)> = self.prog.open.to_vec();
            let effects: Vec<(Id, u32)> = self.effects_at.iter().map(|(a, b)| (*a, *b)).collect();
            for (e2, func, exact) in opens {
                if e2 != e {
                    continue;
                }
                for &(s, k) in &effects {
                    if !kinds.is_empty() && !kinds.contains(&self.effect_kinds[k as usize]) {
                        continue;
                    }
                    if f.sites[s as usize].func != func
                        || guarded.contains(&s)
                        || !seen.insert((e, s))
                    {
                        continue;
                    }
                    hit = true;
                    let mut witness = vec![format!(
                        "{}:{} {} `{}` is registered without a guard",
                        f.files[f.funcs[e as usize].file as usize].path,
                        f.funcs[e as usize].line,
                        spec,
                        f.funcs[e as usize].name
                    )];
                    witness.extend(
                        self.path(e, func, &|s| guarded.contains(&s))
                            .unwrap_or_default(),
                    );
                    witness.push(format!(
                        "{} {} effect",
                        self.loc(s),
                        self.effect_kinds[k as usize]
                    ));
                    let verdict = if exact {
                        Verdict::Violated
                    } else {
                        Verdict::Unknown
                    };
                    let msg = format!(
                        "{} reaches a {} effect with no guard on the path",
                        f.func_label(e),
                        self.effect_kinds[k as usize]
                    );
                    self.push(4, "unguarded-effect", verdict, s, msg, witness, vec![]);
                }
            }
            if !hit && let Some(anchor) = f.sites.iter().position(|s| s.func == e) {
                self.push(
                    4,
                    "unguarded-effect",
                    Verdict::Proven,
                    anchor as Id,
                    format!("{} reaches no effect without a guard", f.func_label(e)),
                    vec![],
                    vec![],
                );
            }
        }
    }

    // ---------- Question 5: closed sets ----------
    fn q5(&mut self) {
        let f = self.f;
        // A check on a segment lies in the same function as the path it guards.
        let mut calls_in: HashMap<Id, Vec<&crate::facts::Call>> = HashMap::new();
        for c in &f.calls {
            calls_in
                .entry(f.sites[c.site as usize].func)
                .or_default()
                .push(c);
        }
        let mut assigns_in: HashMap<Id, Vec<&crate::facts::Assign>> = HashMap::new();
        for a in &f.assigns {
            assigns_in
                .entry(f.sites[a.site as usize].func)
                .or_default()
                .push(a);
        }
        let (k_param, k_external, k_closed) =
            (self.kind(PARAM), self.kind(EXTERNAL), self.kind(CLOSED));
        for c in &f.composes {
            let func = f.sites[c.site as usize].func;
            if f.funcs[func as usize].test {
                continue;
            }
            let mut open_vars = vec![];
            for seg in &c.segments {
                let inner = seg.text.trim_start_matches('{').trim_end_matches('}');
                let top_closed = seg
                    .calls
                    .first()
                    .and_then(|&s| self.call(s))
                    .is_some_and(|cc| {
                        self.closed.is_match(&cc.full)
                            && (inner.starts_with(&format!("{}(", cc.full))
                                || inner.ends_with(')')
                                    && inner.contains(&format!("{}(", cc.full))
                                    && !inner[inner.find(&format!("{}(", cc.full)).unwrap_or(0)..]
                                        .contains(")."))
                    });
                if top_closed {
                    continue;
                }
                for v in &seg.vars {
                    if v.chars()
                        .all(|ch| ch.is_ascii_uppercase() || ch == '_' || ch.is_ascii_digit())
                    {
                        continue;
                    }
                    let sc = self.scope_of(func, v);
                    let ks: HashSet<u32> = self
                        .vars
                        .get(v.as_str())
                        .map(|&id| self.var_kinds(sc, id).into_iter().collect())
                        .unwrap_or_default();
                    let checked = calls_in.get(&func).into_iter().flatten().any(|cc| {
                        self.closed.is_match(&cc.full)
                            && cc
                                .args
                                .iter()
                                .chain(cc.kwargs.iter().map(|(_, e)| e))
                                .any(|a| a.vars.contains(v))
                            && self.dominates(cc.site, c.site)
                    });
                    if (ks.contains(&k_param) || ks.contains(&k_external))
                        && !ks.contains(&k_closed)
                        && !checked
                        && !open_vars.contains(v)
                    {
                        open_vars.push(v.clone());
                    }
                }
            }
            let what = if c.url { "URL" } else { "path" };
            if !open_vars.is_empty()
                && let Some(line) = self.contained(
                    c,
                    calls_in.get(&func).map(Vec::as_slice).unwrap_or_default(),
                    assigns_in.get(&func).map(Vec::as_slice).unwrap_or_default(),
                )
            {
                let msg = format!(
                    "`{}` goes into the {what} unparsed, and the composed {what} is checked to stay under its root at line {line}",
                    open_vars.join("`, `")
                );
                let assume = vec![format!(
                    "the containment check at line {line} runs before every use of the {what}"
                )];
                self.push(
                    5,
                    "closed-segment",
                    Verdict::Proven,
                    c.site,
                    msg,
                    vec![],
                    assume,
                );
                continue;
            }
            if open_vars.is_empty() {
                self.push(
                    5,
                    "closed-segment",
                    Verdict::Proven,
                    c.site,
                    format!("every value in this {what} is a constant or parsed into a closed set"),
                    vec![],
                    vec![],
                );
            } else {
                let mut msg = format!(
                    "`{}` goes into a {what} segment unparsed: a value outside the expected set (`/`, `..`, `?`) changes what the {what} reaches",
                    open_vars.join("`, `")
                );
                let mut witness = vec![format!("{} {}", self.loc(c.site), c.parts.text)];
                // A refusing test that is not a closed parse filters the listed forms only.
                if let Some(cc) = calls_in.get(&func).into_iter().flatten().find(|cc| {
                    cc.predicate
                        && self.dominates(cc.site, c.site)
                        && cc
                            .args
                            .iter()
                            .any(|a| a.vars.iter().any(|v| open_vars.contains(v)))
                }) {
                    msg.push_str(&format!(
                        "; `{}` refuses the forms it lists, an open set",
                        cc.full
                    ));
                    witness.push(format!("{} checked by `{}`", self.loc(cc.site), cc.full));
                }
                self.push(
                    5,
                    "closed-segment",
                    Verdict::Violated,
                    c.site,
                    msg,
                    witness,
                    vec![],
                );
            }
        }
        let accepted = self.cfg.q5.accepted_deny.clone();
        for d in &f.denies {
            let loc = self.loc(d.site);
            if let Some(a) = accepted.iter().find(|a| loc.ends_with(&a.site)) {
                self.push(
                    5,
                    "open-deny",
                    Verdict::Proven,
                    d.site,
                    format!("deny list accepted: {}", a.reason),
                    vec![],
                    vec![],
                );
            } else {
                let msg = format!(
                    "a refusal decided by matching a deny pattern (`{}`): an open set misses forms nobody listed and catches neighbors it was not meant for; an allowlist of what may pass is closed",
                    truncate(&d.what, 120)
                );
                self.push(
                    5,
                    "open-deny",
                    Verdict::Violated,
                    d.site,
                    msg,
                    vec![],
                    vec![],
                );
            }
        }
    }

    /// The line of a refusing containment check on the variable a composed path is assigned to
    /// (`p.resolve().parent != root.resolve()`, `p.is_relative_to(root)`, `commonpath`), if any.
    fn contained(
        &self,
        c: &crate::facts::Compose,
        calls: &[&crate::facts::Call],
        assigns: &[&crate::facts::Assign],
    ) -> Option<u32> {
        let f = self.f;
        let site = &f.sites[c.site as usize];
        let target = assigns.iter().find(|a| {
            let s = &f.sites[a.site as usize];
            s.func == site.func
                && s.line == site.line
                && a.value.text.contains(c.parts.text.as_str())
        })?;
        let var = target.target.as_str();
        calls
            .iter()
            .filter(|cc| {
                cc.predicate
                    && f.sites[cc.site as usize].func == site.func
                    && f.sites[cc.site as usize].line >= site.line
            })
            .filter(|cc| {
                matches!(
                    cc.name.as_str(),
                    "resolve"
                        | "is_relative_to"
                        | "relative_to"
                        | "commonpath"
                        | "realpath"
                        | "canonicalize"
                        | "starts_with"
                )
            })
            .find(|cc| cc.recv == var || cc.args.iter().any(|a| a.vars.iter().any(|v| v == var)))
            .map(|cc| f.sites[cc.site as usize].line)
    }

    // ---------- Question 9: release on every exit ----------
    fn q9(&mut self) {
        use crate::config::{PatternKind, lang_scoped, pattern_kind};
        let f = self.f;
        type Pat = (PatternKind, Option<crate::facts::Lang>, Regex);
        let compile = |v: &[String]| -> Vec<Pat> {
            v.iter()
                .filter_map(|p| {
                    let (k, rest) = pattern_kind(p);
                    let (l, rest) = lang_scoped(rest);
                    Regex::new(rest).ok().map(|r| (k, l, r))
                })
                .collect()
        };
        let report: Vec<Regex> = self
            .cfg
            .q1
            .report
            .iter()
            .filter_map(|r| Regex::new(r).ok())
            .collect();
        let no_raise: Vec<Regex> = self
            .cfg
            .q9
            .no_raise
            .iter()
            .filter_map(|r| Regex::new(r).ok())
            .collect();
        let lang_at = |s: Id| f.files[f.sites[s as usize].file as usize].lang;
        // (site, text) of each call and assignment, by function, in source order.
        let mut calls_in: HashMap<Id, Vec<&crate::facts::Call>> = HashMap::new();
        for c in &f.calls {
            calls_in
                .entry(f.sites[c.site as usize].func)
                .or_default()
                .push(c);
        }
        let hits = |pats: &[Pat],
                    site: Id,
                    call: Option<&crate::facts::Call>,
                    assign: Option<&str>| {
            let lang = lang_at(site);
            pats.iter().any(|(k, l, r)| {
                l.is_none_or(|l| l == lang)
                    && match (k, call, assign) {
                        (PatternKind::Call, Some(c), _) => r.is_match(&c.full),
                        (PatternKind::Arg, Some(c), _) => c.str_args.iter().any(|a| r.is_match(a)),
                        (PatternKind::Assign, _, Some(t)) => r.is_match(t),
                        _ => false,
                    }
            })
        };
        let resources = self.cfg.q9.resource.clone();
        for res in &resources {
            let (acq, rel) = (compile(&res.acquire), compile(&res.release));
            // Every acquire and release site: (site, line, is_release).
            let mut sites: Vec<(Id, bool)> = vec![];
            for c in &f.calls {
                if f.funcs[f.sites[c.site as usize].func as usize].test {
                    continue;
                }
                if hits(&rel, c.site, Some(c), None) {
                    sites.push((c.site, true));
                } else if hits(&acq, c.site, Some(c), None) {
                    sites.push((c.site, false));
                }
            }
            for a in &f.assigns {
                if f.funcs[f.sites[a.site as usize].func as usize].test {
                    continue;
                }
                let t = format!("{} = {}", a.target, a.value.text);
                if hits(&rel, a.site, None, Some(&t)) {
                    sites.push((a.site, true));
                } else if hits(&acq, a.site, None, Some(&t)) {
                    sites.push((a.site, false));
                }
            }
            sites.sort();
            for &(r, is_release) in &sites {
                if !is_release {
                    continue;
                }
                let rs = &f.sites[r as usize];
                let others = calls_in
                    .get(&rs.func)
                    .map(Vec::as_slice)
                    .unwrap_or_default();
                // A call can stop the block unless it only reports, is taken not to raise, or is
                // the condition that decides whether to release at all.
                let risky = |c: &&&crate::facts::Call| {
                    c.site != r
                        && !c.predicate
                        && !report.iter().any(|p| p.is_match(&c.full))
                        && !no_raise.iter().any(|p| p.is_match(&c.full))
                        && !sites.iter().any(|(s, rl)| *rl && *s == c.site)
                };
                if let Some(fid) = rs.ctx.finally_id {
                    // A release in a finally block: nothing before it in that block may raise.
                    let before = others.iter().filter(risky).find(|c| {
                        let cs = &f.sites[c.site as usize];
                        cs.ctx.finally_id == Some(fid) && !cs.ctx.shielded && cs.line < rs.line
                    });
                    match before {
                        Some(c) => {
                            let msg = format!(
                                "the {} is released in a finally block after `{}`, which can raise or be cancelled first and leave it held",
                                res.name, c.full
                            );
                            let witness = vec![
                                format!("{} `{}` runs first in the finally block", self.loc(c.site), c.full),
                                format!("{} releases the {}", self.loc(r), res.name),
                            ];
                            self.push(9, "release-interrupted", Verdict::Violated, r, msg, witness, vec![]);
                        }
                        None => self.push(
                            9,
                            "release-interrupted",
                            Verdict::Proven,
                            r,
                            format!("the {} is released before anything in its finally block can raise", res.name),
                            vec![],
                            vec!["a nested try inside the finally block catches what its body raises".into()],
                        ),
                    }
                    continue;
                }
                if rs.ctx.handler.is_some() {
                    continue;
                }
                // A release on the ordinary path: a raise between the acquire and it skips it.
                let Some(&(a, _)) = sites.iter().rev().find(|(s, rl)| {
                    !*rl && {
                        let x = &f.sites[*s as usize];
                        x.func == rs.func && x.line < rs.line
                    }
                }) else {
                    continue;
                };
                let al = f.sites[a as usize].line;
                let handled = sites.iter().any(|(s, rl)| {
                    let x = &f.sites[*s as usize];
                    *rl && *s != r && x.func == rs.func && x.ctx.handler.is_some()
                });
                let between = others.iter().filter(risky).find(|c| {
                    let cs = &f.sites[c.site as usize];
                    c.site != a && cs.line > al && cs.line < rs.line
                });
                match (between, handled) {
                    (Some(c), false) => {
                        let msg = format!(
                            "the {} taken at line {al} is released only on the ordinary path: a raise or cancellation in `{}` leaves it held",
                            res.name, c.full
                        );
                        let witness = vec![
                            format!("{} acquires the {}", self.loc(a), res.name),
                            format!("{} `{}` can raise", self.loc(c.site), c.full),
                            format!("{} releases it outside any finally block", self.loc(r)),
                        ];
                        self.push(
                            9,
                            "release-on-error",
                            Verdict::Violated,
                            r,
                            msg,
                            witness,
                            vec![],
                        );
                    }
                    (Some(_), true) => self.push(
                        9,
                        "release-on-error",
                        Verdict::Proven,
                        r,
                        format!("the {} is also released in an exception handler", res.name),
                        vec![],
                        vec!["the handler catches every exception, cancellation included".into()],
                    ),
                    (None, _) => self.push(
                        9,
                        "release-on-error",
                        Verdict::Proven,
                        r,
                        format!(
                            "nothing between taking the {} and releasing it can raise",
                            res.name
                        ),
                        vec![],
                        vec![],
                    ),
                }
            }
        }
    }

    // ---------- Question 10: secrets never reach a sink ----------
    fn q10(&mut self) {
        let f = self.f;
        let k_secret = self.kind(SECRET);
        let sinks: Vec<CallPat> = self
            .cfg
            .q10
            .sink
            .iter()
            .chain(&self.cfg.q1.report)
            .map(|s| CallPat::new(s))
            .collect();
        let sources: Vec<CallPat> = self
            .cfg
            .q10
            .source
            .iter()
            .map(|s| CallPat::new(s))
            .collect();
        let pipe_ok = Regex::new(&self.cfg.q10.pipe_sanitize).ok();
        let quiet_kw = Regex::new(&self.cfg.q10.not_sink_kwarg).ok();
        let print_cmd = Regex::new(&self.cfg.q10.print_cmd).ok();
        let wrapper = Regex::new(&self.cfg.q10.wrapper_cmd).ok();
        let quiet = Regex::new(&self.cfg.q10.quiet_arg).ok();
        let word = Regex::new(
            r"(^|[\s;|&(])(cat|tac|head|tail|less|more|jq|yq|base64|xxd|strings|grep|sed|awk)\s",
        )
        .ok();
        let prints = |c: &crate::facts::Call| {
            let is = |r: &Option<Regex>, t: &str| r.as_ref().is_some_and(|r| r.is_match(t));
            // Only grep and sed have flags that silence what they read.
            let searcher = matches!(c.full.as_str(), "grep" | "egrep" | "sed");
            if searcher && c.str_args.iter().any(|a| is(&quiet, a)) {
                return false;
            }
            is(&print_cmd, &c.full)
                || is(&wrapper, &c.full) && c.str_args.iter().any(|a| is(&word, a))
        };
        let src_sites: HashSet<Id> = self
            .prog
            .src_site
            .iter()
            .filter(|(_, k)| *k == k_secret)
            .map(|(s, _)| *s)
            .collect();
        let mut src_in: HashMap<Id, Vec<Id>> = HashMap::new();
        for &s in &src_sites {
            src_in.entry(f.sites[s as usize].func).or_default().push(s);
        }
        let mut out: Vec<Pending> = vec![];
        let mut leaked_from: HashSet<Id> = HashSet::new();
        for c in &f.calls {
            let st = &f.sites[c.site as usize];
            if f.funcs[st.func as usize].test {
                continue;
            }
            let lang = f.files[st.file as usize].lang;
            // A shell command that reads a store and prints it.
            if lang == crate::facts::Lang::Bash && sources.iter().any(|x| x.hit_in(c, lang)) {
                if !c.output_only || !prints(c) {
                    continue;
                }
                let tail = c
                    .pipe_to
                    .iter()
                    .find(|p| pipe_ok.as_ref().is_some_and(|r| r.is_match(p)));
                match tail {
                    Some(t) => out.push((
                        Verdict::Proven,
                        c.site,
                        format!("the store read here is printed only through `{t}`"),
                        vec![],
                        vec!["that command prints a length or a digest, never the value".into()],
                    )),
                    None => {
                        leaked_from.insert(c.site);
                        let to = if c.pipe_to.is_empty() {
                            "to the output".to_string()
                        } else {
                            format!("through `{}` to the output", c.pipe_to.join(" | "))
                        };
                        out.push((
                            Verdict::Violated,
                            c.site,
                            format!("this command reads a credential store and its contents go {to}, where a transcript or log keeps them"),
                            vec![format!("{} {}", self.loc(c.site), truncate(&c.args.first().map(|a| a.text.clone()).unwrap_or_default(), 120))],
                            vec![],
                        ));
                    }
                }
                continue;
            }
            if !sinks.iter().any(|x| x.hit_in(c, lang)) {
                continue;
            }
            let mut tainted = vec![];
            for (i, e) in c.args.iter().enumerate() {
                if self.kinds_direct(st.func, e).contains(&k_secret) {
                    tainted.push(format!("argument {}", i + 1));
                }
            }
            for (k, e) in &c.kwargs {
                if quiet_kw.as_ref().is_some_and(|r| r.is_match(k)) {
                    continue;
                }
                if self.kinds_direct(st.func, e).contains(&k_secret) {
                    tainted.push(format!("`{k}=`"));
                }
            }
            if tainted.is_empty() {
                continue;
            }
            let local = src_in.get(&st.func).cloned().unwrap_or_default();
            leaked_from.extend(local.iter().copied());
            let mut witness: Vec<String> = local
                .iter()
                .map(|&s| format!("{} reads a credential", self.loc(s)))
                .collect();
            if witness.is_empty() {
                witness.push(
                    "the credential arrives through a parameter, an attribute or a call's result"
                        .into(),
                );
            }
            witness.push(format!(
                "{} passes it to `{}` ({})",
                self.loc(c.site),
                c.full,
                tainted.join(", ")
            ));
            out.push((
                Verdict::Violated,
                c.site,
                format!(
                    "a value derived from a credential reaches `{}`, which puts it where others read it (a log, an argument list, error text)",
                    c.full
                ),
                witness,
                vec![],
            ));
        }
        let mut srcs: Vec<Id> = src_sites.into_iter().collect();
        srcs.sort();
        for s in srcs {
            if leaked_from.contains(&s) {
                continue;
            }
            let lang = f.files[f.sites[s as usize].file as usize].lang;
            if lang == crate::facts::Lang::Bash {
                continue;
            }
            out.push((
                Verdict::Proven,
                s,
                "the credential read here reaches no log, argument list or error text the model follows".into(),
                vec![],
                vec![
                    "a sanitizer call returns no part of the value".into(),
                    "a value is not passed on through a subscript, an attribute store or a container method".into(),
                ],
            ));
        }
        for (v, s, msg, w, a) in out {
            let rule =
                if f.files[f.sites[s as usize].file as usize].lang == crate::facts::Lang::Bash {
                    "store-printed"
                } else {
                    "secret-sink"
                };
            self.push(10, rule, v, s, msg, w, a);
        }
    }

    // ---------- Question 6: bounds and exits ----------
    fn pending_deliveries_have_no_attempt_limit(&self, repo: Id) -> bool {
        let mut stores = HashMap::new();
        for call in &self.f.calls {
            let site = &self.f.sites[call.site as usize];
            let file = &self.f.files[site.file as usize];
            let function = &self.f.funcs[site.func as usize];
            let Some(class) = function.class.as_deref() else {
                continue;
            };
            if file.repo != repo {
                continue;
            }
            let evidence = match (function.name.as_str(), call.name.as_str()) {
                ("pending", "prepare") => call.str_args.iter().any(|sql| {
                    sql.strip_prefix("SELECT id,binding_id,source_id,text FROM deliveries WHERE state='pending' ORDER BY ")
                        .is_some_and(|tail| matches!(tail, "attempts,id LIMIT 100" | "id LIMIT 100"))
                }).then_some(1),
                ("delivery_result", "execute") => call.str_args.iter().any(|sql| {
                    sql == "UPDATE deliveries SET state=CASE WHEN ?2 THEN 'sent' ELSE 'pending' END, attempts=attempts+1, last_error=?3 WHERE id=?1"
                }).then_some(2),
                _ => None,
            };
            if let Some(evidence) = evidence {
                *stores.entry((site.file, class)).or_default() |= evidence;
            }
        }
        stores.values().any(|&evidence: &u8| evidence == 3)
    }

    fn q6(&mut self) {
        let f = self.f;
        let wall = self
            .kinds
            .iter()
            .position(|k| k == "clock")
            .map(|i| i as u32);
        let write_funcs: HashSet<Id> = self
            .effects_at
            .keys()
            .map(|s| f.sites[*s as usize].func)
            .collect();
        for p in &f.prunes {
            let func = f.sites[p.site as usize].func;
            if f.funcs[func as usize].test {
                continue;
            }
            let ks = self.kinds_of(func, &p.bound);
            let wall_set = wall.is_some_and(|w| ks.contains(&w));
            let writes = p.writes_back || write_funcs.contains(&func);
            if wall_set && writes {
                let msg = format!(
                    "a kept collection is cut by `{}`, a bound set by the wall clock: a clock stepped forward drops what should stay, and one stepped back keeps everything",
                    p.bound.text
                );
                self.push(
                    6,
                    "wall-date-bound",
                    Verdict::Violated,
                    p.site,
                    msg,
                    vec![],
                    vec![],
                );
            } else if writes {
                self.push(
                    6,
                    "wall-date-bound",
                    Verdict::Proven,
                    p.site,
                    "the bound on this kept collection is not set by the wall clock".into(),
                    vec![],
                    vec![],
                );
            }
        }
        let mut delivery_stores = HashMap::new();
        for r in &f.retries {
            let mut witness = vec![];
            let (verdict, message, assumptions) = match &r.bound {
                RetryBound::Keyword(keyword) => (
                    Verdict::Unknown,
                    format!("no exiting comparison was found that establishes a retry bound (keyword `{keyword}`)"),
                    vec![],
                ),
                RetryBound::None => (
                    Verdict::Violated,
                    "a loop retries after an error with no counter or deadline".into(),
                    vec![],
                ),
                RetryBound::Counter(check) => (
                    Verdict::Proven,
                    format!("the counter advances toward an exit on every retry: {check}"),
                    vec!["the counter and limit are ordinary integers, the limit is invariant, the counter cannot wrap or stop advancing before the exit, and calls do not rebind them".into()],
                ),
                RetryBound::Deadline(check) => (
                    Verdict::Proven,
                    format!("the deadline comparison is refreshed on every retry: {check}"),
                    vec!["the standard clock advances past the finite, invariant deadline, and the operations between readings return".into()],
                ),
                RetryBound::RemainingDuration(check) => (
                    Verdict::Proven,
                    format!("the fresh remaining duration controls a deadline exit on every retry: {check}"),
                    vec!["the standard Instant clock advances past the fixed deadline, its remaining duration saturates to zero or its checked subtraction returns None, and operations between readings return".into()],
                ),
                RetryBound::CivilDeadline(check) => (
                    Verdict::Proven,
                    format!("every retry samples the civil clock and checks the fixed deadline: {check}"),
                    vec!["the Jiff or Chrono civil clock eventually reaches and passes the deadline in the same time basis even if it steps backward, and operations between readings return".into()],
                ),
                RetryBound::EnumeratorDeadline(check, protocol) => (
                    Verdict::Proven,
                    format!("each back edge checks the deadline or consumes an item from the enumerator: {check}"),
                    vec![format!("the {protocol} enumerator is finite and forward-only, successful reads consume an item, the monotonic clock advances past the fixed deadline, and operations between readings return")],
                ),
                RetryBound::FiniteGrowth(check) => (
                    Verdict::Proven,
                    format!("every retry strictly grows the allocation using a finite-width size: {check}"),
                    vec!["standard Vec length and integer arithmetic preserve strict growth, the finite-width byte count fits usize without truncation or overflow, and the operation cannot change the Vec length through its data pointer".into()],
                ),
                RetryBound::ItemReplay(check) => (
                    Verdict::Proven,
                    format!("each popped item can replay at most once: {check}"),
                    vec!["the queue moves each item with its flag intact, the replay flag cannot be reset between pop and requeue, and external producers do not submit the same item anew".into()],
                ),
                RetryBound::UnknownReplay(line) => {
                    let site = self.loc(r.site);
                    let file = site.rsplit_once(':').map_or(site.as_str(), |(file, _)| file);
                    witness.push(format!("{file}:{line} an item goes back on the queue"));
                    (
                        Verdict::Unknown,
                        "the item is requeued across worker branches, and a persistent per-item replay bound is unproven".into(),
                        vec![],
                    )
                }
                RetryBound::PendingDelivery if *delivery_stores.entry(
                    f.files[f.sites[r.site as usize].file as usize].repo,
                ).or_insert_with_key(|repo| self.pending_deliveries_have_no_attempt_limit(*repo)) => (
                    Verdict::Violated,
                    "failed deliveries remain pending and the next batch has no per-item attempt limit".into(),
                    vec![],
                ),
                RetryBound::UnknownBatch | RetryBound::PendingDelivery => (
                    Verdict::Unknown,
                    "failed work can return in a later pending batch, and a per-item retry bound is unproven".into(),
                    vec![],
                ),
                RetryBound::OneShotFlags(flags) => (
                    Verdict::Proven,
                    format!("one-shot flags bound the retry: `{flags}`"),
                    vec!["one-shot flags are loop-local booleans initialized before the loop and are only set on their guarded retry edges".into()],
                ),
                RetryBound::RegistryGrowth(check) => (
                    Verdict::Proven,
                    format!("registry retries grow the byte buffer, and other back edges advance the capped item index when present: {check}"),
                    vec!["the standard nonempty byte Vec has length at most isize::MAX, so doubling strictly grows or allocation fails, the registry API writes bytes through the pointer without changing the Vec length, and the item index cannot wrap before its cap".into()],
                ),
                RetryBound::UnknownStateProgress(detail) => (Verdict::Unknown, detail.clone(), vec![]),
                RetryBound::BoundedRange(range) => (
                    Verdict::Proven,
                    format!("a bounded range ends the retry loop: {range}"),
                    vec!["the standard integer range has finite endpoints and advances once per iteration".into()],
                ),
                RetryBound::InputProgress(assumptions) => (
                    Verdict::Proven,
                    "input progress: every continuing error path shortens the input byte slice, and success exits".into(),
                    std::iter::once("input progress is bounded by the initial byte length".into())
                        .chain(assumptions.iter().cloned()).collect(),
                ),
                RetryBound::UnknownProgress => (
                    Verdict::Unknown,
                    "the loop updates its input, but strict byte-slice progress on every continuing path is unproven".into(),
                    vec![],
                ),
            };
            self.push(
                6,
                "retry-limit",
                verdict,
                r.site,
                message,
                witness,
                assumptions,
            );
        }
        for l in &f.latest {
            if l.loop_has_membership_filter {
                self.push(6, "state-exit", Verdict::Proven, l.site, format!("the newest value per `{}` is kept only for keys the loop checks against a live set", l.key), vec![], vec![]);
            } else {
                let msg = format!(
                    "`{}` keeps the newest value per `{}` with no check that the key is still live: a key that stops producing values keeps its last value forever",
                    l.map, l.key
                );
                self.push(
                    6,
                    "state-exit",
                    Verdict::Violated,
                    l.site,
                    msg,
                    vec![],
                    vec![],
                );
            }
        }
        // A durable resource needs a release reachable from every start.
        for (ri, r) in self.cfg.q6.resource.clone().iter().enumerate() {
            let acq = CallPat::new(&r.acquire);
            let acquires: Vec<Id> = f
                .calls
                .iter()
                .filter(|c| acq.hit(c) && !f.funcs[f.sites[c.site as usize].func as usize].test)
                .map(|c| c.site)
                .collect();
            if acquires.is_empty() || !r.durable {
                continue;
            }
            let swept = self.prog.swept.iter().any(|(x,)| *x == ri as u32);
            // Sweep calls: a release, or a call whose callee reaches one. A site is covered when a
            // sweep call in its function runs before it on every path (dominates it).
            let mut sweeps: HashMap<Id, Vec<Id>> = HashMap::new();
            let releasing: HashSet<Id> = match r.sweep.as_deref().and_then(|p| Regex::new(p).ok()) {
                // The named sweepers and every function that calls into one.
                Some(re) => {
                    let mut set: HashSet<Id> = (0..f.funcs.len() as Id)
                        .filter(|&i| re.is_match(&f.funcs[i as usize].name))
                        .collect();
                    let mut callers: HashMap<Id, Vec<Id>> = HashMap::new();
                    for &(a, b, _, _) in &self.g.edges {
                        callers.entry(b).or_default().push(a);
                    }
                    let mut work: Vec<Id> = set.iter().copied().collect();
                    while let Some(g) = work.pop() {
                        for &a in callers.get(&g).into_iter().flatten() {
                            if set.insert(a) {
                                work.push(a);
                            }
                        }
                    }
                    set
                }
                None => self
                    .prog
                    .rel_reach
                    .iter()
                    .filter(|(_, x)| *x == ri as u32)
                    .map(|(g, _)| *g)
                    .collect(),
            };
            for &(a, b, site, _) in &self.g.edges {
                if releasing.contains(&b) {
                    sweeps.entry(a).or_default().push(site);
                }
            }
            for &(site, func, x) in &self.prog.release {
                if x == ri as u32 && r.sweep.is_none() {
                    sweeps.entry(func).or_default().push(site);
                }
            }
            let covered = |s: Id| -> Option<Id> {
                let func = f.sites[s as usize].func;
                sweeps
                    .get(&func)
                    .into_iter()
                    .flatten()
                    .copied()
                    .find(|&x| x != s && self.dominates(x, s))
            };
            let mut pending: Vec<Pending> = vec![];
            let starts: Vec<Id> = self.prog.startup.iter().map(|(x,)| *x).collect();
            for s in acquires {
                let func = f.sites[s as usize].func;
                if swept && let Some(x) = covered(s) {
                    pending.push((
                        Verdict::Proven,
                        s,
                        format!(
                            "a {} made here is swept first at line {} on every path into it",
                            r.name, f.sites[x as usize].line
                        ),
                        vec![],
                        vec!["every start of the program runs through a startup function".into()],
                    ));
                    continue;
                }
                let open_path = if swept {
                    starts.iter().find_map(|&st| {
                        self.path(st, func, &|c| covered(c).is_some())
                            .map(|p| (st, p))
                    })
                } else {
                    None
                };
                let reached = starts
                    .iter()
                    .any(|&st| st == func || self.path(st, func, &|_| false).is_some());
                if swept && open_path.is_none() && !reached {
                    pending.push((
                        Verdict::Unknown,
                        s,
                        format!(
                            "no startup function reaches the code that makes this {} through calls the model follows",
                            r.name
                        ),
                        vec![],
                        vec![],
                    ));
                    continue;
                }
                if swept && open_path.is_none() {
                    pending.push((
                        Verdict::Proven,
                        s,
                        format!(
                            "every start path to this {} passes a sweep that releases it first",
                            r.name
                        ),
                        vec![],
                        vec!["every start of the program runs through a startup function".into()],
                    ));
                    continue;
                }
                if let Some((st, mut witness)) = open_path {
                    witness.insert(0, format!("{} starts", f.func_label(st)));
                    witness.push(format!("{} makes the {}", self.loc(s), r.name));
                    let msg = format!(
                        "a {} made here outlives the process, and this start path reaches it with no sweep first: a kill after making it leaves it until a start that sweeps",
                        r.name
                    );
                    pending.push((Verdict::Violated, s, msg, witness, vec![]));
                } else {
                    let releases: Vec<String> = self
                        .prog
                        .release
                        .iter()
                        .filter(|(_, _, x)| *x == ri as u32)
                        .map(|(rs, rf, _)| {
                            format!(
                                "{} released only from {}",
                                self.loc(*rs),
                                self.f.func_label(*rf)
                            )
                        })
                        .collect();
                    let msg = format!(
                        "a {} made here outlives the process, and no release is reachable from startup: a restart between making and releasing it leaks it",
                        r.name
                    );
                    pending.push((Verdict::Violated, s, msg, releases, vec![]));
                }
            }
            for (v, s, msg, w, a) in pending {
                self.push(6, "durable-exit", v, s, msg, w, a);
            }
        }
        // A failure handler that runs the query whose failure it handles has no exit.
        let mut qreach: HashMap<Id, Vec<Id>> = HashMap::new();
        for &(a, q) in &self.prog.qreach {
            qreach.entry(a).or_default().push(q);
        }
        let mut tries: HashMap<(Id, u32), (Vec<Id>, Vec<Id>)> = HashMap::new();
        for c in &f.calls {
            let s = &f.sites[c.site as usize];
            if let Some(t) = s.ctx.try_body {
                tries.entry((s.func, t)).or_default().0.push(c.site);
            }
            if let Some(t) = s.ctx.handler {
                tries.entry((s.func, t)).or_default().1.push(c.site);
            }
        }
        // One finding per try block and query: its handler's other calls add nothing.
        let mut done: HashSet<(Id, u32, Id)> = HashSet::new();
        let mut items: Vec<_> = tries.into_iter().collect();
        items.sort_by_key(|(k, _)| *k);
        for ((func, try_id), (body, handler)) in items {
            if f.funcs[func as usize].test {
                continue;
            }
            let reach = |s: Id| -> HashSet<Id> {
                self.g
                    .targets
                    .get(&s)
                    .into_iter()
                    .flatten()
                    .flat_map(|(t, _)| qreach.get(t).into_iter().flatten().copied())
                    .collect()
            };
            let b: HashSet<Id> = body.iter().flat_map(|&s| reach(s)).collect();
            for &hs in &handler {
                for q in reach(hs) {
                    if b.contains(&q) && done.insert((func, try_id, q)) {
                        let bs = body
                            .iter()
                            .find(|&&s| reach(s).contains(&q))
                            .copied()
                            .unwrap_or(hs);
                        let mut witness = vec![format!(
                            "{} try body reaches {}",
                            self.loc(bs),
                            f.func_label(q)
                        )];
                        witness.extend(
                            self.g
                                .targets
                                .get(&bs)
                                .into_iter()
                                .flatten()
                                .find_map(|(t, _)| self.path(*t, q, &|_| false))
                                .unwrap_or_default(),
                        );
                        witness.push(format!(
                            "{} its failure handler reaches {} again",
                            self.loc(hs),
                            f.func_label(q)
                        ));
                        witness.extend(
                            self.g
                                .targets
                                .get(&hs)
                                .into_iter()
                                .flatten()
                                .find_map(|(t, _)| self.path(*t, q, &|_| false))
                                .unwrap_or_default(),
                        );
                        let msg = format!(
                            "the handler for a failure in {} calls it again on its way out, so the failure state has no exit when the query keeps failing",
                            f.func_label(q)
                        );
                        self.push(
                            6,
                            "handler-requery",
                            Verdict::Violated,
                            hs,
                            msg,
                            witness,
                            vec![],
                        );
                    }
                }
            }
        }
    }

    // ---------- Question 7: proof by effect ----------
    fn q7(&mut self) {
        let f = self.f;
        for w in self.cfg.q7.weak_probe.clone() {
            let (Ok(call), arg) = (
                Regex::new(&w.call),
                w.arg1.as_deref().and_then(|a| Regex::new(a).ok()),
            ) else {
                continue;
            };
            for c in &f.calls {
                if !call.is_match(&c.full) || f.funcs[f.sites[c.site as usize].func as usize].test {
                    continue;
                }
                if let Some(a) = &arg
                    && !c.args.get(1).is_some_and(|x| a.is_match(&x.text))
                {
                    continue;
                }
                self.push(
                    7,
                    "weak-probe",
                    Verdict::Violated,
                    c.site,
                    format!("`{}` is used as evidence of state: {}", c.full, w.why),
                    vec![],
                    vec![],
                );
            }
        }
    }

    /// Constructs the model cannot follow make the questions that depend on the call graph unknown there.
    fn dyn_unknowns(&mut self) {
        for d in self.f.dyns.clone() {
            if self.f.funcs[self.f.sites[d.site as usize].func as usize].test {
                continue;
            }
            for q in [1u8, 3, 4] {
                self.push(
                    q,
                    "model-limit",
                    Verdict::Unknown,
                    d.site,
                    format!(
                        "{}: calls and values through it are not modeled",
                        d.construct
                    ),
                    vec![],
                    vec![],
                );
            }
        }
    }
}

/// A frame's shape: per comma field, its character class and length.
fn shape(s: &str) -> Vec<(char, usize)> {
    s.split(',')
        .map(|field| {
            let class = if field.chars().all(|c| c.is_ascii_digit()) {
                'd'
            } else if field.chars().all(|c| c.is_ascii_hexdigit()) {
                'h'
            } else {
                't'
            };
            (class, field.len())
        })
        .collect()
}

/// The first field where a literal's shape differs from every capture of its kind, if any.
fn field_mismatch(mine: &[(char, usize)], caps: &[&Vec<(char, usize)>]) -> Option<String> {
    if caps.is_empty() {
        return None;
    }
    for (i, (class, len)) in mine.iter().enumerate() {
        let theirs: Vec<(char, usize)> = caps.iter().filter_map(|c| c.get(i).copied()).collect();
        if theirs.is_empty() {
            return Some(format!("field {} is not in any capture", i + 1));
        }
        if *class == 't' {
            continue;
        }
        let fixed: HashSet<usize> = theirs
            .iter()
            .filter(|(c, _)| *c != 't')
            .map(|(_, l)| *l)
            .collect();
        if fixed.len() == 1 && !fixed.contains(len) {
            let want = fixed.iter().next().copied().unwrap_or(0);
            return Some(format!(
                "field {} has {} characters; every capture has {}",
                i + 1,
                len,
                want
            ));
        }
    }
    None
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        format!("{}...", s.chars().take(n).collect::<String>())
    }
}
