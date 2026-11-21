//! State that outlives a call. Question 6: a held attribute that stops an entry while it is held
//! needs an exit a refusal can take, and the calls that run before that check must not write the
//! held run's files without reading the holder. Question 3: a value read from a store and written
//! back must not have another writer of that store between the two. Question 5: a structural
//! guard keyed by a hand-kept name table checks only what was listed.

use super::*;

/// Store keys a function names (file-name literals, path constants given to a path call) and
/// whether it writes, closed over the calls it makes and the functions nested in it.
/// Exits by function: each exit statement's path and kind.
type ExitsByFunc = HashMap<Id, Vec<(Vec<(u32, u32)>, u8)>>;

pub(super) struct Stores {
    keys: Vec<String>,
    /// Keys a function or anything it reaches names.
    touch: HashMap<Id, HashSet<u32>>,
    /// Keys a function or anything it reaches names in a function that writes.
    write: HashMap<Id, HashSet<u32>>,
    /// Keys a function names itself, when it writes.
    own_write: HashMap<Id, HashSet<u32>>,
    /// Keys a function names itself.
    own_touch: HashMap<Id, HashSet<u32>>,
    /// Exits by function: (path, kind).
    exits: ExitsByFunc,
    /// Callees by call site.
    callees: HashMap<Id, Vec<Id>>,
    /// Callees and nested functions by function.
    down: HashMap<Id, Vec<Id>>,
    /// Callers and enclosing functions by function.
    up: HashMap<Id, Vec<Id>>,
    /// Calls by function, as indexes into the facts' calls.
    calls_in: HashMap<Id, Vec<usize>>,
}

fn literal_refusal(text: &str) -> bool {
    matches!(text.trim(), "" | "False" | "None" | "false")
}

impl<'a> Analysis<'a> {
    pub(super) fn stores(&self) -> Stores {
        let f = self.f;
        let file_re = Regex::new(&self.cfg.q3.store_file).ok();
        let write_re = Regex::new(&self.cfg.q3.store_write).ok();
        let path_re = Regex::new(&self.cfg.q10.path_call).ok();
        // A constant names a store when its module value is a file-name literal (`RUN_LOG =
        // "runs.jsonl"`), not a directory (`HOME = os.path.expanduser("~")`).
        let mut file_consts: HashSet<(Id, String)> = HashSet::new();
        for a in &f.assigns {
            let s = &f.sites[a.site as usize];
            let v = a.value.text.trim();
            let lit = v.len() >= 2
                && (v.starts_with('"') && v.ends_with('"')
                    || v.starts_with('\'') && v.ends_with('\''));
            if lit
                && f.funcs[s.func as usize].kind == ScopeKind::Module
                && file_re
                    .as_ref()
                    .is_some_and(|r| r.is_match(&v[1..v.len() - 1]))
            {
                file_consts.insert((s.file, a.target.clone()));
            }
        }
        let mut keys: Vec<String> = vec![];
        let mut key_of: HashMap<String, u32> = HashMap::new();
        let mut own_touch: HashMap<Id, HashSet<u32>> = HashMap::new();
        let mut writes: HashSet<Id> = HashSet::new();
        for c in &f.calls {
            let func = f.sites[c.site as usize].func;
            let mut names: Vec<String> = c
                .str_args
                .iter()
                .filter(|a| file_re.as_ref().is_some_and(|r| r.is_match(a)))
                .cloned()
                .collect();
            if path_re.as_ref().is_some_and(|r| r.is_match(&c.full)) {
                names.extend(
                    c.args
                        .iter()
                        .flat_map(|e| e.vars.iter())
                        .filter(|v| {
                            file_consts.contains(&(f.sites[c.site as usize].file, (*v).clone()))
                        })
                        .cloned(),
                );
            }
            for n in names {
                let next = keys.len() as u32;
                let k = *key_of.entry(n.clone()).or_insert_with(|| {
                    keys.push(n);
                    next
                });
                own_touch.entry(func).or_default().insert(k);
            }
            // A write through a local (a list's append, a local file handle) writes no store.
            let local = !c.recv.is_empty()
                && !c.recv.starts_with("self")
                && self
                    .locals
                    .get(&func)
                    .is_some_and(|l| l.contains(c.recv.split('.').next().unwrap_or("")));
            if !local && write_re.as_ref().is_some_and(|r| r.is_match(&c.name)) {
                writes.insert(func);
            }
        }
        let mut callees: HashMap<Id, Vec<Id>> = HashMap::new();
        let mut down: HashMap<Id, Vec<Id>> = HashMap::new();
        // A call dispatched by method name is followed only inside its file: across files and
        // repositories a common name joins unrelated code and every store would reach every other.
        for &(a, b, s, exact) in &self.g.edges {
            if !exact && f.funcs[a as usize].file != f.funcs[b as usize].file {
                continue;
            }
            callees.entry(s).or_default().push(b);
            down.entry(a).or_default().push(b);
        }
        for (i, func) in f.funcs.iter().enumerate() {
            if let Some(p) = func.parent
                && func.kind == ScopeKind::Function
                && f.funcs[p as usize].kind == ScopeKind::Function
            {
                down.entry(p).or_default().push(i as Id);
            }
        }
        let own_write: HashMap<Id, HashSet<u32>> = own_touch
            .iter()
            .filter(|(g, _)| writes.contains(g))
            .map(|(g, k)| (*g, k.clone()))
            .collect();
        let mut up: HashMap<Id, Vec<Id>> = HashMap::new();
        for (a, bs) in &down {
            for b in bs {
                up.entry(*b).or_default().push(*a);
            }
        }
        let up_ref = &up;
        let close = |own: HashMap<Id, HashSet<u32>>| -> HashMap<Id, HashSet<u32>> {
            let mut out = own;
            let mut work: VecDeque<Id> = out.keys().copied().collect();
            while let Some(b) = work.pop_front() {
                let ks = out.get(&b).cloned().unwrap_or_default();
                for &a in up_ref.get(&b).into_iter().flatten() {
                    let set = out.entry(a).or_default();
                    let before = set.len();
                    set.extend(ks.iter().copied());
                    if set.len() != before {
                        work.push_back(a);
                    }
                }
            }
            out
        };
        let mut exits: ExitsByFunc = HashMap::new();
        for x in &f.exits {
            let s = &f.sites[x.site as usize];
            exits
                .entry(s.func)
                .or_default()
                .push((s.ctx.path.clone(), x.kind));
        }
        let (touch, write) = (close(own_touch.clone()), close(own_write.clone()));
        let mut calls_in: HashMap<Id, Vec<usize>> = HashMap::new();
        for (i, c) in f.calls.iter().enumerate() {
            calls_in
                .entry(f.sites[c.site as usize].func)
                .or_default()
                .push(i);
        }
        Stores {
            keys,
            up,
            calls_in,
            touch,
            write,
            own_write,
            own_touch,
            exits,
            callees,
            down,
        }
    }

    /// Whether `b` can run after `a` in one pass through their function: `a`'s statement comes
    /// first, and no statement after `a` in a block holding it leaves unconditionally.
    pub(super) fn falls_to(&self, st: &Stores, a: Id, b: Id) -> bool {
        let (sa, sb) = (&self.f.sites[a as usize], &self.f.sites[b as usize]);
        if sa.func != sb.func || a == b {
            return false;
        }
        let (pa, pb) = (&sa.ctx.path, &sb.ctx.path);
        let mut i = 0;
        while i < pa.len() && i < pb.len() && pa[i] == pb[i] {
            i += 1;
        }
        if i == pa.len() || i == pb.len() {
            // One statement holds the other: an `if` site and its body, or two sites in one
            // statement, which run in site order.
            return pa.len() < pb.len() || (pa.len() == pb.len() && a < b);
        }
        let (la, lb) = (pa[i], pb[i]);
        if la.0 != lb.0 || la.1 >= lb.1 {
            return false;
        }
        let none = vec![];
        let exits = st.exits.get(&sa.func).unwrap_or(&none);
        let cuts = |level: usize, from: u32, to: u32| {
            exits.iter().any(|(p, _)| {
                p.len() == level + 1
                    && p[..level] == pa[..level]
                    && p[level].0 == pa[level].0
                    && p[level].1 >= from
                    && p[level].1 < to
            })
        };
        if cuts(i, la.1, lb.1) {
            return false;
        }
        (i + 1..pa.len()).all(|j| !cuts(j, pa[j].1, u32::MAX))
    }

    fn reach(&self, st: &Stores, from: &[Id]) -> HashSet<Id> {
        let mut seen: HashSet<Id> = from.iter().copied().collect();
        let mut work: Vec<Id> = from.to_vec();
        while let Some(g) = work.pop() {
            for &b in st.down.get(&g).into_iter().flatten() {
                if seen.insert(b) {
                    work.push(b);
                }
            }
        }
        seen
    }

    /// Every function that reaches one of `seeds` (the seeds included).
    fn reaching(&self, st: &Stores, seeds: &HashSet<Id>) -> HashSet<Id> {
        let mut seen = seeds.clone();
        let mut work: Vec<Id> = seeds.iter().copied().collect();
        while let Some(b) = work.pop() {
            for &a in st.up.get(&b).into_iter().flatten() {
                if seen.insert(a) {
                    work.push(a);
                }
            }
        }
        seen
    }

    fn calls_of<'s>(&'s self, st: &'s Stores, g: Id) -> impl Iterator<Item = &'a Call> + 's {
        st.calls_in
            .get(&g)
            .into_iter()
            .flatten()
            .map(|&i| &self.f.calls[i])
    }

    /// Variables a function reads anywhere: conditions, values, arguments, receivers, returns.
    fn reads_var(&self, funcs: &HashSet<Id>, v: &str) -> bool {
        let f = self.f;
        let inside = |s: Id| funcs.contains(&f.sites[s as usize].func);
        let has = |e: &Expr| e.vars.iter().any(|x| x == v);
        f.calls.iter().any(|c| {
            inside(c.site)
                && (c.recv == v
                    || c.recv.starts_with(&format!("{v}."))
                    || c.args.iter().any(has)
                    || c.kwargs.iter().any(|(_, e)| has(e)))
        }) || f.assigns.iter().any(|a| inside(a.site) && has(&a.value))
            || f.conds.iter().any(|c| inside(c.site) && has(&c.cond))
            || f.returns.iter().any(|r| inside(r.site) && has(&r.value))
            || f.compares
                .iter()
                .any(|c| inside(c.site) && (has(&c.left) || has(&c.right)))
    }

    /// Question 6: held state. An attribute that stops a function while it is held (`if self.x
    /// is not None: return`) and is retried there needs an exit a refusal can take; the calls
    /// that run before that check and write the held run's files must read the holder.
    pub(super) fn held_state(&mut self, st: &Stores) {
        let f = self.f;
        type Key = (Id, String);
        let mut sets: HashMap<Key, Vec<Id>> = HashMap::new();
        let mut clears: HashMap<Key, Vec<Id>> = HashMap::new();
        for a in &f.assigns {
            let func = f.sites[a.site as usize].func;
            if !a.target.starts_with("self.") || a.target.matches('.').count() != 1 {
                continue;
            }
            let Some(class) = class_of(f, func) else {
                continue;
            };
            // The constructor's first value is no plan and no exit.
            if f.funcs[func as usize].name == "__init__" {
                continue;
            }
            let key = (class, a.target.clone());
            if a.value.text.trim() == "None" {
                clears.entry(key).or_default().push(a.site);
            } else {
                sets.entry(key).or_default().push(a.site);
            }
        }
        // Gates: (key, function, if site, body block).
        let mut gates: BTreeMap<Key, Vec<(Id, Id, u32)>> = BTreeMap::new();
        for c in &f.conds {
            let func = f.sites[c.site as usize].func;
            if c.exit != EXIT_RETURN || f.funcs[func as usize].test {
                continue;
            }
            let Some(class) = class_of(f, func) else {
                continue;
            };
            // Condition text is squashed: `self.x is not None` reads `self.xisnotNone`.
            let text = c.cond.text.as_str();
            for v in c.cond.vars.iter().filter(|v| v.starts_with("self.")) {
                let key = (class, v.clone());
                if !sets.contains_key(&key) || !clears.contains_key(&key) {
                    continue;
                }
                let held = text == v
                    || text.contains(&format!("{v}isnotNone"))
                    || text.starts_with(&format!("{v}and"))
                    || text.ends_with(&format!("and{v}"));
                if held {
                    gates.entry(key).or_default().push((func, c.site, c.body));
                }
            }
        }
        let func_of = |s: Id| f.sites[s as usize].func;
        for (key, gs) in gates {
            let (_, attr) = &key;
            let clear_sites = &clears[&key];
            let set_funcs: HashSet<Id> = sets[&key].iter().map(|&s| func_of(s)).collect();
            let clear_funcs: HashSet<Id> = clear_sites.iter().map(|&s| func_of(s)).collect();
            let setting = self.reaching(st, &set_funcs);
            let clearing = self.reaching(st, &clear_funcs);
            let sets_it = |g: Id| setting.contains(&g);
            let mut retries: BTreeMap<Id, Id> = BTreeMap::new();
            let mut before: Vec<(Id, Id, Id)> = vec![];
            for &(g, gsite, body) in &gs {
                for c in self.calls_of(st, g) {
                    let s = &f.sites[c.site as usize];
                    let inside = s.ctx.path.iter().any(|(b, _)| *b == body);
                    if !(self.dominates(c.site, gsite) || inside) {
                        continue;
                    }
                    for &callee in st.callees.get(&c.site).into_iter().flatten() {
                        if clearing.contains(&callee) {
                            retries.entry(callee).or_insert(c.site);
                        } else if !inside {
                            before.push((g, c.site, callee));
                        }
                    }
                }
            }
            if retries.is_empty() {
                continue;
            }
            // Refusals: a literal False or None (or a bare return) from a retry, with no clear
            // before it on every path.
            let mut refusals: Vec<Id> = vec![];
            for r in &f.returns {
                let rf = func_of(r.site);
                if retries.contains_key(&rf)
                    && literal_refusal(&r.value.text)
                    && !clear_sites.iter().any(|&c| self.dominates(c, r.site))
                {
                    refusals.push(r.site);
                }
            }
            let refusal_funcs: HashSet<Id> = refusals.iter().map(|&s| func_of(s)).collect();
            let gate_funcs: HashSet<Id> = gs.iter().map(|g| g.0).collect();
            let mut exits_on_refusal = vec![];
            let mut witness_clears = vec![];
            for &cl in clear_sites {
                let h = func_of(cl);
                let replans = self.calls_of(st, h).any(|c| {
                    self.falls_to(st, cl, c.site)
                        && st
                            .callees
                            .get(&c.site)
                            .into_iter()
                            .flatten()
                            .any(|&b| sets_it(b))
                }) || sets[&key]
                    .iter()
                    .any(|&s| func_of(s) == h && self.falls_to(st, cl, s));
                if replans {
                    witness_clears.push(format!("{} clears it and plans again", self.loc(cl)));
                    continue;
                }
                let on_refusal = gate_funcs.contains(&h)
                    || f.returns.iter().any(|r| {
                        func_of(r.site) == h
                            && (refusal_funcs.contains(&h) || retries.contains_key(&h))
                            && literal_refusal(&r.value.text)
                            && self.falls_to(st, cl, r.site)
                    });
                if on_refusal {
                    exits_on_refusal.push(cl);
                } else {
                    witness_clears
                        .push(format!("{} clears it after the work is done", self.loc(cl)));
                }
            }
            let first_gate = gs.iter().map(|g| g.1).min().unwrap_or(gs[0].1);
            let gname = |g: Id| f.funcs[g as usize].name.clone();
            let gate_names: Vec<String> = {
                let mut v: Vec<String> = gs.iter().map(|g| gname(g.0)).collect();
                v.dedup();
                v
            };
            let rnames: Vec<String> = retries.keys().map(|&r| gname(r)).collect();
            if refusals.is_empty() {
                self.push(
                    6,
                    "held-state-exit",
                    Verdict::Proven,
                    first_gate,
                    format!(
                        "`{attr}` stops `{}` while it is held, and its retry `{}` returns no refusal that keeps it",
                        gate_names.join("`, `"),
                        rnames.join("`, `")
                    ),
                    vec![],
                    vec!["a return that is not a literal False or None settles the held state".into()],
                );
            } else if let Some(&x) = exits_on_refusal.first() {
                self.push(
                    6,
                    "held-state-exit",
                    Verdict::Proven,
                    first_gate,
                    format!(
                        "`{attr}` stops `{}` while it is held, and a refusal can end it (line {})",
                        gate_names.join("`, `"),
                        f.sites[x as usize].line
                    ),
                    vec![],
                    vec!["the refusals that keep it are ones a later call can pass".into()],
                );
            } else {
                let mut witness: Vec<String> = gs
                    .iter()
                    .map(|&(g, s, _)| {
                        format!(
                            "{} {} returns while `{attr}` is held",
                            self.loc(s),
                            gname(g)
                        )
                    })
                    .collect();
                witness.extend(refusals.iter().map(|&r| {
                    format!("{} {} refuses and keeps it", self.loc(r), gname(func_of(r)))
                }));
                witness.extend(witness_clears);
                self.push(
                    6,
                    "held-state-exit",
                    Verdict::Violated,
                    first_gate,
                    format!(
                        "`{attr}` stops `{}` while it is held, and its retry `{}` refuses without ending it: every exit is a success or a new plan, so a refusal that repeats (a passed window, a changed date) holds it and the function does nothing else again",
                        gate_names.join("`, `"),
                        rnames.join("`, `")
                    ),
                    witness,
                    vec![],
                );
            }
            if refusals.is_empty() {
                continue;
            }
            // Files the held run writes, and the calls before the check that write them too.
            let held_reach = self.reach(st, &retries.keys().copied().collect::<Vec<_>>());
            let held_keys: HashSet<u32> = held_reach
                .iter()
                .filter_map(|g| st.write.get(g))
                .flatten()
                .copied()
                .collect();
            if held_keys.is_empty() {
                continue;
            }
            let mut writers: Vec<(Id, Id, Vec<u32>)> = vec![];
            let mut reach_all: HashSet<Id> = HashSet::new();
            for &(_, site, callee) in &before {
                let ks: Vec<u32> = st
                    .write
                    .get(&callee)
                    .into_iter()
                    .flatten()
                    .filter(|k| held_keys.contains(k))
                    .copied()
                    .collect();
                if ks.is_empty() {
                    continue;
                }
                let r = self.reach(st, &[callee]);
                reach_all.extend(r.iter().copied());
                writers.push((site, callee, ks));
            }
            if writers.is_empty() {
                continue;
            }
            writers.sort();
            writers.dedup_by_key(|w| w.0);
            let site = writers[0].0;
            let names = |ks: &[u32]| {
                let mut v: Vec<&str> = ks.iter().map(|&k| st.keys[k as usize].as_str()).collect();
                v.sort();
                v.dedup();
                v.join(", ")
            };
            if self.reads_var(&reach_all, attr) {
                self.push(
                    6,
                    "held-run-recovery",
                    Verdict::Proven,
                    site,
                    format!("the calls before the check on `{attr}` that write the held run's files read `{attr}` first"),
                    vec![],
                    vec!["reading the holder is enough to tell its records from a dead run's".into()],
                );
            } else {
                let mut witness: Vec<String> = vec![];
                let mut shown: HashSet<Id> = HashSet::new();
                for (s, callee, ks) in &writers {
                    witness.push(format!(
                        "{} calls {}, which writes {}",
                        self.loc(*s),
                        f.func_label(*callee),
                        names(ks)
                    ));
                    // The functions in its reach that write those files themselves.
                    // Nearest first, in call order.
                    let mut order: Vec<Id> = vec![*callee];
                    let mut seen: HashSet<Id> = HashSet::from([*callee]);
                    let mut i = 0;
                    while i < order.len() {
                        for &b in st.down.get(&order[i]).into_iter().flatten() {
                            if seen.insert(b) {
                                order.push(b);
                            }
                        }
                        i += 1;
                    }
                    let own = order
                        .into_iter()
                        .filter(|g| {
                            st.own_write
                                .get(g)
                                .is_some_and(|k| ks.iter().any(|x| k.contains(x)))
                        })
                        .filter(|g| shown.insert(*g));
                    for g in own.take(3) {
                        let func = &f.funcs[g as usize];
                        witness.push(format!(
                            "{}:{} {} writes them without reading `{attr}`",
                            f.files[func.file as usize].path,
                            func.line,
                            f.func_label(g)
                        ));
                    }
                }
                let held: Vec<u32> = held_keys.iter().copied().collect();
                witness.push(format!(
                    "{} writes {} for the held run, which outlives the call",
                    rnames.join(", "),
                    names(&held)
                ));
                let ks: Vec<u32> = writers.iter().flat_map(|w| w.2.iter().copied()).collect();
                self.push(
                    6,
                    "held-run-recovery",
                    Verdict::Violated,
                    site,
                    format!(
                        "a run held in `{attr}` keeps its records in {} between calls, and the calls that run before the check write {} without reading `{attr}`: they cannot tell the held run's records from a dead run's",
                        names(&held),
                        names(&ks)
                    ),
                    witness,
                    vec![],
                );
            }
        }
    }

    /// Questions 3 and 4 around a guard that vouches for a provider (a clock check): an effect
    /// after it must use a reading taken after it (`read-before-check`), and no call before it
    /// may write a store with that provider's reading (`write-before-guard`).
    pub(super) fn guard_order(&mut self, st: &Stores) {
        let f = self.f;
        let vouch: Vec<(u32, Regex)> = self
            .cfg
            .q3
            .vouch
            .iter()
            .filter_map(|(k, p)| {
                let i = self.cfg.providers.keys().position(|x| x == k)? as u32;
                Regex::new(p).ok().map(|r| (i, r))
            })
            .collect();
        if vouch.is_empty() {
            return;
        }
        let mut reads_of: HashMap<Id, HashSet<u32>> = HashMap::new();
        for &(func, _, p, _) in &self.prog.reads {
            reads_of.entry(func).or_default().insert(p);
        }
        let eff: HashSet<Id> = self.prog.eff_reach.iter().map(|(g, _)| *g).collect();
        // Functions whose own calls name a provider's status check.
        let mut checks: HashMap<Id, HashSet<u32>> = HashMap::new();
        for c in &f.calls {
            for (k, re) in &vouch {
                if re.is_match(&c.full) || c.str_args.iter().any(|a| re.is_match(a)) {
                    checks
                        .entry(f.sites[c.site as usize].func)
                        .or_default()
                        .insert(*k);
                }
            }
        }
        for (i, func) in f.funcs.iter().enumerate() {
            for (k, re) in &vouch {
                if re.is_match(&func.name) {
                    checks.entry(i as Id).or_default().insert(*k);
                }
            }
        }
        let accepted = self.cfg.q4.accepted_order.clone();
        let mut seen: HashSet<(Id, Id)> = HashSet::new();
        for gc in &f.calls {
            let gf = f.sites[gc.site as usize].func;
            if !gc.predicate || f.funcs[gf as usize].test {
                continue;
            }
            let callees: Vec<Id> = st.callees.get(&gc.site).cloned().unwrap_or_default();
            let reach = self.reach(st, &callees);
            let vouched: HashSet<u32> = reach
                .iter()
                .filter_map(|g| checks.get(g))
                .flatten()
                .copied()
                .collect();
            for k in vouched {
                let gline = f.sites[gc.site as usize].line;
                let kn = self.kinds[k as usize].clone();
                let fcalls: Vec<&'a Call> = self.calls_of(st, gf).collect();
                for &e in &fcalls {
                    if !self.dominates(gc.site, e.site) {
                        continue;
                    }
                    let targets: Vec<Id> = st.callees.get(&e.site).cloned().unwrap_or_default();
                    let acts = self.effects_at.contains_key(&e.site)
                        || targets.iter().any(|t| {
                            eff.contains(t) || st.write.get(t).is_some_and(|w| !w.is_empty())
                        });
                    if !acts {
                        continue;
                    }
                    for arg in e.args.iter().chain(e.kwargs.iter().map(|(_, x)| x)) {
                        for v in &arg.vars {
                            let one = Expr {
                                vars: vec![v.clone()],
                                ..Expr::default()
                            };
                            if !self.kinds_of(gf, &one).contains(&k)
                                || !seen.insert((e.site, gc.site))
                            {
                                continue;
                            }
                            let defs: Vec<Id> = f
                                .assigns
                                .iter()
                                .filter(|a| a.target == *v && f.sites[a.site as usize].func == gf)
                                .map(|a| a.site)
                                .collect();
                            let fresh = defs
                                .iter()
                                .any(|&a| self.dominates(gc.site, a) && self.dominates(a, e.site));
                            let param = f.funcs[gf as usize].params.iter().any(|p| p.name == *v);
                            let before: Vec<Id> = defs
                                .iter()
                                .copied()
                                .filter(|&a| !self.dominates(gc.site, a))
                                .collect();
                            if fresh {
                                self.push(
                                    3,
                                    "read-before-check",
                                    Verdict::Proven,
                                    e.site,
                                    format!("the {kn} reading `{v}` this effect uses is taken after the check at line {gline}"),
                                    vec![],
                                    vec![format!("`{}` checks the {kn} it vouches for", gc.full)],
                                );
                            } else if param || !before.is_empty() {
                                let from = if param {
                                    format!(
                                        "a parameter of {}, read by its caller",
                                        f.func_label(gf)
                                    )
                                } else {
                                    format!("line {}", f.sites[before[0] as usize].line)
                                };
                                let mut witness = vec![];
                                if let Some(&b) = before.first() {
                                    witness
                                        .push(format!("{} reads the {kn} into `{v}`", self.loc(b)));
                                }
                                witness.push(format!(
                                    "{} `{}` vouches for the {kn}",
                                    self.loc(gc.site),
                                    gc.full
                                ));
                                witness.push(format!("{} acts on `{v}`", self.loc(e.site)));
                                self.push(
                                    3,
                                    "read-before-check",
                                    Verdict::Violated,
                                    e.site,
                                    format!(
                                        "the {kn} reading `{v}` this effect uses was taken before `{}` vouched for the {kn} (line {gline}), at {from}: a {kn} that steps between the reading and the check is acted on unchecked",
                                        gc.full
                                    ),
                                    witness,
                                    vec![],
                                );
                            }
                        }
                    }
                }
                // Calls that run before the check and write a store with a reading of the provider.
                for &w in &fcalls {
                    if w.site == gc.site
                        || !self.dominates(w.site, gc.site)
                        || !seen.insert((w.site, gc.site))
                    {
                        continue;
                    }
                    let targets: Vec<Id> = st.callees.get(&w.site).cloned().unwrap_or_default();
                    let keys: HashSet<u32> = targets
                        .iter()
                        .filter_map(|t| st.write.get(t))
                        .flatten()
                        .copied()
                        .collect();
                    // A reading of the provider in what the call reaches: a source call, or a call whose
                    // result is of the provider's kind (`self.now()` holding an injected clock).
                    let reads_k = self.reach(st, &targets).iter().any(|&g| {
                        reads_of.get(&g).is_some_and(|p| p.contains(&k))
                            || self.calls_of(st, g).any(|c| {
                                self.kinds()
                                    .site
                                    .get(&c.site)
                                    .is_some_and(|ks| ks.contains(&k))
                            })
                    });
                    if keys.is_empty() || !reads_k {
                        continue;
                    }
                    let mut names: Vec<&str> =
                        keys.iter().map(|&x| st.keys[x as usize].as_str()).collect();
                    names.sort();
                    let store = names.join(", ");
                    let loc = self.loc(w.site);
                    let label = f.func_label(gf);
                    if let Some(a) = accepted
                        .iter()
                        .find(|a| loc.ends_with(&a.site) || a.site == label)
                    {
                        self.push(
                            4,
                            "write-before-guard",
                            Verdict::Proven,
                            w.site,
                            format!("write before the {kn} check accepted: {}", a.reason),
                            vec![],
                            vec![],
                        );
                    } else {
                        self.push(
                            4,
                            "write-before-guard",
                            Verdict::Violated,
                            w.site,
                            format!(
                                "`{}` can write {store} with a {kn} reading before `{}` vouches for the {kn} (line {gline}): what the check refuses is already written",
                                w.full, gc.full
                            ),
                            vec![
                                format!("{loc} `{}` writes {store} and reads the {kn}", w.full),
                                format!("{} `{}` checks the {kn} afterwards", self.loc(gc.site), gc.full),
                            ],
                            vec![],
                        );
                    }
                }
            }
        }
    }

    /// Question 3: a value read from a store and written back is stale when a call between the
    /// read and the write can write that store.
    pub(super) fn stale_write_back(&mut self, st: &Stores) {
        let f = self.f;
        let mut by_func: HashMap<Id, Vec<&Assign>> = HashMap::new();
        for a in &f.assigns {
            by_func
                .entry(f.sites[a.site as usize].func)
                .or_default()
                .push(a);
        }
        let mut calls_in: HashMap<Id, Vec<&Call>> = HashMap::new();
        for c in &f.calls {
            calls_in
                .entry(f.sites[c.site as usize].func)
                .or_default()
                .push(c);
        }
        let mut seen: HashSet<(Id, Id)> = HashSet::new();
        let mut items: Vec<(&Id, &Vec<&Assign>)> = by_func.iter().collect();
        items.sort_by_key(|(g, _)| **g);
        for (&g, assigns) in items {
            if f.funcs[g as usize].test {
                continue;
            }
            let calls = calls_in.get(&g).cloned().unwrap_or_default();
            for a in assigns {
                if a.target.contains('.') {
                    continue;
                }
                let read_keys: HashSet<u32> = a
                    .value
                    .calls
                    .iter()
                    .flat_map(|s| st.callees.get(s).into_iter().flatten())
                    .filter_map(|b| st.touch.get(b))
                    .flatten()
                    .copied()
                    .collect();
                if read_keys.is_empty() {
                    continue;
                }
                // Values built from the read.
                let mut derived: HashSet<&str> = HashSet::from([a.target.as_str()]);
                loop {
                    let n = derived.len();
                    for b in assigns {
                        if !b.target.contains('.')
                            && b.value.vars.iter().any(|v| derived.contains(v.as_str()))
                        {
                            derived.insert(b.target.as_str());
                        }
                    }
                    if derived.len() == n {
                        break;
                    }
                }
                // A write back passes the value itself, or a literal built around it.
                let writes_back = |c: &Call| {
                    c.args
                        .iter()
                        .chain(c.kwargs.iter().map(|(_, e)| e))
                        .any(|e| {
                            derived.contains(e.text.as_str())
                                || ((e.text.starts_with('{') || e.text.starts_with('['))
                                    && e.vars.iter().any(|v| derived.contains(v.as_str())))
                        })
                };
                // A call given anything built from the read writes the same snapshot, not another.
                let mentions = |c: &Call| {
                    c.args
                        .iter()
                        .chain(c.kwargs.iter().map(|(_, e)| e))
                        .any(|e| e.vars.iter().any(|v| derived.contains(v.as_str())))
                };
                // A second read into a value built from the first starts a fresh snapshot.
                let rereads: Vec<Id> = assigns
                    .iter()
                    .filter(|b| {
                        b.site != a.site
                            && derived.contains(b.target.as_str())
                            && b.value
                                .calls
                                .iter()
                                .flat_map(|s| st.callees.get(s).into_iter().flatten())
                                .filter_map(|x| st.touch.get(x))
                                .any(|ks| !ks.is_disjoint(&read_keys))
                    })
                    .map(|b| b.site)
                    .collect();
                let writes_of = |c: &Call| -> HashSet<u32> {
                    st.callees
                        .get(&c.site)
                        .into_iter()
                        .flatten()
                        .filter_map(|b| st.write.get(b))
                        .flatten()
                        .filter(|k| read_keys.contains(k))
                        .copied()
                        .collect()
                };
                let nested = |c: &Call, outer: &Call| {
                    outer
                        .args
                        .iter()
                        .chain(outer.kwargs.iter().map(|(_, e)| e))
                        .any(|e| e.calls.contains(&c.site))
                };
                for w in &calls {
                    if a.value.calls.contains(&w.site)
                        || !writes_back(w)
                        || !self.falls_to(st, a.site, w.site)
                        || rereads
                            .iter()
                            .any(|&b| self.falls_to(st, a.site, b) && self.falls_to(st, b, w.site))
                    {
                        continue;
                    }
                    let wk = writes_of(w);
                    if wk.is_empty() || !seen.insert((a.site, w.site)) {
                        continue;
                    }
                    let between = calls.iter().find(|m| {
                        m.site != w.site
                            && !a.value.calls.contains(&m.site)
                            && !nested(m, w)
                            && !mentions(m)
                            && self.falls_to(st, a.site, m.site)
                            && self.falls_to(st, m.site, w.site)
                            && !writes_of(m).is_disjoint(&wk)
                    });
                    let mut names: Vec<&str> =
                        wk.iter().map(|&k| st.keys[k as usize].as_str()).collect();
                    names.sort();
                    let store = names.join(", ");
                    let rl = f.sites[a.site as usize].line;
                    match between {
                        Some(m) => {
                            let witness = vec![
                                format!("{} reads {store} into `{}`", self.loc(a.site), a.target),
                                format!("{} `{}` can write {store}", self.loc(m.site), m.full),
                                format!("{} writes back a value built from line {rl}", self.loc(w.site)),
                            ];
                            self.push(
                                3,
                                "stale-write-back",
                                Verdict::Violated,
                                w.site,
                                format!(
                                    "{store} is read at line {rl} and written back here from that read, but `{}` between them can write {store}: what it wrote is overwritten with the older copy",
                                    m.full
                                ),
                                witness,
                                vec![],
                            );
                        }
                        None => self.push(
                            3,
                            "stale-write-back",
                            Verdict::Proven,
                            w.site,
                            format!("no call between the read of {store} at line {rl} and this write reaches another writer of it"),
                            vec![],
                            vec![format!("no other thread or process writes {store} between the read and the write")],
                        ),
                    }
                }
            }
        }
    }

    /// Question 6: a status attribute (a reason or error a refusal records, `None` when clear)
    /// that an attempt sets on its refusals and clears only after success. An attempt that ends
    /// any other way, by an exception or a refusal that records nothing, leaves the previous
    /// attempt's reason showing. Proven when a clear at the attempt's start comes before every
    /// set, or when every call into the attempt comes after such a clear in its caller.
    pub(super) fn stale_status(&mut self, st: &Stores) {
        let f = self.f;
        let is_str = |t: &str| {
            // A reason split over lines is wrapped in parentheses.
            let t = t.trim_start().trim_start_matches('(').trim_start();
            t.starts_with('"') || t.starts_with('\'') || t.starts_with("f\"") || t.starts_with("f'")
        };
        // Attributes assigned both a string and None: a status a refusal records.
        let mut sets: HashMap<&str, Vec<Id>> = HashMap::new();
        let mut clears: HashMap<&str, Vec<Id>> = HashMap::new();
        for a in &f.assigns {
            if !a.target.starts_with("self.")
                || f.funcs[f.sites[a.site as usize].func as usize].test
            {
                continue;
            }
            let v = a.value.text.trim();
            if v == "None" {
                clears.entry(a.target.as_str()).or_default().push(a.site);
            } else if is_str(v) {
                sets.entry(a.target.as_str()).or_default().push(a.site);
            }
        }
        // A refusal reason is set just before the refusal leaves: a falsy return or a raise within a
        // few lines on the same path. A string set on success (`source = 'file'`) is no reason.
        let return_at: HashMap<Id, &Return> = f.returns.iter().map(|r| (r.site, r)).collect();
        let mut refusals: HashMap<Id, Vec<Id>> = HashMap::new();
        for x in &f.exits {
            if x.kind == EXIT_RAISE
                || (x.kind == EXIT_RETURN
                    && return_at
                        .get(&x.site)
                        .is_some_and(|r| literal_refusal(&r.value.text)))
            {
                refusals
                    .entry(f.sites[x.site as usize].func)
                    .or_default()
                    .push(x.site);
            }
        }
        let refusing = |s: Id| {
            let ss = &f.sites[s as usize];
            refusals.get(&ss.func).into_iter().flatten().any(|&r| {
                let rs = &f.sites[r as usize];
                rs.line > ss.line && rs.line <= ss.line + 6 && self.falls_to(st, s, r)
            })
        };
        for v in sets.values_mut() {
            v.retain(|&s| refusing(s));
        }
        sets.retain(|_, v| !v.is_empty());
        let mut names: Vec<&str> = sets
            .keys()
            .copied()
            .filter(|n| clears.contains_key(n))
            .collect();
        names.sort();
        for name in names {
            let set_sites = &sets[name];
            let clear_sites = &clears[name];
            // Attempts: functions that both set and clear the status themselves.
            let mut attempts: Vec<Id> = set_sites
                .iter()
                .map(|&s| f.sites[s as usize].func)
                .filter(|g| clear_sites.iter().any(|&c| f.sites[c as usize].func == *g))
                .filter(|g| f.funcs[*g as usize].name != "__init__")
                .collect();
            attempts.sort();
            attempts.dedup();
            for g in attempts {
                let own_sets: Vec<Id> = set_sites
                    .iter()
                    .copied()
                    .filter(|&s| f.sites[s as usize].func == g)
                    .collect();
                let own_clears: Vec<Id> = clear_sites
                    .iter()
                    .copied()
                    .filter(|&c| f.sites[c as usize].func == g)
                    .collect();
                let at_start = own_clears
                    .iter()
                    .find(|&&c| own_sets.iter().all(|&s| self.dominates(c, s)));
                let label = f.func_label(g);
                if let Some(&c) = at_start {
                    self.push(
                        6,
                        "stale-status",
                        Verdict::Proven,
                        c,
                        format!("{label} clears `{name}` before any refusal sets it: each attempt starts without the last one's reason"),
                        vec![],
                        vec![],
                    );
                    continue;
                }
                // Every exit of the attempt follows a set or a clear: each call leaves its own
                // outcome, and nothing earlier can show through.
                let exits: Vec<Id> = f
                    .exits
                    .iter()
                    .filter(|x| f.sites[x.site as usize].func == g)
                    .map(|x| x.site)
                    .collect();
                // A write just before the exit on its path, as a refusal's reason is found above
                // (dominance does not reach into an `except` body).
                let silent: Vec<Id> = exits
                    .iter()
                    .copied()
                    .filter(|&x| {
                        let xl = f.sites[x as usize].line;
                        !own_sets.iter().chain(own_clears.iter()).any(|&w| {
                            let wl = f.sites[w as usize].line;
                            wl < xl && wl + 6 >= xl && self.falls_to(st, w, x)
                        })
                    })
                    .collect();
                let every_exit_writes = !exits.is_empty() && silent.is_empty();
                if every_exit_writes {
                    self.push(
                        6,
                        "stale-status",
                        Verdict::Proven,
                        own_sets[0],
                        format!("every exit of {label} sets or clears `{name}`: each call leaves its own outcome"),
                        vec![],
                        vec![],
                    );
                    continue;
                }
                // Every call into the attempt follows a clear in its caller.
                let calls: Vec<Id> = st
                    .callees
                    .iter()
                    .filter(|(_, gs)| gs.contains(&g))
                    .map(|(s, _)| *s)
                    .collect();
                let cleared_by_callers = !calls.is_empty()
                    && calls
                        .iter()
                        .all(|&cs| clear_sites.iter().any(|&c| self.dominates(c, cs)));
                if cleared_by_callers {
                    self.push(
                        6,
                        "stale-status",
                        Verdict::Proven,
                        own_sets[0],
                        format!("every call into {label} follows a clear of `{name}`"),
                        vec![],
                        vec![],
                    );
                    continue;
                }
                let mut witness: Vec<String> = own_sets
                    .iter()
                    .take(4)
                    .map(|&s| format!("{} a refusal sets `{name}`", self.loc(s)))
                    .collect();
                // Sets in functions nested in the attempt (a freshness helper) show the same reason.
                for &s in set_sites
                    .iter()
                    .filter(|&&s| {
                        let h = f.sites[s as usize].func;
                        h != g && st.up.get(&h).is_some_and(|u| u.contains(&g))
                    })
                    .take(3)
                {
                    witness.push(format!(
                        "{} a function the attempt reaches sets `{name}`",
                        self.loc(s)
                    ));
                }
                for &c in &own_clears {
                    witness.push(format!("{} `{name}` is cleared only here", self.loc(c)));
                }
                for &x in silent.iter().take(3) {
                    witness.push(format!(
                        "{} leaves without setting or clearing `{name}`: the last reason stays",
                        self.loc(x)
                    ));
                }
                let first = own_clears[0];
                self.push(
                    6,
                    "stale-status",
                    Verdict::Violated,
                    first,
                    format!(
                        "{label} sets `{name}` on refusals and clears it only after it gets through, not when an attempt starts: an attempt that ends by an exception or a refusal that records nothing leaves the last attempt's reason showing"
                    ),
                    witness,
                    vec![],
                );
            }
        }
    }

    /// Question 6: a window that ends at a clock reading and starts a fixed number of whole days
    /// before it (`fetch(now - timedelta(days=1), now)`), in a repository that schedules in local
    /// time. A day of the schedule is 23 or 25 hours across a daylight saving change, so the window
    /// misses or repeats an hour of what happened since the last scheduled run.
    pub(super) fn fixed_day_span(&mut self) {
        let f = self.f;
        let zoned =
            Regex::new(r"(^|\.)(ZoneInfo|astimezone|tz_localize|timezone|gettz)$").expect("zone");
        if !f.calls.iter().any(|c| zoned.is_match(&c.full)) {
            return;
        }
        let span = Regex::new(
            r"^\(?([A-Za-z_][\w.]*(?:\(\))?)-(?:[\w.]*\.)?timedelta\((days=\d+|\d+|hours=(24|48|72|96|120|144|168)|weeks=\d+)\)\)?$",
        )
        .expect("span");
        let clock = self
            .cfg
            .providers
            .keys()
            .position(|k| k == "clock")
            .map(|i| i as u32);
        let Some(clock) = clock else { return };
        for c in &f.calls {
            let s = &f.sites[c.site as usize];
            if f.funcs[s.func as usize].test {
                continue;
            }
            let args: Vec<&Expr> = c
                .args
                .iter()
                .chain(c.kwargs.iter().map(|(_, x)| x))
                .collect();
            for a in &args {
                let t: String = a.text.chars().filter(|ch| !ch.is_whitespace()).collect();
                let Some(m) = span.captures(&t) else { continue };
                let end = m.get(1).map_or("", |x| x.as_str());
                // The window's other end is the same reading, and that reading is a clock instant.
                let pair = args.iter().any(|b| {
                    let u: String = b.text.chars().filter(|ch| !ch.is_whitespace()).collect();
                    u == end
                });
                if !pair || !self.kinds_of(s.func, a).contains(&clock) {
                    continue;
                }
                self.push(
                    6,
                    "fixed-day-span",
                    Verdict::Violated,
                    c.site,
                    format!(
                        "`{}` is given a window from `{}` to `{end}`: a fixed span of whole days, while the schedule keeps local time, where the day across a daylight saving change is 23 or 25 hours; start the window at the previous scheduled run, or count the days in the zone",
                        c.full,
                        a.text.trim()
                    ),
                    vec![],
                    vec![],
                );
            }
        }
    }

    /// Question 2 on a diff: a key the change starts reading from a stored document has a stand-in
    /// for the stored file the previous release left, a test that writes the store with a literal
    /// lacking the key. Without one, the upgrade path is checked by hand or not at all.
    pub(super) fn upgrade_shape(&mut self, st: &Stores) {
        let f = self.f;
        let new_keys = std::mem::take(&mut self.new_keys);
        if new_keys.is_empty() {
            return;
        }
        let mut done: HashSet<(Id, String)> = HashSet::new();
        let call_at: HashMap<Id, &Call> = f.calls.iter().map(|c| (c.site, c)).collect();
        let mut assigns_of: HashMap<(Id, &str), Vec<&Assign>> = HashMap::new();
        for a in &f.assigns {
            assigns_of
                .entry((f.sites[a.site as usize].func, a.target.as_str()))
                .or_default()
                .push(a);
        }
        // Functions that name a store themselves, by name: a test calls them across files.
        // Functions that return a stored document: a return is a parse call (`json.load`), a
        // variable assigned from one, or a call to such a function. A function that only touches a
        // store and returns what it computed (a run's report) is not one.
        let parse = Regex::new(r"(^|\.)(loads?|safe_load|load_all|read_json)$").expect("parse");
        let mut readers: HashSet<Id> = HashSet::new();
        for _ in 0..4 {
            let before = readers.len();
            let yields = |g: Id, e: &Expr, readers: &HashSet<Id>| {
                let gives = |cs: &Id| {
                    call_at.get(cs).is_some_and(|c| parse.is_match(&c.full))
                        || st
                            .callees
                            .get(cs)
                            .is_some_and(|hs| hs.iter().any(|h| readers.contains(h)))
                };
                e.calls.iter().any(gives)
                    || e.vars.iter().any(|v| {
                        assigns_of
                            .get(&(g, v.as_str()))
                            .is_some_and(|xs| xs.iter().any(|a| a.value.calls.iter().any(gives)))
                    })
            };
            let found: Vec<Id> = f
                .returns
                .iter()
                .filter(|r| yields(f.sites[r.site as usize].func, &r.value, &readers))
                .map(|r| f.sites[r.site as usize].func)
                .collect();
            readers.extend(found);
            if readers.len() == before {
                break;
            }
        }
        let stores_of = |h: Id| -> HashSet<u32> {
            if !readers.contains(&h) {
                return HashSet::new();
            }
            let own: HashSet<u32> = st
                .own_touch
                .get(&h)
                .into_iter()
                .flatten()
                .copied()
                .collect();
            if own.is_empty() {
                st.touch.get(&h).into_iter().flatten().copied().collect()
            } else {
                own
            }
        };
        let names_store: HashMap<&str, HashSet<u32>> =
            readers.iter().fold(HashMap::new(), |mut m, &g| {
                m.entry(f.funcs[g as usize].name.as_str())
                    .or_insert_with(HashSet::new)
                    .extend(stores_of(g));
                m
            });
        for (path, line, key, base, subscript) in &new_keys {
            let Some(site) = f
                .sites
                .iter()
                .position(|s| s.line == *line && f.files[s.file as usize].path == *path)
            else {
                continue;
            };
            let func = f.sites[site].func;
            // The value the key is read from came from a store: assigned in this function from a
            // call to a function that names the store, directly or through one more assignment.
            let root = base.split(['.', '[']).next().unwrap_or(base).to_string();
            // A variable of `g` that holds a store's document: assigned from a call to a function
            // that names the store, directly or through one more assignment.
            let from_store = |g: Id, v: &str| -> HashSet<u32> {
                let direct = |v: &str| -> HashSet<u32> {
                    let mut out = HashSet::new();
                    for a in f
                        .assigns
                        .iter()
                        .filter(|a| a.target == v && f.sites[a.site as usize].func == g)
                    {
                        for &cs in &a.value.calls {
                            for h in st.callees.get(&cs).into_iter().flatten() {
                                out.extend(stores_of(*h));
                            }
                            if let Some(c) = f.calls.iter().find(|c| c.site == cs) {
                                out.extend(
                                    names_store
                                        .get(c.name.as_str())
                                        .into_iter()
                                        .flatten()
                                        .copied(),
                                );
                            }
                        }
                    }
                    out
                };
                let mut out = direct(v);
                if out.is_empty() {
                    for a in f
                        .assigns
                        .iter()
                        .filter(|a| a.target == v && f.sites[a.site as usize].func == g)
                    {
                        for w in &a.value.vars {
                            out.extend(direct(w));
                        }
                    }
                }
                out
            };
            let mut stores = from_store(func, base);
            if stores.is_empty() {
                stores = from_store(func, &root);
            }
            // A parameter: the document a caller read from a store and passed in.
            // Only the argument bound to that parameter counts, by position or keyword.
            let pi = f.funcs[func as usize]
                .params
                .iter()
                .position(|p| p.name == root);
            if let (true, Some(pi)) = (stores.is_empty(), pi) {
                for (cs, gs) in &st.callees {
                    if !gs.contains(&func) {
                        continue;
                    }
                    let caller = f.sites[*cs as usize].func;
                    let off = self.g.offset.get(&(*cs, func)).copied().unwrap_or(0) as usize;
                    if let Some(c) = f.calls.iter().find(|c| c.site == *cs) {
                        let arg = pi
                            .checked_sub(off)
                            .and_then(|i| c.args.get(i))
                            .or_else(|| c.kwargs.iter().find(|(k, _)| *k == root).map(|(_, x)| x));
                        for v in arg.into_iter().flat_map(|a| a.vars.iter()) {
                            stores.extend(from_store(caller, v));
                        }
                    }
                }
            }
            if stores.is_empty() || !done.insert((func, key.clone())) {
                continue;
            }
            let mut names: Vec<&str> = stores
                .iter()
                .map(|&k| st.keys[k as usize].as_str())
                .collect();
            names.sort();
            // A store the change introduces: the previous release left no such file.
            if let Some(seen) = &self.in_base
                && names.iter().all(|n| !seen(n))
            {
                continue;
            }
            // A test that writes one of these stores from a literal without the key.
            let quoted = [format!("\"{key}\""), format!("'{key}'")];
            let old_shape = f.calls.iter().find(|c| {
                let cs = &f.sites[c.site as usize];
                if !f.funcs[cs.func as usize].test {
                    return false;
                }
                let writes = st.callees.get(&c.site).is_some_and(|gs| {
                    gs.iter().any(|g| {
                        st.write
                            .get(g)
                            .is_some_and(|w| w.iter().any(|k| stores.contains(k)))
                    })
                }) || st.own_write.iter().any(|(g, k)| {
                    f.funcs[*g as usize].name == c.name && k.iter().any(|x| stores.contains(x))
                }) || c
                    .str_args
                    .iter()
                    .any(|a| names.iter().any(|n| a.ends_with(n)));
                writes
                    && c.args
                        .iter()
                        .chain(c.kwargs.iter().map(|(_, x)| x))
                        .any(|a| {
                            let t = a.text.trim_start();
                            // `{**current, ...}` spreads today's shape back: no older one.
                            (t.starts_with('{') || t.starts_with("json.dumps({"))
                                && !t.contains("**")
                                && !quoted.iter().any(|q| t.contains(q.as_str()))
                        })
            });
            let store = names.join(", ");
            let site_id = site as Id;
            match old_shape {
                Some(c) => self.push(
                    2,
                    "upgrade-shape",
                    Verdict::Proven,
                    site_id,
                    format!(
                        "`{key}` is new in this change, and {} writes the stored document from a literal without it",
                        self.loc(c.site)
                    ),
                    vec![],
                    vec!["that literal holds the shape the previous release wrote".to_string()],
                ),
                None if *subscript => self.push(
                    2,
                    "upgrade-shape",
                    Verdict::Violated,
                    site_id,
                    format!(
                        "`{key}` is read here by subscript and appears nowhere in the base, and no test writes {store} from a literal without it: a file the previous release left raises here, and only production loads one"
                    ),
                    vec![],
                    vec![],
                ),
                // `.get` names its own answer for a file without the key; whether that answer is right
                // is what a test of the previous shape would show.
                None => self.push(
                    2,
                    "upgrade-shape",
                    Verdict::Unknown,
                    site_id,
                    format!(
                        "`{key}` is new in this change and read with a default; no test writes {store} from a literal without it, so nothing shows the default is right for a file the previous release left"
                    ),
                    vec![],
                    vec![],
                ),
            }
        }
    }

    /// Question 5: a structural test (one that walks a syntax tree) whose check is gated by
    /// membership in a hand-kept table checks only the listed names.
    pub(super) fn name_table_guard(&mut self) {
        let f = self.f;
        let walks =
            Regex::new(r"^ast\.(walk|parse|iter_child_nodes|NodeVisitor)$|(^|\.)getsource$")
                .expect("walk pattern");
        let walking: HashSet<Id> = f
            .calls
            .iter()
            .filter(|c| walks.is_match(&c.full))
            .map(|c| f.sites[c.site as usize].file)
            .collect();
        if walking.is_empty() {
            return;
        }
        let mut tables: HashMap<(Id, String), String> = HashMap::new();
        for a in &f.assigns {
            let s = &f.sites[a.site as usize];
            let t = a.value.text.trim_start();
            if f.funcs[s.func as usize].kind == ScopeKind::Module
                && (t.starts_with('{')
                    || t.starts_with('(')
                    || t.starts_with('[')
                    || t.starts_with("frozenset(")
                    || t.starts_with("set("))
            {
                tables.insert((s.file, a.target.clone()), a.value.text.clone());
            }
        }
        // What a name test is about: a syntax-tree name field (`node.name`, `func.attr`,
        // `alias.name`), and a bound name (`Name.id`), which an alias or a rename changes.
        // Condition text is kept without spaces (`node.idifx`), so a keyword may follow a field.
        let field = Regex::new(r"\.(id|name|attr|module|arg|names)(\b|if|else|and|or|for|in|not)")
            .expect("field");
        let bound = Regex::new(r"\.(id|arg)(\b|if|else|and|or|for|in|not)").expect("bound");
        let quoted = Regex::new(r#""([^"\\]*)"|'([^'\\]*)'"#).expect("quoted");
        // The texts a left operand comes from: itself, the values a plain name was assigned in
        // its function, and the returns of a same-file function those values call.
        let sources = |func: Id, file: Id, lhs: &str| -> Vec<String> {
            let mut out = vec![lhs.to_string()];
            if !lhs.chars().all(|ch| ch.is_alphanumeric() || ch == '_') {
                return out;
            }
            for a in f
                .assigns
                .iter()
                .filter(|a| a.target == lhs && f.sites[a.site as usize].func == func)
            {
                // `a, b = x, y`: each target gets its own element of the value.
                let targets: Vec<&str> = f
                    .assigns
                    .iter()
                    .filter(|b| b.site == a.site)
                    .map(|b| b.target.as_str())
                    .collect();
                let parts = top_level_commas(&a.value.text);
                let value = match targets.iter().position(|t| *t == lhs) {
                    Some(i) if targets.len() > 1 && parts.len() == targets.len() => {
                        parts[i].clone()
                    }
                    _ => a.value.text.clone(),
                };
                out.push(value.clone());
                for &cs in &a.value.calls {
                    let Some(c) = f.calls.iter().find(|c| c.site == cs) else {
                        continue;
                    };
                    if !value.contains(&format!("{}(", c.full)) {
                        continue;
                    }
                    let name = c.full.rsplit('.').next().unwrap_or("");
                    for r in &f.returns {
                        let g = f.sites[r.site as usize].func;
                        if f.funcs[g as usize].name == name && f.funcs[g as usize].file == file {
                            out.push(r.value.text.clone());
                        }
                    }
                }
            }
            out
        };
        // Per repository: in a sweep, one repository's names say nothing about another's tables.
        let mut defined: HashSet<(Id, &str)> = f
            .funcs
            .iter()
            .filter(|x| !x.test && x.kind != ScopeKind::Module)
            .map(|x| (f.files[x.file as usize].repo, x.name.as_str()))
            .collect();
        let production: HashSet<Id> = defined.iter().map(|(r, _)| *r).collect();
        defined.extend(
            f.files
                .iter()
                .map(|x| (x.repo, x.path.rsplit('/').next().unwrap_or(""))),
        );
        let mut once: HashSet<(Id, String, String)> = HashSet::new();
        for c in &f.conds {
            let s = &f.sites[c.site as usize];
            if !walking.contains(&s.file) || !f.funcs[s.func as usize].test {
                continue;
            }
            let repo = f.files[s.file as usize].repo;
            for m in &c.memberships {
                // `on in T` repeated across an `or` is one test.
                if !once.insert((c.site, m.lhs.clone(), m.table.clone())) {
                    continue;
                }
                let table_text = if m.table == "{literal}" {
                    m.rhs.clone()
                } else {
                    match tables.get(&(s.file, m.table.clone())) {
                        Some(t) => t.clone(),
                        None => continue,
                    }
                };
                let from = sources(s.func, s.file, &m.lhs);
                // A test on a value (`r.status_code in (200, 201)`, a parsed keyword) is no name guard.
                if !from.iter().any(|t| field.is_match(t)) {
                    continue;
                }
                let binding = from.iter().any(|t| bound.is_match(t));
                let members: Vec<String> = quoted
                    .captures_iter(&table_text)
                    .filter_map(|x| x.get(1).or(x.get(2)).map(|y| y.as_str().to_string()))
                    .collect();
                let own: Vec<&str> = members
                    .iter()
                    .map(|x| x.as_str())
                    .filter(|x| defined.contains(&(repo, *x)))
                    .collect();
                // A `return` in a helper may be the detection itself; only `continue` skips an item.
                let skips = c.exit == EXIT_CONTINUE;
                let shown = if m.table == "{literal}" {
                    "a literal set".to_string()
                } else {
                    format!("`{}`", m.table)
                };
                let (verdict, msg) = match (m.negated, skips, c.fails) {
                    (true, true, _) => (
                        Verdict::Violated,
                        format!(
                            "the guard checks only the names listed in {shown}: code added outside the table passes it unchecked; enumerate by the primitive and allow-list where it may appear"
                        ),
                    ),
                    (false, _, true) => (
                        Verdict::Violated,
                        format!(
                            "the guard refuses the names listed in {shown}: one not yet listed passes; enumerate by the primitive and allow-list where it may appear"
                        ),
                    ),
                    (true, false, true) => (
                        Verdict::Proven,
                        format!("the guard refuses whatever {shown} does not allow"),
                    ),
                    (false, true, _) => (
                        Verdict::Proven,
                        format!("the guard skips only what {shown} allows"),
                    ),
                    _ => continue,
                };
                let mut sample: Vec<&str> = members.iter().map(|x| x.as_str()).collect();
                sample.truncate(6);
                let sample = sample.join(", ");
                // Bound names (`Name.id`) change with an alias or a rename: the table never closes.
                // Names this repository defines grow with its code. Mostly outside names, matched by
                // a field an alias cannot change, are a closed domain of the library they belong to.
                let (verdict, msg, assumptions) = if verdict == Verdict::Proven {
                    let a = vec![
                        "the names tested are the primitive itself, not a list of its callers"
                            .to_string(),
                    ];
                    (verdict, msg, a)
                } else if binding {
                    (
                        verdict,
                        format!(
                            "{msg}; the names ({sample}) are bound names, which an import alias or a rename changes"
                        ),
                        vec![],
                    )
                } else if !production.contains(&repo) {
                    (
                        Verdict::Unknown,
                        format!(
                            "{msg}; whether {sample} are this repository's names or an outside library's is not known: no production code is in the scan"
                        ),
                        vec!["the scope leaves out the code the table names".to_string()],
                    )
                } else if own.len() * 2 > members.len() {
                    let mut o = own.clone();
                    o.truncate(4);
                    (
                        verdict,
                        format!("{msg}; it lists names defined here ({})", o.join(", ")),
                        vec![],
                    )
                } else {
                    (
                        Verdict::Proven,
                        format!(
                            "the guard's table names outside names ({sample}) that this repository mostly does not define: a closed domain, which grows only when that library does"
                        ),
                        vec!["the table holds the whole outside domain it names".to_string()],
                    )
                };
                self.push(
                    5,
                    "name-table-guard",
                    verdict,
                    c.site,
                    msg,
                    vec![],
                    assumptions,
                );
            }
        }
    }
}

/// An expression's text split at its commas outside brackets and strings.
fn top_level_commas(text: &str) -> Vec<String> {
    let (mut out, mut cur, mut depth, mut quote) = (vec![], String::new(), 0i32, None::<char>);
    for ch in text.chars() {
        match (quote, ch) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), _) => {}
            (None, '"' | '\'') => quote = Some(ch),
            (None, '(' | '[' | '{') => depth += 1,
            (None, ')' | ']' | '}') => depth -= 1,
            (None, ',') if depth == 0 => {
                out.push(std::mem::take(&mut cur));
                continue;
            }
            _ => {}
        }
        cur.push(ch);
    }
    out.push(cur);
    out
}
