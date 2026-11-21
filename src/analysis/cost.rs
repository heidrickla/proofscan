//! Question 6 over work that input sizes: a loop that searches a list linearly and adds to the
//! same list costs the square of its input, so a request of a few kilobytes can hold a core.

use super::Analysis;
use crate::facts::*;
use crate::report::Verdict;
use std::collections::BTreeMap;

/// The linear searches a Rust iterator chain makes over its receiver.
const RUST_SEARCH: &[&str] = &["any", "all", "find", "find_map", "position", "rposition"];
/// The calls that add to a list.
const GROW: &[&str] = &["push", "append", "insert", "push_back", "extend"];

impl<'a> Analysis<'a> {
    pub(super) fn grow_and_search(&mut self) {
        let f = self.f;
        let at = |site: Id| &f.sites[site as usize];
        let lang = |site: Id| f.files[at(site).file as usize].lang;
        let test = |site: Id| f.files[at(site).file as usize].test;
        // A list made in the function: `[]` or `list(...)` in Python; `Vec::new()`, `vec![...]`
        // or `Vec::with_capacity(...)` in Rust. A name bound to anything else may be a set.
        let mut lists: BTreeMap<(Id, String), ()> = BTreeMap::new();
        for a in &f.assigns {
            let v = a.value.text.trim();
            let list = v == "[]"
                || v.starts_with("list(")
                || v.starts_with("Vec::new(")
                || v.starts_with("vec![")
                || v.starts_with("Vec::with_capacity(")
                || v.starts_with("Vec::<");
            if list {
                let target = a.target.trim_start_matches("mut ").to_string();
                lists.insert((at(a.site).func, target), ());
            }
        }
        let reach = self.untrusted_reach();
        // Searches: (site, list) for each linear search inside a loop.
        let mut searches: Vec<(Id, String)> = vec![];
        for c in &f.calls {
            let s = at(c.site);
            if s.ctx.loop_id.is_none() || test(c.site) {
                continue;
            }
            match lang(c.site) {
                Lang::Rust => {
                    if let Some(base) = c.recv.strip_suffix(".iter()")
                        && RUST_SEARCH.contains(&c.name.as_str())
                    {
                        searches.push((c.site, base.to_string()));
                    } else if c.name == "contains" && lists.contains_key(&(s.func, c.recv.clone()))
                    {
                        searches.push((c.site, c.recv.clone()));
                    }
                }
                Lang::Python
                    if (c.name == "index" || c.name == "count")
                        && lists.contains_key(&(s.func, c.recv.clone())) =>
                {
                    searches.push((c.site, c.recv.clone()));
                }
                _ => {}
            }
        }
        for k in &f.compares {
            let s = at(k.site);
            if s.ctx.loop_id.is_none() || test(k.site) || lang(k.site) != Lang::Python {
                continue;
            }
            let op = k.op.replace(' ', "");
            if (op == "in" || op == "notin") && lists.contains_key(&(s.func, k.right.text.clone()))
            {
                searches.push((k.site, k.right.text.clone()));
            }
        }
        for (site, list) in searches {
            let s = at(site);
            // The question is cost sized by untrusted input: code no entry reaches is not asked.
            if !reach.contains(&s.func) {
                continue;
            }
            let grow = f.calls.iter().find(|g| {
                let gs = at(g.site);
                gs.file == s.file
                    && gs.func == s.func
                    && gs.ctx.loop_id == s.ctx.loop_id
                    && g.recv == list
                    && GROW.contains(&g.name.as_str())
            });
            let Some(grow) = grow else { continue };
            // A list made inside the loop starts empty on every step: it never carries the
            // previous steps' growth, so the search is not quadratic.
            let fresh = f.assigns.iter().any(|a| {
                let asite = at(a.site);
                asite.file == s.file
                    && asite.func == s.func
                    && asite.ctx.loop_id == s.ctx.loop_id
                    && a.target.trim_start_matches("mut ").trim() == list
            });
            if fresh {
                continue;
            }
            let path = &f.files[s.file as usize].path;
            // What is added is a value taken from a literal array, chosen only when the list does
            // not hold it yet (`[..].into_iter().find(|n| !seen.contains(n))`): the list holds
            // distinct elements of that array and can never be longer than it.
            let added = grow
                .args
                .first()
                .map(|a| a.text.trim().trim_start_matches('&').trim().to_string())
                .unwrap_or_default();
            let word = regex::Regex::new(&format!(r"\b{}\b", regex::escape(&added))).ok();
            let distinct = f.assigns.iter().find(|a| {
                !added.is_empty() && {
                    let asite = at(a.site);
                    let v = a.value.text.trim();
                    asite.file == s.file
                        && asite.func == s.func
                        && asite.line <= at(grow.site).line
                        && word.as_ref().is_some_and(|w| w.is_match(&a.target))
                        && v.starts_with('[')
                        && v.contains(&format!("!{list}.contains("))
                }
            });
            if let Some(a) = distinct {
                self.push(
                    6,
                    "grow-and-search",
                    Verdict::Proven,
                    site,
                    format!(
                        "`{list}` only gains `{added}`, a value of a literal array that `{list}` does not hold yet (line {}): it can never be longer than that array",
                        at(a.site).line
                    ),
                    vec![
                        format!("{path}:{} searches `{list}` from its start", s.line),
                        format!("{path}:{} `{added}` comes from a literal array", at(a.site).line),
                    ],
                    vec!["the literal array is the only source of what is added".into()],
                );
                continue;
            }
            let bound_of = |name: &str| {
                let len_rust = format!("{name}.len()");
                let len_py = format!("len({name})");
                f.compares.iter().find(|k| {
                    let ks = at(k.site);
                    ks.file == s.file
                        && ks.func == s.func
                        && [&k.left.text, &k.right.text]
                            .iter()
                            .any(|t| t.contains(&len_rust) || t.contains(&len_py))
                })
            };
            // The list the loop walks: a bound on it bounds the list grown once per step.
            let walked = f
                .loops
                .iter()
                .find(|l| {
                    let ls = at(l.site);
                    ls.file == s.file && Some(l.id) == s.ctx.loop_id
                })
                .map(|l| iterated(&l.iter));
            let bound = bound_of(&list).or_else(|| walked.as_deref().and_then(bound_of));
            let witness = vec![
                format!("{path}:{} searches `{list}` from its start", s.line),
                format!(
                    "{path}:{} adds to `{list}` in the same loop",
                    at(grow.site).line
                ),
            ];
            // A walked or searched parameter may be bounded by every caller; that is not followed.
            let is_param = |w: &str| {
                f.funcs[s.func as usize]
                    .params
                    .iter()
                    .any(|p| p.name.trim_start_matches("mut ") == w)
            };
            let param = walked
                .as_deref()
                .filter(|w| is_param(w))
                .or_else(|| is_param(&list).then_some(list.as_str()));
            if bound.is_none()
                && let Some(p) = param
            {
                self.push(
                    6,
                    "grow-and-search",
                    Verdict::Unknown,
                    site,
                    format!(
                        "`{list}` is searched from its start and grown in one loop that depends on the parameter `{p}`, which this function does not bound; a bound at its callers is not followed"
                    ),
                    witness,
                    vec![],
                );
                continue;
            }
            match bound {
                Some(b) => self.push(
                    6,
                    "grow-and-search",
                    Verdict::Proven,
                    site,
                    format!(
                        "`{list}` is searched and grown in one loop, and its length is checked at line {}: the work stays within that bound",
                        at(b.site).line
                    ),
                    witness,
                    vec![format!(
                        "the check at line {} bounds `{list}`",
                        at(b.site).line
                    )],
                ),
                None => self.push(
                    6,
                    "grow-and-search",
                    Verdict::Violated,
                    site,
                    format!(
                        "`{list}` is searched from its start and grown in the same loop, with no bound on its length: the loop costs the square of its input"
                    ),
                    witness,
                    vec![],
                ),
            }
        }
    }
}

impl<'a> Analysis<'a> {
    /// Functions registered with a router or named as untrusted by configuration.
    pub(super) fn untrusted_entries(&self) -> Vec<Id> {
        let f = self.f;
        let q6 = &self.cfg.q6;
        let route = regex::Regex::new(&q6.untrusted_route).ok();
        let method = regex::Regex::new(&q6.untrusted_method).ok();
        let named = (!q6.untrusted_function.is_empty())
            .then(|| regex::Regex::new(&q6.untrusted_function).ok())
            .flatten();
        let mut seeds: Vec<Id> = vec![];
        if let Some(re) = &named {
            for (i, x) in f.funcs.iter().enumerate() {
                let at = format!("{}:{}", f.files[x.file as usize].path, x.name);
                if x.kind == ScopeKind::Function && re.is_match(&at) {
                    seeds.push(i as Id);
                }
            }
        }
        if let (Some(route), Some(method)) = (&route, &method)
            && !q6.untrusted_route.is_empty()
        {
            for r in &f.calls {
                if !route.is_match(&r.full)
                    || r.args.len() < 2
                    || f.files[f.sites[r.site as usize].file as usize].test
                {
                    continue;
                }
                let file = f.sites[r.site as usize].file;
                for &m in &r.args[1].calls {
                    let Some(c) = self.call(m) else { continue };
                    if !method.is_match(&c.name) {
                        continue;
                    }
                    let Some(a) = c.args.first() else { continue };
                    let path = a.text.trim();
                    if path.is_empty()
                        || !path.split("::").all(|part| {
                            !part.is_empty()
                                && part.chars().all(|ch| ch.is_alphanumeric() || ch == '_')
                        })
                    {
                        continue;
                    }
                    let (module, name) = path.rsplit_once("::").unwrap_or(("", path));
                    // `super::` and `self::` name a module relative to this one; what follows is
                    // matched as a module suffix, and nothing following means a bare name.
                    let mut module = module.strip_prefix("crate::").unwrap_or(module);
                    while let Some(rest) = module.strip_prefix("super::") {
                        module = rest;
                    }
                    if module == "super" {
                        module = "";
                    }
                    let module = module.strip_prefix("self::").unwrap_or(module);
                    let here = &f.files[file as usize];
                    let mut candidates = f.funcs.iter().enumerate().filter(|(_, x)| {
                        let there = &f.files[x.file as usize];
                        x.kind == ScopeKind::Function
                            && x.name == name
                            && !x.test
                            && x.class.is_none()
                            && here.repo == there.repo
                            && here.lang == there.lang
                            && (module.is_empty()
                                || if matches!(module, "crate" | "self") {
                                    file == x.file
                                } else {
                                    there.module == module
                                        || there.module.ends_with(&format!("::{module}"))
                                })
                    });
                    let target = candidates
                        .clone()
                        .find(|(_, x)| x.file == file)
                        .or_else(|| {
                            let first = candidates.next()?;
                            candidates.next().is_none().then_some(first)
                        });
                    if let Some((h, _)) = target {
                        seeds.push(h as Id);
                    }
                }
            }
        }
        seeds.sort_unstable();
        seeds.dedup();
        seeds
    }

    /// The functions reached from an untrusted entry through the call graph.
    pub(super) fn untrusted_reach(&self) -> std::collections::HashSet<Id> {
        let mut seeds = self.untrusted_entries();
        let mut out: std::collections::HashSet<Id> = seeds.iter().copied().collect();
        let mut next: std::collections::HashMap<Id, Vec<Id>> = std::collections::HashMap::new();
        // Exact edges, and a name-resolved call only when its name has one candidate: a method
        // resolved by name to many functions would carry the question to code no request reaches.
        for &(caller, callee, site, exact) in &self.g.edges {
            let single = self.g.targets.get(&site).is_some_and(|t| t.len() == 1);
            if exact || single {
                next.entry(caller).or_default().push(callee);
            }
        }
        while let Some(x) = seeds.pop() {
            for &y in next.get(&x).into_iter().flatten() {
                if out.insert(y) {
                    seeds.push(y);
                }
            }
        }
        out
    }
}

/// The list a loop walks, from its iterated expression: `&raw_attrs`, `raw_attrs.iter()` and
/// `self.items.drain(..)` walk `raw_attrs` and `self.items`.
fn iterated(text: &str) -> String {
    let t = text
        .trim_start_matches('&')
        .trim_start_matches("mut ")
        .trim();
    let t = t.strip_prefix("enumerate(").unwrap_or(t);
    let mut out = String::new();
    for part in t.split('.') {
        let ident: String = part
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if ident.is_empty() || ident.len() != part.len() {
            if out.is_empty() {
                out = ident;
            }
            break;
        }
        if !out.is_empty() {
            out.push('.');
        }
        out.push_str(&ident);
    }
    out
}
