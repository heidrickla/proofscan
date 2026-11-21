//! Call resolution: each call site to the in-repo functions it may reach.
//! An edge is exact when the target is determined by the name's binding (a local or imported
//! def, a method on `self`'s own class or its bases, a qualified path); it is a may edge when only
//! the method name is known (`obj.m()` with `obj` untyped), in which case every in-repo method of
//! that name is a candidate. A call with no in-repo candidate is external. `self.x.m()` is typed
//! when every assignment to `self.x` is a constructor call: an in-repo class gives exact edges,
//! a call outside the repository gives none. In a sweep, an edge between two repositories needs
//! a module path (an import or a qualified name); a match by name stays in the caller's repository.

use crate::facts::*;
use std::collections::HashMap;

pub struct Graph {
    /// caller, callee, call site, exact
    pub edges: Vec<(Id, Id, Id, bool)>,
    /// For each call site, its targets.
    pub targets: HashMap<Id, Vec<(Id, bool)>>,
    /// Positional offset of argument 0 in the callee's parameters (1 when `self` is bound).
    pub offset: HashMap<(Id, Id), u32>,
    /// Calls by a method name more than `MAX_DISPATCH` in-repo methods share, not followed.
    pub wide: usize,
}

/// The most in-repo methods a call by name alone is taken to reach.
pub const MAX_DISPATCH: usize = 8;

pub fn class_of(f: &Facts, func: Id) -> Option<Id> {
    let mut cur = f.funcs[func as usize].parent;
    while let Some(p) = cur {
        if f.funcs[p as usize].kind == ScopeKind::Class {
            return Some(p);
        }
        cur = f.funcs[p as usize].parent;
    }
    None
}

/// The crate a Rust file belongs to: the path up to its `src/` directory (`tools/x/src/a.rs` is
/// in `tools/x`).
fn crate_of(path: &str) -> &str {
    path.rfind("/src/")
        .map(|i| &path[..i])
        .or_else(|| path.starts_with("src/").then_some(""))
        .unwrap_or(path)
}

pub fn module_of_func(f: &Facts, func: Id) -> Id {
    let mut cur = func;
    while let Some(p) = f.funcs[cur as usize].parent {
        cur = p;
    }
    cur
}

pub fn build(f: &Facts) -> Graph {
    let mut by_name: HashMap<&str, Vec<Id>> = HashMap::new();
    let mut methods: HashMap<(&str, &str), Vec<Id>> = HashMap::new();
    let mut classes: HashMap<&str, Vec<Id>> = HashMap::new();
    let mut top: HashMap<(Id, &str), Id> = HashMap::new();
    let mut nested: HashMap<(Id, &str), Id> = HashMap::new();
    let mut subclasses: HashMap<&str, Vec<&str>> = HashMap::new();
    for (i, func) in f.funcs.iter().enumerate() {
        let i = i as Id;
        match func.kind {
            ScopeKind::Class => {
                classes.entry(&func.name).or_default().push(i);
                for b in &func.bases {
                    subclasses
                        .entry(b.rsplit('.').next().unwrap_or(b))
                        .or_default()
                        .push(&func.name);
                }
            }
            ScopeKind::Function => {
                by_name.entry(&func.name).or_default().push(i);
                if let Some(c) = &func.class {
                    methods
                        .entry((c.as_str(), func.name.as_str()))
                        .or_default()
                        .push(i);
                }
                if let Some(p) = func.parent {
                    let pk = f.funcs[p as usize].kind;
                    if pk == ScopeKind::Module && func.class.is_none() {
                        top.insert((func.file, func.name.as_str()), i);
                    } else if pk == ScopeKind::Function {
                        nested.insert((p, func.name.as_str()), i);
                    }
                }
            }
            ScopeKind::Module => {}
        }
    }
    let mut imports: HashMap<(Id, &str), &str> = HashMap::new();
    for (file, local, target) in &f.imports {
        imports.insert((*file, local.as_str()), target.trim_start_matches('.'));
    }
    // Every dotted suffix of every module path, to its files: `a.b.c` is found as `c`, `b.c`, `a.b.c`.
    let mut module_index: HashMap<String, Vec<Id>> = HashMap::new();
    for (i, x) in f.files.iter().enumerate() {
        let m = x.module.replace("::", ".");
        let mut rest = m.as_str();
        loop {
            module_index
                .entry(rest.to_string())
                .or_default()
                .push(i as Id);
            match rest.split_once('.') {
                Some((_, r)) => rest = r,
                None => break,
            }
        }
    }
    // In a sweep two repositories can hold the same module path; the caller's own repository wins.
    let file_for_module = |m: &str, from: Id| -> Option<Id> {
        let repo = f.files[from as usize].repo;
        module_index
            .get(&m.replace("::", "."))?
            .iter()
            .min_by_key(|i| (f.files[**i as usize].repo != repo, **i))
            .copied()
    };
    // Methods of a class and its in-repo bases, nearest first.
    let lookup = |class: &str, name: &str| -> Vec<Id> {
        let mut seen = vec![class.to_string()];
        let mut queue = vec![class.to_string()];
        while let Some(c) = queue.pop() {
            if let Some(m) = methods.get(&(c.as_str(), name)) {
                return m.clone();
            }
            for cid in classes.get(c.as_str()).into_iter().flatten() {
                for b in &f.funcs[*cid as usize].bases {
                    let b = b.rsplit('.').next().unwrap_or(b).to_string();
                    if !seen.contains(&b) {
                        seen.push(b.clone());
                        queue.push(b);
                    }
                }
            }
        }
        vec![]
    };
    let overrides = |class: &str, name: &str| -> Vec<Id> {
        let mut out = vec![];
        let mut queue: Vec<&str> = subclasses.get(class).cloned().unwrap_or_default();
        let mut seen: Vec<&str> = vec![];
        while let Some(c) = queue.pop() {
            if seen.contains(&c) {
                continue;
            }
            seen.push(c);
            out.extend(methods.get(&(c, name)).cloned().unwrap_or_default());
            queue.extend(subclasses.get(c).cloned().unwrap_or_default());
        }
        out
    };
    let init_of = |class_name: &str| -> Vec<Id> {
        lookup(class_name, "__init__")
            .into_iter()
            .chain(lookup(class_name, "new"))
            .collect()
    };

    // The types an attribute `self.x` is given: every assignment is a constructor call (an in-repo
    // class, or a call to code outside the repository) or `None`. Any other value leaves it untyped.
    let call_at: HashMap<Id, &Call> = f.calls.iter().map(|c| (c.site, c)).collect();
    let mut attr_types: HashMap<(String, String), Option<Vec<String>>> = HashMap::new();
    for a in &f.assigns {
        let Some(attr) = a.target.strip_prefix("self.").filter(|x| !x.contains('.')) else {
            continue;
        };
        let func = f.sites[a.site as usize].func;
        let Some(cl) = class_of(f, func)
            .map(|k| f.funcs[k as usize].name.clone())
            .or_else(|| f.funcs[func as usize].class.clone())
        else {
            continue;
        };
        let text = a.value.text.trim();
        let entry = attr_types
            .entry((cl, attr.to_string()))
            .or_insert_with(|| Some(vec![]));
        if text == "None" {
            continue;
        }
        let top = a
            .value
            .calls
            .first()
            .and_then(|s| call_at.get(s))
            .filter(|c| text.starts_with(&format!("{}(", c.full)) && text.ends_with(')'));
        let kind = top.and_then(|c| {
            let n = c.full.rsplit('.').next().unwrap_or(&c.full);
            if classes.contains_key(n) {
                Some(n.to_string())
            } else if !by_name.contains_key(n) && !classes.contains_key(n) {
                Some(String::new()) // outside the repository
            } else {
                None
            }
        });
        match (entry.as_mut(), kind) {
            (Some(v), Some(k)) => {
                if !v.contains(&k) {
                    v.push(k);
                }
            }
            _ => *entry = None,
        }
    }
    // The attribute's types seen from `class` and its in-repo bases.
    let attr_type = |class: &str, attr: &str| -> Option<Vec<String>> {
        let mut queue = vec![class.to_string()];
        let mut seen = vec![];
        while let Some(c) = queue.pop() {
            if seen.contains(&c) {
                continue;
            }
            if let Some(t) = attr_types.get(&(c.clone(), attr.to_string())) {
                return t.clone();
            }
            for cid in classes.get(c.as_str()).into_iter().flatten() {
                queue.extend(
                    f.funcs[*cid as usize]
                        .bases
                        .iter()
                        .map(|b| b.rsplit('.').next().unwrap_or(b).to_string()),
                );
            }
            seen.push(c);
        }
        None
    };

    let mut g = Graph {
        edges: vec![],
        targets: HashMap::new(),
        offset: HashMap::new(),
        wide: 0,
    };
    for c in &f.calls {
        let site = &f.sites[c.site as usize];
        let caller = site.func;
        let file = site.file;
        let lang = f.files[file as usize].lang;
        let class = class_of(f, caller)
            .map(|k| f.funcs[k as usize].name.clone())
            .or_else(|| f.funcs[caller as usize].class.clone());
        let mut out: Vec<(Id, bool)> = vec![];
        // Targets reached through a module path, the only edges allowed between repositories.
        let mut by_module: Vec<Id> = vec![];
        let mut bound_self = false;
        let recv = c.recv.as_str();
        let name = c.name.as_str();
        if recv.is_empty() {
            let mut cur = Some(caller);
            while let Some(s) = cur {
                if let Some(t) = nested.get(&(s, name)) {
                    out.push((*t, true));
                    break;
                }
                cur = f.funcs[s as usize]
                    .parent
                    .filter(|p| f.funcs[*p as usize].kind == ScopeKind::Function);
            }
            if out.is_empty()
                && let Some(t) = top.get(&(file, name))
            {
                out.push((*t, true));
            }
            if out.is_empty()
                && classes
                    .get(name)
                    .is_some_and(|v| v.iter().any(|k| f.funcs[*k as usize].file == file))
            {
                out.extend(init_of(name).into_iter().map(|t| (t, true)));
                bound_self = true;
            }
            if out.is_empty()
                && let Some(target) = imports.get(&(file, name))
            {
                let (m, n) = target.rsplit_once('.').unwrap_or(("", target));
                if let Some(mf) = file_for_module(m, file)
                    && let Some(t) = top.get(&(mf, n))
                {
                    out.push((*t, true));
                    by_module.push(*t);
                } else if classes.contains_key(n) {
                    out.extend(init_of(n).into_iter().map(|t| (t, true)));
                    bound_self = true;
                }
            }
            if out.is_empty() && lang == Lang::Rust {
                // A bare name reaches a function of the caller's own crate; another crate's
                // function is reached through a `use` path, resolved above.
                let krate = crate_of(&f.files[file as usize].path);
                let cands: Vec<Id> = by_name
                    .get(name)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|t| {
                        let tf = &f.funcs[*t as usize];
                        tf.class.is_none() && crate_of(&f.files[tf.file as usize].path) == krate
                    })
                    .collect();
                let exact = cands.len() == 1;
                out.extend(cands.into_iter().map(|t| (t, exact)));
            }
        } else if matches!(recv, "self" | "cls" | "super()" | "Self") {
            if let Some(cl) = &class {
                let found = if recv == "super()" {
                    classes
                        .get(cl.as_str())
                        .into_iter()
                        .flatten()
                        .flat_map(|k| f.funcs[*k as usize].bases.clone())
                        .flat_map(|b| lookup(b.rsplit('.').next().unwrap_or(&b), name))
                        .collect()
                } else {
                    lookup(cl, name)
                };
                out.extend(found.into_iter().map(|t| (t, true)));
                if recv != "super()" {
                    for t in overrides(cl, name) {
                        if !out.iter().any(|(x, _)| *x == t) {
                            out.push((t, false));
                        }
                    }
                }
                bound_self = lang == Lang::Python && recv != "Self";
            }
        } else if let Some(types) = recv
            .strip_prefix("self.")
            .filter(|x| !x.contains('.') && lang == Lang::Python)
            .and_then(|attr| class.as_deref().and_then(|cl| attr_type(cl, attr)))
            .filter(|v| !v.is_empty())
        {
            // `self.x.m()` where every value `self.x` is given has a known type.
            for ty in types.iter().filter(|t| !t.is_empty()) {
                out.extend(lookup(ty, name).into_iter().map(|t| (t, true)));
                for t in overrides(ty, name) {
                    if !out.iter().any(|(x, _)| *x == t) {
                        out.push((t, false));
                    }
                }
            }
            bound_self = true;
        } else {
            let head = recv.split(['.', ':']).next().unwrap_or(recv);
            let module_target = imports
                .get(&(file, head))
                .copied()
                .map(str::to_string)
                .or_else(|| (lang == Lang::Rust).then(|| recv.to_string()));
            let mut done = false;
            if let Some(m) = module_target
                && let Some(mf) = file_for_module(
                    &format!("{}{}", m, recv[head.len()..].replace("::", ".")),
                    file,
                )
                && let Some(t) = top.get(&(mf, name))
            {
                out.push((*t, true));
                by_module.push(*t);
                done = true;
            }
            let type_name = recv.rsplit(['.', ':']).next().unwrap_or(recv);
            if !done && classes.contains_key(type_name)
                || (!done && lang == Lang::Rust && methods.contains_key(&(type_name, name)))
            {
                let found = lookup(type_name, name);
                if !found.is_empty() {
                    out.extend(found.into_iter().map(|t| (t, true)));
                    done = true;
                }
            }
            if !done {
                let here = &f.files[file as usize];
                let cands: Vec<Id> = by_name
                    .get(name)
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|&t| {
                        let tf = &f.funcs[t as usize];
                        let there = &f.files[tf.file as usize];
                        tf.class.is_some() && there.repo == here.repo && there.lang == lang
                    })
                    .collect();
                // A name many methods share says nothing about the target; following every one
                // would make the graph quadratic. Such calls are counted and reported.
                if cands.len() > MAX_DISPATCH {
                    g.wide += 1;
                } else {
                    out.extend(cands.into_iter().map(|t| (t, false)));
                }
                bound_self = lang == Lang::Python;
            }
        }
        // An edge stays in the caller's language, and in its repository (and for Rust its crate)
        // unless a module path resolved it.
        let here = &f.files[file as usize];
        out.retain(|(t, _)| {
            let there = &f.files[f.funcs[*t as usize].file as usize];
            let local = there.repo == here.repo
                && (lang != Lang::Rust || crate_of(&there.path) == crate_of(&here.path));
            there.lang == lang && (local || by_module.contains(t))
        });
        for (t, exact) in &out {
            g.edges.push((caller, *t, c.site, *exact));
            let first = f.funcs[*t as usize].params.first().map(|p| p.name.as_str());
            if bound_self && matches!(first, Some("self") | Some("cls")) {
                g.offset.insert((c.site, *t), 1);
            }
        }
        g.targets.insert(c.site, out);
    }
    g
}
