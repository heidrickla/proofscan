//! Question 4 for a request size check and a Tokio semaphore wait on the same path.

use super::Analysis;
use crate::facts::{Id, Lang};
use crate::lang::{lang_of, line, named_children, text};
use crate::report::{Finding, Verdict};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::Path;
use tree_sitter::{Node, Parser};

const ACQUIRE: &[&str] = &[
    "acquire",
    "acquire_owned",
    "acquire_many",
    "acquire_many_owned",
];

impl Analysis<'_> {
    pub(super) fn guard_after_wait(&mut self) {
        let f = self.f;
        let group = |file: Id| {
            let f = &f.files[file as usize];
            let root = f.path.rsplit_once("/src/").map_or("", |(root, _)| root);
            (f.repo, root)
        };
        let mut waits = HashSet::new();
        let mut routes = BTreeMap::<_, Vec<_>>::new();
        for call in &f.calls {
            let s = &f.sites[call.site as usize];
            if f.files[s.file as usize].lang != Lang::Rust || f.funcs[s.func as usize].test {
                continue;
            }
            if ACQUIRE.contains(&call.name.as_str()) {
                waits.insert(group(s.file));
            }
            if call.name == "route"
                && let Some(arg) = call.args.get(1)
            {
                for method in arg.calls.iter().filter_map(|&id| self.call(id)) {
                    if matches!(
                        method.name.as_str(),
                        "get" | "post" | "put" | "patch" | "delete"
                    ) && let Some(handler) = method.args.first()
                    {
                        routes.entry(group(s.file)).or_default().push((
                            s.file,
                            method.full.as_str(),
                            handler.text.as_str(),
                        ));
                    }
                }
            }
        }
        if !routes.keys().any(|key| waits.contains(key)) {
            return;
        }

        // load emits one fact file per supported text, in source order, including parse failures.
        let mut groups = BTreeMap::<_, Vec<_>>::new();
        let texts = self
            .texts
            .iter()
            .filter(|(p, _)| lang_of(Path::new(p)).is_some());
        let mut parser = Parser::new();
        if parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .is_err()
        {
            return;
        }
        for ((id, file), (path, src)) in f.files.iter().enumerate().zip(texts) {
            let id = id as Id;
            let key = group(id);
            // The pairing is by position; a text whose path differs is not this file's.
            if file.path != *path {
                continue;
            }
            if file.lang == Lang::Rust
                && !file.test
                && waits.contains(&key)
                && routes.contains_key(&key)
                && let Some(tree) = parser.parse(src, None)
            {
                groups
                    .entry(key)
                    .or_default()
                    .push((id, src.as_str(), tree));
            }
        }
        let mut findings = Vec::new();
        for (key, files) in &groups {
            let mut code = Code::new(self);
            for (file, src, tree) in files {
                code.index(*file, src, tree.root_node());
            }
            let mut seen = HashSet::new();
            for &(file, method, handler) in &routes[key] {
                if !code.is_import(file, method, "axum::routing") {
                    continue;
                }
                let Some(routine) = code.function(file, handler, None) else {
                    continue;
                };
                if !seen.insert((routine.file, routine.body.id())) {
                    continue;
                }
                let mut entry = Frame::new(routine);
                for param in &routine.params {
                    if code.request_input(routine, param) {
                        entry.inputs.insert(
                            param.name,
                            Origin {
                                name: param.name.to_string(),
                                entry: code.loc(routine.file, param.node),
                                copy: None,
                                filtered: false,
                            },
                        );
                    }
                }
                if entry.inputs.is_empty() {
                    continue;
                }
                code.inspect(&entry, &[], &mut findings);
                for (call, _) in awaited(entry.body) {
                    if let Some(next) = code.follow(&entry, call)
                        && !next.inputs.is_empty()
                    {
                        code.inspect(&next, &[(&entry, call)], &mut findings);
                    }
                }
            }
        }
        findings
            .sort_by(|a, b| (&a.repo, &a.site, &a.message).cmp(&(&b.repo, &b.site, &b.message)));
        findings.dedup_by(|a, b| a.repo == b.repo && a.site == b.site && a.witness == b.witness);
        self.findings.extend(findings);
    }
}

#[derive(Clone, Copy)]
struct Type<'a> {
    node: Node<'a>,
    src: &'a str,
    file: Id,
}

struct Param<'a> {
    node: Node<'a>,
    name: &'a str,
    ty: Option<Type<'a>>,
    input: bool,
    // A mutable or destructured parameter can still take a positional argument.
    simple: bool,
}

struct Routine<'a> {
    file: Id,
    src: &'a str,
    name: &'a str,
    owner: Option<Type<'a>>,
    body: Node<'a>,
    params: Vec<Param<'a>>,
}

struct Code<'a, 'data> {
    analysis: &'a Analysis<'data>,
    functions: Vec<Routine<'a>>,
    types: HashMap<&'a str, Vec<Type<'a>>>,
    constants: HashMap<(Id, &'a str), Node<'a>>,
    imports: HashMap<(Id, &'a str), String>,
}

impl<'a, 'data> Code<'a, 'data> {
    fn new(analysis: &'a Analysis<'data>) -> Self {
        Self {
            analysis,
            functions: Vec::new(),
            types: HashMap::new(),
            constants: HashMap::new(),
            imports: HashMap::new(),
        }
    }

    fn index(&mut self, file: Id, src: &'a str, root: Node<'a>) {
        let mut cfg = false;
        for item in statements(root) {
            if item.kind() == "attribute_item" {
                cfg |= text(item, src).contains("cfg");
                continue;
            }
            if std::mem::take(&mut cfg) {
                continue;
            }
            let ty = |node| Type { node, src, file };
            match item.kind() {
                "use_declaration" => {
                    if let Some(arg) = field(item, "argument") {
                        self.index_import(file, src, arg, "");
                    }
                }
                "struct_item" | "type_item" => {
                    if let Some(name) = field(item, "name") {
                        self.types
                            .entry(text(name, src))
                            .or_default()
                            .push(ty(item));
                    }
                }
                "const_item" => {
                    if let (Some(name), Some(value)) = (field(item, "name"), field(item, "value")) {
                        self.constants.insert((file, text(name, src)), value);
                    }
                }
                "function_item" => self.index_function(file, src, item, None),
                "impl_item" if field(item, "trait").is_none() => {
                    if let (Some(owner), Some(body)) = (field(item, "type"), field(item, "body")) {
                        let mut cfg = false;
                        for method in statements(body) {
                            if method.kind() == "attribute_item" {
                                cfg |= text(method, src).contains("cfg");
                            } else if !std::mem::take(&mut cfg) && method.kind() == "function_item"
                            {
                                self.index_function(file, src, method, Some(ty(owner)));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn index_import(&mut self, file: Id, src: &'a str, node: Node<'a>, prefix: &str) {
        match node.kind() {
            "scoped_use_list" => {
                if let (Some(path), Some(list)) = (field(node, "path"), field(node, "list")) {
                    self.index_import(file, src, list, &format!("{prefix}{}::", text(path, src)));
                }
            }
            "use_list" => {
                for child in statements(node) {
                    self.index_import(file, src, child, prefix);
                }
            }
            "scoped_identifier" | "identifier" => {
                let path = text(node, src);
                self.imports
                    .insert((file, short(path)), format!("{prefix}{path}"));
            }
            _ => {}
        }
    }

    fn is_import(&self, file: Id, name: &str, module: &str) -> bool {
        let path = self.imports.get(&(file, name)).map_or(name, String::as_str);
        path.rsplit_once("::")
            .is_some_and(|(prefix, _)| prefix == module)
    }

    fn request_input(&self, routine: &Routine<'_>, param: &Param<'a>) -> bool {
        if !param.input {
            return false;
        }
        let Some(ty) = param.ty else { return false };
        if text(ty.node, ty.src) == "String" {
            return self.standard_string(ty.file, "String");
        }
        let Some(extractor) = field(ty.node, "type") else {
            return false;
        };
        let name = text(extractor, routine.src);
        self.is_import(ty.file, name, "axum::extract") || self.is_import(ty.file, name, "axum")
    }

    fn standard_string(&self, file: Id, name: &str) -> bool {
        match name {
            "String" => {
                self.definition(file, name).is_none()
                    && self
                        .imports
                        .get(&(file, name))
                        .is_none_or(|path| path == "std::string::String")
            }
            "str" | "std::string::String" => true,
            _ => false,
        }
    }

    fn index_function(&mut self, file: Id, src: &'a str, node: Node<'a>, owner: Option<Type<'a>>) {
        let (Some(name), Some(body), Some(params)) = (
            field(node, "name"),
            field(node, "body"),
            field(node, "parameters"),
        ) else {
            return;
        };
        if node.has_error() {
            return;
        }
        let params = statements(params)
            .into_iter()
            .filter(|p| p.kind() == "parameter")
            .map(|p| {
                let pattern = field(p, "pattern");
                let ty = field(p, "type").map(|node| Type { node, src, file });
                let mut name = pattern
                    .filter(|v| v.kind() == "identifier")
                    .map_or("", |v| text(v, src));
                let mut input = ty.is_some_and(|t| text(t.node, src) == "String");
                if let Some(pat) = pattern.filter(|p| p.kind() == "tuple_struct_pattern")
                    && let Some(extractor) = field(pat, "type")
                    && let [_, binding] = statements(pat).as_slice()
                    && binding.kind() == "identifier"
                    && let Some(ty) = ty
                    && generic(ty.node, text(extractor, src), src).is_some()
                {
                    name = text(*binding, src);
                    input = matches!(short(text(extractor, src)), "Form" | "Json");
                }
                let simple = !name.is_empty() && !has_mut(p) && ty.is_none_or(|t| !has_mut(t.node));
                Param {
                    node: p,
                    name,
                    ty,
                    input: input && simple,
                    simple,
                }
            })
            .collect();
        self.functions.push(Routine {
            file,
            src,
            name: text(name, src),
            owner,
            body,
            params,
        });
    }

    fn loc(&self, file: Id, node: Node<'_>) -> String {
        format!(
            "{}:{}",
            self.analysis.f.files[file as usize].path,
            line(node)
        )
    }

    fn module(&self, file: Id, path: &str) -> bool {
        let module = &self.analysis.f.files[file as usize].module;
        module.split_once("src::").is_some_and(|(_, m)| m == path)
    }

    fn function(&self, file: Id, name: &str, owner: Option<Type<'a>>) -> Option<&Routine<'a>> {
        let owner = owner.and_then(|ty| self.nominal(ty, 0));
        let mut matches = self.functions.iter().filter(|r| {
            if r.name != short(name) {
                return false;
            }
            match (owner, r.owner) {
                (Some(a), Some(b)) => self.nominal(b, 0).is_some_and(|b| a == b),
                (None, None) => match name.rsplit_once("::") {
                    Some((path, _)) => path
                        .strip_prefix("crate::")
                        .is_some_and(|p| self.module(r.file, p)),
                    None => r.file == file,
                },
                _ => false,
            }
        });
        let first = matches.next()?;
        matches.next().is_none().then_some(first)
    }

    fn nominal(&self, ty: Type<'a>, depth: u8) -> Option<(&'a str, Id)> {
        if depth == 8 {
            return None;
        }
        let descend = |node| self.nominal(Type { node, ..ty }, depth + 1);
        if ty.node.kind() == "reference_type" {
            return descend(field(ty.node, "type")?);
        }
        for wrapper in ["State", "Form", "Json", "Arc", "Option"] {
            if let Some(node) = generic(ty.node, wrapper, ty.src) {
                return descend(node);
            }
        }
        let name = text(ty.node, ty.src);
        if let Some(def) = self.definition(ty.file, name) {
            return match def.node.kind() {
                "type_item" => self.nominal(
                    Type {
                        node: field(def.node, "type")?,
                        ..def
                    },
                    depth + 1,
                ),
                _ => Some((short(name), def.file)),
            };
        }
        Some((name, ty.file))
    }

    fn definition(&self, file: Id, name: &str) -> Option<Type<'a>> {
        let defs = self.types.get(short(name))?;
        if let Some((path, _)) = name.rsplit_once("::") {
            let path = path.strip_prefix("crate::")?;
            return defs.iter().find(|ty| self.module(ty.file, path)).copied();
        }
        let imported = self.imports.get(&(file, name));
        let mut matches = defs.iter().filter(|ty| match imported {
            Some(path) => path
                .strip_prefix("crate::")
                .and_then(|p| p.rsplit_once("::"))
                .is_some_and(|(m, _)| self.module(ty.file, m)),
            None => ty.file == file,
        });
        let first = matches.next().copied()?;
        matches.next().is_none().then_some(first)
    }

    fn expr_type(&self, frame: &Frame<'_, 'a>, expr: Node<'a>, depth: u8) -> Option<Type<'a>> {
        if depth == 12 {
            return None;
        }
        let r = frame.routine;
        let infer = |v| self.expr_type(frame, v, depth + 1);
        match expr.kind() {
            "self" => r.owner,
            "identifier" => {
                let name = text(expr, r.src);
                if let Some(alias) = frame.binding(name, expr) {
                    infer(alias?)
                } else {
                    r.params.iter().find(|p| p.name == name)?.ty
                }
            }
            "reference_expression" => infer(field(expr, "value")?),
            "try_expression" => infer(expr.named_child(0)?),
            "field_expression" => {
                let (name, file) = self.nominal(infer(field(expr, "value")?)?, 0)?;
                let def = self.definition(file, name)?;
                let name = text(field(expr, "field")?, r.src);
                let member = statements(field(def.node, "body")?)
                    .into_iter()
                    .find(|n| field(*n, "name").is_some_and(|v| text(v, def.src) == name))?;
                Some(Type {
                    node: field(member, "type")?,
                    ..def
                })
            }
            "call_expression" => {
                let (recv, name, args) = call_parts(expr, r.src)?;
                match (recv, name, args.as_slice()) {
                    (None, "Arc::clone", [arg]) if self.is_import(r.file, "Arc", "std::sync") => {
                        infer(*arg)
                    }
                    (None, "std::sync::Arc::clone", [arg]) => infer(*arg),
                    (Some(recv), "as_ref" | "ok_or_else" | "to_owned" | "clone", _) => infer(recv),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn follow<'p>(&'p self, frame: &Frame<'_, 'a>, call: Node<'a>) -> Option<Frame<'p, 'a>> {
        let (recv, name, args) = call_parts(call, frame.routine.src)?;
        let owner = match recv {
            Some(recv) => Some(self.expr_type(frame, recv, 0)?),
            None if frame.binding(name, call).is_none()
                && !frame.routine.params.iter().any(|p| p.name == name) =>
            {
                None
            }
            None => return None,
        };
        let callee = self.function(frame.routine.file, name, owner)?;
        if args.len() != callee.params.len() {
            return None;
        }
        let mut next = Frame::new(callee);
        for (arg, param) in args.into_iter().zip(&callee.params) {
            if param.simple
                && let Some(origin) = self.origin(frame, arg, 0)
            {
                next.inputs.insert(param.name, origin);
            }
        }
        Some(next)
    }

    fn origin(&self, frame: &Frame<'_, 'a>, node: Node<'a>, depth: u8) -> Option<Origin> {
        if depth == 12 {
            return None;
        }
        let r = frame.routine;
        let trace = |v| self.origin(frame, v, depth + 1);
        match node.kind() {
            "identifier" => {
                let name = text(node, r.src);
                match frame.binding(name, node) {
                    Some(v) => trace(v?),
                    None => frame.inputs.get(name).cloned(),
                }
            }
            "reference_expression" if !has_mut(node) => trace(field(node, "value")?),
            "field_expression" => {
                let mut origin = trace(field(node, "value")?)?;
                origin.name.push('.');
                origin.name.push_str(text(field(node, "field")?, r.src));
                Some(origin)
            }
            "call_expression" => {
                let (recv, name, args) = call_parts(node, r.src)?;
                let recv = recv?;
                if args.is_empty()
                    && matches!(name, "to_owned" | "clone" | "as_str")
                    && self.string_type(frame, recv)
                {
                    let mut origin = trace(recv)?;
                    if matches!(name, "to_owned" | "clone") {
                        origin.copy = Some(self.loc(r.file, node));
                    }
                    return Some(origin);
                }
                // A String collected from a filter over str::chars is no longer than the input.
                if name == "collect"
                    && args.is_empty()
                    && let (Some(chars), "filter", filter_args) = call_parts(recv, r.src)?
                    && filter_args.len() == 1
                    && let (Some(input), "chars", args) = call_parts(chars, r.src)?
                    && args.is_empty()
                    && self.string_type(frame, input)
                    && let Some(ty) = node
                        .parent()
                        .filter(|p| {
                            p.kind() == "let_declaration" && field(*p, "value") == Some(node)
                        })
                        .and_then(|p| field(p, "type"))
                    && self.standard_string(r.file, text(ty, r.src))
                {
                    let mut origin = trace(input)?;
                    origin.filtered = true;
                    return Some(origin);
                }
                None
            }
            _ => None,
        }
    }

    fn string_type(&self, frame: &Frame<'_, 'a>, node: Node<'a>) -> bool {
        self.expr_type(frame, node, 0)
            .and_then(|ty| self.nominal(ty, 0))
            .is_some_and(|(name, file)| self.standard_string(file, name))
    }

    fn semaphore(&self, frame: &Frame<'_, 'a>, call: Node<'a>) -> bool {
        let Some((Some(recv), name, _)) = call_parts(call, frame.routine.src) else {
            return false;
        };
        if !ACQUIRE.contains(&name) {
            return false;
        }
        self.expr_type(frame, recv, 0)
            .and_then(|ty| self.nominal(ty, 0))
            .is_some_and(|(name, file)| {
                short(name) == "Semaphore" && self.is_import(file, name, "tokio::sync")
            })
    }

    fn limit(&self, node: Node<'a>, frame: &Frame<'_, 'a>, depth: u8) -> Option<u64> {
        if depth == 8 {
            return None;
        }
        let r = frame.routine;
        let value = |node| self.limit(node, frame, depth + 1);
        match node.kind() {
            "integer_literal" => text(node, r.src).replace('_', "").parse().ok(),
            "identifier" => {
                let name = text(node, r.src);
                if frame.binding(name, node).is_some() || r.params.iter().any(|p| p.name == name) {
                    return None;
                }
                value(*self.constants.get(&(r.file, name))?)
            }
            "binary_expression"
                if field(node, "operator").is_some_and(|o| text(o, r.src) == "*") =>
            {
                value(field(node, "left")?)?.checked_mul(value(field(node, "right")?)?)
            }
            "call_expression" => {
                let (Some(recv), "div_ceil", args) = call_parts(node, r.src)? else {
                    return None;
                };
                let [rhs] = args.as_slice() else { return None };
                let n = value(*rhs)?;
                (n != 0).then_some(value(recv)?).map(|v| v.div_ceil(n))
            }
            _ => None,
        }
    }

    fn guards(&self, frame: &Frame<'_, 'a>) -> Vec<Guard<'a>> {
        let mut out = Vec::new();
        let r = frame.routine;
        for site in expressions(frame.body)
            .into_iter()
            .filter(|n| n.kind() == "if_expression")
        {
            let (Some(condition), Some(body)) =
                (field(site, "condition"), field(site, "consequence"))
            else {
                continue;
            };
            let leaves = statements(body)
                .last()
                .is_some_and(|&stmt| expression(stmt).kind() == "return_expression");
            for cmp in expressions(condition)
                .into_iter()
                .filter(|n| n.kind() == "binary_expression")
            {
                let (Some(lhs), Some(rhs), Some(op)) = (
                    field(cmp, "left"),
                    field(cmp, "right"),
                    field(cmp, "operator"),
                ) else {
                    continue;
                };
                let op = text(op, r.src);
                let (length, limit) = match op {
                    ">" | ">=" => (lhs, rhs),
                    "<" | "<=" => (rhs, lhs),
                    _ => continue,
                };
                let Some((Some(input), "len", args)) = call_parts(length, r.src) else {
                    continue;
                };
                if !args.is_empty() {
                    continue;
                }
                let Some(origin) = self.origin(frame, input, 0) else {
                    continue;
                };
                if !origin.filtered && !self.string_type(frame, input) {
                    continue;
                }
                let limit = self.limit(limit, frame, 0).and_then(|n| {
                    if matches!(op, ">=" | "<=") {
                        n.checked_sub(1)
                    } else {
                        Some(n)
                    }
                });
                let exact = cmp == condition && leaves && direct(frame.body, site);
                out.push(Guard {
                    site,
                    origin,
                    limit,
                    exact,
                });
            }
        }
        out
    }

    fn inspect(
        &self,
        frame: &Frame<'_, 'a>,
        path: &[(&Frame<'_, 'a>, Node<'a>)],
        findings: &mut Vec<Finding>,
    ) {
        let guards = self.guards(frame);
        for (call, _) in awaited(frame.body) {
            if self.semaphore(frame, call) {
                for late in guards
                    .iter()
                    .filter(|g| g.site.start_byte() > call.end_byte())
                {
                    let mut earlier = path.to_vec();
                    earlier.push((frame, call));
                    self.report(
                        frame,
                        call,
                        &late.origin,
                        Some((frame, late)),
                        &earlier,
                        direct(frame.body, call),
                        vec![],
                        findings,
                    );
                }
                // A checked caller can forward the same value to a worker whose permit wait
                // precedes work on it, even when that worker has no second size check.
                if !guards.iter().any(|g| g.site.start_byte() > call.end_byte()) {
                    let mut earlier = path.to_vec();
                    earlier.push((frame, call));
                    let mut seen = HashSet::new();
                    for (owner, stop) in &earlier {
                        for guard in self.guards(owner) {
                            if guard.site.end_byte() < stop.start_byte()
                                && self.relevant(frame, &guard.origin)
                                && seen.insert(guard.origin.name.clone())
                            {
                                self.report(
                                    frame,
                                    call,
                                    &guard.origin,
                                    None,
                                    &earlier,
                                    true,
                                    vec![],
                                    findings,
                                );
                            }
                        }
                    }
                }
                continue;
            }

            let Some(queue) = self.follow(frame, call) else {
                continue;
            };
            let Some((_, _, args)) = call_parts(call, frame.routine.src) else {
                continue;
            };
            let ([closure], [param]) = (args.as_slice(), queue.routine.params.as_slice()) else {
                continue;
            };
            if !param
                .ty
                .is_some_and(|t| text(t.node, t.src).contains("FnOnce()"))
            {
                continue;
            }
            let Some(body) = closure_body(*closure) else {
                continue;
            };
            let Some((permit, callback)) = self.queue_order(&queue, param.name) else {
                continue;
            };
            let cb = frame.closure(body);
            let steps = vec![
                format!(
                    "{} sends the check to the queue",
                    self.loc(frame.routine.file, call)
                ),
                format!(
                    "{} runs the callback after the wait",
                    self.loc(queue.routine.file, callback)
                ),
            ];
            let mut earlier = path.to_vec();
            earlier.push((frame, call));
            for g in self.guards(&cb) {
                self.report(
                    &queue,
                    permit,
                    &g.origin,
                    Some((&cb, &g)),
                    &earlier,
                    direct(frame.body, call),
                    steps.clone(),
                    findings,
                );
            }
            for check in expressions(body)
                .into_iter()
                .filter(|n| n.kind() == "call_expression")
            {
                let Some(checked) = self.follow(&cb, check) else {
                    continue;
                };
                for g in self.guards(&checked) {
                    let mut steps = steps.clone();
                    steps.push(format!(
                        "{} calls the size checker",
                        self.loc(cb.routine.file, check)
                    ));
                    self.report(
                        &queue,
                        permit,
                        &g.origin,
                        Some((&checked, &g)),
                        &earlier,
                        direct(frame.body, call) && direct(body, check),
                        steps,
                        findings,
                    );
                }
            }
        }
    }

    fn queue_order(&self, queue: &Frame<'_, 'a>, callback: &str) -> Option<(Node<'a>, Node<'a>)> {
        if callback.is_empty() {
            return None;
        }
        let src = queue.routine.src;
        let invoke = |node| {
            call_parts(node, src).is_some_and(|(recv, name, args)| {
                recv.is_none()
                    && name == callback
                    && args.is_empty()
                    && queue.binding(callback, node).is_none()
            })
        };
        for (permit, wait) in awaited(queue.body) {
            if !direct(queue.body, permit) || !self.semaphore(queue, permit) {
                continue;
            }
            if let Some(run) = expressions(queue.body).into_iter().find(|&node| {
                node.start_byte() > wait.end_byte() && direct(queue.body, node) && invoke(node)
            }) {
                return Some((permit, run));
            }
            for (spawn, _) in awaited(queue.body) {
                if spawn.start_byte() <= wait.end_byte() || !direct(queue.body, spawn) {
                    continue;
                }
                if let Some((None, "tokio::task::spawn_blocking", args)) = call_parts(spawn, src)
                    && let [closure] = args.as_slice()
                    && let Some(body) = closure_body(*closure)
                    && let Some(run) = expressions(body)
                        .into_iter()
                        .find(|&n| direct(body, n) && invoke(n))
                {
                    return Some((permit, run));
                }
            }
        }
        None
    }

    fn relevant(&self, frame: &Frame<'_, 'a>, origin: &Origin) -> bool {
        frame.inputs.values().any(|v| v.name == origin.name)
            || self
                .guards(frame)
                .iter()
                .any(|g| g.origin.name == origin.name)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the path and its evidence are assembled at each wait"
    )]
    fn report(
        &self,
        queue: &Frame<'_, 'a>,
        permit: Node<'a>,
        origin: &Origin,
        late: Option<(&Frame<'_, 'a>, &Guard<'a>)>,
        earlier: &[(&Frame<'_, 'a>, Node<'a>)],
        ordered: bool,
        steps: Vec<String>,
        findings: &mut Vec<Finding>,
    ) {
        let mut proved = None;
        let mut unresolved = None;
        for &(frame, stop) in earlier {
            for g in self.guards(frame) {
                if g.site.end_byte() > stop.start_byte() || g.origin.name != origin.name {
                    continue;
                }
                let loc = self.loc(frame.routine.file, g.site);
                if g.exact
                    && !g.origin.filtered
                    && let Some(max) = g.limit
                    && (late.is_none() || late.and_then(|(_, g)| g.limit).is_some_and(|n| max <= n))
                {
                    proved = Some((loc, max));
                } else {
                    unresolved = Some(format!("{loc} may limit the request before the wait"));
                }
            }
            if unresolved.is_none() {
                unresolved = self.opaque_before(frame, stop, origin);
            }
        }
        let wait = self.loc(queue.routine.file, call_head(permit));
        let mut witness = vec![format!("{} binds request input", origin.entry)];
        let site = origin
            .copy
            .clone()
            .filter(|_| !steps.is_empty())
            .unwrap_or_else(|| wait.clone());
        if site != wait {
            witness.push(format!("{site} copies request input for the queued check"));
        }
        let mut steps = steps.into_iter();
        witness.extend(steps.next());
        witness.push(format!("{wait} waits for a semaphore permit"));
        witness.extend(steps);
        if let Some((frame, guard)) = late {
            witness.push(format!(
                "{} checks the input length after the wait",
                self.loc(frame.routine.file, guard.site)
            ));
        }
        let (verdict, message, assumptions) = if let Some((loc, max)) = proved {
            witness.insert(
                1,
                format!("{loc} rejects input over {max} bytes before the wait"),
            );
            (
                Verdict::Proven,
                "the request length is bounded before the semaphore wait",
                vec![format!(
                    "the returning guard at {loc} caps the same input at {max} bytes before it reaches {wait}"
                )],
            )
        } else if let Some((_, guard)) = late {
            if let Some(why) = unresolved {
                witness.insert(1, why);
                (
                    Verdict::Unknown,
                    "an earlier call or conditional check may bound this input",
                    vec![],
                )
            } else if ordered && guard.exact && guard.limit.is_some() {
                (
                    Verdict::Violated,
                    "the request can wait for a semaphore permit before its size check rejects it",
                    vec![],
                )
            } else {
                (
                    Verdict::Unknown,
                    "the request size or the order of the wait and check is unresolved",
                    vec![],
                )
            }
        } else {
            return;
        };
        findings.push(Finding {
            question: 4,
            rule: "guard-after-wait",
            verdict,
            repo: self.analysis.repo_of_file[queue.routine.file as usize].clone(),
            site,
            message: message.into(),
            witness,
            assumptions,
        });
    }

    fn opaque_before(
        &self,
        frame: &Frame<'_, 'a>,
        stop: Node<'a>,
        origin: &Origin,
    ) -> Option<String> {
        let r = frame.routine;
        let related = |value| {
            self.origin(frame, value, 0).is_some_and(|v| {
                v.name == origin.name
                    || origin
                        .name
                        .strip_prefix(&v.name)
                        .is_some_and(|s| s.starts_with('.'))
            })
        };
        expressions(frame.body)
            .into_iter()
            .filter(|n| n.end_byte() <= stop.start_byte())
            .find_map(|node| {
                let (recv, name, args) = call_parts(node, r.src)?;
                if matches!(name, "clone" | "to_owned" | "as_str")
                    && args.is_empty()
                    && recv.is_some_and(|v| self.string_type(frame, v))
                {
                    return None;
                }
                (recv.is_some_and(related) || args.into_iter().any(related)).then(|| {
                    format!(
                        "{} may bound the request through `{name}`",
                        self.loc(r.file, node)
                    )
                })
            })
    }
}

#[derive(Clone)]
struct Origin {
    name: String,
    entry: String,
    copy: Option<String>,
    filtered: bool,
}

struct Guard<'a> {
    site: Node<'a>,
    origin: Origin,
    limit: Option<u64>,
    exact: bool,
}

struct Frame<'p, 'a> {
    routine: &'p Routine<'a>,
    body: Node<'a>,
    bindings: Vec<(&'a str, Node<'a>, Option<Node<'a>>)>,
    inputs: HashMap<&'a str, Origin>,
}

impl<'p, 'a> Frame<'p, 'a> {
    fn new(routine: &'p Routine<'a>) -> Self {
        let mut frame = Self {
            routine,
            body: routine.body,
            bindings: Vec::new(),
            inputs: HashMap::new(),
        };
        frame.add_bindings(routine.body);
        frame
    }

    fn closure(&self, body: Node<'a>) -> Self {
        let mut frame = Self {
            routine: self.routine,
            body,
            bindings: self.bindings.clone(),
            inputs: self.inputs.clone(),
        };
        frame.add_bindings(body);
        frame
    }

    fn add_bindings(&mut self, body: Node<'a>) {
        if body.kind() != "block" {
            return;
        }
        for stmt in statements(body) {
            let Some(pattern) = field(stmt, "pattern").filter(|_| stmt.kind() == "let_declaration")
            else {
                continue;
            };
            let value = field(stmt, "value").filter(|_| !has_mut(stmt));
            let mut save = |p: Node<'a>, value| {
                self.bindings.push((text(p, self.routine.src), stmt, value));
            };
            if pattern.kind() == "identifier" {
                save(pattern, value);
            } else if pattern.kind() == "tuple_pattern"
                && let Some(value) = value.filter(|v| v.kind() == "tuple_expression")
                && let patterns = statements(pattern)
                && patterns.iter().all(|p| p.kind() == "identifier")
                && let values = statements(value)
                && patterns.len() == values.len()
            {
                for (p, v) in patterns.into_iter().zip(values) {
                    save(p, Some(v));
                }
            } else {
                for name in expressions(pattern)
                    .into_iter()
                    .filter(|n| n.kind() == "identifier")
                {
                    save(name, None);
                }
            }
        }
    }

    fn binding(&self, name: &str, read: Node<'a>) -> Option<Option<Node<'a>>> {
        let names = |pat| {
            expressions(pat)
                .iter()
                .any(|&n| n.kind() == "identifier" && text(n, self.routine.src) == name)
        };
        let mut parent = read.parent();
        while let Some(node) = parent {
            if node.kind() == "block"
                && statements(node).iter().any(|&stmt| {
                    let nested_let = node != self.body
                        && node != self.routine.body
                        && stmt.kind() == "let_declaration"
                        && stmt.end_byte() <= read.start_byte()
                        && field(stmt, "pattern").is_some_and(names);
                    let local_item = matches!(
                        stmt.kind(),
                        "const_item" | "static_item" | "function_item" | "use_declaration"
                    ) && (field(stmt, "name").is_some_and(names)
                        || field(stmt, "argument").is_some_and(names));
                    nested_let || local_item
                })
            {
                return Some(None);
            }
            let branch_pattern = match node.kind() {
                "match_arm" | "for_expression" => field(node, "pattern"),
                "if_expression" | "while_expression" => field(node, "condition")
                    .filter(|c| c.kind() == "let_condition")
                    .and_then(|c| field(c, "pattern")),
                _ => None,
            };
            if branch_pattern.is_some_and(names) {
                return Some(None);
            }
            if node == self.routine.body {
                break;
            }
            parent = node.parent();
        }
        self.bindings.iter().rev().find_map(|&(key, stmt, value)| {
            (key == name && stmt.end_byte() <= read.start_byte()).then_some(value)
        })
    }
}

fn field<'a>(node: Node<'a>, name: &str) -> Option<Node<'a>> {
    node.child_by_field_name(name)
}

fn has_mut(node: Node<'_>) -> bool {
    statements(node)
        .iter()
        .any(|v| v.kind() == "mutable_specifier")
}

fn call_head(call: Node<'_>) -> Node<'_> {
    field(call, "function")
        .and_then(|node| field(node, "field"))
        .unwrap_or(call)
}

fn short(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

fn generic<'a>(node: Node<'a>, name: &str, src: &str) -> Option<Node<'a>> {
    if node.kind() == "generic_type" && short(text(field(node, "type")?, src)) == short(name) {
        field(node, "type_arguments")?.named_child(0)
    } else {
        None
    }
}

fn call_parts<'a>(
    node: Node<'a>,
    src: &'a str,
) -> Option<(Option<Node<'a>>, &'a str, Vec<Node<'a>>)> {
    if node.kind() != "call_expression" {
        return None;
    }
    let mut callee = field(node, "function")?;
    if callee.kind() == "generic_function" {
        callee = field(callee, "function")?;
    }
    let args = statements(field(node, "arguments")?);
    if callee.kind() == "field_expression" {
        Some((
            Some(field(callee, "value")?),
            text(field(callee, "field")?, src),
            args,
        ))
    } else {
        Some((None, text(callee, src), args))
    }
}

fn statements(node: Node<'_>) -> Vec<Node<'_>> {
    named_children(node)
        .into_iter()
        .filter(|n| !matches!(n.kind(), "line_comment" | "block_comment"))
        .collect()
}

fn expressions(node: Node<'_>) -> Vec<Node<'_>> {
    let mut pending = vec![node];
    let mut out = Vec::new();
    while let Some(n) = pending.pop() {
        if matches!(
            n.kind(),
            "closure_expression" | "async_block" | "function_item"
        ) {
            continue;
        }
        out.push(n);
        pending.extend(statements(n).into_iter().rev());
    }
    out
}

fn expression(node: Node<'_>) -> Node<'_> {
    if node.kind() == "expression_statement" {
        node.named_child(0).unwrap_or(node)
    } else {
        node
    }
}

fn direct(body: Node<'_>, node: Node<'_>) -> bool {
    let mut parent = node.parent();
    while let Some(n) = parent {
        if n == body {
            return true;
        }
        if matches!(
            n.kind(),
            "if_expression"
                | "match_expression"
                | "block"
                | "loop_expression"
                | "while_expression"
                | "for_expression"
                | "closure_expression"
                | "binary_expression"
                | "async_block"
        ) {
            return false;
        }
        parent = n.parent();
    }
    node == body
}

fn awaited(body: Node<'_>) -> Vec<(Node<'_>, Node<'_>)> {
    expressions(body)
        .into_iter()
        .filter_map(|n| {
            if n.kind() == "await_expression" {
                let call = n.named_child(0)?;
                (call.kind() == "call_expression").then_some((call, n))
            } else {
                None
            }
        })
        .collect()
}

fn closure_body(node: Node<'_>) -> Option<Node<'_>> {
    (node.kind() == "closure_expression" && field(node, "parameters")?.named_child_count() == 0)
        .then(|| field(node, "body"))
        .flatten()
}
