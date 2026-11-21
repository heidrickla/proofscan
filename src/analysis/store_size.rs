//! Question 6 over the size of Rust values written from request handlers.

use super::Analysis;
use crate::facts::{Call, Facts, Id, Lang, ScopeKind};
use crate::lang::{line, named_children, squash, text};
use crate::report::Verdict;
use crate::resolve::Graph;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use tree_sitter::{Node, Parser, Tree};

const RULE: &str = "untrusted-store-size";

#[derive(Clone, Default)]
struct Flow {
    raw: BTreeSet<String>,
    capped: BTreeSet<String>,
    opaque: BTreeSet<String>,
}

impl Flow {
    fn merge(&mut self, other: Self) {
        self.raw.extend(other.raw);
        self.capped.extend(other.capped);
        self.opaque.extend(other.opaque);
    }

    fn present(&self) -> bool {
        !(self.raw.is_empty() && self.capped.is_empty() && self.opaque.is_empty())
    }

    fn cap(self, reason: String) -> Self {
        let mut capped = self.capped;
        if !self.raw.is_empty() || !self.opaque.is_empty() {
            capped.insert(reason);
        }
        Self {
            capped,
            ..Self::default()
        }
    }

    fn obscure(mut self, at: String) -> Self {
        if !self.raw.is_empty() || !self.capped.is_empty() {
            self.opaque.insert(at);
            self.raw.clear();
            self.capped.clear();
        }
        self
    }
}

#[derive(Clone, Default)]
struct Value {
    flow: Flow,
    ty: String,
    auth_result: bool,
    // Tuple fields and Result/Option/enum payloads retain their own provenance.
    parts: BTreeMap<String, Value>,
    closure: Option<Box<Closure>>,
}

#[derive(Clone)]
struct Closure {
    func: Id,
    bytes: std::ops::Range<usize>,
    vars: BTreeMap<String, Value>,
}

impl Value {
    fn typed(ty: &str) -> Self {
        Self {
            ty: ty.into(),
            ..Self::default()
        }
    }

    fn flat(flow: Flow) -> Self {
        Self {
            flow,
            ..Self::default()
        }
    }

    fn variant(name: &str, value: Self) -> Self {
        Self {
            parts: BTreeMap::from([(name.into(), value)]),
            ..Self::default()
        }
    }

    fn total(&self) -> Flow {
        let mut flow = self.flow.clone();
        for part in self.parts.values() {
            flow.merge(part.total());
        }
        flow
    }

    fn merge(&mut self, other: Self) {
        self.flow.merge(other.flow);
        if self.ty.is_empty() {
            self.ty = other.ty;
        } else if !other.ty.is_empty() && self.ty != other.ty {
            self.ty.clear();
        }
        for (key, value) in other.parts {
            self.parts.entry(key).or_default().merge(value);
        }
    }

    fn payload(&self, key: &str) -> Self {
        let mut value = self.parts.get(key).cloned().unwrap_or_else(|| Self {
            ty: self.ty.clone(),
            ..Self::default()
        });
        value.flow.merge(self.flow.clone());
        value
    }
}

#[derive(Clone, Default)]
struct Frame {
    vars: BTreeMap<String, Value>,
    returned: Value,
    exits: bool,
    authenticated: bool,
}

impl Frame {
    fn join(&mut self, branches: Vec<Self>) {
        let mut continuing = branches.iter().filter(|branch| !branch.exits);
        if let Some(first) = continuing.next() {
            self.authenticated = first.authenticated;
            for (key, value) in &mut self.vars {
                if let Some(next) = first.vars.get(key) {
                    value.clone_from(next);
                }
            }
            for branch in continuing {
                self.authenticated &= branch.authenticated;
                for (key, value) in &mut self.vars {
                    if let Some(other) = branch.vars.get(key) {
                        value.merge(other.clone());
                    }
                }
            }
        } else {
            self.exits = true;
        }
        for branch in branches {
            self.returned.merge(branch.returned);
        }
    }
}

struct Source {
    src: String,
    tree: Tree,
}

struct Model<'b> {
    facts: &'b Facts,
    graph: &'b Graph,
    pattern: Regex,
    auth_pattern: Option<Regex>,
    sources: HashMap<Id, Source>,
    functions: HashMap<(Id, String), Option<Id>>,
    calls: HashMap<(Id, u32), Vec<&'b Call>>,
    methods: HashMap<(Id, String, String), Option<Id>>,
    types: HashMap<(Id, String, String), String>,
    displays: HashSet<(Id, String)>,
    extractors: HashSet<(Id, String)>,
}

struct Trace<'a, 'b> {
    model: &'a Model<'b>,
    active: Vec<Id>,
    writes: &'a mut BTreeMap<Id, Flow>,
    fuel: usize,
    depth: usize,
}

impl Analysis<'_> {
    pub(super) fn untrusted_store_size(&mut self) {
        let q6 = &self.cfg.q6;
        let Ok(pattern) = Regex::new(&q6.store_write) else {
            return;
        };
        if q6.store_write.is_empty() {
            return;
        }
        let reach = self.untrusted_reach();
        let repos: HashSet<Id> = self
            .f
            .calls
            .iter()
            .filter_map(|call| {
                let site = &self.f.sites[call.site as usize];
                let file = &self.f.files[site.file as usize];
                (file.lang == Lang::Rust
                    && !self.f.funcs[site.func as usize].test
                    && reach.contains(&site.func)
                    && pattern.is_match(&call.full))
                .then_some(file.repo)
            })
            .collect();
        if repos.is_empty() {
            return;
        }
        let model = Model::new(self, pattern, &repos);
        let entries = self.untrusted_entries();
        let authenticated = Regex::new(&q6.authenticated_extractors)
            .ok()
            .filter(|_| !q6.authenticated_extractors.is_empty());
        // Rust expressions and calls nest on the trace stack. Keep it independent of the
        // platform's main-thread stack and bound the depth as well as the work per entry.
        let writes = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    model.trace_entries(entries, authenticated.as_ref())
                })
                .expect("store size trace thread")
                .join()
                .expect("store size trace")
        });
        for (site, flow) in writes {
            let mut witness: Vec<_> = flow.raw.into_iter().collect();
            let (verdict, message, assumptions) = if !witness.is_empty() {
                (
                    Verdict::Violated,
                    "request text sets the size of a durable write",
                    vec![],
                )
            } else if !flow.opaque.is_empty() {
                witness.extend(flow.opaque);
                (
                    Verdict::Unknown,
                    "the size of request text passes through an unresolved expression",
                    vec![],
                )
            } else if !flow.capped.is_empty() {
                witness.extend(flow.capped.iter().cloned());
                (
                    Verdict::Proven,
                    "request text at this durable write has a local size bound",
                    flow.capped.into_iter().collect(),
                )
            } else {
                continue;
            };
            self.push(6, RULE, verdict, site, message.into(), witness, assumptions);
        }
    }
}

impl<'b> Model<'b> {
    fn new(analysis: &Analysis<'b>, pattern: Regex, repos: &HashSet<Id>) -> Self {
        let f = analysis.f;
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .expect("Rust grammar");
        // Texts include files without facts. The parsed files keep the input order, including
        // duplicate relative paths in different repositories.
        let mut files = f.files.iter().enumerate().peekable();
        let mut sources = HashMap::new();
        for (path, src) in analysis.texts {
            let Some(&(id, file)) = files.peek() else {
                break;
            };
            if &file.path != path {
                continue;
            }
            files.next();
            if file.lang == Lang::Rust
                && !file.test
                && repos.contains(&file.repo)
                && let Some(tree) = parser.parse(src, None)
            {
                let (src, tree) = readable_macros(&mut parser, src, tree);
                sources.insert(id as Id, Source { src, tree });
            }
        }
        let mut model = Self {
            facts: analysis.f,
            graph: analysis.g,
            pattern,
            auth_pattern: Regex::new(&analysis.cfg.q6.authenticated_calls)
                .ok()
                .filter(|_| !analysis.cfg.q6.authenticated_calls.is_empty()),
            sources,
            functions: HashMap::new(),
            calls: HashMap::new(),
            methods: HashMap::new(),
            types: HashMap::new(),
            displays: HashSet::new(),
            extractors: HashSet::new(),
        };
        for (id, function) in f.funcs.iter().enumerate() {
            if function.kind != ScopeKind::Function
                || function.test
                || !model.sources.contains_key(&function.file)
            {
                continue;
            }
            if function.class.is_none() {
                model
                    .functions
                    .entry((function.file, function.name.clone()))
                    .and_modify(|target| *target = None)
                    .or_insert(Some(id as Id));
            }
            if let Some(class) = &function.class {
                let repo = f.files[function.file as usize].repo;
                if function.trait_name.as_deref().is_some_and(|name| {
                    matches!(
                        name.rsplit("::").next(),
                        Some("FromRequest" | "FromRequestParts")
                    )
                }) {
                    model.extractors.insert((repo, class.clone()));
                }
                model
                    .methods
                    .entry((repo, class.clone(), function.name.clone()))
                    .and_modify(|target| *target = None)
                    .or_insert(Some(id as Id));
            }
        }
        for call in &f.calls {
            let site = &f.sites[call.site as usize];
            if model.sources.contains_key(&site.file) {
                model
                    .calls
                    .entry((site.func, site.line))
                    .or_default()
                    .push(call);
            }
        }
        for (&file, source) in &model.sources {
            let repo = f.files[file as usize].repo;
            for node in named_children(source.tree.root_node()) {
                let Some(name) = node
                    .child_by_field_name("name")
                    .map(|n| text(n, &source.src))
                else {
                    continue;
                };
                match node.kind() {
                    "type_item" => {
                        if let Some(ty) = node.child_by_field_name("type") {
                            let ty = base_type(text(ty, &source.src));
                            model
                                .types
                                .insert((repo, String::new(), name.into()), ty.into());
                        }
                    }
                    "struct_item" => {
                        for field in node
                            .child_by_field_name("body")
                            .map(named_children)
                            .unwrap_or_default()
                        {
                            if let (Some(field), Some(ty)) = (
                                field.child_by_field_name("name"),
                                field.child_by_field_name("type"),
                            ) {
                                model.types.insert(
                                    (repo, name.into(), text(field, &source.src).into()),
                                    base_type(text(ty, &source.src)).into(),
                                );
                            }
                        }
                    }
                    "enum_item"
                        if node.prev_named_sibling().is_some_and(|attr| {
                            text(attr, &source.src).contains("thiserror::Error")
                        }) =>
                    {
                        for variant in node
                            .child_by_field_name("body")
                            .map(named_children)
                            .unwrap_or_default()
                        {
                            if variant
                                .prev_named_sibling()
                                .is_some_and(|attr| text(attr, &source.src).contains("{0}"))
                                && let Some(tag) = variant.child_by_field_name("name")
                            {
                                model
                                    .displays
                                    .insert((repo, format!("{name}::{}", text(tag, &source.src))));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        model
    }

    fn trace_entries(&self, entries: Vec<Id>, authenticated: Option<&Regex>) -> BTreeMap<Id, Flow> {
        let mut writes = BTreeMap::new();
        for entry in entries {
            let Some(node) = self.function(entry) else {
                continue;
            };
            if self.parameters(node).iter().any(|(_, ty)| {
                let ty = self.text(entry, *ty);
                let name = ty.rsplit("::").next().unwrap_or(ty);
                !ty.contains('<')
                    && authenticated.is_some_and(|p| p.is_match(name))
                    && self
                        .extractors
                        .contains(&(self.repo(entry), name.to_string()))
            }) {
                continue;
            }
            let source = self.at(entry, node);
            let values = self
                .parameters(node)
                .into_iter()
                .map(|(_, ty)| {
                    let ty = self.text(entry, ty);
                    let mut value = Value::typed(&self.ty(entry, ty));
                    if request_parameter(ty) {
                        value
                            .flow
                            .raw
                            .insert(format!("{source} receives request data"));
                    }
                    value
                })
                .collect();
            let mut trace = Trace {
                model: self,
                active: vec![],
                writes: &mut writes,
                fuel: 20_000,
                depth: 0,
            };
            trace.invoke(entry, values, false);
        }
        writes
    }

    fn file(&self, func: Id) -> Id {
        self.facts.funcs[func as usize].file
    }

    fn repo(&self, func: Id) -> Id {
        self.facts.files[self.file(func) as usize].repo
    }

    fn text(&self, func: Id, node: Node) -> &str {
        text(node, &self.sources[&self.file(func)].src)
    }

    fn at(&self, func: Id, node: Node) -> String {
        format!(
            "{}:{}",
            self.facts.files[self.file(func) as usize].path,
            line(node)
        )
    }

    fn function(&self, func: Id) -> Option<Node<'_>> {
        let file = self.file(func);
        let source = self.sources.get(&file)?;
        let target = &self.facts.funcs[func as usize];
        let mut todo = vec![source.tree.root_node()];
        while let Some(node) = todo.pop() {
            if line(node) > target.line || node.end_position().row + 1 < target.line as usize {
                continue;
            }
            if node.kind() == "function_item"
                && line(node) == target.line
                && node
                    .child_by_field_name("name")
                    .is_some_and(|n| self.text(func, n) == target.name)
            {
                return Some(node);
            }
            todo.extend(named_children(node));
        }
        None
    }

    fn parameters<'n>(&self, node: Node<'n>) -> Vec<(Node<'n>, Node<'n>)> {
        node.child_by_field_name("parameters")
            .map(named_children)
            .unwrap_or_default()
            .into_iter()
            .filter_map(|p| {
                Some((
                    p.child_by_field_name("pattern")?,
                    p.child_by_field_name("type")?,
                ))
            })
            .collect()
    }

    fn resolve(&self, func: Id, call: Option<&Call>, receiver: &Value, name: &str) -> Option<Id> {
        let targets = call.and_then(|c| self.graph.targets.get(&c.site));
        if let Some([(target, true)]) = targets.map(Vec::as_slice) {
            return Some(*target);
        }
        let typed = self
            .methods
            .get(&(self.repo(func), receiver.ty.clone(), name.into()));
        if let Some(Some(target)) = typed {
            return Some(*target);
        }
        None
    }

    fn ty(&self, func: Id, ty: &str) -> String {
        let ty = base_type(ty);
        self.types
            .get(&(self.repo(func), String::new(), ty.into()))
            .cloned()
            .unwrap_or_else(|| ty.into())
    }
}

fn base_type(ty: &str) -> &str {
    let ty = ty
        .trim()
        .trim_start_matches('&')
        .trim_start()
        .trim_start_matches("mut ");
    let ty = if ty.starts_with('\'') {
        ty.split_once(char::is_whitespace)
            .map_or(ty, |(_, ty)| ty.trim_start())
    } else {
        ty
    };
    let (prefix, arg) = ty.split_once('<').unwrap_or((ty, ""));
    match prefix.rsplit("::").next().unwrap_or(prefix) {
        "Arc" | "Box" | "State" | "Option" => base_type(arg.trim_end_matches('>')),
        base => base,
    }
}

fn request_parameter(ty: &str) -> bool {
    let prefix = ty
        .trim()
        .trim_start_matches('&')
        .split('<')
        .next()
        .unwrap_or(ty);
    matches!(
        prefix.rsplit("::").next().unwrap_or(prefix),
        "str"
            | "String"
            | "Bytes"
            | "Body"
            | "Request"
            | "Form"
            | "Json"
            | "Query"
            | "Path"
            | "HeaderMap"
    )
}

fn finite(text: &str) -> bool {
    text.trim().replace('_', "").parse::<usize>().is_ok()
}

// Parse positional format and SQL-bind arguments as Rust expressions, preserving source offsets.
fn readable_macros(parser: &mut Parser, source: &str, tree: Tree) -> (String, Tree) {
    let mut bytes = source.as_bytes().to_vec();
    let mut todo = vec![tree.root_node()];
    while let Some(node) = todo.pop() {
        if node.kind() == "macro_invocation"
            && let Some(name) = node.child_by_field_name("macro")
            && matches!(text(name, source), "format" | "params")
            && bytes.get(name.end_byte()) == Some(&b'!')
            && bytes.get(name.end_byte() + 1) == Some(&b'(')
        {
            bytes[name.end_byte()] = b'_';
        }
        todo.extend(named_children(node));
    }
    let source = String::from_utf8(bytes).expect("only ASCII punctuation replaced");
    let tree = parser.parse(&source, None).expect("Rust parse");
    (source, tree)
}

impl Trace<'_, '_> {
    fn invoke(&mut self, func: Id, args: Vec<Value>, authenticated: bool) -> Value {
        let model = self.model;
        let Some(node) = model
            .function(func)
            .filter(|_| !self.active.contains(&func))
        else {
            let mut flow = Flow::default();
            for arg in args {
                flow.merge(arg.total());
            }
            return Value::flat(flow.obscure(model.facts.func_label(func)));
        };
        let mut frame = Frame {
            authenticated,
            ..Frame::default()
        };
        let mut args = args.into_iter();
        if model.facts.funcs[func as usize]
            .params
            .first()
            .is_some_and(|p| p.name == "self")
        {
            frame
                .vars
                .insert("self".into(), args.next().unwrap_or_default());
        }
        for ((pattern, ty), mut value) in model.parameters(node).into_iter().zip(args) {
            let ty = model.ty(func, model.text(func, ty));
            if !ty.is_empty() && !ty.starts_with("impl ") && !matches!(ty.as_str(), "T" | "F") {
                value.ty = ty;
            }
            self.bind(func, pattern, &value, &mut frame);
        }
        self.active.push(func);
        let result = node
            .child_by_field_name("body")
            .map(|body| self.eval(func, body, &mut frame))
            .unwrap_or_default();
        self.active.pop();
        if !frame.exits {
            frame.returned.merge(result);
        }
        frame.returned.auth_result = model.auth_pattern.as_ref().is_some_and(|pattern| {
            pattern.is_match(&model.facts.funcs[func as usize].name)
                && model
                    .parameters(node)
                    .iter()
                    .any(|(_, ty)| base_type(model.text(func, *ty)) == "HeaderMap")
        });
        frame.returned
    }

    fn bind(&self, func: Id, pattern: Node, value: &Value, frame: &mut Frame) {
        let model = self.model;
        let token = model.text(func, pattern);
        match pattern.kind() {
            "identifier" if token != "_" => {
                frame.vars.insert(token.into(), value.clone());
            }
            "match_pattern" | "mut_pattern" | "reference_pattern" | "or_pattern" => {
                for child in named_children(pattern)
                    .into_iter()
                    .filter(|n| Some(*n) != pattern.child_by_field_name("condition"))
                {
                    self.bind(func, child, value, frame);
                }
            }
            "tuple_pattern" | "tuple_struct_pattern" => {
                let tag = pattern.child_by_field_name("type");
                let children = named_children(pattern)
                    .into_iter()
                    .filter(|n| Some(*n) != tag);
                let payload = tag.map(|t| value.payload(model.text(func, t)));
                for (i, child) in children.enumerate() {
                    let part = match &payload {
                        Some(v) if i == 0 => v.clone(),
                        Some(v) => v.payload(&i.to_string()),
                        None => value.payload(&i.to_string()),
                    };
                    self.bind(func, child, &part, frame);
                }
            }
            _ => {}
        }
    }

    fn eval(&mut self, func: Id, node: Node, frame: &mut Frame) -> Value {
        if frame.exits {
            return Value::default();
        }
        let model = self.model;
        if self.fuel == 0 || self.depth == 128 {
            let mut flow = Flow::default();
            for value in frame.vars.values() {
                flow.merge(value.total());
            }
            return Value::flat(
                flow.obscure(format!("{} reached the trace limit", model.at(func, node))),
            );
        }
        self.fuel -= 1;
        self.depth += 1;
        let value = self.eval_node(func, node, frame);
        self.depth -= 1;
        value
    }

    fn eval_node(&mut self, func: Id, node: Node, frame: &mut Frame) -> Value {
        let model = self.model;
        let txt = model.text(func, node);
        let children = || named_children(node).into_iter().filter(|n| !n.is_extra());
        match node.kind() {
            "identifier" | "self" => frame.vars.get(txt).cloned().unwrap_or_default(),
            "string_literal" | "raw_string_literal" => Value::typed("str"),
            "block" => {
                let mut tail = Value::default();
                let mut shadows = BTreeMap::new();
                for child in children() {
                    if child.kind() == "let_declaration"
                        && let Some(pattern) = child.child_by_field_name("pattern")
                    {
                        let mut names = Frame::default();
                        self.bind(func, pattern, &Value::default(), &mut names);
                        for name in names.vars.into_keys() {
                            shadows
                                .entry(name.clone())
                                .or_insert_with(|| frame.vars.get(&name).cloned());
                        }
                    }
                    tail = self.eval(func, child, frame);
                }
                for (name, old) in shadows {
                    if let Some(old) = old {
                        frame.vars.insert(name, old);
                    } else {
                        frame.vars.remove(&name);
                    }
                }
                tail
            }
            "let_declaration" => {
                if let (Some(pattern), Some(initial)) = (
                    node.child_by_field_name("pattern"),
                    node.child_by_field_name("value"),
                ) {
                    let mut value = self.eval(func, initial, frame);
                    if let Some(ty) = node.child_by_field_name("type") {
                        value.ty = model.ty(func, model.text(func, ty));
                    }
                    if let Some(otherwise) = node.child_by_field_name("alternative") {
                        let mut branch = frame.clone();
                        self.eval(func, otherwise, &mut branch);
                        frame.returned.merge(branch.returned);
                    }
                    self.bind(func, pattern, &value, frame);
                }
                Value::default()
            }
            "assignment_expression" => {
                if let (Some(left), Some(right)) = (
                    node.child_by_field_name("left"),
                    node.child_by_field_name("right"),
                ) {
                    let value = self.eval(func, right, frame);
                    self.bind(func, left, &value, frame);
                }
                Value::default()
            }
            "field_expression" => {
                let Some(fld) = node.child_by_field_name("field") else {
                    return Value::default();
                };
                let parent = self.field(func, node, "value", frame);
                let name = model.text(func, fld);
                let mut value = parent.payload(name);
                value.ty = model
                    .types
                    .get(&(model.repo(func), parent.ty.clone(), name.into()))
                    .cloned()
                    .unwrap_or_else(|| {
                        if parent.ty == "XmlPart" {
                            parent.ty
                        } else {
                            String::new()
                        }
                    });
                value
            }
            "tuple_expression" | "array_expression" => Value {
                parts: children()
                    .enumerate()
                    .map(|(index, child)| (index.to_string(), self.eval(func, child, frame)))
                    .collect(),
                ..Value::default()
            },
            "reference_expression"
            | "parenthesized_expression"
            | "await_expression"
            | "expression_statement"
            | "else_clause" => children()
                .next_back()
                .map(|child| self.eval(func, child, frame))
                .unwrap_or_default(),
            "unary_expression" if txt.starts_with('*') => {
                let value = children()
                    .next()
                    .map(|child| self.eval(func, child, frame))
                    .unwrap_or_default();
                if matches!(value.ty.as_str(), "str" | "String" | "XmlPart") {
                    value
                } else {
                    Value::flat(value.total().obscure(model.at(func, node)))
                }
            }
            "return_expression" => {
                let value = children()
                    .next()
                    .map(|child| self.eval(func, child, frame))
                    .unwrap_or_default();
                frame.returned.merge(value);
                frame.exits = true;
                Value::default()
            }
            "try_expression" => {
                let value = children()
                    .next()
                    .map(|child| self.eval(func, child, frame))
                    .unwrap_or_default();
                frame.authenticated |= value.auth_result;
                if let Some(error) = value.parts.get("Err") {
                    frame.returned.merge(Value::variant("Err", error.clone()));
                }
                if value.parts.contains_key("Ok") {
                    value.payload("Ok")
                } else if value.parts.contains_key("Some") {
                    value.payload("Some")
                } else {
                    value
                }
            }
            "if_expression" => self.branch(func, node, frame),
            "match_expression" => {
                let value = self.field(func, node, "value", frame);
                let mut result = Value::default();
                let mut branches = vec![];
                for arm in node
                    .child_by_field_name("body")
                    .map(named_children)
                    .unwrap_or_default()
                {
                    let mut branch = frame.clone();
                    if let Some(pattern) = arm.child_by_field_name("pattern") {
                        self.bind(func, pattern, &value, &mut branch);
                    }
                    result.merge(self.field(func, arm, "value", &mut branch));
                    branches.push(branch);
                }
                frame.join(branches);
                result
            }
            "for_expression" | "while_expression" | "loop_expression" => {
                let iter = self.field(func, node, "value", frame);
                let mut branch = frame.clone();
                if let Some(pattern) = node.child_by_field_name("pattern") {
                    self.bind(func, pattern, &Value::flat(iter.total()), &mut branch);
                }
                self.field(func, node, "body", &mut branch);
                // One iteration can expose flow to a write, but a loop cannot establish a cap.
                for (name, value) in &mut branch.vars {
                    if let Some(previous) = frame.vars.get(name)
                        && (!value.flow.capped.is_empty() || previous.flow.present())
                    {
                        value.flow.opaque.extend(value.flow.capped.iter().cloned());
                        value.flow.capped.clear();
                    }
                }
                frame.join(vec![frame.clone(), branch]);
                Value::default()
            }
            "closure_expression" => Value {
                closure: Some(Box::new(Closure {
                    func,
                    bytes: node.byte_range(),
                    vars: frame.vars.clone(),
                })),
                ..Value::default()
            },
            "call_expression" => self.call(func, node, frame),
            "binary_expression" => {
                let left = self.field(func, node, "left", frame);
                let op = node
                    .child_by_field_name("operator")
                    .map(|op| model.text(func, op));
                if matches!(op, Some("&&" | "||")) {
                    let mut right = frame.clone();
                    self.field(func, node, "right", &mut right);
                    frame.join(vec![frame.clone(), right]);
                    return Value::default();
                }
                let right = self.field(func, node, "right", frame);
                if matches!(op, Some("==" | "!=" | "<" | "<=" | ">" | ">=")) {
                    return Value::default();
                }
                let mut flow = left.total();
                flow.merge(right.total());
                Value::flat(flow.obscure(model.at(func, node)))
            }
            _ => {
                let mut flow = Flow::default();
                for child in children() {
                    flow.merge(self.eval(func, child, frame).total());
                }
                Value::flat(flow.obscure(model.at(func, node)))
            }
        }
    }

    fn field(&mut self, func: Id, node: Node, field: &str, frame: &mut Frame) -> Value {
        node.child_by_field_name(field)
            .map(|child| self.eval(func, child, frame))
            .unwrap_or_default()
    }

    fn branch(&mut self, func: Id, node: Node, frame: &mut Frame) -> Value {
        let model = self.model;
        let mut yes = frame.clone();
        let mut no = frame.clone();
        if let Some(cond) = node.child_by_field_name("condition") {
            if cond.kind() == "let_condition" {
                let value = self.field(func, cond, "value", &mut yes);
                if let Some(pattern) = cond.child_by_field_name("pattern") {
                    self.bind(func, pattern, &value, &mut yes);
                }
            } else {
                self.eval(func, cond, &mut yes);
                if let Some((name, cap_yes)) = length_guard(model, func, cond) {
                    let bounded = if cap_yes { &mut yes } else { &mut no };
                    if let Some(value) = bounded.vars.get_mut(name)
                        && matches!(value.ty.as_str(), "str" | "String" | "Bytes")
                    {
                        value.flow = value.total().cap(format!(
                            "{} bounds `{name}` by a literal length",
                            model.at(func, cond)
                        ));
                        value.parts.clear();
                    }
                }
            }
        }
        let mut result = self.field(func, node, "consequence", &mut yes);
        result.merge(self.field(func, node, "alternative", &mut no));
        frame.join(vec![yes, no]);
        result
    }

    fn callback(&mut self, closure: Closure, args: Vec<Value>, authenticated: bool) -> Value {
        let model = self.model;
        let func = closure.func;
        let root = model.sources[&model.file(func)].tree.root_node();
        let Some(node) = root
            .descendant_for_byte_range(closure.bytes.start, closure.bytes.end)
            .filter(|node| node.kind() == "closure_expression")
        else {
            return Value::default();
        };
        let mut frame = Frame {
            vars: closure.vars,
            authenticated,
            ..Frame::default()
        };
        for (pattern, value) in node
            .child_by_field_name("parameters")
            .map(named_children)
            .unwrap_or_default()
            .into_iter()
            .zip(args)
        {
            self.bind(
                func,
                pattern.child_by_field_name("pattern").unwrap_or(pattern),
                &value,
                &mut frame,
            );
        }
        let value = self.field(func, node, "body", &mut frame);
        frame.returned.merge(value);
        frame.returned
    }

    fn call(&mut self, func: Id, node: Node, frame: &mut Frame) -> Value {
        let model = self.model;
        let Some(mut callee) = node.child_by_field_name("function") else {
            return Value::default();
        };
        if callee.kind() == "generic_function"
            && let Some(inner) = callee.child_by_field_name("function")
        {
            callee = inner;
        }
        let full = squash(model.text(func, callee));
        let name = full.rsplit(['.', ':']).next().unwrap_or(&full);
        let receiver_node = (callee.kind() == "field_expression")
            .then(|| callee.child_by_field_name("value"))
            .flatten();
        let receiver = receiver_node
            .map(|n| self.eval(func, n, frame))
            .unwrap_or_default();
        let nodes: Vec<_> = node
            .child_by_field_name("arguments")
            .map(named_children)
            .unwrap_or_default()
            .into_iter()
            .filter(|n| !n.is_extra())
            .collect();
        let mut args: Vec<_> = nodes
            .iter()
            .map(|&n| {
                if full == "format_" && n.kind() == "assignment_expression" {
                    self.field(func, n, "right", frame)
                } else {
                    self.eval(func, n, frame)
                }
            })
            .collect();
        let at = model.at(func, node);
        let facts = model.calls.get(&(func, line(node)));
        let fact = facts.and_then(|calls| calls.iter().copied().find(|c| c.full == full));
        if model.pattern.is_match(&full)
            && let Some(fact) = fact
        {
            if frame.authenticated {
                return Value::default();
            }
            if name == "execute"
                && nodes.first().is_some_and(|&n| {
                    n.kind() == "string_literal"
                        && model
                            .text(func, n)
                            .trim_start_matches('"')
                            .trim_start()
                            .to_ascii_uppercase()
                            .starts_with("DELETE ")
                })
            {
                return Value::default();
            }
            let flow = self.writes.entry(fact.site).or_default();
            for arg in args {
                flow.merge(arg.total());
            }
            return Value::default();
        }
        if name == "format_" {
            return format_flow(model, func, &nodes, &args, frame, &at);
        }
        if full == "params_" {
            let mut flow = Flow::default();
            for arg in args {
                flow.merge(arg.total());
            }
            return Value::flat(flow);
        }
        if let Some(closure) = frame.vars.get(&full).and_then(|v| v.closure.clone()) {
            return self.callback(*closure, args, frame.authenticated);
        }
        let local = (fact.is_none() && receiver_node.is_none())
            .then(|| {
                model
                    .functions
                    .get(&(model.file(func), full.clone()))
                    .copied()
                    .flatten()
            })
            .flatten();
        if let Some(target) = local.or_else(|| model.resolve(func, fact, &receiver, name)) {
            if receiver_node.is_some()
                && model.facts.funcs[target as usize]
                    .params
                    .first()
                    .is_some_and(|p| p.name == "self")
            {
                args.insert(0, receiver);
            }
            for n in nodes {
                if n.kind() == "reference_expression"
                    && model.text(func, n).starts_with("&mut ")
                    && let Some(var) = n.child_by_field_name("value")
                    && let Some(value) = frame.vars.get_mut(model.text(func, var))
                {
                    value.flow = value
                        .total()
                        .obscure(format!("{at} passes a mutable reference to `{full}`"));
                    value.parts.clear();
                }
            }
            return self.invoke(target, args, frame.authenticated);
        }
        let mut args = args.into_iter();
        let first = args.next().unwrap_or_default();
        let mut flow = receiver.total();
        let recv_ty = receiver.ty.as_str();
        let is_text = matches!(recv_ty, "String" | "str" | "Bytes");
        let is_iterator = matches!(recv_ty, "CharIter" | "TextIter" | "XmlPart");
        match (full.as_str(), name) {
            ("Ok" | "Err" | "Some", _) => return Value::variant(name, first),
            ("String::new" | "String::with_capacity", _) => return Value::typed("String"),
            ("Arc::clone", _) => return first,
            ("String::from", _) if matches!(first.ty.as_str(), "String" | "str") => {
                return Value {
                    ty: "String".into(),
                    ..first
                };
            }
            ("uppsala::Parser::new", _) => return Value::typed("UppsalaParser"),
            ("String::from_utf8" | "String::from_utf8_lossy", _) => {
                let value = Value {
                    ty: "String".into(),
                    ..first
                };
                return if name == "from_utf8" {
                    Value::variant("Ok", value)
                } else {
                    value
                };
            }
            ("tokio::task::spawn_blocking" | "tokio::spawn", _) => {
                if let Some(closure) = first.closure {
                    return Value::variant(
                        "Ok",
                        self.callback(*closure, vec![], frame.authenticated),
                    );
                }
            }
            (_, "new") if receiver_node.is_none() && full.contains("::") && nodes.is_empty() => {
                return Value::typed(
                    full.rsplit_once("::")
                        .map(|(ty, _)| base_type(ty))
                        .unwrap_or_default(),
                );
            }
            (_, "decode")
                if matches!(
                    full.as_str(),
                    "STANDARD.decode"
                        | "URL_SAFE.decode"
                        | "STANDARD_NO_PAD.decode"
                        | "URL_SAFE_NO_PAD.decode"
                ) =>
            {
                return Value::variant(
                    "Ok",
                    Value {
                        ty: "Bytes".into(),
                        ..first
                    },
                );
            }
            (_, _) if model.displays.contains(&(model.repo(func), full.clone())) => {
                return Value { ty: full, ..first };
            }
            (_, "clone" | "as_str" | "trim" | "as_bytes" | "to_owned" | "to_string" | "into")
                if is_text =>
            {
                return receiver;
            }
            (_, "to_string")
                if model
                    .displays
                    .contains(&(model.repo(func), receiver.ty.clone())) =>
            {
                return Value {
                    ty: "String".into(),
                    ..receiver
                };
            }
            (_, "len") if is_text || is_iterator => {
                return Value::flat(flow.cap(format!("{at} uses a fixed-width length")));
            }
            (_, "chars") if is_text => {
                return Value {
                    ty: "CharIter".into(),
                    ..receiver
                };
            }
            (_, "filter")
                if recv_ty == "CharIter"
                    && nodes.first().is_some_and(|&n| {
                        let Some(body) = n.child_by_field_name("body") else {
                            return false;
                        };
                        let Some(params) = n.child_by_field_name("parameters") else {
                            return false;
                        };
                        let Some(param) = named_children(params).first().copied() else {
                            return false;
                        };
                        squash(model.text(func, body))
                            == format!("!{}.is_ascii_whitespace()", model.text(func, param))
                    }) =>
            {
                return receiver;
            }
            (_, "take")
                if recv_ty == "CharIter"
                    && nodes.first().is_some_and(|n| finite(model.text(func, *n))) =>
            {
                return Value {
                    flow: flow.cap(format!("{at} takes a literal number of characters")),
                    ..receiver
                };
            }
            (_, "collect") if is_iterator => {
                return Value {
                    ty: "String".into(),
                    ..receiver
                };
            }
            (_, "split" | "rsplit" | "split_whitespace" | "lines") if is_text => {
                return Value {
                    ty: "TextIter".into(),
                    ..receiver
                };
            }
            (_, "next") if is_iterator => {
                return Value::variant(
                    "Some",
                    Value {
                        ty: "str".into(),
                        ..receiver
                    },
                );
            }
            (_, "truncate" | "clear" | "push_str" | "push" | "insert_str" | "extend")
                if recv_ty == "String" =>
            {
                if let Some(target) =
                    receiver_node.and_then(|n| frame.vars.get_mut(model.text(func, n)))
                {
                    match name {
                        "clear" => target.flow = flow.cap(format!("{at} clears the string")),
                        "truncate"
                            if nodes.first().is_some_and(|n| finite(model.text(func, *n))) =>
                        {
                            target.flow =
                                flow.cap(format!("{at} truncates the string to a literal length"));
                        }
                        "truncate" => {
                            target.flow =
                                flow.obscure(format!("{at} truncates to a runtime length"))
                        }
                        "insert_str" => target.flow.merge(args.next().unwrap_or_default().total()),
                        _ => target.flow.merge(first.total()),
                    }
                    target.parts.clear();
                }
                return Value::default();
            }
            (_, "unwrap" | "expect" | "unwrap_or" | "unwrap_or_default") => {
                if let Some(value) = receiver
                    .parts
                    .get("Ok")
                    .or_else(|| receiver.parts.get("Some"))
                {
                    let mut value = value.clone();
                    value.merge(first);
                    return value;
                }
            }
            (_, "map_err")
                if receiver.parts.contains_key("Ok") || receiver.parts.contains_key("Err") =>
            {
                let mut result = Value::default();
                if let Some(value) = receiver.parts.get("Ok") {
                    result = Value::variant("Ok", value.clone());
                }
                if let Some(error) = receiver.parts.get("Err") {
                    let error = match first.closure {
                        Some(closure) => {
                            self.callback(*closure, vec![error.clone()], frame.authenticated)
                        }
                        None => Value::flat(error.total().obscure(at)),
                    };
                    result.merge(Value::variant("Err", error));
                }
                return result;
            }
            (_, "ok_or" | "ok_or_else") if receiver.parts.contains_key("Some") => {
                return Value::variant("Ok", receiver.payload("Some"));
            }
            (_, "as_ref" | "as_deref" | "clone") if !receiver.parts.is_empty() => return receiver,
            (_, "as_ref" | "as_deref") if !receiver.ty.is_empty() => {
                return Value::variant("Some", receiver);
            }
            (_, "iter" | "into_iter" | "find") if recv_ty == "XmlPart" => {
                return if name == "find" {
                    Value::variant("Some", receiver)
                } else {
                    receiver
                };
            }
            (_, "map")
                if receiver.parts.contains_key("Some") || receiver.parts.contains_key("Ok") =>
            {
                let tag = if receiver.parts.contains_key("Some") {
                    "Some"
                } else {
                    "Ok"
                };
                if let Some(closure) = first.closure {
                    return Value::variant(
                        tag,
                        self.callback(*closure, vec![receiver.payload(tag)], frame.authenticated),
                    );
                }
            }
            (_, "element") if recv_ty == "Document" => {
                return Value::variant(
                    "Some",
                    Value {
                        ty: "XmlPart".into(),
                        ..receiver
                    },
                );
            }
            (_, "node_kind") if recv_ty == "Document" => {
                let mut part = Value::variant(
                    "NodeKind::Text",
                    Value {
                        ty: "str".into(),
                        ..receiver.clone()
                    },
                );
                part.merge(Value::variant(
                    "NodeKind::CData",
                    Value {
                        ty: "str".into(),
                        ..receiver
                    },
                ));
                return Value::variant("Some", part);
            }
            (_, "children") if recv_ty == "Document" => {
                return Value {
                    ty: "XmlPart".into(),
                    ..receiver
                };
            }
            (_, "parse") if recv_ty == "UppsalaParser" => {
                let error = first
                    .total()
                    .obscure(format!("{at} returns a parser diagnostic"));
                let mut result = Value::variant(
                    "Ok",
                    Value {
                        ty: "Document".into(),
                        ..first
                    },
                );
                result.merge(Value::variant("Err", Value::flat(error)));
                return result;
            }
            (_, method) if recv_ty == "UppsalaParser" && method.starts_with("with_") => {
                return receiver;
            }
            _ => {}
        }
        flow.merge(first.total());
        for arg in args {
            flow.merge(arg.total());
        }
        for n in nodes {
            if model.text(func, n).starts_with("&mut ")
                && let Some(var) = n.child_by_field_name("value")
                && let Some(value) = frame.vars.get_mut(model.text(func, var))
            {
                value.flow = value
                    .total()
                    .obscure(format!("{at} passes a mutable reference to `{full}`"));
                value.parts.clear();
            }
        }
        Value::flat(flow.obscure(format!("{at} cannot trace `{full}`")))
    }
}

fn format_flow(
    model: &Model<'_>,
    func: Id,
    nodes: &[Node],
    args: &[Value],
    frame: &Frame,
    at: &str,
) -> Value {
    let Some(literal) = nodes
        .first()
        .filter(|n| matches!(n.kind(), "string_literal" | "raw_string_literal"))
    else {
        return Value::default();
    };
    let mut flow = Flow::default();
    let named: BTreeMap<_, _> = nodes
        .iter()
        .zip(args)
        .filter_map(|(node, value)| {
            let name = node
                .child_by_field_name("left")
                .filter(|_| node.kind() == "assignment_expression")?;
            Some((model.text(func, name), value))
        })
        .collect();
    let template = model
        .text(func, *literal)
        .replace("{{", "")
        .replace("}}", "");
    let mut position = 1;
    for entry in template.split('{').skip(1) {
        let Some((field, _)) = entry.split_once('}') else {
            continue;
        };
        let (value, spec) = field.split_once(':').unwrap_or((field, ""));
        let found = if value.is_empty() {
            let next = args.get(position);
            position += 1;
            next
        } else if let Ok(index) = value.parse::<usize>() {
            args.get(index + 1)
        } else {
            named.get(value).copied().or_else(|| frame.vars.get(value))
        };
        if let Some(found) = found {
            let mut contribution = found.total();
            if let Some(limit) = spec.strip_prefix('.').filter(|limit| finite(limit))
                && matches!(found.ty.as_str(), "String" | "str")
            {
                contribution = contribution.cap(format!("{at} formats at most {limit} characters"));
            } else if !spec.is_empty() {
                contribution = contribution.obscure(format!(
                    "{at} has a format specifier outside the size model"
                ));
            }
            flow.merge(contribution);
        }
    }
    if !flow.raw.is_empty() {
        flow.raw
            .insert(format!("{at} interpolates request text into a string"));
    }
    Value {
        flow,
        ty: "String".into(),
        ..Value::default()
    }
}

fn length_guard<'a>(model: &'a Model<'_>, func: Id, cond: Node) -> Option<(&'a str, bool)> {
    if cond.kind() != "binary_expression" {
        return None;
    }
    let op = model.text(func, cond.child_by_field_name("operator")?);
    let (len, max) = (
        cond.child_by_field_name("left")?,
        cond.child_by_field_name("right")?,
    );
    if !matches!(op, "<" | "<=" | "==" | ">" | ">=" | "!=")
        || max.kind() != "integer_literal"
        || !finite(model.text(func, max))
        || len.kind() != "call_expression"
    {
        return None;
    }
    let len = len.child_by_field_name("function")?;
    let var = len.child_by_field_name("value")?;
    (var.kind() == "identifier" && model.text(func, len.child_by_field_name("field")?) == "len")
        .then(|| (model.text(func, var), matches!(op, "<" | "<=" | "==")))
}
