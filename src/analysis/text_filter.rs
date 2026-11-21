//! Question 5 over diagnostic lines captured from a Rust subprocess.

use super::Analysis;
use crate::facts::{Id, Lang};
use crate::lang::{lang_of, line, named_children, text};
use crate::report::Verdict;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use tree_sitter::{Node, Parser};

const RULE: &str = "text-filter-pass";
const PATTERNS: &[&str] = &["contains", "starts_with", "is_match", "split_once"];

impl Analysis<'_> {
    pub(super) fn text_filter_pass(&mut self) {
        let mut sites = HashMap::<Id, HashMap<u32, Id>>::new();
        for call in &self.f.calls {
            if !PATTERNS.contains(&call.name.as_str()) {
                continue;
            }
            let site = &self.f.sites[call.site as usize];
            let file = &self.f.files[site.file as usize];
            if file.lang == Lang::Rust && !file.test && !self.f.funcs[site.func as usize].test {
                sites
                    .entry(site.file)
                    .or_default()
                    .insert(site.line, call.site);
            }
        }
        let test_functions: HashSet<_> = self
            .f
            .funcs
            .iter()
            .filter(|func| func.test && sites.contains_key(&func.file))
            .map(|func| (func.file, func.line))
            .collect();
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .expect("Rust grammar");
        // The loader emits one file fact per recognized source, in source order.
        let sources = self
            .texts
            .iter()
            .filter(|(path, _)| lang_of(Path::new(path)).is_some());
        for ((id, file), (path, src)) in self.f.files.iter().enumerate().zip(sources) {
            let Some(anchors) = sites.get(&(id as Id)) else {
                continue;
            };
            if file.path != *path
                || !src.contains("Command")
                || !(src.contains("stderr") || src.contains("stdout"))
            {
                continue;
            }
            let Some(tree) = parser.parse(src, None) else {
                continue;
            };
            if tree.root_node().has_error() {
                continue;
            }
            let model = FileModel {
                src,
                root: tree.root_node(),
            };
            for node in descendants(model.root) {
                if !matches!(node.kind(), "for_expression" | "while_expression")
                    || enclosing_function(node)
                        .is_none_or(|func| test_functions.contains(&(id as Id, line(func))))
                {
                    continue;
                }
                for finding in model.filters(node) {
                    let Some(&site) = anchors.get(&line(finding.pattern)) else {
                        continue;
                    };
                    let witness = finding
                        .steps
                        .into_iter()
                        .map(|(node, step)| format!("{path}:{} {step}", line(node)))
                        .collect();
                    self.push(
                        5,
                        RULE,
                        finding.verdict,
                        site,
                        finding.message,
                        witness,
                        finding.assumptions,
                    );
                }
            }
        }
    }
}

struct FileModel<'a> {
    src: &'a str,
    root: Node<'a>,
}

struct Filter<'a> {
    pattern: Node<'a>,
    verdict: Verdict,
    message: String,
    steps: Vec<(Node<'a>, &'static str)>,
    assumptions: Vec<String>,
}

#[derive(Clone, Copy)]
struct Pattern<'a> {
    node: Node<'a>,
    error_text: bool,
    open: bool,
    closed: bool,
}

impl<'a> FileModel<'a> {
    fn t(&self, node: Node<'_>) -> &'a str {
        text(node, self.src)
    }

    fn call(&self, node: Node<'a>) -> Option<(Option<Node<'a>>, &'a str, Vec<Node<'a>>)> {
        if node.kind() != "call_expression" {
            return None;
        }
        let fun = field(node, "function")?;
        let args = items(field(node, "arguments")?);
        if fun.kind() == "field_expression" {
            Some((field(fun, "value"), self.t(field(fun, "field")?), args))
        } else {
            Some((None, self.t(fun), args))
        }
    }

    fn function(&self, name: &str) -> Option<Node<'a>> {
        let mut defs = items(self.root).into_iter().filter(|n| {
            n.kind() == "function_item" && field(*n, "name").is_some_and(|n| self.t(n) == name)
        });
        let fun = defs.next()?;
        defs.next().is_none().then_some(fun)
    }

    fn binding(&self, name: Node<'a>) -> Option<Node<'a>> {
        self.binding_before(name, self.t(name))
    }

    fn binding_before(&self, at: Node<'a>, name_text: &str) -> Option<Node<'a>> {
        let mut child = at;
        while let Some(parent) = child.parent() {
            if parent.kind() == "block" {
                for stmt in items(parent)
                    .into_iter()
                    .rev()
                    .filter(|s| s.end_byte() <= child.start_byte())
                {
                    if stmt.kind() == "let_declaration"
                        && let Some(pat) = field(stmt, "pattern")
                        && (self.t(pat) == name_text
                            || descendants(pat)
                                .any(|n| n.kind() == "identifier" && self.t(n) == name_text))
                    {
                        return field(stmt, "value").filter(|_| pat.kind() == "identifier");
                    }
                    // A reassignment or an opaque mutable borrow can change the origin.
                    if descendants(stmt).any(|n| self.writes(n, name_text)) {
                        return None;
                    }
                }
            }
            if parent.kind() == "if_expression"
                && field(parent, "consequence") == Some(child)
                && let Some(cond) = field(parent, "condition")
                && cond.kind() == "let_condition"
                && let Some(pat) = field(cond, "pattern")
                && pat.kind() == "tuple_struct_pattern"
                && field(pat, "type").is_some_and(|n| self.t(n) == "Some")
                && items(pat)
                    .iter()
                    .any(|&n| n.kind() == "identifier" && self.t(n) == name_text)
            {
                return field(cond, "value");
            }
            if parent.kind() == "function_item" {
                break;
            }
            child = parent;
        }
        None
    }

    fn writes(&self, node: Node<'a>, name: &str) -> bool {
        match node.kind() {
            "assignment_expression" | "compound_assignment_expr" => {
                field(node, "left").is_some_and(|n| self.t(n) == name)
            }
            "reference_expression" if self.t(node).starts_with("&mut") => {
                field(node, "value").is_some_and(|n| self.t(n) == name)
            }
            _ => false,
        }
    }

    fn parameter(&self, func: Node<'a>, name: &str) -> Option<(usize, &'a str)> {
        items(field(func, "parameters")?)
            .into_iter()
            .enumerate()
            .find_map(|(i, p)| {
                let pat = field(p, "pattern")?;
                (self.t(pat) == name && !items(p).iter().any(|n| n.kind() == "mutable_specifier"))
                    .then(|| Some((i, self.t(field(p, "type")?))))?
            })
    }

    fn command(&self, node: Node<'a>, depth: u8) -> bool {
        if depth == 0 {
            return false;
        }
        if let Some((recv, name, _)) = self.call(node) {
            return matches!(name, "Command::new" | "std::process::Command::new")
                || recv.is_some_and(|recv| self.command(recv, depth - 1));
        }
        if node.kind() != "identifier" {
            return false;
        }
        if let Some(value) = self.binding(node) {
            return self.command(value, depth - 1);
        }
        enclosing_function(node)
            .and_then(|func| self.parameter(func, self.t(node)))
            .is_some_and(|(_, ty)| {
                matches!(
                    ty,
                    "Command" | "&mut Command" | "&mut std::process::Command"
                )
            })
    }

    fn stream(&self, node: Node<'a>, depth: u8) -> Option<Node<'a>> {
        if depth == 0 {
            return None;
        }
        let node = self.fallible(node);
        if node.kind() == "identifier" {
            if let Some(value) = self.binding(node) {
                return self.stream(value, depth - 1);
            }
            let func = enclosing_function(node)?;
            let name = self.t(field(func, "name")?);
            let (index, ty) = self.parameter(func, self.t(node))?;
            if !ty.contains("BufRead") || self.function(name)? != func {
                return None;
            }
            return descendants(self.root).find_map(|call| {
                let (recv, called, args) = self.call(call)?;
                (recv.is_none() && called == name && enclosing_function(call)? != func)
                    .then(|| self.stream(*args.get(index)?, depth - 1))?
            });
        }
        if node.kind() == "field_expression"
            && matches!(self.t(field(node, "field")?), "stderr" | "stdout")
        {
            let value = peel(field(node, "value")?);
            let output = if value.kind() == "identifier" {
                self.fallible(self.binding(value)?)
            } else {
                value
            };
            let (recv, method, _) = self.call(output)?;
            return (matches!(method, "spawn" | "output") && self.command(recv?, 8))
                .then_some(node);
        }
        let (recv, method, args) = self.call(node)?;
        let source = match method {
            "BufReader::new" | "String::from_utf8_lossy" => *args.first()?,
            "take" | "map_err" | "ok_or" | "ok_or_else" | "unwrap" | "expect" => recv?,
            _ => return None,
        };
        self.stream(source, depth - 1)
    }

    fn fallible(&self, mut node: Node<'a>) -> Node<'a> {
        loop {
            node = peel(node);
            match self.call(node) {
                Some((Some(recv), "unwrap" | "expect" | "map_err" | "ok_or" | "ok_or_else", _)) => {
                    node = recv
                }
                _ => return node,
            }
        }
    }

    fn derives_from_line(
        &self,
        node: Node<'a>,
        name: &str,
        loop_node: Node<'a>,
        depth: u8,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        let node = peel(node);
        if node.kind() == "identifier" {
            return self
                .binding(node)
                .filter(|v| v.start_byte() >= loop_node.start_byte())
                .map_or_else(
                    || self.t(node) == name,
                    |value| self.derives_from_line(value, name, loop_node, depth - 1),
                );
        }
        if let Some((recv, method, args)) = self.call(node) {
            let value = match method {
                "String::from_utf8_lossy" => args.first().copied(),
                "map_err" | "unwrap" | "expect" | "as_str" => recv,
                _ => None,
            };
            return value
                .is_some_and(|value| self.derives_from_line(value, name, loop_node, depth - 1));
        }
        false
    }

    fn literal(&self, node: Node<'a>) -> Option<&'a str> {
        let value = if node.kind() == "identifier" {
            self.binding(node)
                .or_else(|| {
                    items(self.root).into_iter().find_map(|item| {
                        (item.kind() == "const_item"
                            && self.t(field(item, "name")?) == self.t(node))
                        .then(|| field(item, "value"))?
                    })
                })
                .unwrap_or(node)
        } else {
            node
        };
        matches!(value.kind(), "string_literal" | "raw_string_literal").then(|| self.t(value))
    }

    fn error_literal(&self, node: Node<'a>) -> bool {
        self.literal(node).is_some_and(|literal| {
            ["error", "failure", "failed", "fatal"]
                .iter()
                .any(|word| literal.to_ascii_lowercase().contains(word))
        })
    }

    fn pattern(
        &self,
        node: Node<'a>,
        name: &str,
        scope: Node<'a>,
        depth: u8,
    ) -> Option<Pattern<'a>> {
        if depth == 0 {
            return None;
        }
        let node = peel(node);
        if node.kind() == "identifier" {
            return self.pattern(self.binding(node)?, name, scope, depth - 1);
        }
        if node.kind() == "binary_expression" && self.t(field(node, "operator")?) == "&&" {
            let left = field(node, "left")?;
            let right = field(node, "right")?;
            let (mut pattern, other) = if let Some(p) = self.pattern(left, name, scope, depth - 1) {
                (p, right)
            } else {
                (self.pattern(right, name, scope, depth - 1)?, left)
            };
            pattern.open = false;
            pattern.closed = self.closed_lines(other, name, scope);
            return Some(pattern);
        }
        let (recv, method, args) = self.call(node)?;
        let parsed = |n| self.derives_from_line(n, name, scope, 6);
        if matches!(method, "contains" | "starts_with" | "split_once") && parsed(recv?) {
            return Some(Pattern {
                node,
                error_text: self.error_literal(*args.first()?),
                open: method != "split_once" && self.literal(*args.first()?).is_some(),
                closed: false,
            });
        }
        if method == "is_match" && parsed(*args.first()?) {
            let regex = recv?;
            let value = self.fallible(self.binding(regex).unwrap_or(regex));
            let literal = self.call(value).and_then(|(_, name, args)| {
                matches!(name, "Regex::new" | "regex::Regex::new").then(|| args.first().copied())?
            });
            return Some(Pattern {
                node,
                error_text: literal.is_some_and(|arg| self.error_literal(arg)),
                open: literal.and_then(|arg| self.literal(arg)).is_some_and(|s| {
                    let start = s.contains('^') || s.contains("\\A");
                    let end = s.contains('$') || s.contains("\\z");
                    !(start && end)
                }),
                closed: false,
            });
        }
        if method == "is_some_and" {
            let receiver = peel(recv?);
            let (None, helper, args) = self.call(receiver)? else {
                return None;
            };
            if !parsed(*args.first()?) {
                return None;
            }
            let helper = self.function(helper)?;
            let param = first_parameter(helper)?;
            let first = *items(field(helper, "body")?).first()?;
            let matched = field(first, "value").filter(|n| n.kind() == "try_expression")?;
            let part = peel(matched);
            let (Some(recv), "split_once", args) = self.call(part)? else {
                return None;
            };
            return (self.t(peel(recv)) == self.t(param) && self.error_literal(*args.first()?))
                .then_some(Pattern {
                    node: part,
                    error_text: true,
                    open: false,
                    closed: false,
                });
        }
        if recv.is_none() && args.len() == 1 && parsed(args[0]) {
            let fun = self.function(method)?;
            let body = field(fun, "body")?;
            let params = items(field(fun, "parameters")?);
            let stmts = items(body);
            if params.len() == 1 && stmts.len() == 1 {
                return self.pattern(
                    statement(stmts[0]),
                    self.t(first_parameter(fun)?),
                    body,
                    depth - 1,
                );
            }
        }
        None
    }

    fn closed_lines(&self, node: Node<'a>, name: &str, scope: Node<'a>) -> bool {
        let Some((Some(table), "contains", args)) = self.call(peel(node)) else {
            return false;
        };
        let table = self
            .binding(table)
            .filter(|value| immutable_initializer(*value))
            .unwrap_or(table);
        table.kind() == "array_expression"
            && !items(table).is_empty()
            && items(table)
                .iter()
                .all(|n| matches!(n.kind(), "string_literal" | "raw_string_literal"))
            && args.len() == 1
            && self.derives_from_line(args[0], name, scope, 6)
    }

    fn loop_stream(&self, node: Node<'a>) -> Option<(&'a str, Node<'a>)> {
        if node.kind() == "for_expression" {
            let pat = field(node, "pattern")?;
            let (recv, method, args) = self.call(field(node, "value")?)?;
            let by_line = match (method, args.as_slice()) {
                ("lines", []) => true,
                ("split", [delimiter]) => matches!(self.t(*delimiter), "b'\\n'" | "'\\n'"),
                _ => false,
            };
            if pat.kind() != "identifier" || !by_line {
                return None;
            }
            return Some((self.t(pat), self.stream(recv?, 10)?));
        }
        let cond = field(node, "condition")?;
        if self.t(field(cond, "operator")?) != ">" || self.t(field(cond, "right")?) != "0" {
            return None;
        }
        let (recv, method, args) = self.call(peel(field(cond, "left")?))?;
        let buffer = peel(*args.get(1)?);
        (method == "read_until"
            && self.t(*args.first()?) == "b'\\n'"
            && buffer.kind() == "identifier")
            .then(|| Some((self.t(buffer), self.stream(recv?, 10)?)))?
    }

    fn increment(&self, node: Node<'a>) -> Option<&'a str> {
        if node.kind() != "compound_assignment_expr" || self.t(field(node, "right")?) != "1" {
            return None;
        }
        let left = field(node, "left")?;
        let op = self.t(field(node, "operator")?);
        (left.kind() == "identifier" && op == "+=").then(|| self.t(left))
    }

    fn expected(&self, node: Node<'a>) -> bool {
        if let Some((Some(recv), "len", args)) = self.call(node) {
            return args.is_empty()
                && enclosing_function(node)
                    .and_then(|func| self.parameter(func, self.t(recv)))
                    .is_some_and(|(_, ty)| {
                        ty.starts_with("&BTreeSet<") || ty.starts_with("&HashSet<")
                    })
                && self.binding(recv).is_none()
                && !enclosing_function(node).is_some_and(|func| {
                    descendants(func)
                        .any(|n| n.start_byte() < node.start_byte() && self.writes(n, self.t(recv)))
                });
        }
        if node.kind() == "integer_literal" {
            return true;
        }
        if node.kind() != "identifier" {
            return false;
        }
        if let Some(value) = self.binding(node) {
            return value.kind() == "integer_literal" && immutable_initializer(value);
        }
        let Some(func) = enclosing_function(node) else {
            return false;
        };
        self.parameter(func, self.t(node))
            .is_some_and(|(_, ty)| matches!(ty, "usize" | "u64" | "u32"))
            && !descendants(func)
                .any(|n| n.start_byte() < node.start_byte() && self.writes(n, self.t(node)))
    }

    fn rejects(&self, node: Node<'a>) -> bool {
        if node.kind() != "if_expression" || field(node, "alternative").is_some() {
            return false;
        }
        let Some(body) = field(node, "consequence") else {
            return false;
        };
        let stmts = items(body);
        let [one] = stmts.as_slice() else {
            return false;
        };
        let last = statement(*one);
        if last.kind() == "return_expression" {
            return items(last)
                .first()
                .and_then(|n| self.call(*n))
                .is_some_and(|(recv, name, _)| recv.is_none() && name == "Err");
        }
        last.kind() == "macro_invocation"
            && field(last, "macro").is_some_and(|m| self.t(m) == "panic")
    }

    fn count_check(&self, node: Node<'a>, name: &str) -> Option<Node<'a>> {
        if !self.rejects(node) {
            return None;
        }
        let cond = field(node, "condition")?;
        let left = field(cond, "left")?;
        let right = field(cond, "right")?;
        let op = self.t(field(cond, "operator")?);
        let result = (self.t(left) == name
            && matches!(op, "!=" | ">" | ">=")
            && self.expected(right))
            || (self.t(right) == name && matches!(op, "!=" | "<" | "<=") && self.expected(left));
        result.then_some(cond)
    }

    fn retains_line(&self, node: Node<'a>, name: &str, scope: Node<'a>) -> bool {
        let node = self.fallible(node);
        if node.kind() != "macro_invocation" {
            return false;
        }
        let Some(macro_name) = field(node, "macro") else {
            return false;
        };
        if !matches!(self.t(macro_name), "eprint" | "eprintln" | "writeln") {
            return false;
        }
        let Some(tokens) = items(node).into_iter().find(|n| n.kind() == "token_tree") else {
            return false;
        };
        let tokens = items(tokens);
        let format_index = usize::from(self.t(macro_name) == "writeln");
        let Some(format) = tokens.get(format_index) else {
            return false;
        };
        if format.kind() != "string_literal" {
            return false;
        }
        let format = self.t(*format).trim_matches('"');
        let variable = if format == "{}" {
            tokens
                .get(format_index + 1)
                .filter(|n| n.kind() == "identifier")
                .map(|n| self.t(*n))
        } else {
            format
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .filter(|s| !s.is_empty() && s.chars().all(|ch| ch.is_alphanumeric() || ch == '_'))
        };
        variable.is_some_and(|var| {
            self.binding_before(node, var)
                .filter(|value| value.start_byte() >= scope.start_byte())
                .map_or(var == name, |value| {
                    self.derives_from_line(value, name, scope, 6)
                })
        })
    }

    fn filters(&self, loop_node: Node<'a>) -> Vec<Filter<'a>> {
        let Some((name, stream)) = self.loop_stream(loop_node) else {
            return vec![];
        };
        let Some(body) = field(loop_node, "body") else {
            return vec![];
        };
        let Some(loop_block) = statement_parent(loop_node) else {
            return vec![];
        };
        let after: Vec<_> = items(loop_block)
            .into_iter()
            .filter(|s| s.start_byte() >= loop_node.end_byte())
            .map(statement)
            .collect();
        let mut results = vec![];
        for branch in descendants(body).filter(|n| n.kind() == "if_expression") {
            if branch.parent().and_then(|p| enclosing_loop(p)) != Some(loop_node) {
                continue;
            }
            let Some(condition) = field(branch, "condition") else {
                continue;
            };
            let Some(pattern) = self.pattern(condition, name, loop_node, 6) else {
                continue;
            };
            let Some(pass) = field(branch, "consequence") else {
                continue;
            };
            let pass: Vec<_> = items(pass).into_iter().map(statement).collect();
            let increments: Vec<_> = pass
                .iter()
                .filter_map(|&n| self.increment(n).map(|name| (n, name)))
                .collect();
            if pass.is_empty()
                || increments.len() > 1
                || !pass
                    .iter()
                    .all(|&n| n.kind() == "continue_expression" || self.increment(n).is_some())
            {
                continue;
            }
            let alternative = field(branch, "alternative");
            let remaining: Vec<_> = if let Some(alt) = alternative {
                items(alt)
                    .into_iter()
                    .filter(|n| n.kind() == "block")
                    .flat_map(items)
                    .map(statement)
                    .collect()
            } else if pass
                .last()
                .is_some_and(|n| n.kind() == "continue_expression")
            {
                statement_parent(branch)
                    .into_iter()
                    .flat_map(items)
                    .filter(|n| n.start_byte() >= branch.end_byte())
                    .map(statement)
                    .collect()
            } else {
                vec![]
            };
            let reporting = remaining
                .iter()
                .find(|&&n| self.retains_line(n, name, loop_node))
                .copied()
                .filter(|_| pattern.error_text);
            let decision = remaining.iter().find_map(|&n| {
                let count = self.increment(n)?;
                if descendants(body).any(|use_site| {
                    use_site.kind() == "identifier"
                        && self.t(use_site) == count
                        && !within(use_site, n)
                }) {
                    return None;
                }
                let result = after.iter().find_map(|&exit| {
                    let cond = field(exit, "condition")?;
                    let left = field(cond, "left")?;
                    (self.rejects(exit)
                        && self.t(left) == count
                        && self.t(field(cond, "operator")?) == ">"
                        && self.t(field(cond, "right")?) == "0")
                        .then_some(exit)
                })?;
                (!descendants(loop_block).any(|use_site| {
                    use_site.start_byte() >= loop_node.end_byte()
                        && use_site.start_byte() < result.start_byte()
                        && use_site.kind() == "identifier"
                        && self.t(use_site) == count
                }))
                .then_some((n, result))
            });
            if reporting.is_none() && decision.is_none() {
                continue;
            }
            let mut steps = vec![
                (stream, "captures subprocess output"),
                (pattern.node, "matches diagnostic text"),
                (branch, "drops matching lines"),
            ];
            if let Some(n) = reporting {
                steps.push((n, "forwards the remaining diagnostics"));
            }
            if let Some((record, reject)) = decision {
                steps.push((record, "counts the remaining lines"));
                steps.push((reject, "rejects on that count"));
            }
            let bound = increments.first().and_then(|&(increment, count)| {
                (statement_parent(branch) == Some(body)
                    && field(loop_node, "pattern").is_none_or(|p| !references(self, p, count)))
                .then(|| self.checked_count(loop_node, loop_block, &after, increment, count))?
            });
            let (verdict, message, assumptions) = if let Some(bound) = bound {
                steps.push((bound, "rejects an unexpected number of dropped lines"));
                (
                    Verdict::Proven,
                    "the filter rejects an unexpected count of dropped diagnostics",
                    vec![
                        format!(
                            "the bound at line {} is the intended allowance for this check's dropped messages",
                            line(bound)
                        ),
                        "the counter does not overflow and callers honor a returned error".into(),
                    ],
                )
            } else if pattern.closed {
                (
                    Verdict::Proven,
                    "the filter drops only lines in a literal set",
                    vec!["the listed complete lines are the check's intended exceptions".into()],
                )
            } else if pattern.open
                && !increments.first().is_some_and(|&(_, count)| {
                    later_statements(loop_node)
                        .into_iter()
                        .any(|n| references(self, n, count) && !self.only_reports(n))
                })
            {
                (
                    Verdict::Violated,
                    "a text match drops subprocess diagnostics without checking their identity or expected count",
                    vec![],
                )
            } else {
                (
                    Verdict::Unknown,
                    "the filter drops subprocess diagnostics but its identity or count check could not be established",
                    vec![],
                )
            };
            results.push(Filter {
                pattern: pattern.node,
                verdict,
                message: message.into(),
                steps,
                assumptions,
            });
        }
        results
    }

    fn only_reports(&self, node: Node<'a>) -> bool {
        let logging = |n| {
            field(n, "macro")
                .is_some_and(|m| matches!(self.t(m), "print" | "println" | "eprint" | "eprintln"))
        };
        if node.kind() == "if_expression" && field(node, "alternative").is_none() {
            return field(node, "consequence")
                .is_some_and(|body| items(body).into_iter().map(statement).all(logging));
        }
        logging(node)
    }

    fn checked_count(
        &self,
        loop_node: Node<'a>,
        block: Node<'a>,
        after: &[Node<'a>],
        increment: Node<'a>,
        count: &str,
    ) -> Option<Node<'a>> {
        let func = enclosing_function(loop_node)?;
        if field(func, "body")? != block {
            return None;
        }
        let init = items(block).into_iter().rev().find(|n| {
            n.end_byte() <= loop_node.start_byte()
                && n.kind() == "let_declaration"
                && field(*n, "pattern").is_some_and(|p| self.t(p) == count)
        })?;
        let zero = peel(field(init, "value")?);
        if !matches!(self.t(zero), "0" | "0usize" | "0u32" | "0u64") {
            return None;
        }
        let guard = after.iter().find_map(|&n| self.count_check(n, count))?;
        // A second use could mutate, shadow or borrow the counter before the guard.
        let extra_use = descendants(block).any(|n| {
            n.start_byte() >= init.end_byte()
                && n.start_byte() < guard.start_byte()
                && n.kind() == "identifier"
                && self.t(n) == count
                && !within(n, increment)
        });
        let can_bypass = descendants(block).any(|n| {
            n.start_byte() >= init.end_byte()
                && n.start_byte() < guard.start_byte()
                && ((n.kind() == "return_expression"
                    && items(n)
                        .first()
                        .and_then(|n| self.call(*n))
                        .is_none_or(|(_, call, _)| call != "Err"))
                    || self
                        .call(n)
                        .is_some_and(|(_, call, _)| call.rsplit("::").next() == Some("exit")))
        });
        (!extra_use && !can_bypass).then_some(guard)
    }
}

fn field<'a>(node: Node<'a>, name: &str) -> Option<Node<'a>> {
    node.child_by_field_name(name)
}

fn items(node: Node<'_>) -> Vec<Node<'_>> {
    named_children(node)
        .into_iter()
        .filter(|n| !n.is_extra())
        .collect()
}

fn descendants(node: Node<'_>) -> impl Iterator<Item = Node<'_>> {
    let mut stack = vec![node];
    std::iter::from_fn(move || {
        let node = stack.pop()?;
        stack.extend(items(node).into_iter().rev());
        Some(node)
    })
}

fn enclosing_function(node: Node<'_>) -> Option<Node<'_>> {
    std::iter::successors(node.parent(), |n| n.parent()).find(|n| n.kind() == "function_item")
}

fn enclosing_loop(node: Node<'_>) -> Option<Node<'_>> {
    std::iter::successors(Some(node), |n| n.parent()).find(|n| {
        matches!(
            n.kind(),
            "for_expression" | "while_expression" | "loop_expression"
        )
    })
}

fn peel(mut node: Node<'_>) -> Node<'_> {
    while matches!(
        node.kind(),
        "parenthesized_expression" | "reference_expression" | "try_expression"
    ) {
        let Some(inner) = items(node).last().copied() else {
            break;
        };
        node = inner;
    }
    node
}

fn statement(node: Node<'_>) -> Node<'_> {
    if node.kind() == "expression_statement" {
        items(node).first().copied().unwrap_or(node)
    } else {
        node
    }
}

fn immutable_initializer(value: Node<'_>) -> bool {
    value.parent().is_some_and(|stmt| {
        stmt.kind() == "let_declaration"
            && !items(stmt).iter().any(|n| n.kind() == "mutable_specifier")
    })
}

fn statement_parent(node: Node<'_>) -> Option<Node<'_>> {
    let parent = node.parent()?;
    let block = if parent.kind() == "expression_statement" {
        parent.parent()?
    } else {
        parent
    };
    (block.kind() == "block").then_some(block)
}

fn later_statements(node: Node<'_>) -> Vec<Node<'_>> {
    let mut later = vec![];
    let mut child = node;
    while let Some(parent) = child.parent() {
        if parent.kind() == "function_item" {
            break;
        }
        if parent.kind() == "block" {
            later.extend(
                items(parent)
                    .into_iter()
                    .filter(|n| n.start_byte() >= child.end_byte())
                    .map(statement),
            );
        }
        child = parent;
    }
    later
}

fn first_parameter(func: Node<'_>) -> Option<Node<'_>> {
    field(*items(field(func, "parameters")?).first()?, "pattern")
}

fn references(model: &FileModel<'_>, node: Node<'_>, name: &str) -> bool {
    descendants(node).any(|n| n.kind() == "identifier" && model.t(n) == name)
}

fn within(node: Node<'_>, scope: Node<'_>) -> bool {
    node.start_byte() >= scope.start_byte() && node.end_byte() <= scope.end_byte()
}
