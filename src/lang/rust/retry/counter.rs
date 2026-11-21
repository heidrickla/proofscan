//! Collision probes over keys allocated by a local counter.

use super::protocol::{binary, method_call};
use super::{
    Node, call, children, exits_loop, falls_through, ident, imports_symbol, nodes, references,
    squash, statements, text, walk,
};
use std::collections::BTreeMap;

pub(super) fn fresh_probe<'t>(loop_node: Node<'t>, body: Node<'t>, src: &str) -> Option<Node<'t>> {
    if loop_node.kind() != "loop_expression" || body.has_error() {
        return None;
    }
    let block = loop_node
        .parent()
        .filter(|n| n.kind() == "block")
        .or_else(|| {
            loop_node
                .parent()
                .filter(|n| n.kind() == "expression_statement")?
                .parent()
                .filter(|n| n.kind() == "block")
        })?;
    let function = block.parent().filter(|n| n.kind() == "function_item")?;
    let steps = statements(body);
    let split = steps.iter().position(|n| n.kind() == "match_expression")?;
    let (prefix, [matched, tail @ ..]) = steps.split_at(split) else {
        return None;
    };
    if !text(*matched, src).contains("AlreadyExists") {
        return None;
    }
    let attempt = matched.child_by_field_name("value")?;
    let (callee, args) = call(attempt)?;
    let [key] = args[..] else { return None };
    if !matches!(callee.kind(), "identifier" | "scoped_identifier") {
        return None;
    }
    let surrounding = statements(block);
    if surrounding.iter().any(|n| {
        matches!(
            n.kind(),
            "attribute_item" | "inner_attribute_item" | "macro_invocation"
        )
    }) {
        return None;
    }
    surrounding
        .iter()
        .filter(|n| n.end_byte() <= loop_node.start_byte())
        .filter_map(|&n| Counter::declared(n, src).map(|counter| (n, counter)))
        .find_map(|(decl, counter)| {
            if surrounding
                .iter()
                .any(|&n| n != decl && n != loop_node && references(n, counter.name, src))
            {
                return None;
            }
            let mut probe = Probe {
                src,
                function,
                block,
                counter,
                keys: BTreeMap::new(),
            };
            let mut advanced = false;
            for &stmt in prefix {
                if probe.step(stmt) {
                    advanced = true;
                    continue;
                }
                let (name, value) = probe.binding(stmt)?;
                let key = if counter.atomic && !advanced && probe.fetch(value) {
                    advanced = true;
                    Key::Index
                } else {
                    probe.key(value)?
                };
                if name == counter.name || probe.keys.insert(name, key).is_some() {
                    return None;
                }
            }
            probe.key(key)?;
            let tail_step = match tail {
                [] => false,
                [step] if probe.step(*step) => true,
                _ => return None,
            };
            let collision = probe.collision(*matched, attempt, callee)?;
            match probe.collision_path(collision, advanced)? {
                Edge::Fallthrough(done) if !done && !tail_step => None,
                _ => Some(*matched),
            }
        })
}

#[derive(Clone, Copy)]
struct Counter<'s> {
    name: &'s str,
    atomic: bool,
}

impl<'s> Counter<'s> {
    fn declared(n: Node, src: &'s str) -> Option<Self> {
        let value = n.child_by_field_name("value")?;
        if n.kind() == "static_item" && !has_mut(n) {
            let ty = squash(text(n.child_by_field_name("type")?, src));
            let atom = ty.rsplit("::").next()?;
            if !matches!(
                atom,
                "AtomicU8" | "AtomicU16" | "AtomicU32" | "AtomicU64" | "AtomicUsize"
            ) || if ty == atom {
                !std::iter::successors(n.parent(), |n| n.parent())
                    .any(|scope| imports_symbol(scope, "std::sync::atomic", atom, src))
            } else {
                ty.trim_start_matches("::") != format!("std::sync::atomic::{atom}")
            } {
                return None;
            }
            let (callee, args) = call(value)?;
            let [initial] = args[..] else { return None };
            if squash(text(callee, src)) == format!("{ty}::new")
                && initial.kind() == "integer_literal"
            {
                return Some(Self {
                    name: ident(n.child_by_field_name("name")?, src)?,
                    atomic: true,
                });
            }
        }
        if n.kind() == "let_declaration" && has_mut(n) && value.kind() == "integer_literal" {
            return Some(Self {
                name: ident(n.child_by_field_name("pattern")?, src)?,
                atomic: false,
            });
        }
        None
    }
}

fn has_mut(n: Node) -> bool {
    nodes(n).iter().any(|n| n.kind() == "mutable_specifier")
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Index,
    Name,
    Path,
}

enum Edge {
    Exit,
    Fallthrough(bool),
}

struct Probe<'t, 's> {
    src: &'s str,
    function: Node<'t>,
    block: Node<'t>,
    counter: Counter<'s>,
    keys: BTreeMap<&'s str, Key>,
}

impl<'t, 's> Probe<'t, 's> {
    fn t(&self, n: Node) -> String {
        squash(text(n, self.src))
    }

    fn binding(&self, n: Node<'t>) -> Option<(&'s str, Node<'t>)> {
        (n.kind() == "let_declaration"
            && !has_mut(n)
            && n.child_by_field_name("alternative").is_none())
        .then_some(())?;
        Some((
            ident(n.child_by_field_name("pattern")?, self.src)?,
            n.child_by_field_name("value")?,
        ))
    }

    fn fetch(&self, n: Node) -> bool {
        method_call(n, self.src).is_some_and(|(receiver, method, args)| {
            method == "fetch_add"
                && ident(receiver, self.src) == Some(self.counter.name)
                && matches!(args[..], [step, ordering] if self.t(step) == "1"
                    && ordering.kind() == "scoped_identifier")
        })
    }

    fn step(&self, n: Node) -> bool {
        if self.counter.atomic {
            return false;
        }
        (n.kind() == "compound_assignment_expr"
            && n.child_by_field_name("operator")
                .is_some_and(|op| op.kind() == "+=")
            && n.child_by_field_name("left")
                .zip(n.child_by_field_name("right"))
                .is_some_and(|(left, right)| self.counter_step(left, right)))
            || (n.kind() == "assignment_expression"
                && n.child_by_field_name("left")
                    .and_then(|left| ident(left, self.src))
                    == Some(self.counter.name)
                && n.child_by_field_name("right")
                    .and_then(|right| binary(right, "+"))
                    .is_some_and(|(left, right)| self.counter_step(left, right)))
    }

    fn counter_step(&self, left: Node, right: Node) -> bool {
        ident(left, self.src) == Some(self.counter.name) && self.t(right) == "1"
    }

    fn named_key(&self, name: &str) -> Option<Key> {
        if !self.counter.atomic && name == self.counter.name {
            Some(Key::Index)
        } else {
            self.keys.get(name).copied()
        }
    }

    fn key(&self, n: Node<'t>) -> Option<Key> {
        match n.kind() {
            "identifier" => self.named_key(ident(n, self.src)?),
            "reference_expression" if !has_mut(n) => self.key(n.child_by_field_name("value")?),
            "parenthesized_expression" => self.key(n.named_child(0)?),
            "macro_invocation" => self.format_name(n).map(|()| Key::Name),
            "call_expression" => {
                let (receiver, method, args) = method_call(n, self.src)?;
                let [name] = args[..] else { return None };
                (method == "join"
                    && self.path_parameter(receiver)
                    && self.key(name) == Some(Key::Name))
                .then_some(Key::Path)
            }
            _ => None,
        }
    }

    fn path_parameter(&self, n: Node) -> bool {
        let Some(name) = ident(n, self.src) else {
            return false;
        };
        !self.keys.contains_key(name)
            && !statements(self.block).iter().any(|n| {
                n.child_by_field_name("pattern")
                    .is_some_and(|p| references(p, name, self.src))
            })
            && self
                .function
                .child_by_field_name("parameters")
                .is_some_and(|parameters| {
                    nodes(parameters).iter().any(|param| {
                        param
                            .child_by_field_name("pattern")
                            .and_then(|p| ident(p, self.src))
                            == Some(name)
                            && param.child_by_field_name("type").is_some_and(|ty| {
                                match self.t(ty).as_str() {
                                    "&std::path::Path" | "&::std::path::Path" => true,
                                    "&Path" => {
                                        std::iter::successors(Some(self.block), |n| n.parent()).any(
                                            |scope| {
                                                imports_symbol(scope, "std::path", "Path", self.src)
                                            },
                                        )
                                    }
                                    _ => false,
                                }
                            })
                    })
                })
    }

    fn format_name(&self, n: Node<'t>) -> Option<()> {
        let callee = n.child_by_field_name("macro")?;
        if !matches!(
            self.t(callee).as_str(),
            "format" | "std::format" | "::std::format"
        ) {
            return None;
        }
        let tree = nodes(n).into_iter().find(|n| n.kind() == "token_tree")?;
        let tokens = children(tree);
        let [_, literal, args @ .., _] = &tokens[..] else {
            return None;
        };
        let mut format = text(*literal, self.src)
            .strip_prefix('"')?
            .strip_suffix('"')?;
        let parts = args.split(|n| n.kind() == ",").collect::<Vec<_>>();
        let [[], parts @ ..] = parts.as_slice() else {
            return None;
        };
        let mut arguments = parts.iter().copied().filter(|part| !part.is_empty());
        let mut index = false;
        while let Some((prefix, rest)) = format.split_once('{') {
            let (field, suffix) = rest.split_once('}')?;
            if !component(prefix) {
                return None;
            }
            if field.is_empty() {
                let arg = arguments.next()?;
                let value = squash(
                    self.src
                        .get(arg.first()?.start_byte()..arg.last()?.end_byte())?,
                );
                if self.named_key(&value) == Some(Key::Index) {
                    index = true;
                } else if !matches!(
                    value.as_str(),
                    "std::process::id()" | "::std::process::id()"
                ) {
                    return None;
                }
            } else if self.named_key(field) == Some(Key::Index) {
                index = true;
            } else if !self.fixed_component(field) {
                return None;
            }
            format = suffix;
        }
        (index && component(format) && arguments.next().is_none()).then_some(())
    }

    fn fixed_component(&self, name: &str) -> bool {
        !name.is_empty()
            && !self.keys.contains_key(name)
            && !references(self.function, name, self.src)
            && std::iter::successors(self.function.parent(), |n| n.parent()).any(|scope| {
                matches!(scope.kind(), "declaration_list" | "source_file")
                    && nodes(scope).iter().any(|n| {
                        n.kind() == "const_item"
                            && n.child_by_field_name("name")
                                .and_then(|n| ident(n, self.src))
                                == Some(name)
                            && n.child_by_field_name("value").is_some_and(|n| {
                                text(n, self.src)
                                    .strip_prefix('"')
                                    .and_then(|s| s.strip_suffix('"'))
                                    .is_some_and(component)
                            })
                    })
            })
    }

    fn collision(
        &self,
        matched: Node<'t>,
        attempt: Node<'t>,
        callee: Node<'t>,
    ) -> Option<Node<'t>> {
        let mut hidden = false;
        walk(matched, &mut |n| {
            if !attempt.byte_range().contains(&n.start_byte()) {
                hidden |= matches!(n.kind(), "macro_invocation" | "unsafe_block")
                    || call(n).is_some_and(|(other, _)| self.t(other) == self.t(callee));
            }
        });
        if hidden {
            return None;
        }
        let mut collision = None;
        for arm in nodes(matched.child_by_field_name("body")?) {
            let pattern = arm.child_by_field_name("pattern")?;
            let value = arm.child_by_field_name("value")?;
            if !terminal(value) {
                let tag = pattern.named_child(0)?;
                let [err, binding] = nodes(tag)[..] else {
                    return None;
                };
                let error = ident(binding, self.src)?;
                let (kind, exists) = binary(pattern.child_by_field_name("condition")?, "==")?;
                if tag.kind() != "tuple_struct_pattern"
                    || ident(err, self.src) != Some("Err")
                    || error == self.counter.name
                    || self.t(kind) != format!("{error}.kind()")
                    || !matches!(
                        self.t(exists).as_str(),
                        "ErrorKind::AlreadyExists"
                            | "std::io::ErrorKind::AlreadyExists"
                            | "::std::io::ErrorKind::AlreadyExists"
                    )
                    || collision.replace(value).is_some()
                {
                    return None;
                }
            } else if references(arm, self.counter.name, self.src) {
                return None;
            }
        }
        collision
    }

    fn collision_path(&self, n: Node, advanced: bool) -> Option<Edge> {
        match n.kind() {
            "block" => {
                let mut advanced = advanced;
                for stmt in statements(n) {
                    match self.collision_path(stmt, advanced)? {
                        Edge::Exit => return Some(Edge::Exit),
                        Edge::Fallthrough(done) => advanced = done,
                    }
                }
                Some(Edge::Fallthrough(advanced))
            }
            "continue_expression" if nodes(n).is_empty() && advanced => Some(Edge::Exit),
            "if_expression" => {
                // A bare boolean condition cannot update the counter or jump.
                ident(n.child_by_field_name("condition")?, self.src)?;
                let yes = self.collision_path(n.child_by_field_name("consequence")?, advanced)?;
                let no = if let Some(otherwise) = n.child_by_field_name("alternative") {
                    self.collision_path(otherwise.named_child(0)?, advanced)?
                } else {
                    Edge::Fallthrough(advanced)
                };
                Some(match (yes, no) {
                    (Edge::Fallthrough(a), Edge::Fallthrough(b)) => Edge::Fallthrough(a && b),
                    (Edge::Exit, other) | (other, Edge::Exit) => other,
                })
            }
            _ if self.step(n) => Some(Edge::Fallthrough(true)),
            _ => None,
        }
    }
}

fn component(s: &str) -> bool {
    s.bytes()
        .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-'))
}

fn terminal(n: Node) -> bool {
    if n.kind() == "block" {
        return statements(n).split_last().is_some_and(|(&last, prefix)| {
            exits_loop(last) && prefix.iter().copied().all(falls_through)
        });
    }
    exits_loop(n)
}
