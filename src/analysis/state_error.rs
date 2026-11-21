//! Question 9 for bookkeeping that survives an error from a Rust &mut self method.

use super::Analysis;
use crate::facts::Lang;
use crate::lang::{lang_of, line, named_children, python::walk, text};
use crate::report::{Finding, Verdict};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use tree_sitter::{Node, Parser};

impl Analysis<'_> {
    pub(super) fn error_keeps_state(&mut self) {
        let mut methods = BTreeMap::<_, BTreeSet<_>>::new();
        for func in &self.f.funcs {
            if !func.test
                && func.class.is_some()
                && func.params.first().is_some_and(|p| p.name == "self")
                && self.f.files[func.file as usize].lang == Lang::Rust
            {
                methods
                    .entry(func.file as usize)
                    .or_default()
                    .insert(func.line);
            }
        }
        let mut parser = Parser::new();
        if parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .is_err()
        {
            return;
        }
        let texts = self
            .texts
            .iter()
            .filter(|(p, _)| lang_of(Path::new(p)).is_some());
        for (id, ((path, src), file)) in texts.zip(&self.f.files).enumerate() {
            if file.path != *path || !src.contains('?') && !src.contains("Err") {
                continue;
            }
            let Some(lines) = methods.get(&id) else {
                continue;
            };
            let Some(tree) = parser.parse(src, None) else {
                continue;
            };
            walk(tree.root_node(), &mut |node| {
                if node.kind() == "function_item"
                    && lines.contains(&line(node))
                    && let Some(finding) = inspect(path, src, &self.repo_of_file[id], node)
                {
                    self.findings.push(finding);
                }
            });
        }
    }
}

const MUTATORS: &[&str] = &[
    "push",
    "push_back",
    "push_str",
    "insert",
    "append",
    "append_row",
    "extend",
];
const READS: &[&str] = &["len", "is_empty", "contains", "get", "as_ref", "clone"];

fn inspect(path: &str, src: &str, repo: &str, method: Node) -> Option<Finding> {
    let parameters = method.child_by_field_name("parameters")?;
    let receiver = parameters.named_child(0)?;
    let result = text(method.child_by_field_name("return_type")?, src);
    if receiver.kind() != "self_parameter"
        || receiver.child(0)?.kind() != "&"
        || !named_children(receiver)
            .iter()
            .any(|n| n.kind() == "mutable_specifier")
        || result.split('<').next()?.trim_end().rsplit("::").next() != Some("Result")
    {
        return None;
    }
    let body = method.child_by_field_name("body")?;
    if body.has_error() || !text(body, src).contains('?') && !text(body, src).contains("Err") {
        return None;
    }
    let mut limits = BTreeSet::new();
    let mut increments = BTreeSet::new();
    let mut replacements = BTreeSet::new();
    let mut collections = BTreeSet::new();
    let mut fallible_on_collection = BTreeSet::new();
    walk(body, &mut |node| {
        if node.kind() == "if_expression"
            && let Some(test) = node.child_by_field_name("condition")
            && let Some(branch) = node.child_by_field_name("consequence")
        {
            let mut guarded_writes = BTreeSet::new();
            let mut guards_error = false;
            walk(branch, &mut |part| {
                guarded_writes.extend(target(part, src));
                guards_error |= part.kind() == "try_expression"
                    || part.kind() == "call_expression" && constructor(part, src) == Some("Err");
            });
            walk(test, &mut |part| {
                if part.kind() == "binary_expression"
                    && part.child_by_field_name("operator").is_some_and(|op| {
                        matches!(op.kind(), "<" | "<=" | ">" | ">=" | "==" | "!=")
                    })
                {
                    for side in ["left", "right"] {
                        limits.extend(
                            part.child_by_field_name(side)
                                .and_then(|n| field(n, src))
                                .filter(|name| guards_error || guarded_writes.contains(name)),
                        );
                    }
                }
            });
        }
        if let Some(target) = target(node, src) {
            if node.kind() == "assignment_expression" {
                replacements.insert(target);
            } else if node
                .child_by_field_name("operator")
                .is_some_and(|op| matches!(op.kind(), "+=" | "-="))
            {
                increments.insert(target);
            }
        }
        if let Some((receiver, name, _)) = member_call(node, src)
            && MUTATORS.contains(&name)
            && let Some(target) = field(receiver, src)
        {
            collections.insert(target);
        }
        if node.kind() == "try_expression"
            && let Some(operand) = node.named_child(0)
        {
            let (operation, _) = fallible_call(operand, src);
            if let Some((receiver, name, _)) = member_call(operation, src)
                && !MUTATORS.contains(&name)
            {
                fallible_on_collection.extend(field(receiver, src));
            }
        }
    });
    // A bounded count that resets or accompanies a collection update is working state.
    // An attempt count or a flag set during a terminal state transition can outlive a refusal.
    let counters: BTreeSet<_> = increments
        .intersection(&limits)
        .copied()
        .filter(|name| {
            replacements.contains(*name)
                || !collections.is_empty()
                    && fallible_on_collection
                        .iter()
                        .any(|f| collections.contains(f))
        })
        .collect();
    let buffers = collections.intersection(&fallible_on_collection);
    if counters.is_empty() && buffers.clone().next().is_none() {
        return None;
    }
    let mut inputs = BTreeMap::new();
    for parameter in named_children(parameters) {
        if let Some(pattern) = parameter.child_by_field_name("pattern") {
            let input = if named_children(parameter)
                .iter()
                .any(|n| n.kind() == "mutable_specifier")
            {
                Input::Unknown
            } else {
                Input::Own
            };
            bind_input(pattern, src, &mut inputs, input);
        }
    }
    let mut best = None::<Finding>;
    let mut batches = Vec::new();
    walk(body, &mut |node| {
        if let Some(batch) = Batch::at_reset(node, src)
            && target(batch.reset, src).is_some_and(|name| counters.contains(name))
            && buffers.clone().any(|name| *name == batch.buffer)
        {
            batches.push(batch);
        }
    });
    for &name in counters.iter().chain(buffers) {
        if name.split('_').any(|part| {
            matches!(
                part,
                "metric" | "metrics" | "stat" | "stats" | "telemetry" | "log" | "logs"
            )
        }) {
            continue;
        }
        let mut flow = Flow {
            src,
            name,
            error: None,
            write: None,
            restored: None,
            completed: None,
            batches: &batches,
            finding: None,
            budget: 256,
            exhausted: None,
        };
        flow.eval(
            body,
            State {
                inputs: inputs.clone(),
                ..State::default()
            },
            true,
        );
        if let Some(at) = flow.exhausted {
            flow.record(
                Verdict::Unknown,
                at,
                flow.write.unwrap_or(at),
                "the path budget was exhausted",
            );
        }
        let (verdict, at, write, reason) = match flow.finding {
            Some(evidence) => evidence,
            None if flow.error.is_some() => {
                let Some(write) = flow.write else { continue };
                let (site, write, reason) = if let Some((_, write, error)) = flow.completed {
                    (
                        error,
                        write,
                        "the error can keep only bookkeeping for a completed operation on earlier input",
                    )
                } else if flow.restored.is_some() {
                    (
                        write,
                        write,
                        "the error path restores the saved entry value, or returns before editing it",
                    )
                } else {
                    (
                        write,
                        write,
                        "the modeled errors return before the field is edited",
                    )
                };
                (Verdict::Proven, site, write, reason)
            }
            None => continue,
        };
        let loc = |n| format!("{path}:{}", line(n));
        let mut witness = vec![format!("{} changes `self.{name}`", loc(write))];
        match verdict {
            Verdict::Violated => witness.push(format!("{} can return an error", loc(at))),
            Verdict::Unknown => {
                if at == write {
                    witness.clear();
                }
                witness.push(format!("{} {reason}", loc(at)));
            }
            Verdict::Proven => {
                if let Some((operation, _, error)) = flow.completed {
                    witness.push(format!(
                        "{} completes work for earlier calls",
                        loc(operation)
                    ));
                    witness.push(format!("{} can return an error on this call", loc(error)));
                } else if let Some(restore) = flow.restored {
                    witness.push(format!("{} restores the saved value", loc(restore)));
                } else if let Some(error) = flow.error {
                    witness.push(format!(
                        "{} returns an error before editing the field",
                        loc(error)
                    ));
                }
            }
        }
        let mut assumptions = vec![
            "direct fields are independent and recognized reads and collection edits have their usual effects".into(),
            "effects through interior mutability, custom operators and destructors are outside the model".into(),
        ];
        if verdict == Verdict::Proven {
            assumptions.push(reason.into());
            if flow.completed.is_some() {
                assumptions.extend([
                    "the changes kept on the error path carry none of the method's arguments".into(),
                    "each bookkeeping field write follows the successful `?` of the operation it records".into(),
                    "a completed call on state from earlier calls is not undone by a later error of this call".into(),
                    "validation is read-only, and a refused flush or insertion leaves the buffer intact".into(),
                ]);
            }
        }
        let finding = Finding {
            question: 9,
            rule: "error-keeps-state",
            verdict,
            repo: repo.into(),
            site: loc(at),
            message: format!("`self.{name}`: {reason}"),
            witness,
            assumptions,
        };
        if best
            .as_ref()
            .is_none_or(|prev| finding.verdict > prev.verdict)
        {
            best = Some(finding);
        }
    }
    best
}

#[derive(Clone, Default)]
struct State<'a> {
    changed: Option<(Change, Node<'a>)>,
    restored: Option<Node<'a>>,
    saved: BTreeSet<&'a str>,
    inputs: BTreeMap<&'a str, Input>,
    checks: Vec<(&'a str, &'a str)>,
    opaque: Option<(Node<'a>, &'static str)>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Input {
    Independent,
    Unknown,
    Own,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Change {
    Completed,
    UnknownInput,
    Other,
    OwnInput,
}

impl From<Input> for Change {
    fn from(input: Input) -> Self {
        match input {
            Input::Independent => Self::Other,
            Input::Unknown => Self::UnknownInput,
            Input::Own => Self::OwnInput,
        }
    }
}

type Evidence<'a> = (Verdict, Node<'a>, Node<'a>, &'static str);

struct Flow<'a> {
    src: &'a str,
    name: &'a str,
    error: Option<Node<'a>>,
    write: Option<Node<'a>>,
    restored: Option<Node<'a>>,
    completed: Option<(Node<'a>, Node<'a>, Node<'a>)>,
    batches: &'a [Batch<'a>],
    finding: Option<Evidence<'a>>,
    budget: usize,
    exhausted: Option<Node<'a>>,
}

impl<'a> Flow<'a> {
    fn eval(&mut self, node: Node<'a>, mut state: State<'a>, tail: bool) -> Vec<State<'a>> {
        if self.budget == 0 {
            self.exhausted.get_or_insert(node);
            return vec![];
        }
        let src = self.src;
        let children = || named_children(node).into_iter().filter(|n| !n.is_extra());
        match node.kind() {
            "block" | "expression_statement" | "else_clause" | "parenthesized_expression" => {
                let outer = state.clone();
                let nodes: Vec<_> = children().collect();
                let mut paths = self.sequence(&nodes, vec![state], tail);
                if node.kind() == "block" {
                    for path in &mut paths {
                        path.leave_scope(&outer);
                    }
                }
                paths
            }
            "if_expression" | "match_expression" => {
                self.budget -= 1;
                let is_if = node.kind() == "if_expression";
                let arms = (!is_if)
                    .then(|| node.child_by_field_name("body").map(named_children))
                    .flatten()
                    .unwrap_or_default();
                let guard = arms.iter().find_map(|arm| {
                    arm.child_by_field_name("pattern")?
                        .child_by_field_name("condition")
                });
                let subject = node.child_by_field_name(if is_if { "condition" } else { "value" });
                let paths = subject.map_or_else(
                    || vec![state.clone()],
                    |n| self.eval(n, state.clone(), false),
                );
                let mut next = vec![];
                for path in paths {
                    if is_if {
                        for (branch, excluded) in
                            [("consequence", "false"), ("alternative", "true")]
                        {
                            if subject.is_none_or(|n| text(n, src) != excluded) {
                                if let Some(b) = node.child_by_field_name(branch) {
                                    let mut branch_state = path.clone();
                                    if branch == "consequence"
                                        && let Some(condition) = subject
                                    {
                                        walk(condition, &mut |n| {
                                            if n.kind() == "let_condition"
                                                && let Some(pattern) =
                                                    n.child_by_field_name("pattern")
                                            {
                                                self.shadow(pattern, &mut branch_state);
                                            }
                                        });
                                    }
                                    next.extend(self.branch(b, branch_state, &path, tail));
                                } else {
                                    next.push(path.clone());
                                }
                            }
                        }
                    } else {
                        for arm in &arms {
                            if let Some(value) = arm.child_by_field_name("value") {
                                let mut arm_state = path.clone();
                                if let Some(pattern) = arm.child_by_field_name("pattern") {
                                    self.shadow(pattern, &mut arm_state);
                                }
                                if let Some(guard) = guard {
                                    arm_state
                                        .obscure(guard, "a match guard may change the error path");
                                    if text(guard, src).contains('?') {
                                        self.unknown(
                                            guard,
                                            &arm_state,
                                            "a match guard may return an error",
                                        );
                                    }
                                }
                                next.extend(self.branch(value, arm_state, &path, tail));
                            }
                        }
                    }
                }
                next
            }
            "let_declaration" => {
                let value = node.child_by_field_name("value");
                let mut paths = match value {
                    Some(value) => self.eval(value, state, false),
                    None => vec![state],
                };
                if let Some(otherwise) = node.child_by_field_name("alternative") {
                    for path in &paths {
                        self.eval(otherwise, path.clone(), false);
                    }
                }
                if let Some(pattern) = node.child_by_field_name("pattern") {
                    for path in &mut paths {
                        let input = if children().any(|n| n.kind() == "mutable_specifier") {
                            Input::Unknown
                        } else {
                            value.map_or(Input::Unknown, |value| path.input(value, src))
                        };
                        self.shadow(pattern, path);
                        bind_input(pattern, src, &mut path.inputs, input);
                        if pattern.kind() == "identifier"
                            && !children().any(|n| n.kind() == "mutable_specifier")
                            && value.and_then(|v| field(v, src)) == Some(self.name)
                            && path.changed.is_none()
                            && path.opaque.is_none()
                        {
                            path.saved.insert(text(pattern, src));
                        }
                    }
                }
                paths
            }
            "assignment_expression" | "compound_assignment_expr" => {
                let Some(value) = node.child_by_field_name("right") else {
                    return vec![state];
                };
                let mut paths = self.eval(value, state, false);
                if target(node, src) == Some(self.name) {
                    for path in &mut paths {
                        if node.kind() == "assignment_expression"
                            && path.saved.contains(text(value, src))
                        {
                            path.restore(node);
                        } else if node.kind() != "assignment_expression"
                            || field(value, src) != Some(self.name)
                        {
                            let change = if self.batches.iter().any(|batch| batch.reset == node) {
                                Change::Completed
                            } else {
                                let input = path.input(value, src);
                                let recorded = previous_statement(node)
                                    .and_then(|stmt| try_statement(stmt, src))
                                    .and_then(|operation| member_call(operation, src))
                                    .filter(|(receiver, name, _)| {
                                        field(*receiver, src).is_some() && MUTATORS.contains(name)
                                    })
                                    .map_or(Input::Independent, |(_, _, args)| {
                                        path.input(args, src)
                                    });
                                input.max(recorded).into()
                            };
                            self.change(path, node, change);
                        }
                    }
                } else if node
                    .child_by_field_name("left")
                    .is_some_and(|place| affects_field(place, src, self.name))
                {
                    for path in &mut paths {
                        path.obscure(node, "an indirect write may change or restore this field");
                    }
                } else if let Some(place) = node.child_by_field_name("left")
                    && place.kind() == "identifier"
                {
                    for path in &mut paths {
                        path.inputs.insert(text(place, src), Input::Unknown);
                    }
                }
                paths
            }
            "try_expression" => {
                let Some(operand) = node.named_child(0) else {
                    return vec![state];
                };
                let (operation, callback) = fallible_call(operand, src);
                let paths = self.sequence(&named_children(operation), vec![state], false);
                let mut next = vec![];
                for mut path in paths {
                    let mut failure = path.clone();
                    let mut checked = false;
                    if let Some((receiver, name, args)) = member_call(operation, src)
                        && let Some(receiver) = field(receiver, src)
                    {
                        let args = text(args, src);
                        checked =
                            MUTATORS.contains(&name) && path.checks.contains(&(receiver, args));
                        if name.starts_with("check_") || name.starts_with("validate_") {
                            path.checks.push((receiver, args));
                        }
                    }
                    let batch_step = self.batches.iter().find(|batch| {
                        (operation == batch.check
                            || operation == batch.flush
                            || operation == batch.take)
                            && batch.arguments_are_known(&path, src)
                    });
                    let summarize = batch_step.is_some_and(|batch| batch.buffer == self.name);
                    if !summarize {
                        self.note_call(operation, &mut failure, false);
                    }
                    if let Some(callback) = callback {
                        self.map_error(callback, &mut failure);
                    }
                    self.exit(node, &failure, batch_step.filter(|_| checked), checked);
                    match batch_step {
                        Some(batch) if summarize && operation == batch.flush => {
                            self.change(&mut path, operation, Change::Completed);
                        }
                        Some(batch) if summarize && operation == batch.check => {}
                        _ => self.note_call(operation, &mut path, true),
                    }
                    next.push(path);
                }
                next
            }
            "return_expression" => {
                if let Some(value) = node.named_child(0) {
                    self.eval(value, state, true);
                }
                vec![]
            }
            "call_expression" => {
                let mut paths = self.sequence(&named_children(node), vec![state], false);
                for path in &mut paths {
                    match constructor(node, src) {
                        Some("Err") if tail => self.exit(node, path, None, false),
                        Some("Ok") if tail => {}
                        _ => {
                            self.note_call(node, path, true);
                            if tail {
                                self.unknown(
                                    node,
                                    path,
                                    "the returned Result comes from another call",
                                );
                            }
                        }
                    }
                }
                paths
            }
            "binary_expression"
                if !node
                    .child_by_field_name("operator")
                    .is_some_and(|op| matches!(op.kind(), "&&" | "||")) =>
            {
                self.sequence(&named_children(node), vec![state], false)
            }
            "for_expression" | "while_expression" | "loop_expression" | "try_block"
            | "macro_invocation" | "async_block" | "binary_expression" | "let_chain" => {
                let code = text(node, src);
                let mut write = None;
                walk(node, &mut |n| {
                    if target(n, src) == Some(self.name)
                        || member_call(n, src).is_some_and(|(receiver, name, _)| {
                            field(receiver, src) == Some(self.name) && MUTATORS.contains(&name)
                        })
                    {
                        write.get_or_insert(n);
                    }
                });
                if let Some(write) = write {
                    self.change(&mut state, write, Change::UnknownInput);
                }
                if (code.contains('?') || code.contains("Err") || code.contains("bail!"))
                    && (state.changed.is_some() || code.contains(self.name))
                {
                    self.unknown(
                        node,
                        &state,
                        "an error inside an unmodeled expression may keep this change",
                    );
                }
                if code.contains("self") && (code.contains(self.name) || code.contains("self.")) {
                    state.obscure(
                        node,
                        "an unmodeled expression may change or restore this field",
                    );
                }
                vec![state]
            }
            "reference_expression" => {
                if children().any(|n| n.kind() == "mutable_specifier")
                    && node
                        .child_by_field_name("value")
                        .is_some_and(|v| affects_field(v, src, self.name))
                {
                    state.obscure(
                        node,
                        "a mutable borrow may let a helper or guard change this field",
                    );
                }
                self.sequence(&named_children(node), vec![state], false)
            }
            "identifier" | "field_expression" if tail => {
                self.unknown(node, &state, "the returned Result was not traced");
                vec![state]
            }
            "closure_expression" => {
                if text(node, src).contains("self") {
                    state.obscure(node, "a closure may change or restore this field");
                }
                vec![state]
            }
            "function_item" => vec![state],
            _ => {
                let nodes: Vec<_> = children().collect();
                self.sequence(&nodes, vec![state], false)
            }
        }
    }

    fn sequence(
        &mut self,
        nodes: &[Node<'a>],
        mut paths: Vec<State<'a>>,
        tail: bool,
    ) -> Vec<State<'a>> {
        for (i, &node) in nodes.iter().enumerate() {
            paths = paths
                .into_iter()
                .flat_map(|p| self.eval(node, p, tail && i + 1 == nodes.len()))
                .collect();
        }
        paths
    }

    fn change(&mut self, state: &mut State<'a>, node: Node<'a>, change: Change) {
        self.write.get_or_insert(node);
        // An unresolved edit cannot erase evidence of an earlier, unrolled-back change.
        if state.changed.is_none_or(|(previous, _)| change > previous) {
            state.changed = Some((change, node));
        }
    }

    fn branch(
        &mut self,
        node: Node<'a>,
        state: State<'a>,
        outer: &State<'a>,
        tail: bool,
    ) -> Vec<State<'a>> {
        let mut paths = self.eval(node, state, tail);
        for path in &mut paths {
            path.leave_scope(outer);
        }
        paths
    }

    fn shadow(&self, pattern: Node, state: &mut State<'a>) {
        walk(pattern, &mut |part| {
            if part.kind() == "identifier" {
                let name = text(part, self.src);
                state.saved.remove(name);
                state.inputs.insert(name, Input::Unknown);
            }
        });
    }

    fn note_call(&mut self, node: Node<'a>, state: &mut State<'a>, succeeded: bool) {
        if node
            .child_by_field_name("arguments")
            .is_some_and(|args| named_children(args).iter().any(|arg| arg.kind() == "self"))
        {
            state.obscure(
                node,
                "a callee taking self may change or restore this field",
            );
        }
        let Some((receiver, name, args)) = member_call(node, self.src) else {
            return;
        };
        let on_field = field(receiver, self.src) == Some(self.name);
        if on_field && MUTATORS.contains(&name) {
            if succeeded {
                self.change(state, node, state.input(args, self.src).into());
            } else {
                state.obscure(
                    node,
                    "the fallible collection edit may change the field before returning an error",
                );
            }
        } else if affects_field(receiver, self.src, self.name)
            && (receiver.kind() == "self" || !READS.contains(&name))
        {
            state.obscure(
                node,
                "a call on this object or field may change or restore it",
            );
        }
    }

    fn map_error(&self, callback: Node<'a>, failure: &mut State<'a>) {
        let Some(body) = callback.child_by_field_name("body") else {
            failure.obscure(callback, "the error mapper's effects are unavailable");
            return;
        };
        let statements: Vec<_> = named_children(body)
            .into_iter()
            .filter(|n| !n.is_extra())
            .collect();
        if let [stmt, end] = statements.as_slice()
            && end.kind() == "identifier"
            && let Some(assign) = stmt.named_child(0)
            && assign.kind() == "assignment_expression"
            && target(assign, self.src) == Some(self.name)
            && let Some(value) = assign.child_by_field_name("right")
            && failure.saved.contains(text(value, self.src))
            && callback
                .child_by_field_name("parameters")
                .is_some_and(|params| {
                    !text(params, self.src)
                        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                        .any(|part| part == text(value, self.src))
                })
        {
            failure.restore(assign);
        } else if text(body, self.src).contains("self") {
            failure.obscure(
                callback,
                "the error mapper may change or restore this field",
            );
        }
    }

    fn exit(&mut self, at: Node<'a>, state: &State<'a>, batch: Option<&Batch<'a>>, checked: bool) {
        self.error.get_or_insert(at);
        let write = state.changed.map(|(_, write)| write);
        if let Some((operation, reason)) = state.opaque {
            self.record(
                Verdict::Unknown,
                operation,
                write.unwrap_or(operation),
                reason,
            );
        } else if let Some((change, write)) = state.changed {
            if let Some(batch) = batch
                && change == Change::Completed
                && (write == batch.reset || write == batch.flush)
            {
                self.completed.get_or_insert((batch.flush, write, at));
            } else if change == Change::UnknownInput {
                self.unknown(
                    at,
                    state,
                    "argument flow into the earlier change is unknown",
                );
            } else if checked && change != Change::OwnInput {
                self.unknown(
                    at,
                    state,
                    "an earlier check on the same receiver and arguments may rule out this error",
                );
            } else {
                self.record(
                    Verdict::Violated,
                    at,
                    write,
                    "an error can return with the earlier change still in place",
                );
            }
        } else if state.restored.is_some() {
            self.restored = state.restored;
        }
    }

    fn unknown(&mut self, at: Node<'a>, state: &State<'a>, reason: &'static str) {
        if let Some(write) = state
            .changed
            .map(|(_, write)| write)
            .or(state.opaque.map(|(n, _)| n))
        {
            self.record(Verdict::Unknown, at, write, reason);
        }
    }

    fn record(&mut self, verdict: Verdict, at: Node<'a>, write: Node<'a>, reason: &'static str) {
        if self.finding.as_ref().is_none_or(|f| verdict > f.0) {
            self.finding = Some((verdict, at, write, reason));
        }
    }
}

impl<'a> State<'a> {
    fn input(&self, node: Node, src: &str) -> Input {
        match node.kind() {
            "identifier" => self
                .inputs
                .get(text(node, src))
                .copied()
                .unwrap_or(Input::Unknown),
            "integer_literal" | "float_literal" | "boolean_literal" | "char_literal"
            | "string_literal" | "raw_string_literal" | "unit_expression" => Input::Independent,
            "arguments"
            | "parenthesized_expression"
            | "tuple_expression"
            | "array_expression"
            | "binary_expression"
            | "field_expression" => named_children(node)
                .into_iter()
                .filter(|n| !n.is_extra() && n.kind() != "field_identifier")
                .map(|part| self.input(part, src))
                .max()
                .unwrap_or(Input::Independent),
            "call_expression" => member_call(node, src)
                .filter(|(_, name, args)| {
                    matches!(*name, "to_vec" | "to_owned" | "clone")
                        && args.named_child_count() == 0
                })
                .map_or(Input::Unknown, |(receiver, _, _)| self.input(receiver, src)),
            _ => Input::Unknown,
        }
    }

    fn leave_scope(&mut self, outer: &Self) {
        self.saved.clone_from(&outer.saved);
        self.inputs.clone_from(&outer.inputs);
    }

    fn restore(&mut self, at: Node<'a>) {
        if self.changed.take().is_some() || self.opaque.is_some() {
            self.restored = Some(at);
        }
        self.opaque = None;
    }

    fn obscure(&mut self, at: Node<'a>, reason: &'static str) {
        self.opaque = Some((at, reason));
    }
}

fn bind_input<'a>(
    pattern: Node,
    src: &'a str,
    inputs: &mut BTreeMap<&'a str, Input>,
    input: Input,
) {
    if pattern.kind() == "identifier" {
        inputs.insert(text(pattern, src), input);
    } else {
        walk(pattern, &mut |part| {
            if matches!(part.kind(), "identifier" | "shorthand_field_identifier") {
                inputs.insert(text(part, src), Input::Unknown);
            }
        });
    }
}

struct Batch<'a> {
    buffer: &'a str,
    check: Node<'a>,
    flush: Node<'a>,
    reset: Node<'a>,
    take: Node<'a>,
    arguments: Node<'a>,
}

impl<'a> Batch<'a> {
    fn at_reset(reset: Node<'a>, src: &'a str) -> Option<Self> {
        // The guard, flush and reset share a branch, and the insertion follows that branch.
        if reset.kind() != "assignment_expression"
            || target(reset, src).is_none()
            || text(reset.child_by_field_name("right")?, src) != "0"
        {
            return None;
        }
        let flush_stmt = previous_statement(reset)?;
        let flush = try_statement(flush_stmt, src)?;
        let (receiver, name, args) = member_call(flush, src)?;
        let buffer = field(receiver, src)?;
        if name != "flush" || args.named_child_count() != 0 {
            return None;
        }
        let check_stmt = adjacent_statement(flush_stmt, false)?;
        let reset_stmt = reset.parent()?;
        if adjacent_statement(check_stmt, false).is_some()
            || adjacent_statement(reset_stmt, true).is_some()
        {
            return None;
        }
        let check = try_statement(check_stmt, src)?;
        let (receiver, name, checked) = member_call(check, src)?;
        if field(receiver, src) != Some(buffer)
            || !(name.starts_with("check_") || name.starts_with("validate_"))
        {
            return None;
        }
        let block = reset_stmt.parent()?;
        let branch = block.parent()?;
        if branch.kind() != "if_expression"
            || branch.child_by_field_name("consequence") != Some(block)
            || branch.child_by_field_name("alternative").is_some()
        {
            return None;
        }
        let take = try_statement(adjacent_statement(branch.parent()?, true)?, src)?;
        let (receiver, name, arguments) = member_call(take, src)?;
        (field(receiver, src) == Some(buffer)
            && MUTATORS.contains(&name)
            && text(arguments, src) == text(checked, src)
            && named_children(arguments)
                .iter()
                .all(|arg| arg.kind() == "identifier"))
        .then_some(Self {
            buffer,
            check,
            flush,
            reset,
            take,
            arguments,
        })
    }

    fn arguments_are_known(&self, state: &State, src: &str) -> bool {
        named_children(self.arguments)
            .into_iter()
            .all(|arg| state.input(arg, src) != Input::Unknown)
    }
}

fn previous_statement(expression: Node) -> Option<Node> {
    let statement = expression.parent()?;
    (statement.kind() == "expression_statement")
        .then(|| adjacent_statement(statement, false))
        .flatten()
}

fn adjacent_statement(mut node: Node, next: bool) -> Option<Node> {
    loop {
        node = if next {
            node.next_named_sibling()?
        } else {
            node.prev_named_sibling()?
        };
        if !node.is_extra() {
            return Some(node);
        }
    }
}

fn try_statement<'a>(statement: Node<'a>, src: &str) -> Option<Node<'a>> {
    let expression = statement.named_child(0)?;
    if statement.kind() != "expression_statement" || expression.kind() != "try_expression" {
        return None;
    }
    let (operation, callback) = fallible_call(expression.named_child(0)?, src);
    callback.is_none().then_some(operation)
}

fn affects_field(mut place: Node, src: &str, name: &str) -> bool {
    loop {
        if place.kind() == "self" || field(place, src) == Some(name) {
            return true;
        }
        if field(place, src).is_some() {
            return false;
        }
        let parent = match place.kind() {
            "field_expression" => place.child_by_field_name("value"),
            "index_expression" | "parenthesized_expression" | "unary_expression" => {
                place.named_child(0)
            }
            _ => None,
        };
        let Some(parent) = parent else { return false };
        place = parent;
    }
}

fn field<'a>(n: Node, src: &'a str) -> Option<&'a str> {
    (n.kind() == "field_expression" && n.child_by_field_name("value")?.kind() == "self")
        .then(|| n.child_by_field_name("field").map(|f| text(f, src)))
        .flatten()
}

fn target<'a>(n: Node, src: &'a str) -> Option<&'a str> {
    matches!(
        n.kind(),
        "assignment_expression" | "compound_assignment_expr"
    )
    .then(|| field(n.child_by_field_name("left")?, src))
    .flatten()
}

fn member_call<'a, 'tree>(
    n: Node<'tree>,
    src: &'a str,
) -> Option<(Node<'tree>, &'a str, Node<'tree>)> {
    if n.kind() != "call_expression" {
        return None;
    }
    let function = n.child_by_field_name("function")?;
    Some((
        function.child_by_field_name("value")?,
        text(function.child_by_field_name("field")?, src),
        n.child_by_field_name("arguments")?,
    ))
}

fn constructor<'a>(n: Node, src: &'a str) -> Option<&'a str> {
    text(n.child_by_field_name("function")?, src)
        .rsplit("::")
        .next()
}

fn fallible_call<'tree>(operand: Node<'tree>, src: &str) -> (Node<'tree>, Option<Node<'tree>>) {
    let operand = awaited_value(operand);
    member_call(operand, src)
        .filter(|(_, name, _)| *name == "map_err")
        .map_or((operand, None), |(receiver, _, args)| {
            (awaited_value(receiver), args.named_child(0))
        })
}

fn awaited_value(mut node: Node) -> Node {
    while matches!(node.kind(), "await_expression" | "parenthesized_expression") {
        let Some(inner) = named_children(node).into_iter().find(|n| !n.is_extra()) else {
            break;
        };
        node = inner;
    }
    node
}
