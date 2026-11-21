//! Local retry bounds. Only checks and updates on the loop's own statement list can
//! establish a bound. A back edge that can skip either invalidates that proof.

use super::{children, line, named_children, squash, text};
use crate::facts::{Lang, RetryBound};
use tree_sitter::Node;

pub(super) fn legacy_keyword(src: &str, lang: Lang) -> Option<&'static str> {
    let words: &[&str] = match lang {
        Lang::Rust => &[
            "deadline",
            "attempt",
            "retr",
            "tries",
            "limit",
            "max_",
            "timeout",
            "elapsed",
            "budget",
            "remaining",
            "0..",
        ],
        Lang::Python => &[
            "deadline",
            "attempt",
            "retr",
            "tries",
            "limit",
            "max_",
            "timeout",
            "monotonic",
            "budget",
            "remaining",
            "range(",
        ],
        _ => &[
            "deadline", "attempt", "retr", "tries", "limit", "max", "timeout", "-ge", "-gt", "-lt",
            "-le", "break",
        ],
    };
    let low = src.to_ascii_lowercase();
    words.iter().copied().find(|word| low.contains(word))
}

pub(super) fn fallback(src: &str, lang: Lang) -> RetryBound {
    legacy_keyword(src, lang)
        .map(|word| RetryBound::Keyword(word.into()))
        .unwrap_or(RetryBound::None)
}

pub(super) fn any_local<'tree>(n: Node<'tree>, predicate: &impl Fn(Node<'tree>) -> bool) -> bool {
    if matches!(
        n.kind(),
        "loop_expression"
            | "while_expression"
            | "for_expression"
            | "while_statement"
            | "for_statement"
            | "function_item"
            | "function_definition"
            | "closure_expression"
            | "async_block"
            | "lambda"
    ) {
        return false;
    }
    predicate(n)
        || named_children(n)
            .into_iter()
            .any(|child| any_local(child, predicate))
}

pub(super) fn reads(n: Node, name: &str, src: &str) -> bool {
    n.kind() == "identifier" && text(n, src) == name
        || named_children(n)
            .into_iter()
            .any(|child| reads(child, name, src))
}

pub(super) fn prove(loop_node: Node, src: &str, lang: Lang) -> Option<RetryBound> {
    let body = body(loop_node, lang)?;
    if loop_node.has_error() {
        return None;
    }
    let proof = Loop {
        node: loop_node,
        body,
        statements: statements(body),
        src,
        lang,
    };
    if let Some(range) = proof.range() {
        return Some(range);
    }
    if let Some(cond) = loop_node.child_by_field_name("condition")
        && (lang != Lang::Bash
            || src[cond.end_byte()..body.start_byte()]
                .chars()
                .all(|c| c.is_whitespace() || c == ';'))
        && let Some(bound) = proof.comparison(cond, 0, true)
    {
        return Some(bound);
    }
    for (index, &stmt) in proof.statements.iter().enumerate() {
        if has_continue(stmt, src, lang) {
            break;
        }
        if lang == Lang::Rust
            && let Some(check) = proof.remaining_duration(stmt, index)
        {
            return Some(RetryBound::RemainingDuration(check));
        }
        if let Some(cond) = proof.exiting_guard(stmt)
            && let Some(bound) = proof.comparison(cond, index, false)
        {
            return Some(bound);
        }
    }
    None
}

pub(super) fn nested_rust_deadline(loop_node: Node, arm: Node, src: &str) -> Option<String> {
    let proof = Loop {
        node: loop_node,
        body: body(loop_node, Lang::Rust)?,
        statements: statements(arm),
        src,
        lang: Lang::Rust,
    };
    for (index, &stmt) in proof.statements.iter().enumerate() {
        if has_continue(stmt, src, Lang::Rust) {
            break;
        }
        if let Some(cond) = proof.exiting_guard(stmt)
            && let Some(RetryBound::Deadline(check)) = proof.comparison(cond, index, false)
        {
            return Some(check);
        }
    }
    None
}

pub(super) fn guarded_rust_deadline(
    loop_node: Node,
    matched: Node,
    guards: &[Node],
    src: &str,
) -> Option<RetryBound> {
    let body = body(loop_node, Lang::Rust)?;
    let proof = Loop {
        node: loop_node,
        body,
        statements: statements(body),
        src,
        lang: Lang::Rust,
    };
    let (last, prefix) = proof.statements.split_last()?;
    if *last != matched || prefix.iter().any(|&n| has_continue(n, src, Lang::Rust)) {
        return None;
    }
    let mut checks = Vec::new();
    for guard in guards {
        let check = true_conjuncts(*guard).into_iter().find_map(|n| {
            match proof.comparison(n, prefix.len(), true)? {
                RetryBound::Deadline(check) => Some(check),
                _ => None,
            }
        })?;
        if !checks.contains(&check) {
            checks.push(check);
        }
    }
    (!checks.is_empty()).then(|| RetryBound::Deadline(checks.join(", ")))
}

pub(super) fn true_conjuncts(n: Node) -> Vec<Node> {
    if n.kind() == "parenthesized_expression" {
        return n.named_child(0).map_or_else(Vec::new, true_conjuncts);
    }
    if n.kind() == "binary_expression"
        && n.child_by_field_name("operator")
            .is_some_and(|op| op.kind() == "&&")
        && let (Some(left), Some(right)) = (
            n.child_by_field_name("left"),
            n.child_by_field_name("right"),
        )
    {
        let mut conjuncts = true_conjuncts(left);
        conjuncts.extend(true_conjuncts(right));
        return conjuncts;
    }
    vec![n]
}

struct Loop<'tree, 'src> {
    node: Node<'tree>,
    body: Node<'tree>,
    statements: Vec<Node<'tree>>,
    src: &'src str,
    lang: Lang,
}

#[derive(Clone, Copy, PartialEq)]
enum Direction {
    Up,
    Down,
}

impl Direction {
    fn reversed(self) -> Self {
        match self {
            Self::Up => Self::Down,
            Self::Down => Self::Up,
        }
    }
}

impl<'tree> Loop<'tree, '_> {
    fn t(&self, n: Node) -> String {
        let compact = squash(text(n, self.src));
        if self.lang == Lang::PowerShell {
            compact.to_ascii_lowercase()
        } else {
            compact
        }
    }

    fn range(&self) -> Option<RetryBound> {
        let range = match self.node.kind() {
            "for_expression" => self.node.child_by_field_name("value")?,
            "for_statement" if self.lang == Lang::Python => {
                self.node.child_by_field_name("right")?
            }
            _ => return None,
        };
        let range_text = self.t(range);
        match self.lang {
            Lang::Rust => {
                if range.kind() != "range_expression" {
                    return None;
                }
                let [start, end] = named_children(range)[..] else {
                    return None;
                };
                if ![start, end].into_iter().all(|n| simple(&self.t(n))) {
                    return None;
                }
            }
            Lang::Python => {
                let end = range_text.strip_prefix("range(")?.strip_suffix(')')?;
                if range.kind() != "call" || !simple(end) {
                    return None;
                }
            }
            _ => return None,
        }
        Some(RetryBound::BoundedRange(self.at(range, &range_text)))
    }

    fn at(&self, n: Node, expression: &str) -> String {
        format!("`{expression}` at line {}", line(n))
    }

    fn remaining_duration(&self, stmt: Node<'tree>, index: usize) -> Option<String> {
        let (value, method) = if stmt.kind() == "let_declaration" {
            let pattern = stmt.child_by_field_name("pattern")?;
            if pattern.kind() != "tuple_struct_pattern"
                || self.t(pattern.child_by_field_name("type")?) != "Some"
                || !self.arm_exits(stmt.child_by_field_name("alternative")?)
            {
                return None;
            }
            (
                self.t(stmt.child_by_field_name("value")?),
                "checked_duration_since",
            )
        } else {
            let cond = self.exiting_guard(stmt)?;
            if cond.kind() == "let_condition" {
                if self.t(cond.child_by_field_name("pattern")?) != "None" {
                    return None;
                }
                (
                    self.t(cond.child_by_field_name("value")?),
                    "checked_duration_since",
                )
            } else if let Some((left, op, right)) = operands(cond, self.src, self.lang) {
                let zero = |s: &str| {
                    matches!(
                        s.trim_start_matches("::"),
                        "Duration::ZERO"
                            | "std::time::Duration::ZERO"
                            | "core::time::Duration::ZERO"
                    )
                };
                if op != "==" {
                    return None;
                }
                if zero(&left) {
                    (right, "saturating_duration_since")
                } else if zero(&right) {
                    (left, "saturating_duration_since")
                } else if left == "None" {
                    (right, "checked_duration_since")
                } else if right == "None" {
                    (left, "checked_duration_since")
                } else {
                    return None;
                }
            } else {
                let compact = self.t(cond);
                if let Some(value) = compact.strip_suffix(".is_none()") {
                    (value.to_owned(), "checked_duration_since")
                } else {
                    (
                        compact.strip_suffix(".is_zero()")?.to_owned(),
                        "saturating_duration_since",
                    )
                }
            }
        };
        let operation = format!(".{method}(");
        let is_fresh_remainder = |s: &str| {
            s.split_once(&operation).is_some_and(|(deadline, clock)| {
                variable(deadline, Lang::Rust).is_some()
                    && self.unchanged(deadline, None)
                    && clock.strip_suffix(')').is_some_and(rust_now)
            })
        };
        (is_fresh_remainder(&value)
            || variable(&value, Lang::Rust).is_some_and(|name| {
                self.statements[..index].iter().any(|&decl| {
                    self.initializer(decl, name)
                        .is_some_and(|init| is_fresh_remainder(&init))
                        && self.unchanged(name, Some(decl))
                })
            }))
        .then(|| {
            self.at(
                stmt,
                text(
                    stmt.child_by_field_name("condition").unwrap_or(stmt),
                    self.src,
                )
                .trim(),
            )
        })
    }

    fn exiting_guard(&self, stmt: Node<'tree>) -> Option<Node<'tree>> {
        let kind = match self.lang {
            Lang::Rust => "if_expression",
            _ => "if_statement",
        };
        if stmt.kind() != kind {
            return None;
        }
        let cond = stmt.child_by_field_name("condition")?;
        let arm = match self.lang {
            Lang::Bash => {
                // The grammar gives the then-arm no node of its own.
                let [condition, exit, ..] = named_children(stmt)[..] else {
                    return None;
                };
                if condition != cond || exit.kind() != "command" {
                    return None;
                }
                // An else, or a following statement after an unconditional exit, is harmless.
                // A compound condition has another statement before the then-arm.
                let between = &self.src[cond.end_byte()..exit.start_byte()];
                if !between
                    .trim_matches(|c: char| c.is_whitespace() || c == ';')
                    .eq("then")
                {
                    return None;
                }
                return self.exits(exit).then_some(cond);
            }
            Lang::PowerShell => child_kind(stmt, "statement_block")?,
            _ => stmt.child_by_field_name("consequence")?,
        };
        self.arm_exits(arm).then_some(cond)
    }

    fn arm_exits(&self, arm: Node) -> bool {
        let mut arm = statements(arm);
        let Some(last) = arm.pop() else {
            return false;
        };
        self.exits(last) && !arm.iter().any(|&n| has_continue(n, self.src, self.lang))
    }

    fn exits(&self, n: Node) -> bool {
        match self.lang {
            Lang::Bash => matches!(self.t(n).as_str(), "break" | "exit" | "return"),
            Lang::PowerShell => {
                n.kind() == "flow_control_statement"
                    && matches!(
                        n.child(0).map(|c| c.kind()),
                        Some("break" | "return" | "exit")
                    )
                    && child_kind(n, "label_expression").is_none()
            }
            _ => match n.kind() {
                "break_expression" | "break_statement" => {
                    child_kind(n, "label").is_none()
                        && child_kind(n, "statement_identifier").is_none()
                }
                "return_expression" | "return_statement" | "raise_statement"
                | "throw_statement" => true,
                "try_expression" => n.named_child(0).is_some_and(|value| {
                    let value = self.t(value);
                    value == "None" || value.starts_with("Err(") && value.ends_with(')')
                }),
                _ => false,
            },
        }
    }

    fn comparison(&self, cond: Node, index: usize, loop_condition: bool) -> Option<RetryBound> {
        let (lhs, op, rhs) = operands(cond, self.src, self.lang)?;
        let mut direction = match op.as_str() {
            ">" | ">=" | "-gt" | "-ge" => Direction::Up,
            "<" | "<=" | "-lt" | "-le" => Direction::Down,
            _ => return None,
        };
        if loop_condition {
            direction = direction.reversed();
        }
        let check = || self.at(cond, text(cond, self.src).trim());
        for (value, limit, direction) in
            [(&lhs, &rhs, direction), (&rhs, &lhs, direction.reversed())]
        {
            let Some(limit_name) =
                variable(limit, self.lang).or_else(|| integer(limit).map(|_| ""))
            else {
                continue;
            };
            if !limit_name.is_empty() && !self.unchanged(limit_name, None) {
                continue;
            }
            if direction == Direction::Up
                && self.fresh_clock(value, index)
                && self.clock_limit(limit_name)
            {
                return Some(RetryBound::Deadline(check()));
            }
            if self.lang == Lang::Rust
                && direction == Direction::Up
                && !limit_name.is_empty()
                && self.fresh_reading(value, index, rust_civil_now)
            {
                return Some(RetryBound::CivilDeadline(check()));
            }
            if let Some(counter) = variable(value, self.lang)
                && counter != limit_name
                && let Some(initial) = self.initial_value(counter)
                && integer(&initial).is_some()
                && self.counter_step(counter, direction)
            {
                return Some(RetryBound::Counter(check()));
            }
        }
        None
    }

    fn fresh_clock(&self, value: &str, index: usize) -> bool {
        self.fresh_reading(value, index, |v| self.clock(v))
    }

    fn fresh_reading(&self, value: &str, index: usize, is_clock: impl Fn(&str) -> bool) -> bool {
        if is_clock(value) {
            return true;
        }
        let Some(name) = variable(value, self.lang) else {
            return false;
        };
        self.statements[..index].iter().any(|&stmt| {
            self.initializer(stmt, name)
                .is_some_and(|init| is_clock(&init) && self.unchanged(name, Some(stmt)))
        })
    }

    fn clock(&self, value: &str) -> bool {
        match self.lang {
            Lang::Rust => {
                rust_now(value)
                    || value.strip_suffix(".elapsed()").is_some_and(|start| {
                        self.unchanged(start, None)
                            && self.initial_value(start).is_some_and(|v| rust_now(&v))
                    })
            }
            Lang::Python => value == "time.monotonic()",
            Lang::JavaScript => matches!(value, "performance.now()" | "Date.now()"),
            Lang::Bash => {
                variable(value, self.lang) == Some("SECONDS") && self.unchanged("SECONDS", None)
            }
            Lang::PowerShell => false,
        }
    }

    fn clock_limit(&self, name: &str) -> bool {
        if name.is_empty() || self.lang == Lang::Rust {
            // Instant and Duration are finite in their standard implementations.
            return true;
        }
        self.initial_value(name).is_some_and(|value| {
            integer(&value).is_some()
                || match self.lang {
                    Lang::Python => value.strip_prefix("time.monotonic()+").is_some_and(simple),
                    Lang::JavaScript => ["performance.now()+", "Date.now()+"]
                        .iter()
                        .any(|clock| value.strip_prefix(clock).is_some_and(simple)),
                    Lang::Bash => value
                        .strip_prefix("$((SECONDS+")
                        .is_some_and(|s| s.ends_with("))")),
                    _ => false,
                }
        })
    }

    fn initial_value(&self, name: &str) -> Option<String> {
        let mut node = self.node;
        while let Some(parent) = node.parent() {
            if matches!(
                parent.kind(),
                "block"
                    | "module"
                    | "source_file"
                    | "program"
                    | "statement_block"
                    | "statement_list"
                    | "do_group"
                    | "compound_statement"
            ) {
                for stmt in statements(parent)
                    .into_iter()
                    .rev()
                    .filter(|s| s.end_byte() <= node.start_byte())
                {
                    if self.writes(stmt, name, None) {
                        return self.initializer(stmt, name);
                    }
                }
            }
            if matches!(
                parent.kind(),
                "function_item"
                    | "function_definition"
                    | "function_declaration"
                    | "function_statement"
                    | "closure_expression"
                    | "arrow_function"
            ) {
                break;
            }
            node = parent;
        }
        None
    }

    fn initializer(&self, stmt: Node, name: &str) -> Option<String> {
        let stmt = if matches!(
            stmt.kind(),
            "lexical_declaration" | "variable_declaration" | "pipeline"
        ) {
            sole_child(stmt)?
        } else {
            stmt
        };
        let (left, right) = match stmt.kind() {
            "let_declaration" => ("pattern", "value"),
            "variable_declarator" | "variable_assignment" => ("name", "value"),
            "assignment" => ("left", "right"),
            "assignment_expression" if self.lang == Lang::PowerShell => {
                let assignment = self.t(stmt);
                let (left, right) = assignment.split_once('=')?;
                return (variable(left, self.lang) == Some(name)).then(|| right.to_owned());
            }
            _ => return None,
        };
        let lhs = self.t(stmt.child_by_field_name(left)?);
        if lhs.trim_start_matches('$') != name {
            return None;
        }
        Some(self.t(stmt.child_by_field_name(right)?))
    }

    fn counter_step(&self, name: &str, direction: Direction) -> bool {
        let step = match direction {
            Direction::Up => '+',
            Direction::Down => '-',
        };
        let variable = match self.lang {
            Lang::PowerShell => format!("${name}"),
            _ => name.to_owned(),
        };
        for &stmt in &self.statements {
            if has_continue(stmt, self.src, self.lang) {
                return false;
            }
            let s = self.t(stmt).trim_end_matches(';').to_owned();
            let offset = s
                .strip_prefix(&format!("{variable}{step}="))
                .or_else(|| s.strip_prefix(&format!("{variable}={variable}{step}")))
                .or_else(|| {
                    s.strip_prefix(&format!("{variable}=$(({variable}{step}"))
                        .and_then(|s| s.strip_suffix("))"))
                });
            let increment = matches!(self.lang, Lang::JavaScript | Lang::PowerShell)
                && (s == format!("{variable}{step}{step}")
                    || s == format!("{step}{step}{variable}"));
            if increment || offset.and_then(integer).is_some_and(|n| n > 0) {
                return self.unchanged(name, Some(stmt));
            }
        }
        false
    }

    fn unchanged(&self, name: &str, except: Option<Node>) -> bool {
        !self.writes(self.body, name, except)
    }

    fn writes(&self, node: Node, name: &str, except: Option<Node>) -> bool {
        if except == Some(node) {
            return false;
        }
        let kind = node.kind();
        let field = match kind {
            "assignment"
            | "assignment_expression"
            | "augmented_assignment"
            | "augmented_assignment_expression"
            | "compound_assignment_expr"
            | "for_in_statement" => node.child_by_field_name("left"),
            "variable_assignment"
            | "variable_declarator"
            | "function_definition"
            | "function_declaration"
            | "class_definition" => node.child_by_field_name("name"),
            "let_declaration" | "let_condition" | "for_expression" | "match_pattern" => {
                node.child_by_field_name("pattern")
            }
            "for_statement" if self.lang == Lang::Python => node.child_by_field_name("left"),
            "for_statement" if self.lang == Lang::Bash => node.child_by_field_name("variable"),
            _ => None,
        };
        let binding = |word: &str| {
            if self.lang == Lang::PowerShell {
                word.eq_ignore_ascii_case(name)
            } else {
                word == name
            }
        };
        if field.is_some_and(|target| names(text(target, self.src)).any(binding)) {
            return true;
        }
        // These nodes have targets without a common field, or can expose a mutable binding.
        let may_write = matches!(
            kind,
            "update_expression"
                | "named_expression"
                | "delete_statement"
                | "as_pattern"
                | "with_item"
                | "import_statement"
                | "import_from_statement"
                | "parameters"
                | "reference_expression"
                | "postfix_expression"
                | "post_increment_expression"
                | "post_decrement_expression"
                | "pre_increment_expression"
                | "pre_decrement_expression"
                | "left_assignment_expression"
                | "macro_invocation"
                | "foreach_statement"
        ) || self.lang == Lang::Bash
            && matches!(kind, "arithmetic_expansion" | "command");
        if may_write && names(text(node, self.src)).any(binding) {
            // In a shell command an expansion reads its variable. The bare name can be an
            // assignment target (read, unset, printf -v, arithmetic, and similar builtins).
            if self.lang != Lang::Bash
                || kind != "command"
                || text(node, self.src).split_whitespace().any(|word| {
                    !word.starts_with('$') && !word.starts_with('"') && names(word).any(binding)
                })
            {
                return true;
            }
        }
        named_children(node)
            .into_iter()
            .any(|child| self.writes(child, name, except))
    }
}

fn operands(n: Node, src: &str, lang: Lang) -> Option<(String, String, String)> {
    if n.kind() == "parenthesized_expression" {
        return operands(sole_child(n)?, src, lang);
    }
    let t = |n| squash(text(n, src));
    match lang {
        Lang::Rust | Lang::JavaScript if n.kind() == "binary_expression" => Some((
            t(n.child_by_field_name("left")?),
            t(n.child_by_field_name("operator")?),
            t(n.child_by_field_name("right")?),
        )),
        Lang::Python if n.kind() == "comparison_operator" => {
            let [left, right] = named_children(n)[..] else {
                return None;
            };
            Some((t(left), t(n.child_by_field_name("operators")?), t(right)))
        }
        Lang::Bash | Lang::PowerShell => {
            // These grammars wrap the comparison in shell test or pipeline nodes. Accept only
            // the entire simple test, with no redirects, pipeline stages or extra operands.
            let raw = text(n, src).trim();
            let expr = match lang {
                Lang::Bash if n.kind() == "test_command" => raw
                    .strip_prefix("[[")
                    .and_then(|s| s.strip_suffix("]]"))
                    .or_else(|| raw.strip_prefix('[')?.strip_suffix(']'))?,
                Lang::PowerShell => raw
                    .strip_prefix('(')
                    .and_then(|s| s.strip_suffix(')'))
                    .unwrap_or(raw),
                _ => return None,
            };
            let words = expr.split_whitespace().collect::<Vec<_>>();
            let [left, op, right] = words[..] else {
                return None;
            };
            if lang == Lang::PowerShell {
                Some((
                    left.to_ascii_lowercase(),
                    op.to_ascii_lowercase(),
                    right.to_ascii_lowercase(),
                ))
            } else {
                Some((left.to_owned(), op.to_owned(), right.to_owned()))
            }
        }
        _ => None,
    }
}

pub(super) fn body(n: Node, lang: Lang) -> Option<Node> {
    if lang == Lang::PowerShell {
        child_kind(n, "statement_block")
    } else {
        n.child_by_field_name("body")
    }
}

pub(super) fn statements(n: Node) -> Vec<Node> {
    let block = match n.kind() {
        "statement_block" => child_kind(n, "statement_list").unwrap_or(n),
        _ => n,
    };
    let nodes = if matches!(
        block.kind(),
        "block"
            | "module"
            | "source_file"
            | "program"
            | "statement_list"
            | "statement_block"
            | "do_group"
            | "compound_statement"
    ) {
        named_children(block)
    } else {
        vec![block]
    };
    nodes
        .into_iter()
        .filter(|c| !c.is_extra())
        .map(|stmt| {
            if stmt.kind() == "expression_statement" {
                stmt.named_child(0).unwrap_or(stmt)
            } else {
                stmt
            }
        })
        .collect()
}

fn child_kind<'tree>(n: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    named_children(n)
        .into_iter()
        .find(|child| child.kind() == kind)
}

fn sole_child(n: Node) -> Option<Node> {
    let [child] = named_children(n)[..] else {
        return None;
    };
    Some(child)
}

fn has_continue(n: Node, src: &str, lang: Lang) -> bool {
    let here = match lang {
        Lang::Bash => {
            n.kind() == "command"
                && n.child_by_field_name("name").is_some_and(|name| {
                    matches!(text(name, src), "continue" | "eval" | "source" | ".")
                        || matches!(text(name, src), "builtin" | "command")
                            && names(text(n, src)).any(|arg| arg == "continue")
                })
        }
        Lang::PowerShell => {
            n.kind() == "flow_control_statement"
                && n.child(0).is_some_and(|child| child.kind() == "continue")
        }
        Lang::Rust if n.kind() == "macro_invocation" => rust_macro_hides_control(n, src),
        Lang::Rust if matches!(n.kind(), "attribute_item" | "inner_attribute_item") => true,
        _ => matches!(n.kind(), "continue_expression" | "continue_statement"),
    };
    here || named_children(n)
        .into_iter()
        .any(|c| has_continue(c, src, lang))
}

pub(super) fn rust_macro_hides_control(n: Node, src: &str) -> bool {
    fn contains_jump(n: Node) -> bool {
        n.kind() == "continue" || children(n).into_iter().any(contains_jump)
    }
    !n.child_by_field_name("macro").is_some_and(|callee| {
        matches!(
            text(callee, src),
            "format" | "println" | "eprintln" | "vec" | "std::ptr::addr_of" | "core::ptr::addr_of"
        ) && !contains_jump(n)
    })
}

pub(super) fn rust_now(s: &str) -> bool {
    matches!(
        s.trim_start_matches("::"),
        "Instant::now()" | "std::time::Instant::now()" | "tokio::time::Instant::now()"
    )
}

fn rust_civil_now(s: &str) -> bool {
    let Some((clock, projection)) = s.trim_start_matches("::").split_once("::now()") else {
        return false;
    };
    match clock {
        "ZonedDateTime" | "Zoned" | "jiff::Zoned" => matches!(projection, "" | ".datetime()"),
        "Local" | "Utc" | "chrono::Local" | "chrono::Utc" => {
            matches!(projection, "" | ".naive_local()" | ".naive_utc()")
        }
        _ => false,
    }
}

fn names(s: &str) -> impl Iterator<Item = &str> {
    s.split(|c: char| !c.is_alphanumeric() && c != '_')
}

fn variable(s: &str, lang: Lang) -> Option<&str> {
    let s = match lang {
        Lang::Bash | Lang::PowerShell => s
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .unwrap_or(s)
            .strip_prefix('$')?,
        _ => s,
    };
    (s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && s.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_'))
    .then_some(s)
}

fn integer(s: &str) -> Option<i64> {
    s.replace('_', "").parse().ok()
}

fn simple(s: &str) -> bool {
    integer(s).is_some() || variable(s, Lang::Rust).is_some()
}
