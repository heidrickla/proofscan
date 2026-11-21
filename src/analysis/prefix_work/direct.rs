use super::{Cardinality, RULE, ResultFlows, Texts};
use crate::analysis::Analysis;
use crate::facts::{Id, LoopIter};
use crate::lang::{line, named_children, squash, text};
use crate::report::Verdict;
use std::collections::{HashMap, HashSet};
use tree_sitter::{Node, Parser};

const BYTE_SLICE: &str = "&[::std::primitive::u8]";
const RESULT: &str = "::std::result::Result<(),()>";
const OK: &str = "::std::result::Result::Ok(())";
const ERR: &str = "::std::result::Result::Err(())";

impl Analysis<'_> {
    pub(super) fn direct_prefix_work(
        &mut self,
        texts: &Texts<'_>,
        entries: &HashSet<Id>,
        flows: &ResultFlows<'_>,
    ) {
        let f = self.f;
        let at = |l: &LoopIter| &f.sites[l.site as usize];
        let loops: HashMap<_, _> = f.loops.iter().map(|l| ((at(l).file, l.id), l)).collect();
        for inner in &f.loops {
            let site = at(inner);
            if !entries.contains(&site.func) || !self.prefix_candidate(site.func) {
                continue;
            }
            let Some(outer) = site.ctx.loop_id.and_then(|id| loops.get(&(site.file, id))) else {
                continue;
            };
            let fun = &f.funcs[site.func as usize];
            let parameter = |name: &str| fun.params.iter().any(|p| p.name == name);
            if inner.iter == outer.iter || !parameter(&inner.iter) || !parameter(&outer.iter) {
                continue;
            }
            let path = f.files[site.file as usize].path.as_str();
            let Some(source) = texts.get(path) else {
                continue;
            };
            let mut parser = Parser::new();
            let Ok(()) = parser.set_language(&tree_sitter_rust::LANGUAGE.into()) else {
                continue;
            };
            let Some(tree) = parser.parse(source, None) else {
                continue;
            };
            let model = Direct {
                source,
                root: tree.root_node(),
                flows,
            };
            let Some(answer) = model.assess(outer, inner) else {
                continue;
            };
            let mut witness = vec![
                format!(
                    "{} visits request slice `{}`",
                    self.loc(outer.site),
                    outer.iter
                ),
                format!(
                    "{} starts over in request slice `{}` on every visit",
                    self.loc(inner.site),
                    inner.iter
                ),
            ];
            let (verdict, message, assumptions) = match answer {
                Work::Unbounded => (Verdict::Violated, "every visited element repeats work across an independently sized request list".into(), vec![]),
                Work::Unknown => (Verdict::Unknown, "cannot establish a rejecting bound on this list before the traversal or a budget charged for every prefix visit".into(), vec![]),
                Work::Bounded(bound) => {
                    witness.push(format!("{} rejects `{}` above {} members before traversal", self.loc(bound.check), bound.value, bound.members));
                    (Verdict::Proven, format!("each element visits at most {} prefixes of {} byte each", bound.members, bound.member_bytes), vec!["the request boundary supplies immutable byte slices and the loop uses the same slice the check bounded".into()])
                }
                Work::Charged { check, limit } => {
                    witness.push(format!("{} refuses an exhausted budget and charges every prefix visit before work", self.loc(check)));
                    (Verdict::Proven, format!("all element visits share one allowance of {limit} prefix visits"), vec!["the allowance counts prefix visits across the whole traversal".into()])
                }
            };
            self.push(6, RULE, verdict, inner.site, message, witness, assumptions);
        }
    }
}

enum Work<'a> {
    Unbounded,
    Unknown,
    Bounded(Cardinality<'a>),
    Charged { check: Id, limit: usize },
}

struct Direct<'a, 'f> {
    source: &'a str,
    root: Node<'a>,
    flows: &'a ResultFlows<'f>,
}

impl Direct<'_, '_> {
    /// Keep the direct model closed: immutable slices, one top-level traversal and a known
    /// constant-cost body. Aliases, extra actions and conditional checks cannot prove a bound.
    fn assess<'a>(&self, outer: &LoopIter, inner: &'a LoopIter) -> Option<Work<'a>> {
        let sites = &self.flows.facts.sites;
        let outer_site = &sites[outer.site as usize];
        let inner_site = &sites[inner.site as usize];
        let func = inner_site.func;
        let fun = &self.flows.facts.funcs[func as usize];
        if outer_site.func != func || fun.class.is_some() {
            return None;
        }
        let function = self.function(&fun.name, Some(fun.line))?;
        if !self.byte_slice(function, &outer.iter) || !self.byte_slice(function, &inner.iter) {
            return None;
        }
        let body = statements(function.child_by_field_name("body")?);
        let (at, visits) = body
            .iter()
            .enumerate()
            .find_map(|(i, &n)| self.for_loop(n, outer_site.line).map(|visit| (i, visit)))?;
        if self.compact(visits.child_by_field_name("pattern")?) != "_"
            || self.compact(visits.child_by_field_name("value")?) != outer.iter
        {
            return None;
        }
        let per_element = statements(visits.child_by_field_name("body")?);
        let [step] = per_element.as_slice() else {
            return None;
        };
        let step = self.for_loop(*step, inner_site.line)?;
        let pattern = step.child_by_field_name("pattern")?;
        if pattern.kind() != "reference_pattern"
            || self.compact(step.child_by_field_name("value")?) != inner.iter
        {
            return None;
        }
        let name = pattern
            .named_child(0)
            .filter(|n| n.kind() == "identifier")?;
        let action = format!("::std::hint::black_box({});", text(name, self.source));
        let repeated = statements(step.child_by_field_name("body")?);
        if !repeated.iter().any(|&n| self.compact(n) == action) {
            return None;
        }
        let (before, tail) = (&body[..at], &body[at + 1..]);
        if !matches!(tail, [ok] if self.compact(*ok) == OK) {
            return Some(Work::Unknown);
        }
        Some(match (before, repeated.as_slice()) {
            ([], [only]) if self.compact(*only) == action => Work::Unbounded,
            ([guard], [only]) if self.compact(*only) == action => self
                .bound(func, *guard, &inner.iter)
                .map_or(Work::Unknown, Work::Bounded),
            ([initial], [guard, debit, only]) if self.compact(*only) == action => self
                .budget(func, *initial, *guard, *debit)
                .unwrap_or(Work::Unknown),
            _ => Work::Unknown,
        })
    }

    fn bound<'a>(&self, func: Id, guard: Node<'_>, value: &'a str) -> Option<Cardinality<'a>> {
        if let Some((check, members)) = self.length_guard(func, guard, value) {
            return Some(Cardinality {
                value,
                check,
                members,
                member_bytes: 1,
            });
        }
        let try_call = expression(guard);
        if try_call.kind() != "try_expression" {
            return None;
        }
        let call = try_call.named_child(0)?;
        let name = call.child_by_field_name("function")?;
        let callee = text(name, self.source);
        if name.kind() != "identifier" || self.compact(call) != format!("{callee}({value})") {
            return None;
        }
        let check = self
            .flows
            .propagated(func, &self.compact(call))
            .find(|flow| flow.byte == call.start_byte())?
            .site;
        let function = self.function(callee, None)?;
        let f = self.flows.facts;
        let mut ids = f.funcs.iter().enumerate().filter(|(_, candidate)| {
            candidate.file == f.funcs[func as usize].file
                && candidate.name == callee
                && candidate.line == line(function)
                && candidate.class.is_none()
        });
        let (callee_id, callee_fact) = ids.next()?;
        let [param] = callee_fact.params.as_slice() else {
            return None;
        };
        if ids.next().is_some() || !self.byte_slice(function, &param.name) {
            return None;
        }
        let body = statements(function.child_by_field_name("body")?);
        let [reject, ok] = body.as_slice() else {
            return None;
        };
        if self.compact(*ok) != OK {
            return None;
        }
        let (_, members) = self.length_guard(callee_id as Id, *reject, &param.name)?;
        Some(Cardinality {
            value,
            check,
            members,
            member_bytes: 1,
        })
    }

    fn length_guard(&self, func: Id, guard: Node<'_>, value: &str) -> Option<(Id, usize)> {
        let branch = expression(guard);
        let condition = self.compact(branch.child_by_field_name("condition")?);
        let amount = condition
            .strip_prefix(&format!("{value}.len()>"))?
            .parse::<usize>()
            .ok()?;
        Some((self.rejects(func, branch, &condition)?, amount))
    }

    fn budget(
        &self,
        func: Id,
        initial: Node<'_>,
        guard: Node<'_>,
        debit: Node<'_>,
    ) -> Option<Work<'static>> {
        let name = initial.child_by_field_name("pattern")?;
        if initial.kind() != "let_declaration" || name.kind() != "identifier" {
            return None;
        }
        let name = text(name, self.source);
        let initial_value = self.compact(initial.child_by_field_name("value")?);
        let limit = initial_value.strip_suffix("usize")?.parse().ok()?;
        if self.compact(initial) != format!("letmut{name}={initial_value};")
            || self.compact(debit) != format!("{name}-=1;")
        {
            return None;
        }
        let check = self.rejects(func, expression(guard), &format!("{name}==0"))?;
        Some(Work::Charged { check, limit })
    }

    fn rejects(&self, func: Id, branch: Node<'_>, condition: &str) -> Option<Id> {
        if branch.kind() != "if_expression" || branch.child_by_field_name("alternative").is_some() {
            return None;
        }
        self.flows
            .rejecting(func, condition, ERR)
            .find(|flow| flow.byte == branch.start_byte())
            .map(|flow| flow.site)
    }

    fn function(&self, name: &str, row: Option<u32>) -> Option<Node<'_>> {
        let mut functions = statements(self.root).into_iter().filter(|&n| {
            n.kind() == "function_item"
                && n.child_by_field_name("name")
                    .is_some_and(|id| text(id, self.source) == name)
        });
        let node = functions.next()?;
        if functions.next().is_some() || node.has_error() || row.is_some_and(|r| line(node) != r) {
            return None;
        }
        let mut previous = node.prev_named_sibling();
        while previous.is_some_and(comment) {
            previous = previous.and_then(|n| n.prev_named_sibling());
        }
        if previous.is_some_and(|n| n.kind() == "attribute_item")
            || self.compact(node.child_by_field_name("return_type")?) != RESULT
        {
            return None;
        }
        Some(node)
    }

    fn byte_slice(&self, function: Node<'_>, name: &str) -> bool {
        let Some(parameters) = function.child_by_field_name("parameters") else {
            return false;
        };
        named_children(parameters).into_iter().any(|p| {
            p.kind() == "parameter"
                && p.child_by_field_name("pattern")
                    .is_some_and(|n| n.kind() == "identifier" && text(n, self.source) == name)
                && p.child_by_field_name("type")
                    .is_some_and(|n| self.compact(n) == BYTE_SLICE)
        })
    }

    fn for_loop<'n>(&self, statement: Node<'n>, row: u32) -> Option<Node<'n>> {
        let n = expression(statement);
        (n.kind() == "for_expression" && line(n) == row).then_some(n)
    }

    fn compact(&self, node: Node<'_>) -> String {
        squash(text(node, self.source))
    }
}

fn statements(n: Node<'_>) -> Vec<Node<'_>> {
    named_children(n)
        .into_iter()
        .filter(|&n| !comment(n))
        .collect()
}

fn comment(n: Node<'_>) -> bool {
    matches!(n.kind(), "line_comment" | "block_comment")
}

fn expression(n: Node<'_>) -> Node<'_> {
    if n.kind() == "expression_statement" {
        n.named_child(0).unwrap_or(n)
    } else {
        n
    }
}
