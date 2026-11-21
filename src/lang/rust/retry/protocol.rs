//! Local Rust retry protocols whose bounds depend on the continuing branch.

use super::{
    Node, call, can_continue, exits_loop, ident, imports_symbol, nodes, references, squash,
    statement, text, walk,
};
use crate::facts::RetryBound;
use crate::lang::line;
use crate::lang::retry::{
    guarded_rust_deadline, nested_rust_deadline, rust_macro_hides_control, statements,
    true_conjuncts,
};

pub(in crate::lang::rust) fn prove(loop_node: Node, src: &str) -> Option<RetryBound> {
    let body = loop_node.child_by_field_name("body")?;
    if body.has_error() || !locally_visible(body, src) {
        return None;
    }
    let local = Local { loop_node, src };
    if loop_node.kind() == "while_expression" {
        return local.item_replay(body);
    }
    if loop_node.kind() != "loop_expression" {
        return None;
    }
    local
        .finite_growth(body)
        .or_else(|| local.registry_growth(body))
        .or_else(|| local.enumerator(body))
        .or_else(|| local.guarded_retry(body))
}

pub(in crate::lang::rust) fn unresolved_progress(loop_node: Node, src: &str) -> Option<RetryBound> {
    let body = loop_node.child_by_field_name("body")?;
    Local { loop_node, src }.unresolved_progress(body)
}

pub(in crate::lang::rust) fn volume_input<'s>(
    loop_node: Node<'_>,
    src: &'s str,
) -> Option<&'s str> {
    let local = Local { loop_node, src };
    let body = loop_node.child_by_field_name("body")?;
    let input = local.volume_input(body)?;
    locally_visible(body, src).then_some(input)
}

struct Local<'t, 's> {
    loop_node: Node<'t>,
    src: &'s str,
}

impl<'t, 's> Local<'t, 's> {
    fn t(&self, n: Node) -> String {
        squash(text(n, self.src))
    }

    fn at(&self, n: Node) -> String {
        format!("`{}` at line {}", text(n, self.src).trim(), line(n))
    }

    fn binding(&self, n: Node<'t>) -> Option<(&'s str, Node<'t>)> {
        (n.kind() == "let_declaration").then_some(())?;
        Some((
            ident(n.child_by_field_name("pattern")?, self.src)?,
            n.child_by_field_name("value")?,
        ))
    }

    fn preceding(&self) -> Vec<Node<'t>> {
        let Some(block) = std::iter::successors(self.loop_node.parent(), |n| n.parent())
            .find(|p| p.kind() == "block")
        else {
            return vec![];
        };
        statements(block)
            .into_iter()
            .filter(|n| n.end_byte() <= self.loop_node.start_byte())
            .collect()
    }

    fn guarded_retry(&self, body: Node<'t>) -> Option<RetryBound> {
        let stmts = statements(body);
        let (&matched, prefix) = stmts.split_last()?;
        let continuing: Vec<_> = self
            .match_arms(matched)?
            .into_iter()
            .filter(|&(_, arm)| can_continue(arm, self.loop_node, self.src))
            .collect();
        if continuing.is_empty()
            || continuing.iter().any(|&(pattern, _)| {
                !pattern
                    .named_child(0)
                    .is_some_and(|n| variant(n, "Err", self.src))
            })
        {
            return None;
        }
        let guards: Vec<_> = continuing
            .iter()
            .map(|(pattern, _)| pattern.child_by_field_name("condition"))
            .collect::<Option<_>>()?;
        guarded_rust_deadline(self.loop_node, matched, &guards, self.src).or_else(|| {
            if prefix.iter().copied().any(has_back_jump) {
                return None;
            }
            self.one_shot_flags(body, &continuing, &guards)
        })
    }

    fn one_shot_flags(
        &self,
        body: Node<'t>,
        continuing: &[(Node<'t>, Node<'t>)],
        guards: &[Node<'t>],
    ) -> Option<RetryBound> {
        let preceding = self.preceding();
        let mut flags = Vec::new();
        for (&(_, arm), &guard) in continuing.iter().zip(guards) {
            let (test, flag) = true_conjuncts(guard).into_iter().find_map(|n| {
                let name = self.t(n);
                let flag = name.strip_prefix('!')?;
                let binding = n.named_child(0).and_then(|v| ident(v, self.src))?;
                (flag == binding).then_some((n, binding))
            })?;
            let assign = *statements(arm).first()?;
            if self.t(assign) != format!("{flag}=true") {
                return None;
            }
            let declaration = preceding.iter().rposition(|&n| {
                self.binding(n)
                    .is_some_and(|(name, value)| name == flag && self.t(value) == "false")
            })?;
            if preceding[declaration + 1..]
                .iter()
                .any(|&n| references(n, flag, self.src))
            {
                return None;
            }
            flags.push((flag, test, assign));
        }
        for &(flag, _, _) in &flags {
            let mut other_use = false;
            walk(body, &mut |n| {
                if ident(n, self.src) == Some(flag)
                    && !flags.iter().any(|&(name, test, assign)| {
                        name == flag
                            && [test, assign]
                                .iter()
                                .any(|span| span.byte_range().contains(&n.start_byte()))
                    })
                {
                    other_use = true;
                }
            });
            if other_use {
                return None;
            }
        }
        let mut names: Vec<_> = flags.into_iter().map(|(flag, _, _)| flag).collect();
        names.sort_unstable();
        names.dedup();
        Some(RetryBound::OneShotFlags(names.join(", ")))
    }

    fn volume_input(&self, body: Node<'t>) -> Option<&'s str> {
        let stmts = statements(body);
        let (&last, prefix) = stmts.split_last()?;
        let (condition, exhausted) = if_branch(last)?;
        let (advance, zero) = binary(condition, "==")?;
        let (callee, args) = unsafe_call(advance)?;
        let [handle, pointer, length] = args[..] else {
            return None;
        };
        let handle = ident(handle, self.src)?;
        let (buffer, method, args) = method_call(pointer, self.src)?;
        let buffer = ident(buffer, self.src)?;
        if self.t(callee) != "FindNextVolumeW"
            || method != "as_mut_ptr"
            || !args.is_empty()
            || self.t(length) != format!("{buffer}.len()asu32")
            || self.t(zero) != "0"
            || last.child_by_field_name("alternative").is_some()
            || !unconditional_exit(exhausted)
            || prefix
                .iter()
                .any(|&n| has_back_jump(n) || references(n, handle, self.src))
        {
            return None;
        }
        let preceding = self.preceding();
        let first = preceding.iter().rposition(|&n| {
            self.binding(n).is_some_and(|(name, value)| {
                name == handle
                    && self.t(value)
                        == format!(
                            "unsafe{{FindFirstVolumeW({buffer}.as_mut_ptr(),{buffer}.len()asu32)}}"
                        )
            })
        })?;
        let checked = preceding[first + 1..].iter().all(|&n| {
            matches!(if_branch(n), Some((test, arm))
                if self.t(test) == format!("{handle}==INVALID_HANDLE_VALUE") && unconditional_exit(arm))
                || !references(n, handle, self.src) && !references(n, buffer, self.src)
        });
        let root = std::iter::successors(Some(self.loop_node), |n| n.parent()).last()?;
        let standard = ["FindFirstVolumeW", "FindNextVolumeW"]
            .into_iter()
            .all(|symbol| {
                imports_symbol(
                    root,
                    "windows_sys::Win32::Storage::FileSystem",
                    symbol,
                    self.src,
                )
            });
        let changes_input = prefix.iter().any(|&n| {
            super::any_local(n, &|n| {
                (matches!(n.kind(), "unsafe_block" | "reference_expression")
                    && references(n, buffer, self.src)
                    && (n.kind() == "unsafe_block" || self.t(n).starts_with("&mut")))
                    || n.child_by_field_name("left").is_some_and(|left| {
                        matches!(
                            n.kind(),
                            "assignment_expression" | "compound_assignment_expr"
                        ) && references(left, buffer, self.src)
                    })
                    || method_call(n, self.src).is_some_and(|(receiver, method, _)| {
                        references(receiver, buffer, self.src)
                            && matches!(method, "as_mut_ptr" | "get_mut" | "as_mut_slice")
                    })
            })
        });
        (checked && standard && !changes_input).then_some(buffer)
    }

    fn registry_growth(&self, body: Node<'t>) -> Option<RetryBound> {
        let stmts = statements(body);
        let index = stmts.iter().position(|n| n.kind() == "match_expression")?;
        let matched = stmts[index];
        let arms = self.match_arms(matched)?;
        let candidate = arms
            .iter()
            .find(|(pattern, _)| self.t(*pattern) == "ERROR_MORE_DATA")?;
        let (buffer, method, args) = method_call(candidate.1, self.src)?;
        let buffer = ident(buffer, self.src)?;
        let [size, fill] = args[..] else { return None };
        let (need, max, args) = method_call(size, self.src)?;
        let [double] = args[..] else { return None };
        let required = self.t(need);
        let required = required.strip_prefix('(')?.strip_suffix("asusize)")?;
        if method != "resize"
            || max != "max"
            || self.t(fill) != "0"
            || self.t(double) != format!("{buffer}.len()*2")
        {
            return None;
        }
        let status = ident(matched.child_by_field_name("value")?, self.src)?;
        let (_, read) = self.binding(*stmts.get(index.checked_sub(1)?)?)?;
        let (callee, args) = unsafe_call(read)?;
        let registry = self.t(callee);
        let prefix = &stmts[..index];
        if self.binding(prefix[index - 1])?.0 != status
            || !matches!(registry.as_str(), "RegQueryValueExW" | "RegEnumValueW")
            || args
                .get(args.len().checked_sub(2)?)
                .is_none_or(|&n| self.t(n) != format!("{buffer}.as_mut_ptr()"))
            || args
                .last()
                .is_none_or(|&n| self.t(n) != format!("&mut{required}"))
            || !prefix.iter().any(|&n| {
                self.binding(n).is_some_and(|(name, init)| {
                    name == required && self.t(init) == format!("{buffer}.len()asu32")
                })
            })
            || prefix
                .iter()
                .any(|&n| has_back_jump(n) || !only_length_or_data_pointer(n, buffer, self.src))
        {
            return None;
        }
        let preceding = self.preceding();
        let init = preceding.iter().rposition(|&n| {
            self.binding(n).is_some_and(|(name, init)| {
                name == buffer
                    && self
                        .t(init)
                        .strip_prefix("vec![0u8;")
                        .and_then(|s| s.strip_suffix(']'))
                        .and_then(|n| n.replace('_', "").parse::<u32>().ok())
                        .is_some_and(|n| n > 0)
            })
        })?;
        if preceding[init + 1..]
            .iter()
            .any(|&n| references(n, buffer, self.src))
        {
            return None;
        }
        let advancing: Vec<_> = arms
            .iter()
            .filter_map(|&(pattern, arm)| {
                (pattern != candidate.0 && can_continue(arm, self.loop_node, self.src))
                    .then_some(arm)
            })
            .collect();
        if advancing.is_empty() && index + 1 == stmts.len() {
            return Some(RetryBound::RegistryGrowth(self.at(candidate.1)));
        }
        let [guard] = stmts[index + 1..] else {
            return None;
        };
        let (condition, exit) = if_branch(guard)?;
        let (item, cap) = binary(condition, ">")?;
        let item = ident(item, self.src)?;
        let cap = self.t(cap).replace('_', "").parse::<u32>().ok()?;
        let initial = preceding.iter().rposition(|&n| {
            self.binding(n)
                .is_some_and(|(name, init)| name == item && self.t(init) == "0")
        })?;
        let count_step = format!("{item}+=1");
        if registry != "RegEnumValueW"
            || cap == u32::MAX
            || !unconditional_exit(exit)
            || guard.child_by_field_name("alternative").is_some()
            || args.get(1).and_then(|&n| ident(n, self.src)) != Some(item)
            || preceding[initial + 1..]
                .iter()
                .any(|&n| references(n, item, self.src))
            || prefix[..index - 1]
                .iter()
                .any(|&n| references(n, item, self.src))
            || advancing.iter().any(|&arm| {
                let steps = statements(arm);
                !steps.split_last().is_some_and(|(&step, before)| {
                    self.t(step) == count_step
                        && before.iter().all(|&n| {
                            !references(n, item, self.src)
                                && !has_back_jump(n)
                                && !any_local_mutation(n, buffer, self.src)
                        })
                })
            })
        {
            return None;
        }
        Some(RetryBound::RegistryGrowth(format!(
            "{} or {}",
            self.at(candidate.1),
            self.at(condition)
        )))
    }

    fn unresolved_progress(&self, body: Node<'t>) -> Option<RetryBound> {
        let stmts = statements(body);
        let (&last, before) = stmts.split_last()?;
        let progress = if self.records_fresh_key(last, before) {
            "the refusal check records each new approval, but its input domain is outside the loop"
        } else if self.match_arms(last).is_some_and(|arms| {
            arms.iter().any(|&(_, arm)| {
                self.match_arms(arm).is_some_and(|responses| {
                    responses
                        .iter()
                        .any(|&(pattern, _)| self.t(pattern) == "Some(Refusal::AlreadyAccepted)")
                        && responses.iter().any(|&(pattern, _)| {
                            self.t(pattern).starts_with("Some(Refusal::NotAccepted)if!")
                        })
                })
            })
        }) {
            "delivery state changes across broker responses whose transition rules are outside the loop"
        } else if self.match_arms(last).is_some_and(|arms| {
            arms.iter().any(|&(pattern, arm)| {
                self.t(pattern).starts_with("Err(RecvError::Refused{")
                    && can_continue(arm, self.loop_node, self.src)
            }) && arms.iter().any(|&(pattern, arm)| {
                self.t(pattern) == "Err(RecvError::Closed|RecvError::Io(_))"
                    && unconditional_exit(arm)
            })
        }) {
            "receive refusals can continue, and whether they consume the packet depends on the channel implementation"
        } else {
            return None;
        };
        Some(RetryBound::UnknownStateProgress(progress.into()))
    }

    fn records_fresh_key(&self, last: Node<'t>, before: &[Node<'t>]) -> bool {
        let Some((receiver, "push", args)) = method_call(last, self.src) else {
            return false;
        };
        let [key] = args[..] else { return false };
        if key.kind() != "field_expression" || before.iter().copied().any(has_back_jump) {
            return false;
        }
        let expected = format!("{}.contains(&{})", self.t(receiver), self.t(key));
        before.iter().any(|&n| {
            if_branch(n).is_some_and(|(test, arm)| {
                let mut clauses = vec![test];
                while let Some(clause) = clauses.pop() {
                    if self.t(clause) == expected {
                        return unconditional_exit(arm);
                    }
                    if let Some((left, right)) = binary(clause, "||") {
                        clauses.extend([left, right]);
                    }
                }
                false
            })
        })
    }

    fn match_arms(&self, n: Node<'t>) -> Option<Vec<(Node<'t>, Node<'t>)>> {
        (n.kind() == "match_expression").then_some(())?;
        nodes(n.child_by_field_name("body")?)
            .into_iter()
            .map(|arm| {
                Some((
                    arm.child_by_field_name("pattern")?,
                    arm.child_by_field_name("value")?,
                ))
            })
            .collect()
    }

    fn item_replay(&self, body: Node<'t>) -> Option<RetryBound> {
        let cond = self.loop_node.child_by_field_name("condition")?;
        if cond.kind() != "let_condition" {
            return None;
        }
        let pattern = cond.child_by_field_name("pattern")?;
        let [tag, binding] = nodes(pattern)[..] else {
            return None;
        };
        let [_, item] = nodes(binding)[..] else {
            return None;
        };
        let item = ident(item, self.src)?;
        if self.t(tag) != "Some" || binding.kind() != "mut_pattern" {
            return None;
        }
        let (queue, method, args) = method_call(cond.child_by_field_name("value")?, self.src)?;
        let queue = ident(queue, self.src)?;
        if method != "pop_front" || !args.is_empty() {
            return None;
        }
        let [matched] = statements(body)[..] else {
            return None;
        };
        let [(err, retried), (other, finished)] = self.match_arms(matched)?[..] else {
            return None;
        };
        let guard = err.child_by_field_name("condition")?;
        let pattern = err.named_child(0)?;
        if !variant(pattern, "Err", self.src)
            || other.child_by_field_name("condition").is_some()
            || !matches!(other.named_child(0)?.kind(), "identifier" | "_")
        {
            return None;
        }
        let flag = self.t(guard);
        let (owner, field) = flag.strip_prefix('!')?.split_once('.')?;
        if owner != item || !field.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return None;
        }
        let [mark, push] = statements(retried)[..] else {
            return None;
        };
        let operation = matched.child_by_field_name("value")?;
        let operation = if operation.kind() == "await_expression" {
            operation.named_child(0)?
        } else {
            operation
        };
        let (_, args) = call(operation)?;
        let [request] = args[..] else { return None };
        let request = self.t(request);
        if !request
            .strip_prefix(&format!("&{item}."))
            .is_some_and(|name| {
                name != field
                    && !name.is_empty()
                    && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            })
            || references(operation, queue, self.src)
            || references(finished, queue, self.src)
            || self.t(mark) != format!("{item}.{field}=true")
            || self.t(push) != format!("{queue}.push_back({item})")
        {
            return None;
        }
        Some(RetryBound::ItemReplay(self.at(guard)))
    }

    fn finite_growth(&self, body: Node<'t>) -> Option<RetryBound> {
        let stmts = statements(body);
        let (&last, _) = stmts.split_last()?;
        if !exits_loop(last) {
            return None;
        }
        for (index, &candidate) in stmts.iter().enumerate() {
            if let Some(bound) = self.growth_branch(&stmts, index, candidate) {
                return Some(bound);
            }
        }
        None
    }

    fn growth_branch(
        &self,
        stmts: &[Node<'t>],
        index: usize,
        candidate: Node<'t>,
    ) -> Option<RetryBound> {
        let (cond, arm) = if_branch(candidate)?;
        if candidate.child_by_field_name("alternative").is_some() {
            return None;
        }
        let [resize, again] = statements(arm)[..] else {
            return None;
        };
        if !is_continue(again)
            || stmts
                .iter()
                .any(|&stmt| stmt != candidate && has_back_jump(stmt))
        {
            return None;
        }
        let (status, cmp) = binary(cond, "&&")?;
        let (code, error) = binary(status, "==")?;
        if ident(code, self.src).is_none() || self.t(error) != "ERROR_INSUFFICIENT_BUFFER" {
            return None;
        }
        let (needed, bytes) = binary(cmp, ">")?;
        let (length, width) = binary(bytes, "*")?;
        let (buffer, method, args) = method_call(length, self.src)?;
        let buffer = ident(buffer, self.src)?;
        if method != "len" || !args.is_empty() {
            return None;
        }
        let width = self.t(width);
        let zero = match width.as_str() {
            "1" => "0u8",
            "2" => "0u16",
            "4" => "0u32",
            "8" => "0u64",
            _ => return None,
        };
        let needed = self.t(needed);
        let name = needed.strip_suffix("asusize")?;
        let (decl, init) = stmts[..index].iter().rev().find_map(|&decl| {
            let (binding, init) = self.binding(decl)?;
            (binding == name).then_some((decl, init))
        })?;
        let finite = decl.child_by_field_name("type").map_or_else(
            || matches!(self.t(init).as_str(), "0u8" | "0u16" | "0u32"),
            |ty| matches!(self.t(ty).as_str(), "u8" | "u16" | "u32"),
        );
        if !finite {
            return None;
        }
        let preceding = self.preceding();
        let init = preceding.iter().rposition(|&n| {
            self.binding(n).is_some_and(|(name, init)| {
                name == buffer && self.t(init).starts_with(&format!("vec![{zero};"))
            })
        })?;
        if preceding[init + 1..]
            .iter()
            .chain(&stmts[..index])
            .any(|&stmt| !only_length_or_data_pointer(stmt, buffer, self.src))
        {
            return None;
        }
        let new_len = format!("({needed}).div_ceil({width})");
        let resize = self.t(resize);
        if resize != format!("{buffer}=vec![{zero};{new_len}]")
            && resize != format!("{buffer}.resize({new_len},{zero})")
            && resize != format!("{buffer}.resize({new_len},0)")
        {
            return None;
        }
        Some(RetryBound::FiniteGrowth(self.at(cmp)))
    }

    fn enumerator(&self, body: Node<'t>) -> Option<RetryBound> {
        let stmts = statements(body);
        if let [matched] = stmts[..] {
            return self.result_enumerator(matched);
        }
        self.wmi_enumerator(&stmts)
    }

    fn result_enumerator(&self, matched: Node<'t>) -> Option<RetryBound> {
        let (receiver, method, args) =
            method_call(matched.child_by_field_name("value")?, self.src)?;
        let receiver = ident(receiver, self.src)?;
        let [wait] = args[..] else { return None };
        if method != "next_for" || !matches!(wait.kind(), "identifier" | "integer_literal") {
            return None;
        }
        let [(timeout, retry), (success, consume), (other, exit)] = self.match_arms(matched)?[..]
        else {
            return None;
        };
        if [timeout, success, other]
            .iter()
            .any(|n| n.child_by_field_name("condition").is_some())
            || self.t(timeout) != "Err(TimedOut)"
            || !nested_variant(success.named_child(0)?, "Ok", "Some", self.src)
            || self.t(other) != "_"
            || !exits_loop(exit)
            || has_back_jump(consume)
            || [retry, consume]
                .iter()
                .any(|&arm| references(arm, receiver, self.src))
        {
            return None;
        }
        let check = nested_rust_deadline(self.loop_node, retry, self.src)?;
        Some(RetryBound::EnumeratorDeadline(check, "next_for".into()))
    }

    fn wmi_enumerator(&self, stmts: &[Node<'t>]) -> Option<RetryBound> {
        let [
            object,
            returned,
            read,
            failed,
            timeout,
            exhausted,
            rest @ ..,
        ] = stmts
        else {
            return None;
        };
        let (object, _) = self.binding(*object)?;
        let (returned, initial_count) = self.binding(*returned)?;
        let (status, read) = self.binding(*read)?;
        if !matches!(self.t(initial_count).as_str(), "0" | "0u32") || read.kind() != "unsafe_block"
        {
            return None;
        }
        let [declare, invoke] = statements(read.named_child(0)?)[..] else {
            return None;
        };
        let (next, address) = self.binding(declare)?;
        let sig = self.t(declare.child_by_field_name("type")?);
        if sig != "unsafeextern\"system\"fn(*mutc_void,i32,u32,*mut*mutc_void,*mutu32,)->i32"
            && sig != "unsafeextern\"system\"fn(*mutc_void,i32,u32,*mut*mutc_void,*mutu32)->i32"
        {
            return None;
        }
        let (callee, args) = call(invoke)?;
        let [receiver, wait, count, out_object, out_count] = args[..] else {
            return None;
        };
        let receiver = self.t(receiver);
        let enumerator = receiver.strip_suffix(".0")?;
        if ident(callee, self.src) != Some(next)
            || !matches!(wait.kind(), "identifier" | "integer_literal")
            || self.t(count) != "1"
            || self.t(out_object) != format!("&mut{object}")
            || self.t(out_count) != format!("&mut{returned}")
            || self.t(address) != format!("std::mem::transmute({enumerator}.slot(4))")
        {
            return None;
        }
        let preceding = self.preceding();
        let wrap = preceding.iter().rposition(|&n| {
            self.binding(n).is_some_and(|(name, init)| {
                name == enumerator && self.t(init) == format!("Com({enumerator})")
            })
        })?;
        let query = preceding[..wrap]
            .iter()
            .rposition(|&n| self.forward_query(n, enumerator).is_some())?;
        if preceding[query + 1..wrap]
            .iter()
            .chain(&preceding[wrap + 1..])
            .chain(rest)
            .any(|&n| references(n, enumerator, self.src))
        {
            return None;
        }
        let (failure_test, failure_arm) = if_branch(*failed)?;
        let (timeout_test, timeout_arm) = if_branch(*timeout)?;
        let (empty_test, empty_arm) = if_branch(*exhausted)?;
        let [retry, again] = statements(timeout_arm)[..] else {
            return None;
        };
        if [failed, timeout, exhausted]
            .iter()
            .any(|n| n.child_by_field_name("alternative").is_some())
            || self.t(failure_test) != format!("{status}<0")
            || !unconditional_exit(failure_arm)
            || self.t(timeout_test) != format!("{status}==WBEM_S_TIMEDOUT&&{returned}==0")
            || self.t(empty_test) != format!("{returned}==0")
            || !unconditional_exit(empty_arm)
            || !is_continue(again)
            || has_back_jump(retry)
            || rest.iter().copied().any(has_back_jump)
        {
            return None;
        }
        let check = nested_rust_deadline(self.loop_node, timeout_arm, self.src)?;
        Some(RetryBound::EnumeratorDeadline(
            check,
            "IEnumWbemClassObject::Next from forward-only IWbemServices::ExecQuery".into(),
        ))
    }

    fn forward_query(&self, stmt: Node<'t>, enumerator: &str) -> Option<()> {
        let (_, query) = self.binding(stmt)?;
        (query.kind() == "unsafe_block").then_some(())?;
        let [declare, invoke] = statements(query.named_child(0)?)[..] else {
            return None;
        };
        let (exec, address) = self.binding(declare)?;
        let (callee, args) = call(invoke)?;
        let [services, _, _, flags, context, returned] = args[..] else {
            return None;
        };
        (self.t(address) == "std::mem::transmute(self.services.slot(20))"
            && ident(callee, self.src) == Some(exec)
            && self.t(services) == "self.services.0"
            && self.t(flags) == "WBEM_FLAG_FORWARD_ONLY|WBEM_FLAG_RETURN_IMMEDIATELY"
            && self.t(context) == "null_mut()"
            && self.t(returned) == format!("&mut{enumerator}"))
        .then_some(())
    }
}

fn unsafe_call(n: Node<'_>) -> Option<(Node<'_>, Vec<Node<'_>>)> {
    (n.kind() == "unsafe_block").then_some(())?;
    let [invoke] = statements(n.named_child(0)?)[..] else {
        return None;
    };
    call(invoke)
}

fn any_local_mutation(n: Node, name: &str, src: &str) -> bool {
    super::any_local(n, &|n| {
        references(n, name, src)
            && match n.kind() {
                "assignment_expression" | "compound_assignment_expr" | "let_declaration" => n
                    .child_by_field_name("left")
                    .or_else(|| n.child_by_field_name("pattern"))
                    .is_some_and(|left| references(left, name, src)),
                "reference_expression" => squash(text(n, src)).starts_with("&mut"),
                "call_expression" => method_call(n, src)
                    .is_some_and(|(receiver, _, _)| ident(receiver, src) == Some(name)),
                _ => false,
            }
    })
}

fn if_branch(n: Node<'_>) -> Option<(Node<'_>, Node<'_>)> {
    (n.kind() == "if_expression").then_some(())?;
    Some((
        n.child_by_field_name("condition")?,
        n.child_by_field_name("consequence")?,
    ))
}

pub(super) fn binary<'a>(n: Node<'a>, operator: &str) -> Option<(Node<'a>, Node<'a>)> {
    if n.kind() == "parenthesized_expression" {
        return binary(n.named_child(0)?, operator);
    }
    (n.kind() == "binary_expression" && n.child_by_field_name("operator")?.kind() == operator)
        .then_some((
            n.child_by_field_name("left")?,
            n.child_by_field_name("right")?,
        ))
}

pub(super) fn method_call<'t, 's>(
    n: Node<'t>,
    src: &'s str,
) -> Option<(Node<'t>, &'s str, Vec<Node<'t>>)> {
    let (method, args) = call(n)?;
    (method.kind() == "field_expression").then_some(())?;
    Some((
        method.child_by_field_name("value")?,
        text(method.child_by_field_name("field")?, src),
        args,
    ))
}

fn variant(n: Node, tag: &str, src: &str) -> bool {
    n.kind() == "tuple_struct_pattern"
        && n.child_by_field_name("type")
            .is_some_and(|n| text(n, src) == tag)
}

fn nested_variant(n: Node, outer: &str, inner: &str, src: &str) -> bool {
    variant(n, outer, src) && nodes(n).get(1).is_some_and(|&n| variant(n, inner, src))
}

fn is_continue(n: Node) -> bool {
    n.kind() == "continue_expression" && nodes(n).is_empty()
}

fn has_back_jump(n: Node) -> bool {
    let mut found = false;
    walk(n, &mut |n| found |= n.kind() == "continue_expression");
    found
}

fn unconditional_exit(n: Node) -> bool {
    statements(n).last().copied().is_some_and(exits_loop) && !has_back_jump(n)
}

fn locally_visible(body: Node, src: &str) -> bool {
    let mut visible = true;
    walk(body, &mut |n| {
        visible &= match n.kind() {
            "attribute_item" | "inner_attribute_item" | "label" => false,
            "macro_invocation" => !rust_macro_hides_control(n, src),
            _ => true,
        };
    });
    visible
}

fn only_length_or_data_pointer(n: Node, buffer: &str, src: &str) -> bool {
    if let Some((receiver, method, args)) = method_call(n, src)
        && ident(receiver, src) == Some(buffer)
        && matches!(method, "len" | "as_mut_ptr")
        && args.is_empty()
    {
        return true;
    }
    ident(n, src) != Some(buffer)
        && (n.kind() != "macro_invocation"
            || !text(n, src)
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .any(|word| word == buffer))
        && nodes(n)
            .into_iter()
            .map(statement)
            .all(|n| only_length_or_data_pointer(n, buffer, src))
}
