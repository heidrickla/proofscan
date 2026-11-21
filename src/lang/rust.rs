//! Rust to facts.

use super::retry as bounds;
use super::{line, named_children, squash, text, unquote};
use crate::facts::*;
use crate::lang::python::walk;
use anyhow::{Result, anyhow};
use tree_sitter::{Node, Parser};

mod retry;

pub fn extract(src: &str, facts: &mut Facts) -> Result<()> {
    let mut parser = Parser::new();
    parser.set_language(&tree_sitter_rust::LANGUAGE.into())?;
    let tree = parser
        .parse(src, None)
        .ok_or_else(|| anyhow!("tree-sitter returned no tree"))?;
    let root = tree.root_node();
    let test = facts.files[0].test;
    let mut x = Rs {
        src,
        f: facts,
        block: 0,
        loops: 0,
    };
    let module = x.f.func(scope_func(
        "<module>",
        ScopeKind::Module,
        None,
        None,
        None,
        root,
        test,
    ));
    x.items(root, module, test);
    Ok(())
}

struct Rs<'a> {
    src: &'a str,
    f: &'a mut Facts,
    block: u32,
    loops: u32,
}

fn scope_func(
    name: &str,
    kind: ScopeKind,
    class: Option<String>,
    trait_name: Option<String>,
    parent: Option<Id>,
    n: Node,
    test: bool,
) -> Func {
    Func {
        file: 0,
        name: name.into(),
        class,
        bases: vec![],
        kind,
        params: vec![],
        line: line(n),
        branches: 0,
        tokens: vec![],
        param_decisions: 0,
        parent,
        trait_name,
        test,
    }
}

const COMMON: [&str; 16] = [
    "len",
    "iter",
    "any",
    "all",
    "clone",
    "unwrap",
    "to_string",
    "is_some",
    "is_none",
    "Some",
    "None",
    "Ok",
    "Err",
    "true",
    "false",
    "as_str",
];

impl<'a> Rs<'a> {
    fn t(&self, n: Node) -> &'a str {
        text(n, self.src)
    }

    /// Items of a file, module or impl body; attributes mark the item after them as test code.
    fn items(&mut self, parent: Node, scope: Id, test: bool) {
        let mut attr_test = false;
        for item in named_children(parent) {
            match item.kind() {
                "attribute_item" => {
                    let t = self.t(item);
                    if t.contains("cfg(test)") || t.contains("#[test]") || t.contains("tokio::test")
                    {
                        attr_test = true;
                    }
                    continue;
                }
                "function_item" => self.function(item, scope, None, None, test || attr_test),
                "mod_item" => {
                    if let Some(body) = item.child_by_field_name("body") {
                        self.items(body, scope, test || attr_test);
                    }
                }
                "impl_item" => {
                    let ty = item
                        .child_by_field_name("type")
                        .map(|t| type_name(self.t(t)))
                        .unwrap_or_default();
                    let tr = item
                        .child_by_field_name("trait")
                        .map(|t| type_name(self.t(t)));
                    if let Some(body) = item.child_by_field_name("body") {
                        for m in named_children(body) {
                            if m.kind() == "function_item" {
                                self.function(
                                    m,
                                    scope,
                                    Some(ty.clone()),
                                    tr.clone(),
                                    test || attr_test,
                                );
                            }
                        }
                    }
                }
                "trait_item" => {
                    let tr = item
                        .child_by_field_name("name")
                        .map(|t| self.t(t).to_string())
                        .unwrap_or_default();
                    if let Some(body) = item.child_by_field_name("body") {
                        for m in named_children(body) {
                            if m.kind() == "function_item" {
                                self.function(
                                    m,
                                    scope,
                                    Some(tr.clone()),
                                    Some(tr.clone()),
                                    test || attr_test,
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
            attr_test = false;
        }
    }

    fn function(
        &mut self,
        n: Node,
        scope: Id,
        class: Option<String>,
        trait_name: Option<String>,
        test: bool,
    ) {
        let name = n
            .child_by_field_name("name")
            .map(|x| self.t(x).to_string())
            .unwrap_or_default();
        let mut func = scope_func(
            &name,
            ScopeKind::Function,
            class,
            trait_name,
            Some(scope),
            n,
            test,
        );
        if let Some(ps) = n.child_by_field_name("parameters") {
            for p in named_children(ps) {
                let pname = match p.kind() {
                    "self_parameter" => "self".to_string(),
                    "parameter" => p
                        .child_by_field_name("pattern")
                        .map(|x| squash(self.t(x)))
                        .unwrap_or_default(),
                    _ => continue,
                };
                func.params.push(Param {
                    name: pname,
                    annotation: String::new(),
                    default_lambda_calls: vec![],
                    default_refs: vec![],
                });
            }
        }
        let id = self.f.func(func);
        if let Some(body) = n.child_by_field_name("body") {
            self.block_stmts(body, id, &Ctx::default());
        }
    }

    fn block_stmts(&mut self, block: Node, scope: Id, ctx: &Ctx) {
        self.block += 1;
        let b = self.block;
        for (i, s) in named_children(block).into_iter().enumerate() {
            let mut c = ctx.clone();
            c.path.push((b, i as u32));
            match s.kind() {
                "let_declaration" => {
                    let target = s
                        .child_by_field_name("pattern")
                        .map(|p| squash(self.t(p)))
                        .unwrap_or_default();
                    if let Some(v) = s.child_by_field_name("value") {
                        let site = self.f.site(0, scope, line(s), &c);
                        let value = self.expr(v, scope, &c);
                        for t in pattern_names(&target) {
                            self.f.assigns.push(Assign {
                                site,
                                target: t,
                                value: value.clone(),
                                refs: vec![],
                                lambda_calls: vec![],
                            });
                        }
                    }
                }
                "expression_statement" => {
                    for e in named_children(s) {
                        self.expr(e, scope, &c);
                    }
                }
                "function_item" => {
                    self.function(s, scope, None, None, self.f.funcs[scope as usize].test)
                }
                "attribute_item" | "line_comment" | "block_comment" => {}
                _ => {
                    self.expr(s, scope, &c);
                }
            }
        }
    }

    fn expr(&mut self, n: Node, scope: Id, ctx: &Ctx) -> Expr {
        let mut e = Expr {
            text: squash(self.t(n)),
            ..Default::default()
        };
        self.collect(n, scope, ctx, &mut e);
        e
    }

    fn collect(&mut self, n: Node, scope: Id, ctx: &Ctx, e: &mut Expr) {
        match n.kind() {
            "call_expression" => self.call(n, scope, ctx, e),
            "try_expression" => {
                for operand in named_children(n) {
                    if operand.kind() == "call_expression" {
                        let site = self.f.site(0, scope, line(operand), ctx);
                        self.f.result_flows.push(ResultFlow {
                            site,
                            byte: operand.start_byte(),
                            kind: ResultFlowKind::Propagate {
                                call: squash(self.t(operand)),
                            },
                        });
                    }
                    self.collect(operand, scope, ctx, e);
                }
            }
            "macro_invocation" => {
                let name = n
                    .child_by_field_name("macro")
                    .map(|m| squash(self.t(m)))
                    .unwrap_or_default();
                let site = self.f.site(0, scope, line(n), ctx);
                e.calls.push(site);
                let args = Expr {
                    text: squash(self.t(n)),
                    ..Default::default()
                };
                self.f.calls.push(Call {
                    site,
                    full: format!("{name}!"),
                    name: format!("{name}!"),
                    recv: String::new(),
                    args: vec![args],
                    kwargs: vec![],
                    str_args: vec![],
                    predicate: false,
                    nargs: 1,
                    output_only: false,
                    pipe_to: vec![],
                });
            }
            "identifier" | "self" => e.vars.push(self.t(n).to_string()),
            "field_expression" => {
                let t = squash(self.t(n));
                e.vars.push(crate::lang::python::var_name(&t));
                if let Some(v) = n.child_by_field_name("value")
                    && !matches!(v.kind(), "identifier" | "self" | "field_expression")
                {
                    self.collect(v, scope, ctx, e);
                }
            }
            "block" => self.block_stmts(n, scope, ctx),
            "if_expression" => {
                self.f.funcs[scope as usize].branches += 1;
                if let Some(c) = n.child_by_field_name("condition") {
                    if let Some(returned) =
                        n.child_by_field_name("consequence").and_then(returned_call)
                    {
                        let site = self.f.site(0, scope, line(n), ctx);
                        self.f.result_flows.push(ResultFlow {
                            site,
                            byte: n.start_byte(),
                            kind: ResultFlowKind::Reject {
                                condition: squash(self.t(c)),
                                returned: squash(self.t(returned)),
                            },
                        });
                    }
                    let toks = self.tokens(c);
                    self.f.funcs[scope as usize].tokens.extend(toks);
                    self.note_param_decision(c, scope);
                    self.collect(c, scope, ctx, e);
                }
                let mut bc = ctx.clone();
                bc.cond = true;
                if let Some(b) = n.child_by_field_name("consequence") {
                    self.block_stmts(b, scope, &bc);
                }
                if let Some(a) = n.child_by_field_name("alternative") {
                    self.collect(a, scope, &bc, e);
                }
            }
            "match_expression" => {
                if let Some(v) = n.child_by_field_name("value") {
                    self.note_param_decision(v, scope);
                    self.collect(v, scope, ctx, e);
                }
                let mut bc = ctx.clone();
                bc.cond = true;
                if let Some(body) = n.child_by_field_name("body") {
                    for arm in named_children(body) {
                        if arm.kind() != "match_arm" {
                            continue;
                        }
                        self.f.funcs[scope as usize].branches += 1;
                        let toks = self.tokens(arm);
                        self.f.funcs[scope as usize].tokens.extend(toks);
                        for c in named_children(arm) {
                            self.collect(c, scope, &bc, e);
                        }
                    }
                }
            }
            "closure_expression" => {
                let mut c = ctx.clone();
                c.cond = true;
                c.in_lambda = true;
                if let Some(b) = n.child_by_field_name("body") {
                    let mut inner = Expr::default();
                    self.collect(b, scope, &c, &mut inner);
                }
            }
            "loop_expression" | "while_expression" | "for_expression" => {
                self.loops += 1;
                let mut c = ctx.clone();
                c.loop_id = Some(self.loops);
                if let Some(v) = n.child_by_field_name("value")
                    && n.kind() == "for_expression"
                {
                    let site = self.f.site(0, scope, line(n), ctx);
                    let iter = squash(self.t(v));
                    self.f.loops.push(LoopIter {
                        site,
                        id: self.loops,
                        iter,
                    });
                }
                for ch in named_children(n) {
                    if ch.kind() == "block" {
                        self.block_stmts(ch, scope, &c);
                    } else {
                        self.collect(ch, scope, ctx, e);
                    }
                }
                self.retry(n, scope, ctx);
            }
            "binary_expression" => {
                let op = n
                    .child_by_field_name("operator")
                    .map(|o| self.t(o).to_string())
                    .unwrap_or_default();
                let (l, r) = (
                    n.child_by_field_name("left"),
                    n.child_by_field_name("right"),
                );
                if matches!(op.as_str(), "<" | ">" | "<=" | ">=" | "==" | "!=")
                    && let (Some(l), Some(r)) = (l, r)
                {
                    let site = self.f.site(0, scope, line(n), ctx);
                    let left = self.expr(l, scope, ctx);
                    let right = self.expr(r, scope, ctx);
                    e.vars
                        .extend(left.vars.iter().cloned().chain(right.vars.iter().cloned()));
                    e.calls.extend(
                        left.calls
                            .iter()
                            .cloned()
                            .chain(right.calls.iter().cloned()),
                    );
                    self.f.compares.push(Compare {
                        site,
                        left,
                        right,
                        op,
                    });
                    return;
                }
                if matches!(op.as_str(), "&&" | "||") {
                    if let Some(l) = l {
                        self.collect(l, scope, ctx, e);
                    }
                    if let Some(r) = r {
                        let mut c = ctx.clone();
                        c.cond = true;
                        self.collect(r, scope, &c, e);
                    }
                    return;
                }
                for c in named_children(n) {
                    self.collect(c, scope, ctx, e);
                }
            }
            "assignment_expression" | "compound_assignment_expr" => {
                let target = n
                    .child_by_field_name("left")
                    .map(|x| crate::lang::python::var_name(&squash(self.t(x))))
                    .unwrap_or_default();
                if let Some(r) = n.child_by_field_name("right") {
                    let site = self.f.site(0, scope, line(n), ctx);
                    let value = self.expr(r, scope, ctx);
                    self.f.assigns.push(Assign {
                        site,
                        target,
                        value,
                        refs: vec![],
                        lambda_calls: vec![],
                    });
                }
            }
            "return_expression" => {
                let site = self.f.site(0, scope, line(n), ctx);
                let value = named_children(n)
                    .into_iter()
                    .next()
                    .map(|v| self.expr(v, scope, ctx))
                    .unwrap_or_default();
                self.f.returns.push(Return { site, value });
            }
            "string_literal" => {
                if self.f.funcs[scope as usize].test {
                    let site = self.f.site(0, scope, line(n), ctx);
                    self.f.strs.push(StrLit {
                        site,
                        text: unquote(self.t(n)),
                    });
                }
            }
            _ => {
                for c in named_children(n) {
                    self.collect(c, scope, ctx, e);
                }
            }
        }
    }

    fn call(&mut self, n: Node, scope: Id, ctx: &Ctx, e: &mut Expr) {
        let mut func = n.child_by_field_name("function");
        if let Some(f) = func
            && f.kind() == "generic_function"
        {
            func = f.child_by_field_name("function");
        }
        let full = func.map(|f| squash(self.t(f))).unwrap_or_default();
        let (recv, name) = match func.map(|f| f.kind()) {
            Some("field_expression") => {
                let f = func.unwrap_or(n);
                let v = f
                    .child_by_field_name("value")
                    .map(|v| squash(self.t(v)))
                    .unwrap_or_default();
                let m = f
                    .child_by_field_name("field")
                    .map(|v| self.t(v).to_string())
                    .unwrap_or_default();
                (v, m)
            }
            Some("scoped_identifier") => match full.rsplit_once("::") {
                Some((p, nm)) => (p.to_string(), nm.to_string()),
                None => (String::new(), full.clone()),
            },
            _ => (String::new(), full.clone()),
        };
        let site = self.f.site(0, scope, line(n), ctx);
        e.calls.push(site);
        if let Some(f) = func
            && f.kind() == "field_expression"
            && let Some(v) = f.child_by_field_name("value")
        {
            self.collect(v, scope, ctx, e);
        }
        let mut args = vec![];
        let mut str_args = vec![];
        for a in n
            .child_by_field_name("arguments")
            .map(named_children)
            .unwrap_or_default()
        {
            // A literal, or the literals of an array passed by reference (`&["snapshot.create", vm]`).
            let mut lit = a;
            while lit.kind() == "reference_expression" {
                match lit.child_by_field_name("value") {
                    Some(v) => lit = v,
                    None => break,
                }
            }
            if lit.kind() == "array_expression" {
                for x in named_children(lit) {
                    if x.kind() == "string_literal" {
                        str_args.push(unquote(self.t(x)));
                    }
                }
            }
            if a.kind() == "string_literal" {
                str_args.push(unquote(self.t(a)));
            }
            let ex = self.expr(a, scope, ctx);
            e.vars.extend(ex.vars.iter().cloned());
            e.calls.extend(ex.calls.iter().cloned());
            args.push(ex);
        }
        self.f.calls.push(Call {
            site,
            full,
            name,
            recv,
            nargs: args.len() as u32,
            args,
            kwargs: vec![],
            str_args,
            predicate: false,
            output_only: false,
            pipe_to: vec![],
        });
    }

    /// A `loop` that swallows an `Err` and goes round again.
    fn retry(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        let t = self.t(n);
        let legacy = n.kind() == "loop_expression";
        let candidate =
            retry::retries_operation(n, self.src) || legacy && retry::unmodeled_retry(n, self.src);
        let progress = legacy
            .then(|| retry::input_progress(n, self.src, candidate))
            .flatten();
        let bound = progress
            .or_else(|| retry::protocol::prove(n, self.src))
            .or_else(|| {
                candidate
                    .then(|| bounds::prove(n, self.src, Lang::Rust))
                    .flatten()
            })
            .or_else(|| {
                (candidate && t.contains(".push_back("))
                    .then(|| retry::unproven_requeue(n, self.src))
                    .flatten()
            })
            .or_else(|| {
                candidate
                    .then(|| retry::protocol::unresolved_progress(n, self.src))
                    .flatten()
            })
            .or_else(|| {
                (candidate && (legacy || t.contains(".push_back(")))
                    .then(|| bounds::fallback(t, Lang::Rust))
            })
            .or_else(|| {
                (legacy && t.contains(".pending()") && retry::retries_pending_batch(n, self.src))
                    .then(|| {
                        if retry::records_failed_delivery(n, self.src) {
                            RetryBound::PendingDelivery
                        } else {
                            RetryBound::UnknownBatch
                        }
                    })
            });
        if let Some(bound) = bound {
            let site = self.f.site(0, scope, line(n), ctx);
            self.f.retries.push(RetryLoop { site, bound });
        }
    }

    /// Counts a condition or match subject that reads one of the function's parameters.
    fn note_param_decision(&mut self, n: Node, scope: Id) {
        let names: std::collections::HashSet<&str> = self.f.funcs[scope as usize]
            .params
            .iter()
            .map(|p| p.name.as_str())
            .filter(|p| *p != "self")
            .collect();
        let mut hit = false;
        walk(n, &mut |m| {
            if m.kind() == "identifier" && names.contains(self.t(m)) {
                hit = true;
            }
        });
        if hit {
            self.f.funcs[scope as usize].param_decisions += 1;
        }
    }

    fn tokens(&self, n: Node) -> Vec<String> {
        let mut out = vec![];
        walk(n, &mut |m| match m.kind() {
            "scoped_identifier" => out.push(squash(self.t(m))),
            "call_expression" => {
                if let Some(f) = m.child_by_field_name("function") {
                    let t = squash(self.t(f));
                    let last = t.rsplit(['.', ':']).next().unwrap_or("").to_string();
                    if !COMMON.contains(&last.as_str()) {
                        out.push(last);
                    }
                }
            }
            "string_literal" => out.push(self.t(m).to_string()),
            _ => {}
        });
        out
    }
}

fn returned_call(block: Node<'_>) -> Option<Node<'_>> {
    let statements: Vec<_> = named_children(block)
        .into_iter()
        .filter(|n| !matches!(n.kind(), "line_comment" | "block_comment"))
        .collect();
    let [statement] = statements.as_slice() else {
        return None;
    };
    let value = if statement.kind() == "expression_statement" {
        statement.named_child(0)?
    } else {
        *statement
    };
    if value.kind() != "return_expression" {
        return None;
    }
    value
        .named_child(0)
        .filter(|n| n.kind() == "call_expression")
}

fn type_name(t: &str) -> String {
    let t = t.trim().trim_start_matches('&');
    let t = t.split('<').next().unwrap_or(t);
    t.rsplit("::").next().unwrap_or(t).trim().to_string()
}

fn pattern_names(p: &str) -> Vec<String> {
    p.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|w| {
            !w.is_empty()
                && !matches!(*w, "mut" | "ref" | "Some" | "Ok" | "Err" | "_")
                && !w.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        })
        .map(str::to_string)
        .collect()
}
