//! Python to facts.

use super::retry as bounds;
use super::{children, line, named_children, squash, text, unquote};
use crate::facts::*;
use anyhow::{Result, anyhow};
use std::collections::{HashMap, HashSet};
use tree_sitter::{Node, Parser};

pub fn extract(src: &str, facts: &mut Facts) -> Result<()> {
    let mut parser = Parser::new();
    parser.set_language(&tree_sitter_python::LANGUAGE.into())?;
    let tree = parser
        .parse(src, None)
        .ok_or_else(|| anyhow!("tree-sitter returned no tree"))?;
    let root = tree.root_node();
    let test = facts.files[0].test;
    let mut x = Py {
        src,
        f: facts,
        block: 0,
        tries: 0,
        loops: 0,
        loop_filter: HashMap::new(),
        test,
    };
    let module = x.f.func(Func {
        file: 0,
        name: "<module>".into(),
        class: None,
        bases: vec![],
        kind: ScopeKind::Module,
        params: vec![],
        line: 1,
        branches: 0,
        tokens: vec![],
        param_decisions: 0,
        parent: None,
        trait_name: None,
        test,
    });
    x.stmts(root, module, &Ctx::default());
    let filters = std::mem::take(&mut x.loop_filter);
    for l in &mut x.f.latest {
        let lid = x.f.sites[l.site as usize].ctx.loop_id;
        l.loop_has_membership_filter =
            lid.is_some_and(|id| filters.get(&id).copied().unwrap_or(false));
    }
    Ok(())
}

struct Py<'a> {
    src: &'a str,
    f: &'a mut Facts,
    block: u32,
    tries: u32,
    loops: u32,
    /// Loops whose body skips items by a membership test against a collection.
    loop_filter: HashMap<u32, bool>,
    test: bool,
}

const GUARD_EXIT: [&str; 4] = [
    "raise_statement",
    "return_statement",
    "continue_statement",
    "break_statement",
];

impl<'a> Py<'a> {
    fn t(&self, n: Node) -> &'a str {
        text(n, self.src)
    }

    fn stmts(&mut self, parent: Node, scope: Id, ctx: &Ctx) {
        self.block += 1;
        let b = self.block;
        for (i, s) in named_children(parent).into_iter().enumerate() {
            if s.kind() == "comment" {
                continue;
            }
            let mut c = ctx.clone();
            c.path.push((b, i as u32));
            self.stmt(s, scope, &c, &[]);
        }
    }

    fn body(&mut self, n: Option<Node>, scope: Id, ctx: &Ctx) {
        if let Some(n) = n {
            self.stmts(n, scope, ctx);
        }
    }

    fn stmt(&mut self, s: Node, scope: Id, ctx: &Ctx, decorators: &[String]) {
        match s.kind() {
            "function_definition" => self.def(s, scope, decorators),
            "class_definition" => self.class(s, scope),
            "decorated_definition" => {
                let decs: Vec<String> = named_children(s)
                    .into_iter()
                    .filter(|c| c.kind() == "decorator")
                    .map(|c| squash(self.t(c).trim_start_matches('@')))
                    .collect();
                // A Hypothesis `@settings(...)` is a call whose arguments question 7 reads; other
                // decorators stay text, so they add no call sites to any rule.
                for d in named_children(s)
                    .into_iter()
                    .filter(|c| c.kind() == "decorator")
                {
                    for c in named_children(d).into_iter().filter(|c| c.kind() == "call") {
                        let callee = c
                            .child_by_field_name("function")
                            .map(|f| self.t(f).to_string())
                            .unwrap_or_default();
                        if callee == "settings" || callee.ends_with(".settings") {
                            self.top_expr(c, scope, ctx);
                        }
                    }
                }
                if let Some(d) = s.child_by_field_name("definition") {
                    self.stmt(d, scope, ctx, &decs);
                }
            }
            "expression_statement" => {
                for c in named_children(s) {
                    self.top_expr(c, scope, ctx);
                }
            }
            "return_statement" => {
                let value = named_children(s).into_iter().next();
                // A literal outcome of a branch is part of the decision a double would re-implement.
                if let Some(v) = value.filter(|v| {
                    matches!(v.kind(), "string" | "integer" | "true" | "false" | "none")
                }) {
                    let t = self.t(v).to_string();
                    self.f.funcs[scope as usize].tokens.push(t);
                }
                let site = self.site(scope, s, ctx);
                let value = value
                    .map(|v| self.pred_expr(v, scope, ctx))
                    .unwrap_or_default();
                self.f.returns.push(Return { site, value });
                self.f.exits.push(Exit {
                    site,
                    kind: EXIT_RETURN,
                });
            }
            "continue_statement" | "break_statement" => {
                let site = self.site(scope, s, ctx);
                let kind = if s.kind() == "break_statement" {
                    EXIT_BREAK
                } else {
                    EXIT_CONTINUE
                };
                self.f.exits.push(Exit { site, kind });
            }
            "if_statement" => self.if_stmt(s, scope, ctx),
            "for_statement" => {
                if let Some(r) = s.child_by_field_name("right") {
                    self.expr(r, scope, ctx);
                }
                self.loops += 1;
                let mut c = ctx.clone();
                c.loop_id = Some(self.loops);
                if let Some(r) = s.child_by_field_name("right") {
                    let site = self.site(scope, s, ctx);
                    let iter = squash(self.t(r));
                    self.f.loops.push(LoopIter {
                        site,
                        id: self.loops,
                        iter,
                    });
                }
                self.body(s.child_by_field_name("body"), scope, &c);
                self.body(
                    s.child_by_field_name("alternative")
                        .and_then(|a| a.child_by_field_name("body")),
                    scope,
                    ctx,
                );
                self.loop_prune(s, scope, &c);
                self.retry(s, scope, ctx);
            }
            "while_statement" => {
                if let Some(cond) = s.child_by_field_name("condition") {
                    self.pred_expr(cond, scope, ctx);
                }
                self.loops += 1;
                let mut c = ctx.clone();
                c.loop_id = Some(self.loops);
                self.body(s.child_by_field_name("body"), scope, &c);
                self.retry(s, scope, ctx);
            }
            "try_statement" => {
                self.tries += 1;
                let id = self.tries;
                let mut c = ctx.clone();
                c.try_body = Some(id);
                c.shielded = ctx.finally_id.is_some();
                self.body(s.child_by_field_name("body"), scope, &c);
                for h in named_children(s) {
                    match h.kind() {
                        "except_clause" | "except_group_clause" => {
                            let mut hc = ctx.clone();
                            hc.handler = Some(id);
                            hc.cond = true;
                            for b in named_children(h) {
                                if b.kind() == "block" {
                                    self.stmts(b, scope, &hc);
                                }
                            }
                        }
                        "else_clause" => self.body(h.child_by_field_name("body"), scope, ctx),
                        "finally_clause" => {
                            let mut fc = ctx.clone();
                            fc.finally = true;
                            fc.finally_id = Some(id);
                            fc.shielded = false;
                            for b in named_children(h) {
                                if b.kind() == "block" {
                                    self.stmts(b, scope, &fc);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            "with_statement" => {
                for c in named_children(s) {
                    if c.kind() == "with_clause" {
                        for item in named_children(c) {
                            self.top_expr(item, scope, ctx);
                        }
                    }
                }
                self.body(s.child_by_field_name("body"), scope, ctx);
            }
            "match_statement" => {
                if let Some(subj) = s.child_by_field_name("subject") {
                    self.note_param_decision(subj, scope);
                    self.expr(subj, scope, ctx);
                }
                if let Some(body) = s.child_by_field_name("body") {
                    for case in named_children(body) {
                        if case.kind() != "case_clause" {
                            continue;
                        }
                        self.f.funcs[scope as usize].branches += 1;
                        for p in named_children(case) {
                            if p.kind() == "case_pattern" {
                                let toks = self.tokens(p);
                                self.f.funcs[scope as usize].tokens.extend(toks);
                            }
                        }
                        let mut c = ctx.clone();
                        c.cond = true;
                        self.body(case.child_by_field_name("consequence"), scope, &c);
                    }
                }
            }
            "raise_statement" | "assert_statement" | "delete_statement" => {
                if s.kind() == "raise_statement" {
                    let site = self.site(scope, s, ctx);
                    self.f.exits.push(Exit {
                        site,
                        kind: EXIT_RAISE,
                    });
                }
                for c in named_children(s) {
                    self.pred_expr(c, scope, ctx);
                }
            }
            "import_statement" | "import_from_statement" => self.import(s),
            _ => {
                for c in named_children(s) {
                    self.expr(c, scope, ctx);
                }
            }
        }
    }

    fn import(&mut self, s: Node) {
        let module = s
            .child_by_field_name("module_name")
            .map(|m| self.t(m).to_string());
        for c in named_children(s) {
            if Some(c) == s.child_by_field_name("module_name") {
                continue;
            }
            let (target, local) = match c.kind() {
                "dotted_name" => (
                    self.t(c).to_string(),
                    self.t(c).split('.').next().unwrap_or("").to_string(),
                ),
                "aliased_import" => {
                    let name = c
                        .child_by_field_name("name")
                        .map(|n| self.t(n))
                        .unwrap_or("");
                    let alias = c
                        .child_by_field_name("alias")
                        .map(|n| self.t(n))
                        .unwrap_or(name);
                    (name.to_string(), alias.to_string())
                }
                _ => continue,
            };
            let full = match &module {
                Some(m) => format!("{m}.{target}"),
                None => target,
            };
            self.f.imports.push((0, local, full));
        }
    }

    fn site(&mut self, scope: Id, n: Node, ctx: &Ctx) -> Id {
        self.f.site(0, scope, line(n), ctx)
    }

    fn params(&mut self, p: Option<Node>) -> Vec<Param> {
        let mut out = vec![];
        let Some(p) = p else { return out };
        for c in named_children(p) {
            let ann = c
                .child_by_field_name("type")
                .map(|t| squash(self.t(t)))
                .unwrap_or_default();
            let (name, default) = match c.kind() {
                "identifier" => (self.t(c).to_string(), None),
                "typed_parameter" => (
                    named_children(c)
                        .into_iter()
                        .find(|x| x.kind() == "identifier")
                        .map(|x| self.t(x).to_string())
                        .unwrap_or_default(),
                    None,
                ),
                "default_parameter" | "typed_default_parameter" => (
                    c.child_by_field_name("name")
                        .map(|x| self.t(x).to_string())
                        .unwrap_or_default(),
                    c.child_by_field_name("value"),
                ),
                "list_splat_pattern" | "dictionary_splat_pattern" => {
                    (self.t(c).trim_start_matches('*').to_string(), None)
                }
                _ => continue,
            };
            let mut param = Param {
                name,
                annotation: ann,
                default_lambda_calls: vec![],
                default_refs: vec![],
            };
            if let Some(d) = default {
                param.default_lambda_calls = self.lambda_calls(d);
                param.default_refs = self.refs(d);
            }
            out.push(param);
        }
        out
    }

    fn def(&mut self, s: Node, scope: Id, decorators: &[String]) {
        let name = s
            .child_by_field_name("name")
            .map(|n| self.t(n).to_string())
            .unwrap_or_default();
        let parent = &self.f.funcs[scope as usize];
        let (class, bases) = if parent.kind == ScopeKind::Class {
            (Some(parent.name.clone()), parent.bases.clone())
        } else {
            (None, vec![])
        };
        let params = self.params(s.child_by_field_name("parameters"));
        let id = self.f.func(Func {
            file: 0,
            name,
            class,
            bases,
            kind: ScopeKind::Function,
            params,
            line: line(s),
            branches: 0,
            tokens: vec![],
            param_decisions: 0,
            parent: Some(scope),
            trait_name: None,
            test: self.test,
        });
        self.body(s.child_by_field_name("body"), id, &Ctx::default());
        self.suite_patch(s, id, decorators);
    }

    fn class(&mut self, s: Node, scope: Id) {
        let name = s
            .child_by_field_name("name")
            .map(|n| self.t(n).to_string())
            .unwrap_or_default();
        let bases = s
            .child_by_field_name("superclasses")
            .map(|b| {
                named_children(b)
                    .into_iter()
                    .filter(|x| x.kind() != "keyword_argument")
                    .map(|x| squash(self.t(x)))
                    .collect()
            })
            .unwrap_or_default();
        let id = self.f.func(Func {
            file: 0,
            name,
            class: None,
            bases,
            kind: ScopeKind::Class,
            params: vec![],
            line: line(s),
            branches: 0,
            tokens: vec![],
            param_decisions: 0,
            parent: Some(scope),
            trait_name: None,
            test: self.test,
        });
        self.body(s.child_by_field_name("body"), id, &Ctx::default());
    }

    fn if_stmt(&mut self, s: Node, scope: Id, ctx: &Ctx) {
        let mut arms: Vec<(Option<Node>, Option<Node>)> = vec![(
            s.child_by_field_name("condition"),
            s.child_by_field_name("consequence"),
        )];
        for alt in children(s) {
            match alt.kind() {
                "elif_clause" => arms.push((
                    alt.child_by_field_name("condition"),
                    alt.child_by_field_name("consequence"),
                )),
                "else_clause" => arms.push((None, alt.child_by_field_name("body"))),
                _ => {}
            }
        }
        let mut first = true;
        for (cond, body) in arms {
            let mut hc = ctx.clone();
            hc.cond = ctx.cond || !first;
            if let Some(cond) = cond {
                self.f.funcs[scope as usize].branches += 1;
                let toks = self.tokens(cond);
                self.f.funcs[scope as usize].tokens.extend(toks);
                self.note_param_decision(cond, scope);
                let e = self.pred_expr(cond, scope, &hc);
                if let Some(body) = body
                    && self.exits(body, &GUARD_EXIT)
                {
                    // A condition whose branch leaves is a check: every call in it decides.
                    for c in self.f.calls.iter_mut().rev().take(64) {
                        if e.calls.contains(&c.site) {
                            c.predicate = true;
                        }
                    }
                }
                if let Some(body) = body {
                    self.deny_check(cond, body, &e, scope, &hc);
                    self.latest_check(cond, body, scope, &hc);
                    if ctx.loop_id.is_some()
                        && self.exits(body, &["continue_statement"])
                        && self.membership(cond)
                    {
                        self.loop_filter.insert(ctx.loop_id.unwrap_or(0), true);
                    }
                }
            }
            let mut bc = ctx.clone();
            bc.cond = ctx.cond || !first;
            let body_block = self.block + 1;
            self.body(body, scope, &bc);
            if let (Some(cond), Some(body)) = (cond, body) {
                self.cond_fact(cond, body, body_block, scope, &hc);
            }
            first = false;
        }
    }

    /// An `if` arm as a fact: its condition's reads, how its body leaves, whether it reports a
    /// violation, and a membership test in the condition.
    fn cond_fact(&mut self, cond: Node, body: Node, body_block: u32, scope: Id, ctx: &Ctx) {
        let site = self.site(scope, cond, ctx);
        let mut e = Expr {
            text: squash(self.t(cond)),
            ..Expr::default()
        };
        walk(cond, &mut |n| {
            if matches!(n.kind(), "identifier" | "attribute")
                && n.parent().is_none_or(|p| p.kind() != "attribute")
            {
                let v = var_name(text(n, self.src));
                if !e.vars.contains(&v) {
                    e.vars.push(v);
                }
            }
        });
        let kids = named_children(body);
        let exit = kids
            .iter()
            .find_map(|c| match c.kind() {
                "return_statement" => Some(EXIT_RETURN),
                "raise_statement" => Some(EXIT_RAISE),
                "continue_statement" => Some(EXIT_CONTINUE),
                "break_statement" => Some(EXIT_BREAK),
                _ => None,
            })
            .unwrap_or(0);
        let fails = kids.iter().any(|c| match c.kind() {
            "raise_statement" | "assert_statement" => true,
            "expression_statement" => {
                let t = self.t(*c);
                let head = t.split('(').next().unwrap_or("");
                head.ends_with(".append")
                    || head.ends_with(".add")
                    || head.ends_with(".extend")
                    || head.ends_with("fail")
                    || head.ends_with("add_error")
            }
            _ => false,
        });
        let mut member = None;
        let mut memberships: Vec<crate::facts::Membership> = vec![];
        walk(cond, &mut |n| {
            if n.kind() != "comparison_operator" {
                return;
            }
            let ops: Vec<String> = children(n)
                .into_iter()
                .filter(|c| !c.is_named())
                .map(|c| squash(text(c, self.src)))
                .collect();
            let negated = ops.iter().any(|o| o == "not in" || o == "notin");
            if !(negated || ops.iter().any(|o| o == "in")) {
                return;
            }
            let Some(rhs) = named_children(n).into_iter().last() else {
                return;
            };
            let table = match rhs.kind() {
                "set" | "tuple" | "list" | "dictionary" => "{literal}".to_string(),
                _ => {
                    let t = text(rhs, self.src);
                    t.split(['.', '(', '[', ' ', '|'])
                        .next()
                        .unwrap_or("")
                        .to_string()
                }
            };
            if !table.is_empty() {
                if member.is_none() {
                    member = Some((table.clone(), negated));
                }
                memberships.push(crate::facts::Membership {
                    lhs: named_children(n)
                        .into_iter()
                        .next()
                        .map(|l| text(l, self.src).to_string())
                        .unwrap_or_default(),
                    rhs: text(rhs, self.src).to_string(),
                    table,
                    negated,
                });
            }
        });
        self.f.conds.push(Cond {
            site,
            body: body_block,
            cond: e,
            exit,
            fails,
            member,
            memberships,
        });
    }

    /// A membership test against a named collection (not a literal tuple, list or set).
    fn membership(&self, cond: Node) -> bool {
        let mut found = false;
        walk(cond, &mut |n| {
            if n.kind() == "comparison_operator" {
                let ops: Vec<String> = children(n)
                    .into_iter()
                    .filter(|c| !c.is_named())
                    .map(|c| self.t(c).to_string())
                    .collect();
                let rhs = named_children(n).into_iter().last();
                if ops.iter().any(|o| o == "in" || o == "not in" || o == "not")
                    && rhs.is_some_and(|r| !matches!(r.kind(), "tuple" | "list" | "set" | "string"))
                {
                    found = true;
                }
            }
        });
        found
    }

    fn exits(&self, body: Node, kinds: &[&str]) -> bool {
        named_children(body)
            .iter()
            .any(|c| kinds.contains(&c.kind()))
    }

    /// A refusal branch guarded by a pattern match: `if PATTERN.search(x): return deny`.
    fn deny_check(&mut self, cond: Node, body: Node, e: &Expr, scope: Id, ctx: &Ctx) {
        let ctext = self.t(cond);
        let pattern_match = e.calls.iter().any(|&s| {
            self.f
                .calls
                .iter()
                .rev()
                .find(|c| c.site == s)
                .is_some_and(|c| {
                    matches!(c.name.as_str(), "search" | "match" | "findall" | "finditer")
                        || (c.name == "any"
                            && c.args.first().is_some_and(|a| a.text.contains(" in ")))
                })
        }) || (ctext.contains(" in ")
            && ctext.chars().any(|c| c.is_ascii_uppercase())
            && is_deny_name(ctext));
        if !pattern_match {
            return;
        }
        let btext = self.t(body).to_ascii_lowercase();
        let refuses = self.exits(body, &["raise_statement"])
            || btext.contains("return false")
            || btext.contains("deny")
            || btext.contains("block")
            || btext.contains("refus")
            || btext.contains("exit(2)")
            || btext.contains("exit(1)")
            || collects_reason(&btext);
        if refuses {
            let site = self.site(scope, cond, ctx);
            self.f.denies.push(DenyMatch {
                site,
                what: squash(ctext),
            });
        }
    }

    /// `if key not in m or newer(v, m[key]): m[key] = v`.
    fn latest_check(&mut self, cond: Node, body: Node, scope: Id, ctx: &Ctx) {
        if cond.kind() != "boolean_operator" {
            return;
        }
        let Some(left) = cond.child_by_field_name("left") else {
            return;
        };
        if left.kind() != "comparison_operator" || !self.t(left).contains("not in") {
            return;
        }
        let parts = named_children(left);
        let (Some(key), Some(map)) = (parts.first(), parts.last()) else {
            return;
        };
        let (key, map) = (squash(self.t(*key)), squash(self.t(*map)));
        let assigns = named_children(body).iter().any(|st| {
            let t = squash(self.t(*st));
            t.starts_with(&format!("{map}[{key}]="))
        });
        if assigns && ctx.loop_id.is_some() {
            let site = self.site(scope, cond, ctx);
            self.f.latest.push(LatestPerKey {
                site,
                map,
                key,
                loop_has_membership_filter: false,
            });
        }
    }

    /// `for e in lines: if <e compared with bound>: kept.append(e)`.
    fn loop_prune(&mut self, s: Node, scope: Id, ctx: &Ctx) {
        let Some(var) = s.child_by_field_name("left").map(|l| self.t(l).to_string()) else {
            return;
        };
        let Some(body) = s.child_by_field_name("body") else {
            return;
        };
        let mut found: Vec<Node> = vec![];
        walk(body, &mut |n| {
            if n.kind() == "if_statement"
                && let (Some(c), Some(k)) = (
                    n.child_by_field_name("condition"),
                    n.child_by_field_name("consequence"),
                )
                && self.t(k).contains(&format!(".append({var})"))
            {
                walk(c, &mut |m| {
                    if m.kind() == "comparison_operator" {
                        found.push(m);
                    }
                });
            }
        });
        for cmp in found {
            let sides = named_children(cmp);
            if let Some(bound) = sides.iter().find(|x| !mentions(self.t(**x), &var)) {
                let site = self.site(scope, cmp, ctx);
                let mut c = ctx.clone();
                c.cond = true;
                let bound = self.expr(*bound, scope, &c);
                self.f.prunes.push(Prune {
                    site,
                    bound,
                    writes_back: true,
                });
            }
        }
    }

    /// A `while True` loop whose handler swallows the error and loops again.
    fn retry(&mut self, s: Node, scope: Id, ctx: &Ctx) {
        let legacy = s
            .child_by_field_name("condition")
            .is_some_and(|cond| matches!(self.t(cond), "True" | "1"));
        let Some(body) = s.child_by_field_name("body") else {
            return;
        };
        let swallowed = |n| {
            let t = self.t(n);
            !t.contains("raise") && !t.contains("return") && !t.contains("break")
        };
        let fresh_client =
            |attempt, handler| self.accepts_and_discards_client(body, attempt, handler);
        let swallows = if legacy {
            let mut swallows = false;
            walk(body, &mut |handler| {
                swallows |= handler.kind() == "except_clause"
                    && swallowed(handler)
                    && handler
                        .parent()
                        .is_some_and(|attempt| !fresh_client(attempt, handler));
            });
            swallows
        } else {
            let index = if s.kind() == "for_statement" {
                let Some(target) = s
                    .child_by_field_name("left")
                    .filter(|n| n.kind() == "identifier")
                else {
                    return;
                };
                Some(self.t(target))
            } else {
                None
            };
            bounds::any_local(body, &|n| {
                n.kind() == "try_statement"
                    && n.child_by_field_name("body").is_some_and(|attempt| {
                        !index.is_some_and(|name| bounds::reads(attempt, name, self.src))
                    })
                    && named_children(n)
                        .into_iter()
                        .any(|child| child.kind() == "except_clause" && swallowed(child))
            })
        };
        if !swallows {
            return;
        }
        let bound = bounds::prove(s, self.src, Lang::Python)
            .or_else(|| legacy.then(|| bounds::fallback(self.t(body), Lang::Python)));
        if let Some(bound) = bound {
            let site = self.site(scope, s, ctx);
            self.f.retries.push(RetryLoop { site, bound });
        }
    }

    fn accepts_and_discards_client(&self, body: Node, attempt: Node, handler: Node) -> bool {
        let stmts = bounds::statements(body);
        let [read, next, ..] = stmts[..] else {
            return false;
        };
        if next != attempt || read.kind() != "expression_statement" && read.kind() != "assignment" {
            return false;
        }
        let assign = if read.kind() == "expression_statement" {
            read.named_child(0).unwrap_or(read)
        } else {
            read
        };
        let Some(binding) = assign.child_by_field_name("left") else {
            return false;
        };
        let [client, _] = named_children(binding)[..] else {
            return false;
        };
        let Some(accept) = assign.child_by_field_name("right") else {
            return false;
        };
        if client.kind() != "identifier" || accept.kind() != "call" {
            return false;
        }
        let Some(socket) = squash(self.t(accept))
            .strip_suffix(".accept()")
            .map(str::to_owned)
        else {
            return false;
        };
        let Some(block) = handler
            .named_child(handler.named_child_count().saturating_sub(1) as u32)
            .filter(|n| n.kind() == "block")
        else {
            return false;
        };
        let [close, again] = bounds::statements(block)[..] else {
            return false;
        };
        let Some(parent) = body.parent().and_then(|n| n.parent()) else {
            return false;
        };
        again.kind() == "continue_statement"
            && squash(self.t(close)) == format!("{}.close()", self.t(client))
            && bounds::statements(parent)
                .into_iter()
                .rev()
                .find(|&n| n.end_byte() <= read.start_byte() && bounds::reads(n, &socket, self.src))
                .is_some_and(|n| {
                    let s = squash(self.t(n));
                    s.starts_with(&format!("{socket}=socket.create_server("))
                })
    }

    /// An autouse fixture in test code that replaces a production name for every test.
    fn suite_patch(&mut self, s: Node, scope: Id, decorators: &[String]) {
        if !self.test
            || !decorators
                .iter()
                .any(|d| d.contains("fixture") && d.contains("autouse=True"))
        {
            return;
        }
        let Some(body) = s.child_by_field_name("body") else {
            return;
        };
        let btext = self.t(body);
        let opt_out = btext.contains("fixturenames")
            || btext.contains("get_closest_marker")
            || btext.contains("request.node");
        let mut found = vec![];
        walk(body, &mut |n| {
            if n.kind() == "call"
                && let Some(f) = n.child_by_field_name("function")
            {
                let ft = squash(self.t(f));
                if ft.ends_with("setattr") || ft.ends_with("patch") || ft.ends_with("patch.object")
                {
                    let args = n
                        .child_by_field_name("arguments")
                        .map(named_children)
                        .unwrap_or_default();
                    // setattr("mod.name", value) and patch("mod.name") name the target in one string;
                    // setattr(obj, "name", value) and patch.object(obj, "name") in two arguments.
                    let take = if args.first().is_some_and(|a| a.kind() == "string") {
                        1
                    } else {
                        2
                    };
                    let target: Vec<String> = args
                        .iter()
                        .take(take)
                        .map(|a| unquote(&squash(self.t(*a))))
                        .collect();
                    found.push((n, target.join(".")));
                }
            }
        });
        for (n, target) in found {
            let site = self.site(scope, n, &Ctx::default());
            self.f.patches.push(SuitePatch {
                site,
                target,
                opt_out,
            });
        }
    }

    /// Counts a condition or match subject that reads one of the function's parameters.
    fn note_param_decision(&mut self, n: Node, scope: Id) {
        let names: HashSet<&str> = self.f.funcs[scope as usize]
            .params
            .iter()
            .map(|p| p.name.as_str())
            .filter(|p| !matches!(*p, "self" | "cls"))
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

    /// Decision tokens of a condition or pattern: dotted names, called names and literals.
    fn tokens(&self, n: Node) -> Vec<String> {
        let mut out = vec![];
        walk(n, &mut |m| match m.kind() {
            "attribute" => out.push(squash(self.t(m))),
            "string" => out.push(self.t(m).to_string()),
            // 0 and 1 compare against almost everything, so only other numbers mark a rule.
            "integer" | "float" if !matches!(self.t(m), "0" | "1") => {
                out.push(self.t(m).to_string())
            }
            "call" => {
                if let Some(f) = m.child_by_field_name("function") {
                    out.push(
                        squash(self.t(f))
                            .rsplit('.')
                            .next()
                            .unwrap_or("")
                            .to_string(),
                    );
                }
            }
            _ => {}
        });
        out
    }

    fn top_expr(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        match n.kind() {
            "assignment" | "augmented_assignment" => self.assign(n, scope, ctx),
            _ => {
                self.expr(n, scope, ctx);
            }
        }
    }

    fn assign(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        let Some(right) = n.child_by_field_name("right") else {
            return;
        };
        let left = n.child_by_field_name("left");
        if right.kind() == "assignment" {
            self.assign(right, scope, ctx);
        }
        let site = self.site(scope, n, ctx);
        let value = self.expr(right, scope, ctx);
        let refs = self.refs(right);
        let lambda_calls = self.lambda_calls(right);
        let targets: Vec<String> = match left {
            Some(l) if matches!(l.kind(), "pattern_list" | "tuple_pattern" | "list_pattern") => {
                named_children(l)
                    .into_iter()
                    .map(|x| var_name(self.t(x)))
                    .collect()
            }
            Some(l) => vec![var_name(self.t(l))],
            None => vec![],
        };
        for target in targets {
            self.f.assigns.push(Assign {
                site,
                target,
                value: value.clone(),
                refs: refs.clone(),
                lambda_calls: lambda_calls.clone(),
            });
        }
    }

    /// An expression whose value is used as a decision: calls directly in it are predicates.
    fn pred_expr(&mut self, n: Node, scope: Id, ctx: &Ctx) -> Expr {
        let start = self.f.calls.len();
        let e = self.expr(n, scope, ctx);
        let inner = if n.kind() == "not_operator" {
            n.child_by_field_name("argument").unwrap_or(n)
        } else {
            n
        };
        if inner.kind() == "call" {
            let l = line(inner);
            for c in &mut self.f.calls[start..] {
                if self.f.sites[c.site as usize].line == l {
                    c.predicate = true;
                    break;
                }
            }
        }
        e
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
            "call" => self.call(n, scope, ctx, e),
            "identifier" => e.vars.push(self.t(n).to_string()),
            "attribute" => {
                let t = squash(self.t(n));
                e.vars.push(var_name(&t));
                if let Some(obj) = n.child_by_field_name("object")
                    && !matches!(obj.kind(), "identifier" | "attribute")
                {
                    self.collect(obj, scope, ctx, e);
                }
            }
            "lambda" => {
                let mut c = ctx.clone();
                c.cond = true;
                c.in_lambda = true;
                if let Some(b) = n.child_by_field_name("body") {
                    let mut inner = Expr::default();
                    self.collect(b, scope, &c, &mut inner);
                }
            }
            "boolean_operator" => {
                if let Some(l) = n.child_by_field_name("left") {
                    self.collect(l, scope, ctx, e);
                }
                if let Some(r) = n.child_by_field_name("right") {
                    let mut c = ctx.clone();
                    c.cond = true;
                    self.collect(r, scope, &c, e);
                }
            }
            "conditional_expression" => {
                self.f.funcs[scope as usize].branches += 1;
                let parts = named_children(n);
                let mut c = ctx.clone();
                c.cond = true;
                for (i, p) in parts.into_iter().enumerate() {
                    if i == 1 {
                        self.collect(p, scope, ctx, e);
                    } else {
                        self.collect(p, scope, &c, e);
                    }
                }
            }
            "list_comprehension"
            | "set_comprehension"
            | "dictionary_comprehension"
            | "generator_expression" => {
                let mut c = ctx.clone();
                c.cond = true;
                self.comprehension_prune(n, scope, &c);
                for p in named_children(n) {
                    self.collect(p, scope, &c, e);
                }
            }
            "comparison_operator" => {
                let parts = named_children(n);
                let op = children(n)
                    .into_iter()
                    .filter(|c| !c.is_named())
                    .map(|c| self.t(c).to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                let site = self.site(scope, n, ctx);
                let mut sides = vec![];
                for p in &parts {
                    let mut s = Expr {
                        text: squash(self.t(*p)),
                        ..Default::default()
                    };
                    self.collect(*p, scope, ctx, &mut s);
                    e.vars.extend(s.vars.iter().cloned());
                    e.calls.extend(s.calls.iter().cloned());
                    sides.push(s);
                }
                if sides.len() >= 2 {
                    let right = sides.pop().unwrap_or_default();
                    let left = sides.swap_remove(0);
                    self.f.compares.push(Compare {
                        site,
                        left,
                        right,
                        op,
                    });
                }
            }
            "named_expression" => {
                let name = n
                    .child_by_field_name("name")
                    .map(|x| self.t(x).to_string())
                    .unwrap_or_default();
                if let Some(v) = n.child_by_field_name("value") {
                    let site = self.site(scope, n, ctx);
                    let value = self.expr(v, scope, ctx);
                    e.vars.extend(value.vars.iter().cloned());
                    e.calls.extend(value.calls.iter().cloned());
                    self.f.assigns.push(Assign {
                        site,
                        target: name,
                        value,
                        refs: vec![],
                        lambda_calls: vec![],
                    });
                }
            }
            "string" => {
                let t = self.t(n);
                let interp = named_children(n)
                    .iter()
                    .any(|c| c.kind() == "interpolation");
                if interp {
                    let mut parts = Expr {
                        text: squash(t),
                        ..Default::default()
                    };
                    let mut segments = vec![];
                    let mut before = String::new();
                    for c in named_children(n) {
                        if c.kind() == "interpolation" {
                            let mut seg = Expr {
                                text: squash(self.t(c)),
                                ..Default::default()
                            };
                            self.collect(c, scope, ctx, &mut seg);
                            parts.vars.extend(seg.vars.iter().cloned());
                            parts.calls.extend(seg.calls.iter().cloned());
                            if before.ends_with('/')
                                && !before.ends_with("://")
                                && !before.contains('?')
                            {
                                segments.push(seg);
                            }
                            before.push_str("{}");
                        } else {
                            before.push_str(self.t(c));
                        }
                    }
                    let body = unquote(t);
                    if body.starts_with('/') || body.contains("://") || body.contains("/{") {
                        let site = self.site(scope, n, ctx);
                        e.vars.extend(parts.vars.iter().cloned());
                        e.calls.extend(parts.calls.iter().cloned());
                        self.f.composes.push(Compose {
                            site,
                            parts,
                            segments,
                            url: true,
                        });
                        return;
                    }
                    e.vars.extend(parts.vars);
                    e.calls.extend(parts.calls);
                } else if self.test {
                    let site = self.site(scope, n, ctx);
                    self.f.strs.push(StrLit {
                        site,
                        text: unquote(t),
                    });
                }
            }
            "binary_operator" => {
                let op = n
                    .child_by_field_name("operator")
                    .map(|o| self.t(o))
                    .unwrap_or("");
                let (l, r) = (
                    n.child_by_field_name("left"),
                    n.child_by_field_name("right"),
                );
                if op == "/"
                    && let (Some(l), Some(r)) = (l, r)
                    && is_pathish(self.t(l))
                {
                    let site = self.site(scope, n, ctx);
                    let parts = self.expr(r, scope, ctx);
                    e.vars.extend(parts.vars.iter().cloned());
                    e.calls.extend(parts.calls.iter().cloned());
                    self.collect(l, scope, ctx, e);
                    let segments = vec![parts.clone()];
                    self.f.composes.push(Compose {
                        site,
                        parts,
                        segments,
                        url: false,
                    });
                    return;
                }
                for c in named_children(n) {
                    self.collect(c, scope, ctx, e);
                }
            }
            _ => {
                for c in named_children(n) {
                    self.collect(c, scope, ctx, e);
                }
            }
        }
    }

    fn comprehension_prune(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        let var = named_children(n)
            .into_iter()
            .find(|c| c.kind() == "for_in_clause")
            .and_then(|f| f.child_by_field_name("left"))
            .map(|l| self.t(l).to_string());
        let Some(var) = var else { return };
        for c in named_children(n) {
            if c.kind() != "if_clause" {
                continue;
            }
            let mut cmps = vec![];
            walk(c, &mut |m| {
                if m.kind() == "comparison_operator" {
                    cmps.push(m);
                }
            });
            for cmp in cmps {
                let sides = named_children(cmp);
                if sides.iter().any(|x| mentions(self.t(*x), &var))
                    && let Some(bound) = sides.iter().find(|x| !mentions(self.t(**x), &var))
                    && !matches!(
                        bound.kind(),
                        "string" | "integer" | "none" | "true" | "false" | "tuple" | "list" | "set"
                    )
                {
                    let site = self.site(scope, cmp, ctx);
                    let mut inner = Expr {
                        text: squash(self.t(*bound)),
                        ..Default::default()
                    };
                    let save = self.f.compares.len();
                    self.collect(*bound, scope, ctx, &mut inner);
                    self.f.compares.truncate(save);
                    self.f.prunes.push(Prune {
                        site,
                        bound: inner,
                        writes_back: false,
                    });
                }
            }
        }
    }

    fn call(&mut self, n: Node, scope: Id, ctx: &Ctx, e: &mut Expr) {
        let func = n.child_by_field_name("function");
        let full = func.map(|f| squash(self.t(f))).unwrap_or_default();
        let (recv, name) = match full.rsplit_once('.') {
            Some((r, nm)) if func.is_some_and(|f| f.kind() == "attribute") => {
                (r.to_string(), nm.to_string())
            }
            _ => (String::new(), full.clone()),
        };
        let site = self.site(scope, n, ctx);
        e.calls.push(site);
        if let Some(f) = func {
            match f.kind() {
                "attribute" => {
                    if let Some(obj) = f.child_by_field_name("object") {
                        self.collect(obj, scope, ctx, e);
                    }
                }
                "identifier" => {}
                _ => self.collect(f, scope, ctx, e),
            }
        }
        let mut args = vec![];
        let mut kwargs = vec![];
        let mut str_args = vec![];
        let argnodes = n
            .child_by_field_name("arguments")
            .map(named_children)
            .unwrap_or_default();
        for a in &argnodes {
            if a.kind() == "string"
                && !named_children(*a)
                    .iter()
                    .any(|c| c.kind() == "interpolation")
            {
                str_args.push(unquote(self.t(*a)));
            }
            if a.kind() == "keyword_argument" {
                let k = a
                    .child_by_field_name("name")
                    .map(|x| self.t(x).to_string())
                    .unwrap_or_default();
                if let Some(v) = a.child_by_field_name("value") {
                    let ex = self.expr(v, scope, ctx);
                    e.vars.extend(ex.vars.iter().cloned());
                    e.calls.extend(ex.calls.iter().cloned());
                    kwargs.push((k, ex));
                }
            } else {
                let ex = self.expr(*a, scope, ctx);
                e.vars.extend(ex.vars.iter().cloned());
                e.calls.extend(ex.calls.iter().cloned());
                args.push(ex);
            }
        }
        let dynamic = match name.as_str() {
            "eval" | "exec" | "__import__" => Some(name.clone()),
            "getattr" | "setattr" | "import_module"
                if recv.is_empty() || recv.ends_with("importlib") =>
            {
                let lit = argnodes
                    .get(if name == "import_module" { 0 } else { 1 })
                    .is_some_and(|a| a.kind() == "string");
                (!lit).then(|| format!("{name} with a computed name"))
            }
            _ => None,
        };
        let dynamic = dynamic.or_else(|| {
            (!self.test
                && (full.ends_with("monkeypatch.setattr")
                    || full == "mock.patch"
                    || full == "patch"))
                .then(|| "monkeypatching in production code".to_string())
        });
        if let Some(construct) = dynamic {
            self.f.dyns.push(Dyn { site, construct });
        }
        self.f.calls.push(Call {
            site,
            full,
            name,
            recv,
            nargs: args.len() as u32,
            args,
            kwargs,
            str_args,
            predicate: false,
            output_only: false,
            pipe_to: vec![],
        });
    }

    /// Dotted names the expression references without calling them.
    fn refs(&self, n: Node) -> Vec<String> {
        let mut out = vec![];
        refs_into(n, self.src, &mut out);
        out
    }

    fn lambda_calls(&self, n: Node) -> Vec<String> {
        let mut out = vec![];
        walk(n, &mut |m| {
            if m.kind() == "lambda"
                && let Some(b) = m.child_by_field_name("body")
            {
                walk(b, &mut |c| {
                    if c.kind() == "call"
                        && let Some(f) = c.child_by_field_name("function")
                    {
                        out.push(squash(self.t(f)));
                    }
                });
            }
        });
        out
    }
}

fn refs_into(n: Node, src: &str, out: &mut Vec<String>) {
    match n.kind() {
        "call" | "lambda" => {}
        "attribute" | "identifier" => out.push(squash(text(n, src))),
        _ => {
            for c in named_children(n) {
                refs_into(c, src, out);
            }
        }
    }
}

pub fn walk<'t>(n: Node<'t>, f: &mut impl FnMut(Node<'t>)) {
    f(n);
    for c in named_children(n) {
        walk(c, f);
    }
}

/// `self.x.y` -> `self.x`; `a.b` -> `a`; other text unchanged.
pub fn var_name(t: &str) -> String {
    let t = t.trim();
    let mut parts = t.split('.');
    match (parts.next(), parts.next()) {
        (Some("self"), Some(attr)) => {
            format!("self.{}", attr.split(['[', '(']).next().unwrap_or(attr))
        }
        (Some(first), _) => first.split(['[', '(']).next().unwrap_or(first).to_string(),
        _ => t.to_string(),
    }
}

fn mentions(t: &str, var: &str) -> bool {
    t.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|w| w == var)
}

fn is_pathish(t: &str) -> bool {
    let low = t.to_ascii_lowercase();
    [
        "root", "dir", "path", "base", "home", "folder", "parent", "store",
    ]
    .iter()
    .any(|w| low.contains(w))
}

/// A branch that records why the input is refused, for a caller that refuses on any reason.
fn collects_reason(body: &str) -> bool {
    [
        "hits",
        "reasons",
        "problems",
        "violations",
        "refusals",
        "denied",
        "blocked",
    ]
    .iter()
    .any(|w| body.contains(&format!("{w}.append(")) || body.contains(&format!("{w}.add(")))
}

fn is_deny_name(t: &str) -> bool {
    let up = t.to_ascii_uppercase();
    [
        "DENY", "BLOCK", "FORBID", "REFUSE", "BAN", "INTERNAL", "PRIVATE",
    ]
    .iter()
    .any(|w| up.contains(w))
}

#[allow(dead_code)]
fn is_guard_exit(kind: &str) -> bool {
    GUARD_EXIT.contains(&kind)
}
