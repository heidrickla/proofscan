//! JavaScript, bash and PowerShell to facts: functions, calls and commands, dynamic evaluation
//! and unbounded retry loops. Scripts carry no classes or imports worth resolving.

use super::retry as bounds;
use super::{line, named_children, squash, text};
use crate::facts::*;
use crate::lang::python::walk;
use anyhow::{Result, anyhow};
use tree_sitter::{Node, Parser};

pub fn extract(src: &str, lang: Lang, facts: &mut Facts) -> Result<()> {
    let mut parser = Parser::new();
    match lang {
        Lang::JavaScript => parser.set_language(&tree_sitter_javascript::LANGUAGE.into())?,
        Lang::Bash => parser.set_language(&tree_sitter_bash::LANGUAGE.into())?,
        Lang::PowerShell => parser.set_language(&tree_sitter_powershell::LANGUAGE.into())?,
        _ => return Err(anyhow!("not a script language")),
    }
    let tree = parser
        .parse(src, None)
        .ok_or_else(|| anyhow!("tree-sitter returned no tree"))?;
    let root = tree.root_node();
    let test = facts.files[0].test;
    let module = facts.func(Func {
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
    let mut x = Sc {
        src,
        f: facts,
        lang,
        test,
        block: 0,
    };
    x.visit(root, module, &Ctx::default());
    Ok(())
}

struct Sc<'a> {
    src: &'a str,
    f: &'a mut Facts,
    lang: Lang,
    test: bool,
    block: u32,
}

impl<'a> Sc<'a> {
    fn t(&self, n: Node) -> &'a str {
        text(n, self.src)
    }

    fn visit(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        let kind = n.kind();
        let is_fn = matches!(
            (self.lang, kind),
            (
                Lang::JavaScript,
                "function_declaration" | "method_definition"
            ) | (Lang::Bash, "function_definition")
                | (Lang::PowerShell, "function_statement")
        );
        if is_fn {
            let name = n
                .child_by_field_name("name")
                .map(|x| self.t(x).to_string())
                .or_else(|| {
                    named_children(n)
                        .into_iter()
                        .find(|c| c.kind().contains("name"))
                        .map(|c| self.t(c).to_string())
                })
                .unwrap_or_default();
            let id = self.f.func(Func {
                file: 0,
                name,
                class: None,
                bases: vec![],
                kind: ScopeKind::Function,
                params: vec![],
                line: line(n),
                branches: 0,
                tokens: vec![],
                param_decisions: 0,
                parent: Some(scope),
                trait_name: None,
                test: self.test,
            });
            for c in named_children(n) {
                self.visit(c, id, &Ctx::default());
            }
            return;
        }
        let mut ctx = ctx.clone();
        if matches!(
            kind,
            "if_statement"
                | "if_clause"
                | "elif_clause"
                | "else_clause"
                | "case_statement"
                | "switch_statement"
        ) {
            self.f.funcs[scope as usize].branches += 1;
            ctx.cond = true;
        }
        if matches!(
            kind,
            "statement_block" | "compound_statement" | "script_block" | "do_group"
        ) {
            self.block += 1;
            ctx.path.push((self.block, 0));
        }
        match (self.lang, kind) {
            (Lang::JavaScript, "call_expression" | "new_expression") => {
                let func = n
                    .child_by_field_name("function")
                    .or_else(|| n.child_by_field_name("constructor"));
                let full = func.map(|f| squash(self.t(f))).unwrap_or_default();
                let full = if kind == "new_expression" {
                    format!("new {full}")
                } else {
                    full
                };
                self.call(n, scope, &ctx, full);
            }
            (Lang::Bash, "command") => {
                let full = n
                    .child_by_field_name("name")
                    .map(|f| squash(self.t(f)))
                    .unwrap_or_default();
                self.call(n, scope, &ctx, full);
            }
            (Lang::PowerShell, "command") => {
                let full = named_children(n)
                    .into_iter()
                    .next()
                    .map(|f| squash(self.t(f)))
                    .unwrap_or_default();
                self.call(n, scope, &ctx, full);
            }
            (Lang::PowerShell, "invokation_expression" | "invocation_expression") => {
                let full = squash(self.t(n))
                    .split('(')
                    .next()
                    .unwrap_or("")
                    .to_string();
                self.call(n, scope, &ctx, full);
            }
            (Lang::Bash, "while_statement")
            | (Lang::PowerShell, "while_statement")
            | (Lang::JavaScript, "while_statement") => {
                self.retry(n, scope, &ctx);
            }
            _ => {}
        }
        for c in named_children(n) {
            self.visit(c, scope, &ctx);
        }
    }

    fn call(&mut self, n: Node, scope: Id, ctx: &Ctx, full: String) {
        let (recv, name) = match full.rsplit_once('.') {
            Some((r, nm)) if self.lang == Lang::JavaScript => (r.to_string(), nm.to_string()),
            _ => (String::new(), full.clone()),
        };
        let site = self.f.site(0, scope, line(n), ctx);
        let whole = squash(self.t(n));
        let nargs = match self.lang {
            Lang::JavaScript => n
                .child_by_field_name("arguments")
                .map_or(0, |a| named_children(a).len()),
            Lang::Bash => named_children(n)
                .iter()
                .filter(|c| c.kind() != "command_name" && c.kind() != "variable_assignment")
                .count(),
            _ => named_children(n).len().saturating_sub(1),
        } as u32;
        let mut output_only = false;
        let mut pipe_to = vec![];
        let mut str_args = vec![];
        if self.lang == Lang::Bash {
            output_only = true;
            let mut p = n.parent();
            while let Some(x) = p {
                if matches!(x.kind(), "command_substitution" | "process_substitution") {
                    output_only = false;
                    break;
                }
                p = x.parent();
            }
            // Output redirected to a file is not printed.
            if let Some(x) = n.parent()
                && x.kind() == "redirected_statement"
                && named_children(x)
                    .iter()
                    .any(|r| r.kind() == "file_redirect" && !self.t(*r).starts_with("2>"))
            {
                output_only = false;
            }
            // `cmd 2>&1 | tail`: the pipeline holds the redirected statement, not the command.
            let member = match n.parent() {
                Some(r) if r.kind() == "redirected_statement" => r,
                _ => n,
            };
            if let Some(x) = member.parent()
                && x.kind() == "pipeline"
            {
                let after: Vec<String> = named_children(x)
                    .into_iter()
                    .skip_while(|c| c.id() != member.id())
                    .skip(1)
                    .map(|c| squash(self.t(c)))
                    .collect();
                pipe_to = after;
            }
            for a in named_children(n) {
                if matches!(a.kind(), "word" | "string" | "raw_string" | "concatenation") {
                    str_args.push(
                        self.t(a)
                            .trim_matches(|c| c == '\'' || c == '"')
                            .to_string(),
                    );
                }
            }
        }
        let args = Expr {
            text: self.t(n).to_string(),
            ..Default::default()
        };
        let low = name.to_ascii_lowercase();
        let construct = match (self.lang, low.as_str()) {
            (Lang::JavaScript, "eval") | (Lang::JavaScript, "function") => Some("eval"),
            (Lang::Bash, "eval") => Some("eval"),
            (Lang::Bash, "source" | ".") if whole.contains('$') => {
                Some("source of a computed path")
            }
            (Lang::PowerShell, "invoke-expression" | "iex") => Some("Invoke-Expression"),
            _ => None,
        };
        if let Some(c) = construct {
            self.f.dyns.push(Dyn {
                site,
                construct: c.to_string(),
            });
        }
        self.f.calls.push(Call {
            site,
            full,
            name,
            recv,
            args: vec![args],
            kwargs: vec![],
            str_args,
            predicate: false,
            nargs,
            output_only,
            pipe_to,
        });
    }

    /// `while true` around a command whose failure is ignored, with no counter or deadline.
    fn retry(&mut self, n: Node, scope: Id, ctx: &Ctx) {
        let t = self.t(n);
        let head = t.lines().next().unwrap_or("").to_ascii_lowercase();
        let legacy = head.contains("true")
            || head.contains("$true")
            || head.contains(": ;")
            || head.contains("(1)");
        let low = t.to_ascii_lowercase();
        let mut handled = false;
        walk(n, &mut |m| {
            if matches!(m.kind(), "catch_clause" | "catch_block" | "list") {
                handled = true;
            }
        });
        let retries =
            handled || low.contains("|| ") || low.contains("sleep") || low.contains("start-sleep");
        if !retries {
            return;
        }
        let bound = bounds::prove(n, self.src, self.lang)
            .or_else(|| legacy.then(|| bounds::fallback(t, self.lang)));
        if let Some(bound) = bound {
            let site = self.f.site(0, scope, line(n), ctx);
            self.f.retries.push(RetryLoop { site, bound });
        }
    }
}
