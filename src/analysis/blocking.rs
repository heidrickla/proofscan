//! Question 6 for CPU-intensive Rust work reached from a request entry.

use super::Analysis;
use crate::facts::*;
use crate::lang::{children, lang_of, line, named_children, squash, text};
use crate::report::Verdict;
use regex::Regex;
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;
use tree_sitter::{Node, Parser};

const RULE: &str = "blocking-unbounded";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dispatch {
    Detached,
    Inline,
    Pool,
}

impl Analysis<'_> {
    pub(super) fn blocking_unbounded(&mut self) {
        let reach = self.untrusted_reach();
        if reach.is_empty() {
            return;
        }
        let f = self.f;
        // The loader preserves the order of parsed files, including across a sweep.
        let sources: Vec<_> = self
            .texts
            .iter()
            .filter(|(path, _)| lang_of(Path::new(path)).is_some())
            .map(|(_, src)| src.as_str())
            .collect();
        let eligible = |func: Id| {
            let fun = &f.funcs[func as usize];
            let file = &f.files[fun.file as usize];
            file.lang == Lang::Rust && !file.test && !fun.test
        };
        let imports: HashMap<_, _> = f
            .files
            .iter()
            .enumerate()
            .filter(|(_, file)| file.lang == Lang::Rust && !file.test)
            .map(|(id, _)| (id as Id, imports(sources[id])))
            .collect();
        let semaphore_field = Regex::new(
            r"\b([a-zA-Z_]\w*)\s*:\s*(?:std::sync::)?Arc<\s*((?:tokio::sync::)?Semaphore)\s*>",
        )
        .expect("semaphore field");
        let struct_body =
            Regex::new(r"(?s)\bstruct\s+([a-zA-Z_]\w*)\s*\{([^{}]*)\}").expect("struct body");
        let state_alias = Regex::new(
            r"\btype\s+([a-zA-Z_]\w*)\s*=\s*(?:std::sync::)?Arc<\s*([a-zA-Z_]\w*)\s*>\s*;",
        )
        .expect("shared state type alias");
        let mut shared = HashMap::<Id, SharedSemaphores<'_>>::new();
        for (&id, imports) in &imports {
            let source = sources[id as usize];
            let semaphores = shared.entry(f.files[id as usize].repo).or_default();
            for alias in state_alias.captures_iter(source) {
                semaphores.aliases.insert(
                    alias.get(1).unwrap().as_str(),
                    alias.get(2).unwrap().as_str(),
                );
            }
            for item in struct_body.captures_iter(source) {
                let structure = item.get(1).unwrap().as_str();
                let body = item.get(2).unwrap().as_str();
                for field in semaphore_field.captures_iter(body) {
                    if &field[2] == "tokio::sync::Semaphore"
                        || imports
                            .get("Semaphore")
                            .is_some_and(|p| p == "tokio::sync::Semaphore")
                    {
                        semaphores
                            .fields
                            .entry(structure)
                            .or_default()
                            .insert(field.get(1).unwrap().as_str());
                    }
                }
            }
        }
        let is_async = |func: Id| {
            let fun = &f.funcs[func as usize];
            let src = sources[fun.file as usize];
            let header = src
                .lines()
                .skip(fun.line.saturating_sub(1) as usize)
                .take(4);
            header
                .flat_map(str::split_whitespace)
                .take_while(|token| *token != "fn")
                .any(|token| token == "async")
        };
        let mut callers: HashMap<Id, Vec<&Call>> = HashMap::new();
        for &(from, to, site, exact) in &self.g.edges {
            if eligible(from)
                && eligible(to)
                && f.files[f.funcs[from as usize].file as usize].repo
                    == f.files[f.funcs[to as usize].file as usize].repo
                && (exact || self.g.targets.get(&site).is_some_and(|t| t.len() == 1))
                && let Some(call) = self.call(site)
            {
                callers.entry(to).or_default().push(call);
            }
        }
        // A synchronous helper inherits the cost of its synchronous calls. A closure's body
        // belongs to the dispatch site, and an async helper is judged at the work inside it.
        let mut work = HashMap::new();
        let mut queue = VecDeque::new();
        let mut admitting = HashSet::new();
        for call in &f.calls {
            let site = &f.sites[call.site as usize];
            if !eligible(site.func) {
                continue;
            }
            if admission_call(&call.name) {
                admitting.insert(site.func);
            }
            if cpu_work(call, &imports[&site.file]) {
                queue.push_back((call, call.site));
            }
        }
        let mut synchronous = HashSet::new();
        while let Some((call, leaf)) = queue.pop_front() {
            if work.contains_key(&call.site) {
                continue;
            }
            work.insert(call.site, leaf);
            let site = &f.sites[call.site as usize];
            if !site.ctx.in_lambda && synchronous.insert(site.func) && !is_async(site.func) {
                for &outer in callers.get(&site.func).into_iter().flatten() {
                    queue.push_back((outer, leaf));
                }
            }
        }

        let mut candidates: HashMap<Id, HashMap<_, Vec<_>>> = HashMap::new();
        for call in &f.calls {
            let site = &f.sites[call.site as usize];
            if reach.contains(&site.func) && eligible(site.func) {
                candidates
                    .entry(site.file)
                    .or_default()
                    .entry((site.line, call.full.as_str()))
                    .or_default()
                    .push(call);
            }
        }
        candidates.retain(|_, calls| calls.values().flatten().any(|c| work.contains_key(&c.site)));
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .expect("Rust grammar");
        for (file, calls) in candidates {
            let source = sources[file as usize];
            let imports = &imports[&file];
            let Some(tree) = parser.parse(source, None) else {
                continue;
            };
            let mut seen = HashSet::new();
            let lookup = |node| {
                let name = callee(node).map(|n| squash(text(n, source)))?;
                match calls.get(&(line(node), name.as_str()))?.as_slice() {
                    [call] => Some(*call),
                    _ => None,
                }
            };
            for node in descendants(tree.root_node()).filter(|n| n.kind() == "call_expression") {
                let Some(call) = lookup(node) else { continue };
                let Some(&leaf) = work.get(&call.site) else {
                    continue;
                };
                let Some((effect, dispatch, closure)) = placement(node, source, imports) else {
                    continue;
                };
                let Some(job) = lookup(effect) else { continue };
                if f.sites[job.site as usize].ctx.in_lambda || !seen.insert(job.site) {
                    continue;
                }
                let func = f.sites[job.site as usize].func;
                let path = &f.files[file as usize].path;
                let mut witness = vec![
                    format!("{} starts CPU work via `{}`", self.loc(job.site), job.full),
                    format!(
                        "{} calls `{}`",
                        self.loc(leaf),
                        self.call(leaf).unwrap().full
                    ),
                ];
                let (verdict, message, assumptions) = if dispatch == Dispatch::Pool {
                    (
                        Verdict::Proven,
                        "the Rayon worker pool bounds the number of jobs running at once",
                        vec!["Rayon uses a fixed number of workers per pool".into()],
                    )
                } else if let Some(permit) = held_permit(
                    effect,
                    closure,
                    dispatch,
                    source,
                    &shared[&f.files[file as usize].repo],
                ) {
                    witness.push(format!(
                        "{path}:{} acquires a permit before the work starts",
                        line(permit.binding)
                    ));
                    (
                        Verdict::Proven,
                        "a semaphore permit stays live until the CPU work finishes",
                        vec![format!(
                            "`{}` is one Tokio semaphore shared by requests with a fixed capacity",
                            permit.semaphore
                        )],
                    )
                } else if upstream_admission(func, &reach, &callers, &admitting, f) {
                    (
                        Verdict::Unknown,
                        "CPU work is reachable from a request, but the rule cannot establish whether the admission control covers this work",
                        vec![],
                    )
                } else {
                    (
                        Verdict::Violated,
                        "CPU work is started per request without a visible concurrency limit before it",
                        vec![],
                    )
                };
                self.push(
                    6,
                    RULE,
                    verdict,
                    job.site,
                    message.into(),
                    witness,
                    assumptions,
                );
            }
        }
    }
}

fn descendants(root: Node<'_>) -> impl Iterator<Item = Node<'_>> {
    let mut stack = vec![root];
    std::iter::from_fn(move || {
        let node = stack.pop()?;
        stack.extend(named_children(node).into_iter().rev());
        Some(node)
    })
}

fn callee(node: Node<'_>) -> Option<Node<'_>> {
    let function = node.child_by_field_name("function")?;
    if function.kind() == "generic_function" {
        function.child_by_field_name("function")
    } else {
        Some(function)
    }
}

// These imports identify external APIs in the absence of Rust type facts.
fn imports(src: &str) -> HashMap<&str, String> {
    let mut out = HashMap::new();
    for path in src
        .lines()
        .filter_map(|line| line.trim().strip_prefix("use ")?.strip_suffix(';'))
    {
        let (prefix, members) = path
            .split_once("::{")
            .and_then(|(p, m)| Some((p, m.strip_suffix('}')?)))
            .unwrap_or(("", path));
        for member in members.split(',').map(str::trim) {
            let (name, alias) = member
                .split_once(" as ")
                .unwrap_or((member, member.rsplit("::").next().unwrap_or(member)));
            if identifier(alias) && !name.contains(['{', '}', '*']) {
                let full = if prefix.is_empty() {
                    name.into()
                } else {
                    format!("{prefix}::{name}")
                };
                out.insert(alias, full);
            }
        }
    }
    out
}

fn cpu_work(call: &Call, imports: &HashMap<&str, String>) -> bool {
    let target = imports.get(call.full.as_str()).unwrap_or(&call.full);
    matches!(
        target.as_str(),
        "bergshamra_dsig::verify::verify_all_document"
            | "bcrypt::hash"
            | "bcrypt::verify"
            | "scrypt::scrypt"
    ) || (matches!(
        call.name.as_str(),
        "hash_password" | "hash_password_into" | "verify_password"
    ) && (call.recv.starts_with("argon2::Argon2::")
        || call.recv.starts_with("Argon2::")
            && imports.get("Argon2").is_some_and(|p| p == "argon2::Argon2")))
}

fn placement<'tree>(
    work: Node<'tree>,
    src: &str,
    imports: &HashMap<&str, String>,
) -> Option<(Node<'tree>, Dispatch, Option<Node<'tree>>)> {
    let mut node = work;
    while let Some(parent) = node.parent() {
        match parent.kind() {
            "closure_expression" => {
                let args = parent.parent()?;
                let call = args.parent()?;
                if args.kind() != "arguments"
                    || named_children(args).last() != Some(&parent)
                    || call.kind() != "call_expression"
                {
                    return None;
                }
                let name = squash(text(callee(call)?, src));
                let target = imports.get(name.as_str()).unwrap_or(&name);
                let kind = match target.trim_start_matches("::") {
                    "tokio::task::spawn_blocking" | "std::thread::spawn" => Dispatch::Detached,
                    "thread::spawn"
                        if imports.get("thread").is_some_and(|p| p == "std::thread") =>
                    {
                        Dispatch::Detached
                    }
                    "tokio::task::block_in_place" => Dispatch::Inline,
                    "rayon::spawn" | "rayon::spawn_fifo" => Dispatch::Pool,
                    _ => return None,
                };
                return Some((call, kind, Some(parent)));
            }
            "async_block" => return None,
            "function_item" => {
                let async_fn = named_children(parent)
                    .into_iter()
                    .find(|n| n.kind() == "function_modifiers")
                    .is_some_and(|n| children(n).iter().any(|k| k.kind() == "async"));
                return async_fn.then_some((work, Dispatch::Inline, None));
            }
            _ => node = parent,
        }
    }
    None
}

struct Permit<'tree> {
    binding: Node<'tree>,
    semaphore: String,
}

#[derive(Default)]
struct SharedSemaphores<'a> {
    fields: HashMap<&'a str, HashSet<&'a str>>,
    aliases: HashMap<&'a str, &'a str>,
}

fn held_permit<'tree>(
    effect: Node<'tree>,
    closure: Option<Node<'tree>>,
    dispatch: Dispatch,
    src: &str,
    shared: &SharedSemaphores<'_>,
) -> Option<Permit<'tree>> {
    let mut statement = effect;
    while let Some(parent) = statement.parent() {
        if matches!(
            parent.kind(),
            "closure_expression" | "function_item" | "async_block"
        ) {
            break;
        }
        if parent.kind() == "block" {
            let prior: Vec<_> = named_children(parent)
                .into_iter()
                .take_while(|n| *n != statement)
                .collect();
            for (i, &binding) in prior.iter().enumerate().rev() {
                let Some((name, value)) = let_binding(binding, src) else {
                    continue;
                };
                let Some(semaphore) = acquired(value, src, shared) else {
                    continue;
                };
                if prior[i + 1..].iter().any(|n| mentions(*n, name, src)) {
                    continue;
                }
                let held = match closure {
                    Some(closure) if captures(closure, name, src) => true,
                    _ => dispatch == Dispatch::Inline && !mentions(statement, name, src),
                };
                if held {
                    return Some(Permit { binding, semaphore });
                }
            }
            break;
        }
        statement = parent;
    }
    None
}

fn let_binding<'tree, 'src>(node: Node<'tree>, src: &'src str) -> Option<(&'src str, Node<'tree>)> {
    let pattern = node.child_by_field_name("pattern")?;
    (node.kind() == "let_declaration"
        && pattern.kind() == "identifier"
        && text(pattern, src) != "_")
        .then_some((text(pattern, src), node.child_by_field_name("value")?))
}

fn mentions(node: Node<'_>, name: &str, src: &str) -> bool {
    descendants(node).any(|n| n.kind() == "identifier" && text(n, src) == name)
}

fn captures(closure: Node<'_>, name: &str, src: &str) -> bool {
    if !children(closure).iter().any(|n| n.kind() == "move") {
        return false;
    }
    let Some(body) = closure.child_by_field_name("body") else {
        return false;
    };
    if body.kind() != "block" {
        return false;
    }
    let statements: Vec<_> = named_children(body)
        .into_iter()
        .filter(|n| !matches!(n.kind(), "line_comment" | "block_comment"))
        .collect();
    let Some((first, rest)) = statements.split_first() else {
        return false;
    };
    let Some((held, value)) = let_binding(*first, src) else {
        return false;
    };
    value.kind() == "identifier"
        && text(value, src) == name
        && !rest.iter().any(|n| mentions(*n, held, src))
}

fn acquired(mut expr: Node<'_>, src: &str, shared: &SharedSemaphores<'_>) -> Option<String> {
    let mut awaited = false;
    let mut unwrapped = false;
    loop {
        match expr.kind() {
            "try_expression" | "await_expression" => {
                awaited |= expr.kind() == "await_expression";
                unwrapped |= expr.kind() == "try_expression";
                expr = expr.named_child(0)?;
            }
            "call_expression" => {
                let function = callee(expr)?;
                let name = squash(text(function, src));
                if let Some(field) = function.child_by_field_name("field") {
                    let method = text(field, src);
                    let recv = function.child_by_field_name("value")?;
                    match method {
                        "unwrap" | "expect" => unwrapped = true,
                        "map_err" => {}
                        "acquire_owned" | "try_acquire_owned"
                            if unwrapped && (awaited || method == "try_acquire_owned") =>
                        {
                            // Cloning a state field uses the same semaphore. A new semaphore in
                            // the request, even with a single permit, limits nothing across requests.
                            let recv = squash(text(recv, src));
                            let field = recv.strip_prefix("Arc::clone(&")?.strip_suffix(')')?;
                            let (state, member) = field.split_once('.')?;
                            let ty = state_type(state, expr, src)?;
                            let ty = ty.trim_start_matches('&');
                            let ty = ty
                                .strip_prefix("Arc<")
                                .and_then(|t| t.strip_suffix('>'))
                                .unwrap_or(ty);
                            let ty = shared.aliases.get(ty).copied().unwrap_or(ty);
                            return shared
                                .fields
                                .get(ty)
                                .is_some_and(|f| f.contains(member))
                                .then(|| field.into());
                        }
                        _ => return None,
                    }
                    expr = recv;
                } else if matches!(
                    name.as_str(),
                    "tokio::sync::Semaphore::acquire" | "tokio::sync::Semaphore::try_acquire"
                ) && unwrapped
                    && (awaited || name.ends_with("::try_acquire"))
                {
                    let args = expr.child_by_field_name("arguments")?;
                    let arg = squash(text(args.named_child(0)?, src));
                    let semaphore = arg.strip_prefix('&')?;
                    return static_semaphore(semaphore, expr, src).then(|| semaphore.into());
                } else {
                    return None;
                }
            }
            _ => return None,
        }
    }
}

fn identifier(name: &str) -> bool {
    !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn state_type(name: &str, node: Node<'_>, src: &str) -> Option<String> {
    let function = enclosing_function(node)?;
    if rebound(name, function, node, src) {
        return None;
    }
    if name == "self" {
        let implementation = function.parent()?.parent()?;
        return (implementation.kind() == "impl_item")
            .then(|| {
                implementation
                    .child_by_field_name("type")
                    .map(|ty| squash(text(ty, src)))
            })
            .flatten();
    }
    let params = function.child_by_field_name("parameters")?;
    for param in named_children(params) {
        if param
            .child_by_field_name("pattern")
            .is_some_and(|p| p.kind() == "identifier" && text(p, src) == name)
        {
            return param
                .child_by_field_name("type")
                .map(|ty| squash(text(ty, src)));
        }
    }
    None
}

fn enclosing_function(mut node: Node<'_>) -> Option<Node<'_>> {
    while node.kind() != "function_item" {
        node = node.parent()?;
    }
    Some(node)
}

fn rebound(name: &str, function: Node<'_>, before: Node<'_>, src: &str) -> bool {
    function.child_by_field_name("body").is_none_or(|body| {
        descendants(body)
            .take_while(|n| n.start_byte() < before.start_byte())
            .any(|n| {
                matches!(n.kind(), "let_declaration" | "assignment_expression")
                    && n.child_by_field_name("pattern")
                        .or_else(|| n.child_by_field_name("left"))
                        .is_some_and(|p| mentions(p, name, src))
            })
    })
}

fn static_semaphore(name: &str, node: Node<'_>, src: &str) -> bool {
    if !identifier(name) {
        return false;
    }
    let mut root = node;
    while let Some(parent) = root.parent() {
        root = parent;
    }
    enclosing_function(node).is_some_and(|f| !rebound(name, f, node, src))
        && named_children(root).iter().any(|item| {
            item.kind() == "static_item"
                && item
                    .child_by_field_name("name")
                    .is_some_and(|n| text(n, src) == name)
                && item
                    .child_by_field_name("type")
                    .is_some_and(|t| squash(text(t, src)) == "tokio::sync::Semaphore")
        })
}

fn admission_call(name: &str) -> bool {
    matches!(
        name,
        "acquire"
            | "acquire_owned"
            | "acquire_many"
            | "acquire_many_owned"
            | "try_acquire"
            | "try_acquire_owned"
            | "try_acquire_many"
            | "try_acquire_many_owned"
            | "lock"
            | "lock_owned"
            | "try_lock"
            | "try_lock_owned"
            | "write_owned"
            | "concurrency_limit"
            | "try_send"
            | "max_blocking_threads"
    )
}

fn upstream_admission(
    func: Id,
    reach: &HashSet<Id>,
    callers: &HashMap<Id, Vec<&Call>>,
    admitting: &HashSet<Id>,
    facts: &Facts,
) -> bool {
    let mut todo = vec![func];
    let mut seen = HashSet::new();
    while let Some(func) = todo.pop() {
        if !seen.insert(func) || !reach.contains(&func) {
            continue;
        }
        if admitting.contains(&func) {
            return true;
        }
        todo.extend(
            callers
                .get(&func)
                .into_iter()
                .flatten()
                .map(|c| facts.sites[c.site as usize].func),
        );
    }
    false
}
