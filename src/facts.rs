//! Language-neutral facts. Extractors fill these from tree-sitter; `resolve` turns names into ids
//! and `rules` derives verdicts from them. Every id is an index into the vector that defines it.

use serde::Serialize;

pub type Id = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, serde::Deserialize)]
pub enum Lang {
    Python,
    Rust,
    JavaScript,
    Bash,
    PowerShell,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct File {
    pub path: String,
    pub lang: Lang,
    pub test: bool,
    /// Module path used for import resolution, e.g. `loops.server` or `engine::readyfix`.
    pub module: String,
    /// The repository it came from, in a sweep over several.
    pub repo: Id,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ScopeKind {
    Module,
    Class,
    Function,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Func {
    pub file: Id,
    pub name: String,
    /// The enclosing class (Python) or impl type (Rust), if any.
    pub class: Option<String>,
    /// Bases of a class scope, or of the class a method belongs to.
    pub bases: Vec<String>,
    pub kind: ScopeKind,
    pub params: Vec<Param>,
    pub line: u32,
    /// Branching statements in the body (if, match, elif, ternary).
    pub branches: u32,
    /// Decision tokens: enum paths, called names and literals inside conditions and match arms.
    pub tokens: Vec<String>,
    /// Branch conditions and match subjects that read a parameter other than `self`: a function
    /// whose branches read none decides from its own state (a canned fake), not from its input.
    #[serde(default)]
    pub param_decisions: u32,
    /// The scope this one is nested in (class for a method, module for a top-level def).
    pub parent: Option<Id>,
    /// Test code: a test file, a `#[cfg(test)]` module or a `#[test]` function.
    pub test: bool,
    /// For a Rust impl method: the trait implemented, if any.
    pub trait_name: Option<String>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Param {
    pub name: String,
    /// The type annotation's text, if any.
    pub annotation: String,
    /// Full texts of calls inside a lambda default, e.g. `dt.datetime.now`.
    pub default_lambda_calls: Vec<String>,
    /// Dotted names referenced (not called) by the default, e.g. `time.monotonic`.
    pub default_refs: Vec<String>,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Ctx {
    /// (block, index) from the function body down to the statement holding the site.
    pub path: Vec<(u32, u32)>,
    /// The site may not run when its statement runs (short-circuit, ternary, lambda, comprehension).
    pub cond: bool,
    pub in_lambda: bool,
    pub try_body: Option<u32>,
    pub handler: Option<u32>,
    pub finally: bool,
    pub loop_id: Option<u32>,
    /// The innermost `finally` block holding the site.
    #[serde(default)]
    pub finally_id: Option<u32>,
    /// Inside a `try` nested in that `finally`, so a raise there is caught before the block goes on.
    #[serde(default)]
    pub shielded: bool,
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Expr {
    /// Variables read: plain names, `self.x`, `self.x.y` kept to the first attribute.
    pub vars: Vec<String>,
    /// Call sites inside the expression.
    pub calls: Vec<Id>,
    pub text: String,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Site {
    pub file: Id,
    pub func: Id,
    pub line: u32,
    pub ctx: Ctx,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Call {
    pub site: Id,
    /// Callee text, e.g. `self.api.get` or `dt.datetime.now` or `Instant::now`.
    pub full: String,
    pub name: String,
    pub recv: String,
    pub args: Vec<Expr>,
    pub kwargs: Vec<(String, Expr)>,
    /// The literal strings among the arguments, for effect patterns such as `backup/remove`.
    pub str_args: Vec<String>,
    /// The call is the direct value of a `return`, an `if`/`while` condition or an assert.
    pub predicate: bool,
    /// Positional arguments given.
    #[serde(default)]
    pub nargs: u32,
    /// The result goes to output, not into a value (a shell command outside `$(...)`).
    #[serde(default)]
    pub output_only: bool,
    /// The commands a shell pipeline sends this command's output to, in order.
    #[serde(default)]
    pub pipe_to: Vec<String>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Assign {
    pub site: Id,
    pub target: String,
    pub value: Expr,
    /// Dotted names referenced without a call (function references).
    pub refs: Vec<String>,
    /// Full callee texts inside lambdas in the value.
    pub lambda_calls: Vec<String>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct LoopIter {
    /// The loop statement's site (its file and function).
    pub site: Id,
    pub id: u32,
    /// The iterated expression's text.
    pub iter: String,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Compare {
    pub site: Id,
    pub left: Expr,
    pub right: Expr,
    pub op: String,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Return {
    pub site: Id,
    pub value: Expr,
}

/// Explicit Result control flow. The analysis must resolve the callee and the error variant.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ResultFlow {
    pub site: Id,
    /// Start offset of the branch or the propagated operand within its source file.
    pub byte: usize,
    pub kind: ResultFlowKind,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum ResultFlowKind {
    /// An `if` consequence whose only action returns a call (possibly an error constructor).
    Reject { condition: String, returned: String },
    /// The direct operand of `?` is a call.
    Propagate { call: String },
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct StrLit {
    pub site: Id,
    pub text: String,
}

/// A construct the model cannot follow: the reason a verdict becomes unknown.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Dyn {
    pub site: Id,
    pub construct: String,
}

/// `if key not in m or newer(...): m[key] = v` inside a loop: the newest value per key.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct LatestPerKey {
    pub site: Id,
    pub map: String,
    pub key: String,
    /// The loop filters its items by membership of something in a collection.
    pub loop_has_membership_filter: bool,
}

/// A collection kept or dropped by comparing its items with a value.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Prune {
    pub site: Id,
    /// The value the items are compared with.
    pub bound: Expr,
    pub writes_back: bool,
}

/// A `while True`/`loop` that can go round again after an error.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RetryLoop {
    pub site: Id,
    pub bound: RetryBound,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum RetryBound {
    Keyword(String),
    None,
    Counter(String),
    Deadline(String),
    BoundedRange(String),
    InputProgress(Vec<String>),
    UnknownProgress,
    RemainingDuration(String),
    CivilDeadline(String),
    EnumeratorDeadline(String, String),
    FiniteGrowth(String),
    ItemReplay(String),
    UnknownReplay(u32),
    UnknownBatch,
    PendingDelivery,
    OneShotFlags(String),
    RegistryGrowth(String),
    UnknownStateProgress(String),
}

/// A pattern match whose success refuses or blocks.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DenyMatch {
    pub site: Id,
    pub what: String,
}

/// A test fixture applied to every test that replaces a production name.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SuitePatch {
    pub site: Id,
    pub target: String,
    pub opt_out: bool,
}

/// A path or URL composed from a value: `root / ref`, `f"/api/{id}/renew"`, `os.path.join`.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Compose {
    pub site: Id,
    pub parts: Expr,
    /// The values placed in a path segment (after a `/`, before any `?`), one per interpolation.
    pub segments: Vec<Expr>,
    pub url: bool,
}

/// An `if` arm with a condition: what it reads, how its body ends, and a membership test in it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Cond {
    /// The `if` (or `elif`) site; a site in the body has `body` in its path.
    pub site: Id,
    pub body: u32,
    pub cond: Expr,
    /// The body's own statements leave: one of the `EXIT_*` kinds, 0 when none does.
    pub exit: u8,
    /// The body reports a violation: it appends to a list, raises, asserts or fails a test.
    pub fails: bool,
    /// `x in T` or `x not in T` in the condition: T's name (or `{literal}`), and whether negated.
    pub member: Option<(String, bool)>,
    /// Every membership test in the condition, in order (`member` is the first).
    #[serde(default)]
    pub memberships: Vec<Membership>,
}

/// `lhs in rhs` or `lhs not in rhs`, as written; `table` is the rhs name or `{literal}`.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Membership {
    pub lhs: String,
    pub rhs: String,
    pub table: String,
    pub negated: bool,
}

pub const EXIT_RETURN: u8 = 1;
pub const EXIT_RAISE: u8 = 2;
pub const EXIT_CONTINUE: u8 = 3;
pub const EXIT_BREAK: u8 = 4;

/// A statement that leaves its block: return, raise, continue or break.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Exit {
    pub site: Id,
    pub kind: u8,
}

#[derive(Default, Debug, serde::Serialize, serde::Deserialize)]
pub struct Facts {
    pub files: Vec<File>,
    pub funcs: Vec<Func>,
    pub sites: Vec<Site>,
    pub calls: Vec<Call>,
    pub assigns: Vec<Assign>,
    pub compares: Vec<Compare>,
    pub returns: Vec<Return>,
    pub strs: Vec<StrLit>,
    pub dyns: Vec<Dyn>,
    pub latest: Vec<LatestPerKey>,
    pub prunes: Vec<Prune>,
    pub retries: Vec<RetryLoop>,
    pub denies: Vec<DenyMatch>,
    pub patches: Vec<SuitePatch>,
    pub composes: Vec<Compose>,
    #[serde(default)]
    pub conds: Vec<Cond>,
    #[serde(default)]
    pub exits: Vec<Exit>,
    /// What each `for` loop iterates, by the loop's id in its file.
    #[serde(default)]
    pub loops: Vec<LoopIter>,
    /// Imports per file: local name -> dotted target.
    pub imports: Vec<(Id, String, String)>,
    /// Files that could not be parsed: (path, reason).
    pub unparsed: Vec<(String, String)>,
    #[serde(default)]
    pub result_flows: Vec<ResultFlow>,
}

impl Facts {
    pub fn site(&mut self, file: Id, func: Id, line: u32, ctx: &Ctx) -> Id {
        self.sites.push(Site {
            file,
            func,
            line,
            ctx: ctx.clone(),
        });
        (self.sites.len() - 1) as Id
    }

    pub fn func(&mut self, f: Func) -> Id {
        self.funcs.push(f);
        (self.funcs.len() - 1) as Id
    }

    pub fn loc(&self, site: Id) -> String {
        let s = &self.sites[site as usize];
        format!("{}:{}", self.files[s.file as usize].path, s.line)
    }

    pub fn func_label(&self, f: Id) -> String {
        let func = &self.funcs[f as usize];
        let file = &self.files[func.file as usize].path;
        match &func.class {
            Some(c) if func.kind == ScopeKind::Function => format!("{file}::{c}.{}", func.name),
            _ => format!("{file}::{}", func.name),
        }
    }

    /// Appends another repository's facts, shifting every id.
    pub fn absorb(&mut self, mut o: Facts) {
        let df = self.files.len() as Id;
        let dfn = self.funcs.len() as Id;
        let ds = self.sites.len() as Id;
        let shift_expr = |e: &mut Expr| e.calls.iter_mut().for_each(|c| *c += ds);
        for f in &mut o.funcs {
            f.file += df;
            if let Some(p) = f.parent.as_mut() {
                *p += dfn;
            }
        }
        for s in &mut o.sites {
            s.file += df;
            s.func += dfn;
        }
        for c in &mut o.calls {
            c.site += ds;
            c.args.iter_mut().for_each(shift_expr);
            c.kwargs.iter_mut().for_each(|(_, e)| shift_expr(e));
        }
        for a in &mut o.assigns {
            a.site += ds;
            shift_expr(&mut a.value);
        }
        for c in &mut o.compares {
            c.site += ds;
            shift_expr(&mut c.left);
            shift_expr(&mut c.right);
        }
        for r in &mut o.returns {
            r.site += ds;
            shift_expr(&mut r.value);
        }
        o.strs.iter_mut().for_each(|x| x.site += ds);
        o.dyns.iter_mut().for_each(|x| x.site += ds);
        o.latest.iter_mut().for_each(|x| x.site += ds);
        for p in &mut o.prunes {
            p.site += ds;
            shift_expr(&mut p.bound);
        }
        o.retries.iter_mut().for_each(|x| x.site += ds);
        o.denies.iter_mut().for_each(|x| x.site += ds);
        o.patches.iter_mut().for_each(|x| x.site += ds);
        for c in &mut o.composes {
            c.site += ds;
            shift_expr(&mut c.parts);
            c.segments.iter_mut().for_each(shift_expr);
        }
        for c in &mut o.conds {
            c.site += ds;
            shift_expr(&mut c.cond);
        }
        o.exits.iter_mut().for_each(|x| x.site += ds);
        o.loops.iter_mut().for_each(|x| x.site += ds);
        o.result_flows.iter_mut().for_each(|x| x.site += ds);
        o.imports.iter_mut().for_each(|x| x.0 += df);
        self.files.extend(o.files);
        self.funcs.extend(o.funcs);
        self.sites.extend(o.sites);
        self.calls.extend(o.calls);
        self.assigns.extend(o.assigns);
        self.compares.extend(o.compares);
        self.returns.extend(o.returns);
        self.strs.extend(o.strs);
        self.dyns.extend(o.dyns);
        self.latest.extend(o.latest);
        self.prunes.extend(o.prunes);
        self.retries.extend(o.retries);
        self.denies.extend(o.denies);
        self.patches.extend(o.patches);
        self.composes.extend(o.composes);
        self.conds.extend(o.conds);
        self.exits.extend(o.exits);
        self.loops.extend(o.loops);
        self.result_flows.extend(o.result_flows);
        self.imports.extend(o.imports);
        self.unparsed.extend(o.unparsed);
    }
}
