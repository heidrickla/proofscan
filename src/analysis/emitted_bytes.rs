//! Question 6: charge repeated output to one allowance before it reaches the consumer.

use super::Analysis;
use crate::facts::{Id, Lang};
use crate::report::Verdict;
use std::collections::{BTreeMap, HashMap, HashSet};
use tree_sitter::Node;

const RULE: &str = "emitted-bytes";
const SAML: &str = "src/saml.rs";
const VERIFY: &str = "bergshamra-dsig/src/verify.rs";
const EXCLUSIVE: &str = "bergshamra-c14n/src/exclusive.rs";

const APP_FILES: &[&str] = &[SAML, "src/sso.rs", "src/web.rs"];
const LIBRARY_FILES: &[&str] = &[
    "bergshamra-c14n/Cargo.toml",
    "bergshamra-c14n/src/escape.rs",
    EXCLUSIVE,
    "bergshamra-c14n/src/inclusive.rs",
    "bergshamra-c14n/src/inclusive11.rs",
    "bergshamra-c14n/src/lib.rs",
    "bergshamra-c14n/src/render.rs",
    "bergshamra-dsig/Cargo.toml",
    "bergshamra-dsig/src/context.rs",
    "bergshamra-dsig/src/lib.rs",
    "bergshamra-dsig/src/sign.rs",
    VERIFY,
];

// c89f0ced: vendored 0.12.0 and the original SAML caller. 86d149ab adds the
// path patches. f3c79673 installs the shared budget in the SAML caller.
const UNBUDGETED_APP: &str = "d95b277b2dcb939978a19e81d083754d22682341c63051b4fed29ee5285f60b1";
const BUDGETED_APP: &str = "0db2c60f1baad28dc636a430d2a6b31a07476eb7e422719cc9f200c1b4d9896d";
const VENDORED_LIBRARY: &str = "af6412d460ba9165c995b4a4374b686e2844886130f265be2fd1e6904979a30d";
const PATCHED_LIBRARY: &str = "269449252a6e96d1cb6c074f028b8231fdabd4f63d0371b67dc0b7f72109dd41";

type Texts<'a> = HashMap<&'a str, &'a str>;

#[derive(Clone, Copy)]
enum Library {
    Vendored,
    Patched,
}

impl Library {
    fn root(self) -> &'static str {
        match self {
            Self::Vendored => "vendor/",
            Self::Patched => "patches/",
        }
    }

    fn fingerprint(self) -> &'static str {
        match self {
            Self::Vendored => VENDORED_LIBRARY,
            Self::Patched => PATCHED_LIBRARY,
        }
    }

    fn witness(self) -> Vec<String> {
        let (lookup, emit, restore, invisible, digest) = match self {
            Self::Vendored => (240, 300, 344, 401, 1049),
            Self::Patched => (244, 304, 348, 405, 1065),
        };
        let root = self.root();
        vec![
            format!(
                "{root}{EXCLUSIVE}:{lookup} looks up a URI from the document's namespace scope"
            ),
            format!(
                "{root}{EXCLUSIVE}:{emit} emits a visible declaration and line {restore} restores the ancestor's rendered state after its subtree, allowing another sibling to emit the same URI"
            ),
            format!(
                "{root}{EXCLUSIVE}:{invisible} also emits declarations on the namespace-filtered path"
            ),
            format!("{root}bergshamra-c14n/src/render.rs:40 escapes the URI into the sink"),
            format!(
                "{root}{VERIFY}:{digest} forwards those bytes to the reference digest before comparison"
            ),
        ]
    }
}

impl Analysis<'_> {
    pub(super) fn emitted_bytes(&mut self) {
        if !self.cfg.q6.emitted_bytes {
            return;
        }
        // Source texts are keyed by relative path. An isolated scan keeps each
        // manifest and its pinned source files in the same repository.
        if self.f.files.iter().any(|f| f.repo != 0) {
            self.not_checked.entry(6).or_default().push(
                "emitted-bytes needs a per-repository scan to identify its source files".into(),
            );
            return;
        }
        let entries: HashSet<_> = self.untrusted_entries().into_iter().collect();
        if entries.is_empty() {
            return;
        }
        let reach = self.untrusted_reach();
        let texts: Texts = self
            .texts
            .iter()
            .map(|(path, source)| (path.as_str(), source.as_str()))
            .collect();
        self.repeated_slice_writes(&texts, &entries);
        self.bergshamra_output(&texts, &reach, &entries);
    }

    fn bergshamra_output(&mut self, texts: &Texts, reach: &HashSet<Id>, entries: &HashSet<Id>) {
        let f = self.f;
        let source_path = |file: Id| f.files[file as usize].path.as_str();
        let saml_entry = f.funcs.iter().enumerate().any(|(id, fun)| {
            !fun.test
                && source_path(fun.file) == SAML
                && fun.name == "accept"
                && fun.class.as_deref() == Some("ServiceProvider")
                && reach.contains(&(id as Id))
        });
        let library_entry = entries.iter().any(|&id| {
            let fun = &f.funcs[id as usize];
            !fun.test
                && source_path(fun.file) == format!("patches/{VERIFY}")
                && fun.name == "verify_all_document_with_source"
        });
        if !saml_entry && !library_entry {
            return;
        }
        let saml_call = saml_entry
            .then(|| self.emission_call(SAML, "verify_all_document"))
            .flatten();
        let bounded_call = library_entry
            .then(|| {
                self.emission_call(
                    &format!("patches/{VERIFY}"),
                    "bergshamra_c14n::canonicalize_doc_bounded_to",
                )
            })
            .flatten();
        let manifest = texts
            .get("Cargo.toml")
            .and_then(|src| toml::from_str::<toml::Value>(src).ok());
        let dep = manifest
            .as_ref()
            .and_then(|m| m.get("dependencies"))
            .and_then(|t| t.get("bergshamra-dsig"));
        // The summaries cover 0.12.0 with the rustcrypto backend. A reached verification of any
        // other selection is still this rule's question, so it is unknown, never skipped.
        let (Some(manifest), Some(dep)) = (manifest.as_ref(), dep) else {
            self.uncovered(&[saml_call, bounded_call], "the manifest does not select bergshamra-dsig in a form the reviewed summary covers");
            return;
        };
        let version = dep.get("version").and_then(toml::Value::as_str);
        if version != Some("=0.12.0") {
            let message = format!(
                "no reviewed source summary covers bergshamra-dsig {}; the summaries cover =0.12.0",
                version.unwrap_or("of unknown version")
            );
            self.uncovered(&[saml_call, bounded_call], &message);
            return;
        }
        let library = active_library(texts, manifest, dep).filter(|lib| {
            fingerprint(texts, lib.root(), LIBRARY_FILES).as_deref() == Some(lib.fingerprint())
        });
        let Some(library) = library else {
            for site in [saml_call, bounded_call].into_iter().flatten() {
                self.push(6, RULE, Verdict::Unknown, site,
                    "the active Bergshamra verifier or renderer does not match the reviewed source summary".into(),
                    vec![], vec![]);
            }
            return;
        };
        if let Some(site) = saml_call {
            self.saml_emission(texts, library, site);
        }
        if let (Library::Patched, Some(site)) = (library, bounded_call)
            && let Some(unset) = self.emission_call(
                &format!("patches/{VERIFY}"),
                "bergshamra_c14n::canonicalize_doc_to",
            )
        {
            self.push(6, RULE, Verdict::Proven, site,
                "with a budget installed, this verification charges all its canonical output against the same allowance".into(),
                budget_witness(), budget_assumptions());
            self.push(6, RULE, Verdict::Violated, unset,
                "with the budget unset, repeated namespace bytes reach the digest or buffer without a shared allowance".into(),
                library.witness(), vec![]);
        }
    }

    fn saml_emission(&mut self, texts: &Texts, library: Library, verify: Id) {
        let mut witness = library.witness();
        witness.insert(
            0,
            format!(
                "{} verifies the document parsed from the ACS form response before authentication",
                self.loc(verify)
            ),
        );
        match (fingerprint(texts, "", APP_FILES).as_deref(), library) {
            (Some(UNBUDGETED_APP), _) => {
                let renderer = format!("{}{EXCLUSIVE}", library.root());
                if let Some(site) = self.f.calls.iter().find(|c| {
                    c.full == "ns_decl.write_to" && self.f.files[self.f.sites[c.site as usize].file as usize].path == renderer
                }).map(|c| c.site) {
                    self.push(6, RULE, Verdict::Violated, site,
                        "sibling visits can re-emit the same request namespace URI into the reference digest without a shared byte allowance".into(),
                        witness, vec![]);
                }
            }
            (Some(BUDGETED_APP), Library::Patched) => {
                if let Some(site) = self.emission_call(SAML, "C14nBudget::new") {
                    witness.extend(budget_witness());
                    let mut assumptions = budget_assumptions();
                    assumptions.push("one fresh budget is installed on the one verification context, sized by saturating arithmetic from the decoded XML length".into());
                    self.push(6, RULE, Verdict::Proven, site,
                        "one shared allowance of three times the decoded XML bytes plus 16 KiB bounds canonical bytes forwarded during SAML verification".into(),
                        witness, assumptions);
                }
            }
            _ => self.push(6, RULE, Verdict::Unknown, verify,
                "cannot establish which byte allowance the SAML caller supplies across the document's passes".into(),
                witness, vec![]),
        }
    }

    fn uncovered(&mut self, sites: &[Option<Id>], message: &str) {
        for site in sites.iter().flatten() {
            self.push(
                6,
                RULE,
                Verdict::Unknown,
                *site,
                message.to_string(),
                vec![],
                vec![],
            );
        }
    }

    fn emission_call(&self, path: &str, callee: &str) -> Option<Id> {
        self.f.calls.iter().find_map(|call| {
            let site = &self.f.sites[call.site as usize];
            let fun = &self.f.funcs[site.func as usize];
            (!fun.test && self.f.files[site.file as usize].path == path && call.full == callee)
                .then_some(call.site)
        })
    }

    fn repeated_slice_writes(&mut self, texts: &Texts, entries: &HashSet<Id>) {
        let f = self.f;
        let loops: HashMap<_, _> = f
            .loops
            .iter()
            .map(|l| ((f.sites[l.site as usize].file, l.id), l))
            .collect();
        let mut candidates = BTreeMap::new();
        for call in &f.calls {
            let site = &f.sites[call.site as usize];
            if !entries.contains(&site.func)
                || f.funcs[site.func as usize].test
                || f.files[site.file as usize].lang != Lang::Rust
                || !matches!(call.name.as_str(), "extend_from_slice" | "write_all")
            {
                continue;
            }
            let Some(loop_fact) = site.ctx.loop_id.and_then(|id| loops.get(&(site.file, id)))
            else {
                continue;
            };
            let [value] = call.args.as_slice() else {
                continue;
            };
            let fun = &f.funcs[site.func as usize];
            let param = |name: &str| fun.params.iter().any(|p| p.name == name);
            if value.text != loop_fact.iter && param(&value.text) && param(&loop_fact.iter) {
                candidates.entry(site.func).or_insert((call, *loop_fact));
            }
        }
        for (func, (call, visit)) in candidates {
            let fun = &f.funcs[func as usize];
            let path = f.files[fun.file as usize].path.as_str();
            let Some(src) = texts.get(path) else { continue };
            let bytes = &call.args[0].text;
            let Some(body) = RepeatedWrites::parse(src, fun.line, &fun.name) else {
                continue;
            };
            if !body.is_slice(bytes) || !body.is_slice(&visit.iter) {
                continue;
            }
            let (verdict, message, assumptions) = match body.allowance(&call.recv, bytes) {
                Some(Some(limit)) => (Verdict::Proven,
                    format!("each visit charges the same {limit}-byte allowance before appending to the output"),
                    vec!["the independently sized slices are supplied by the request boundary, and one call covers all passes in this verification".into()]),
                Some(None) => (Verdict::Violated,
                    "the same request bytes are appended on each visit to an independently sized request slice with no shared byte allowance".into(), vec![]),
                None => (Verdict::Unknown,
                    "cannot establish one non-resetting allowance charged before every write, or resolve the writer's byte accounting".into(), vec![]),
            };
            self.push(
                6,
                RULE,
                verdict,
                call.site,
                message,
                vec![
                    format!(
                        "{path}:{} takes request bytes and visit slices at the verification entry",
                        fun.line
                    ),
                    format!(
                        "{} visits `{}` while reusing `{bytes}`",
                        self.loc(visit.site),
                        visit.iter
                    ),
                    format!(
                        "{} forwards `{bytes}` to `{}`",
                        self.loc(call.site),
                        call.recv
                    ),
                ],
                assumptions,
            );
        }
    }
}

fn active_library(
    texts: &Texts,
    manifest: &toml::Value,
    dependency: &toml::Value,
) -> Option<Library> {
    let features = dependency.get("features")?.as_array()?;
    if dependency.get("default-features")?.as_bool()?
        || features.len() != 1
        || features[0].as_str()? != "rustcrypto"
        || dependency.as_table()?.len() != 3
    {
        return None;
    }
    let cfg: toml::Value = toml::from_str(texts.get(".cargo/config.toml")?).ok()?;
    let sources = cfg.get("source")?;
    if sources.get("crates-io")?.get("replace-with")?.as_str()? != "vendored-sources"
        || sources
            .get("vendored-sources")?
            .get("directory")?
            .as_str()?
            != "vendor"
    {
        return None;
    }
    let lock: toml::Value = toml::from_str(texts.get("Cargo.lock")?).ok()?;
    let packages = lock.get("package")?.as_array()?;
    let patches = manifest.get("patch").and_then(|t| t.get("crates-io"));
    let copies = ["bergshamra-c14n", "bergshamra-dsig"].map(|name| {
        let mut matches = packages
            .iter()
            .filter(|p| p.get("name").and_then(toml::Value::as_str) == Some(name));
        let package = matches.next()?;
        if matches.next().is_some() || package.get("version")?.as_str()? != "0.12.0" {
            return None;
        }
        match (patches.and_then(|p| p.get(name)), package.get("source")) {
            (None, Some(source))
                if source.as_str()? == "registry+https://github.com/rust-lang/crates.io-index" =>
            {
                Some("vendor/")
            }
            (Some(patch), None)
                if patch.as_table()?.len() == 1
                    && patch.get("path")?.as_str()? == format!("patches/{name}") =>
            {
                Some("patches/")
            }
            _ => None,
        }
    });
    match copies {
        [Some("vendor/"), Some("vendor/")] => Some(Library::Vendored),
        [Some("patches/"), Some("patches/")] => Some(Library::Patched),
        _ => None,
    }
}

fn fingerprint(texts: &Texts, prefix: &str, paths: &[&str]) -> Option<String> {
    let mut hash = blake3::Hasher::new();
    for path in paths {
        let source = texts.get(format!("{prefix}{path}").as_str())?;
        hash.update(path.as_bytes());
        hash.update(b"\0");
        hash.update(source.replace("\r\n", "\n").as_bytes());
        hash.update(b"\0");
    }
    Some(hash.finalize().to_hex().to_string())
}

fn budget_witness() -> Vec<String> {
    [
        "patches/bergshamra-dsig/src/verify.rs:399 and :423 borrow the same context allowance for references and SignedInfo",
        "patches/bergshamra-dsig/src/verify.rs:1102 and :1219 use it for streaming and buffered references",
        "patches/bergshamra-dsig/src/verify.rs:913 refuses unsupported transforms before the generic pipeline",
        "patches/bergshamra-c14n/src/lib.rs:143 and :151 charge slices and single bytes before forwarding, and :418 checks exhaustion when canonicalization returns",
    ].map(str::to_owned).to_vec()
}

fn budget_assumptions() -> Vec<String> {
    [
        "the reviewed Cargo dependency selection and Bergshamra 0.12.0 source apply at runtime",
        "the same non-resetting allowance covers streaming references, buffered references and SignedInfo for the document",
        "each slice and byte is charged before forwarding, reservations are capped, and exhaustion propagates through the final write",
        "unsupported transforms are refused before generic fallback",
    ].map(str::to_owned).to_vec()
}

/// The direct Rust model checks a closed function body because a bypass, a reset
/// between passes, or a refusal after forwarding can invalidate the whole bound.
struct RepeatedWrites<'a> {
    src: &'a str,
    tree: tree_sitter::Tree,
    line: u32,
    name: &'a str,
}

impl<'a> RepeatedWrites<'a> {
    fn parse(src: &'a str, line: u32, name: &'a str) -> Option<Self> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .ok()?;
        let tree = parser.parse(src, None)?;
        Some(Self {
            src,
            tree,
            line,
            name,
        })
    }

    fn function(&self) -> Option<Node<'_>> {
        let row = self.line as usize - 1;
        let mut work = vec![self.tree.root_node()];
        while let Some(n) = work.pop() {
            if n.start_position().row > row || n.end_position().row < row {
                continue;
            }
            if n.kind() == "function_item"
                && n.start_position().row == row
                && n.child_by_field_name("name")
                    .is_some_and(|name| self.text(name) == self.name)
            {
                return (!n.has_error()).then_some(n);
            }
            work.extend(n.named_children(&mut n.walk()));
        }
        None
    }

    fn text(&self, n: Node<'_>) -> &str {
        &self.src[n.byte_range()]
    }

    fn is_slice(&self, name: &str) -> bool {
        let Some(params) = self
            .function()
            .and_then(|n| n.child_by_field_name("parameters"))
        else {
            return false;
        };
        params.named_children(&mut params.walk()).any(|p| {
            p.kind() == "parameter"
                && p.child_by_field_name("pattern")
                    .is_some_and(|n| n.kind() == "identifier" && self.text(n) == name)
                && p.child_by_field_name("type")
                    .is_some_and(|n| compact(self.text(n)) == "&[::std::primitive::u8]")
        })
    }

    /// Some(None) is the closed model with no allowance. None is outside that model.
    fn allowance(&self, out: &str, bytes: &str) -> Option<Option<usize>> {
        let body = self.function()?.child_by_field_name("body")?;
        let body_statements = statements(body);
        let (first, rest) = body_statements.split_first()?;
        let (tail, mut passes) = rest.split_last()?;
        if compact(self.text(*first)) != format!("letmut{out}=::std::vec::Vec::new();")
            || compact(self.text(*tail)) != format!("::std::result::Result::Ok({out})")
        {
            return None;
        }
        let mut budget = None;
        if let Some((first, rest)) = passes.split_first()
            && first.kind() == "let_declaration"
        {
            let name = self.text(first.child_by_field_name("pattern")?);
            let amount = self.text(first.child_by_field_name("value")?);
            if compact(self.text(*first)) != format!("letmut{name}={amount};") {
                return None;
            }
            budget = Some((name, amount.parse::<usize>().ok()?));
            passes = rest;
        }
        let write = format!("{out}.extend_from_slice({bytes});");
        if passes.is_empty() {
            return None;
        }
        for statement in passes {
            let visit = statement.named_child(0)?;
            if visit.kind() != "for_expression"
                || self.text(visit.child_by_field_name("pattern")?) != "_"
            {
                return None;
            }
            let iter = self.text(visit.child_by_field_name("value")?);
            if iter == bytes || !self.is_slice(iter) {
                return None;
            }
            let actions: Vec<_> = statements(visit.child_by_field_name("body")?)
                .into_iter()
                .map(|n| compact(self.text(n)))
                .collect();
            let paid = budget.is_some_and(|(left, _)| {
                actions
                    == [
                        format!("if{bytes}.len()>{left}{{return::std::result::Result::Err(());}}"),
                        format!("{left}-={bytes}.len();"),
                        write.clone(),
                    ]
            });
            if !paid && (budget.is_some() || actions != [write.clone()]) {
                return None;
            }
        }
        Some(budget.map(|(_, amount)| amount))
    }
}

fn statements(block: Node<'_>) -> Vec<Node<'_>> {
    block
        .named_children(&mut block.walk())
        .filter(|n| !matches!(n.kind(), "line_comment" | "block_comment"))
        .collect()
}

fn compact(s: &str) -> String {
    s.split_whitespace().collect()
}
