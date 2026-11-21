use super::{Cardinality, RULE, ResultFlows, Texts};
use crate::analysis::Analysis;
use crate::facts::Id;
use crate::report::Verdict;
use std::collections::HashSet;

const SAML: &str = "src/saml.rs";
const VERIFY: &str = "bergshamra-dsig/src/verify.rs";
const EXCLUSIVE: &str = "bergshamra-c14n/src/exclusive.rs";
const PACKAGES: &[(&str, &str)] = &[
    ("bergshamra-c14n", "0.12.0"),
    ("bergshamra-core", "0.12.0"),
    ("bergshamra-dsig", "0.12.0"),
    ("bergshamra-xml", "0.12.0"),
    ("uppsala", "0.12.1"),
];

#[derive(Clone, Copy)]
enum Caller {
    Uncapped,
    Capped,
    Budgeted,
}

impl Caller {
    fn reviewed(texts: &Texts<'_>) -> Option<Self> {
        let saml = texts.get(SAML)?.replace("\r\n", "\n");
        // The application pin covers request provenance, the shape-to-verifier ordering and
        // immutable document identity, as well as the namespace and token selection contract.
        match blake3::hash(saml.as_bytes()).to_hex().as_str() {
            "95f9dd69a669c63830dc7bd22b0dd8503830be0a8f9f90b5fa04c978d1dd211e" => {
                Some(Self::Uncapped)
            } // a26aa982
            "7666dfc6dec67d53273e7eb59b059f16ea263f016cde4a830d0e61cb1f5430cf" => {
                Some(Self::Capped)
            } // c89f0ced
            "55692273b1317942548278dc26c882fae8e283a28ccf3e0c2ba96868b731705b" => {
                Some(Self::Budgeted)
            } // f3c79673
            _ => None,
        }
    }

    fn cardinality(self, flows: &ResultFlows<'_>, file: Id) -> Option<Cardinality<'static>> {
        const VALUE: &str = "attr(doc,inclusive,\"PrefixList\").unwrap_or(\"\")";
        if matches!(self, Self::Uncapped) {
            return None;
        }
        let f = flows.facts;
        let func = f
            .funcs
            .iter()
            .position(|fun| fun.file == file && fun.name == "prefix_list" && !fun.test)?;
        let check = flows
            .rejecting(
                func as Id,
                "seen.len()==MAX_INCLUSIVE_PREFIXES||seen.contains(&p)||!(p==\"#default\"||name)",
                "refuse(SHAPE)",
            )
            .next()?
            .site;
        // The reviewed helper pushes one accepted token per turn, starting with an empty list.
        // An accepted token is ASCII, so the verifier's wider whitespace split agrees.
        f.calls.iter().find(|call| {
            let fun = &f.funcs[f.sites[call.site as usize].func as usize];
            fun.file == file
                && fun.name == "exclusive_c14n"
                && call.full == "prefix_list"
                && matches!(call.args.as_slice(), [arg] if arg.text == VALUE)
        })?;
        Some(Cardinality {
            value: VALUE,
            check,
            members: 8,
            member_bytes: 64,
        })
    }
}

#[derive(Clone, Copy)]
enum Library {
    Vendored,
    Patched,
}

impl Library {
    fn reviewed(
        texts: &Texts<'_>,
        manifest: &toml::Value,
        dependency: &toml::Value,
    ) -> Option<Self> {
        let [feature] = dependency.get("features")?.as_array()?.as_slice() else {
            return None;
        };
        if feature.as_str()? != "rustcrypto"
            || dependency.get("default-features")?.as_bool()?
            || dependency.as_table()?.len() != 3
            || manifest.get("replace").is_some()
        {
            return None;
        }
        let config: toml::Value = toml::from_str(texts.get(".cargo/config.toml")?).ok()?;
        let source = config.get("source")?;
        if source.get("crates-io")?.get("replace-with")?.as_str()? != "vendored-sources"
            || source.get("vendored-sources")?.get("directory")?.as_str()? != "vendor"
        {
            return None;
        }
        let lock: toml::Value = toml::from_str(texts.get("Cargo.lock")?).ok()?;
        let packages = lock.get("package")?.as_array()?;
        let patch = manifest.get("patch").and_then(|p| p.get("crates-io"));
        let mut hash = blake3::Hasher::new();
        for &(name, version) in PACKAGES {
            let mut matching = packages
                .iter()
                .filter(|p| p.get("name").and_then(toml::Value::as_str) == Some(name));
            let package = matching.next()?;
            if matching.next().is_some() || package.get("version")?.as_str()? != version {
                return None;
            }
            let root = match (patch.and_then(|p| p.get(name)), package.get("source")) {
                (None, Some(source))
                    if source.as_str()?
                        == "registry+https://github.com/rust-lang/crates.io-index" =>
                {
                    "vendor/"
                }
                (Some(patch), None)
                    if patch.as_table()?.len() == 1
                        && patch.get("path")?.as_str()? == format!("patches/{name}") =>
                {
                    "patches/"
                }
                _ => return None,
            };
            let prefix = format!("{root}{name}/");
            let manifest_path = format!("{prefix}Cargo.toml");
            let code_prefix = format!("{prefix}src/");
            // Include the selected parser and node-set code, which decide attribute identity
            // and whether the invisible-element membership path can run.
            for (&path, &source) in texts
                .range(prefix.as_str()..)
                .take_while(|(path, _)| path.starts_with(&prefix))
            {
                if path == manifest_path
                    || (path.starts_with(&code_prefix) && path.ends_with(".rs"))
                {
                    for bytes in [
                        path.as_bytes(),
                        b"\0",
                        source.replace("\r\n", "\n").as_bytes(),
                        b"\0",
                    ] {
                        hash.update(bytes);
                    }
                }
            }
        }
        match hash.finalize().to_hex().as_str() {
            // a26aa982 uses the vendored parser, c89f0ced uses the patched parser,
            // and f3c79673 selects the patched renderer and verifier as well.
            "0dcf349f3732bdd9f51d23a5e83685030d757b0cf9fc461b67fcb45a8a94a1b4"
            | "a80f0b1be0079439d708160f2fab3b1f0366e80c09c21645d04d2fff01345306" => {
                Some(Self::Vendored)
            }
            "9d2de91836cfa7f176eb7a28de0a111e3a23c7d9fe5a5e0ce15d83487ba3dee4" => {
                Some(Self::Patched)
            }
            _ => None,
        }
    }

    fn witness(self, list: List) -> Vec<String> {
        let (root, reference, reader, visit, default) = match self {
            Self::Vendored => ("vendor", 1233, 3812, 228, 380),
            Self::Patched => ("patches", 1286, 3865, 232, 384),
        };
        let read = match list {
            List::SignedInfo => 384,
            List::Reference => reference,
        };
        vec![
            format!(
                "{root}/{VERIFY}:{read} selects the {} list, and line {reader} splits its PrefixList before the SignatureValue verdict",
                list.label()
            ),
            format!(
                "{root}/{EXCLUSIVE}:{visit} iterates the inclusive prefix set on every visible element, before looking up or emitting declarations"
            ),
            format!(
                "{root}/{EXCLUSIVE}:{default} searches for #default on invisible elements if namespace filtering is active. The admitted SignedInfo and reference node sets have no namespace filter"
            ),
        ]
    }
}

#[derive(Clone, Copy)]
enum List {
    SignedInfo,
    Reference,
}

impl List {
    fn call(self) -> &'static str {
        match self {
            Self::SignedInfo => "exclusive_c14n(doc,c14n)",
            Self::Reference => "exclusive_c14n(doc,exclusive)",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::SignedInfo => "SignedInfo CanonicalizationMethod",
            Self::Reference => "reference exclusive transform",
        }
    }
}

impl Analysis<'_> {
    pub(super) fn bergshamra_prefix_work(
        &mut self,
        texts: &Texts<'_>,
        reach: &HashSet<Id>,
        flows: &ResultFlows<'_>,
    ) {
        let f = self.f;
        let Some((entry, accept)) = f.funcs.iter().enumerate().find(|(i, fun)| {
            reach.contains(&(*i as Id))
                && self.prefix_candidate(*i as Id)
                && f.files[fun.file as usize].path == SAML
                && fun.name == "accept"
                && fun.class.as_deref() == Some("ServiceProvider")
        }) else {
            return;
        };
        let file = accept.file;
        let entry_call = [
            "self.check_signatures(&doc,root,assertion)",
            "self.check_signatures(&doc,xml.len(),root,assertion)",
        ]
        .into_iter()
        .find_map(|call| {
            flows
                .propagated(entry as Id, call)
                .next()
                .map(|flow| flow.site)
        });
        let mut verification = f.calls.iter().filter(|call| {
            let site = &f.sites[call.site as usize];
            site.file == file
                && self.prefix_candidate(site.func)
                && call.full == "verify_all_document"
                && reach.contains(&site.func)
        });
        let Some(verify) = verification.next() else {
            if let Some(site) = entry_call {
                self.prefix_unknown(
                    site,
                    "cannot resolve the signature verifier reached from the SAML boundary",
                );
            }
            return;
        };
        let manifest = texts
            .get("Cargo.toml")
            .and_then(|s| toml::from_str::<toml::Value>(s).ok());
        let dep = manifest
            .as_ref()
            .and_then(|m| m.get("dependencies"))
            .and_then(|d| d.get("bergshamra-dsig"));
        let version = dep.and_then(|d| d.as_str().or_else(|| d.get("version")?.as_str()));
        if version != Some("=0.12.0") {
            let selection = version.unwrap_or("of unknown version");
            self.prefix_unknown(
                verify.site,
                &format!(
                    "no reviewed prefix-work source summary covers bergshamra-dsig {selection}"
                ),
            );
            return;
        }
        let library = manifest
            .as_ref()
            .zip(dep)
            .and_then(|(m, d)| Library::reviewed(texts, m, d));
        let Some(library) = library else {
            self.prefix_unknown(verify.site, "the active verifier, renderer or XML sources do not match the reviewed Bergshamra summary");
            return;
        };
        let Some(caller) = Caller::reviewed(texts) else {
            self.prefix_unknown(verify.site, "cannot establish that the SAML shape check and verifier read the same PrefixList before canonicalization");
            return;
        };
        let verify_site = &f.sites[verify.site as usize];
        let shape_gate = f
            .funcs
            .iter()
            .position(|fun| {
                fun.file == file
                    && !fun.test
                    && fun.name == "check_signatures"
                    && fun.class.as_deref() == Some("ServiceProvider")
            })
            .and_then(|owner| {
                flows
                    .propagated(owner as Id, "check_signature_shape(doc,*s)")
                    .next()
            })
            .map(|flow| flow.site);
        let Some((entry_call, shape_gate)) = entry_call.zip(shape_gate) else {
            self.prefix_unknown(
                verify.site,
                "cannot establish that shape rejection stops verification of the same document",
            );
            return;
        };
        let shape = f
            .funcs
            .iter()
            .position(|fun| fun.file == file && !fun.test && fun.name == "check_signature_shape");
        let checks = [List::SignedInfo, List::Reference].map(|list| {
            Some((
                list,
                flows.propagated(shape? as Id, list.call()).next()?.site,
            ))
        });
        let [Some(signed_info), Some(reference)] = checks else {
            self.prefix_unknown(
                verify.site,
                "cannot trace both exclusive-canonicalization lists through rejecting shape checks",
            );
            return;
        };
        if verification.next().is_some() {
            self.prefix_unknown(
                verify.site,
                "more than one reached verifier call must be resolved",
            );
            return;
        }
        let bound = caller.cardinality(flows, file);
        let cert_loop = f.loops.iter().find(|l| {
            f.sites[l.site as usize].func == verify_site.func
                && Some(l.id) == verify_site.ctx.loop_id
                && l.iter == "&self.idp.certs"
        });
        for (list, site) in [signed_info, reference] {
            let mut witness = vec![
                format!(
                    "{} passes the request document to signature checking before authentication",
                    self.loc(entry_call)
                ),
                format!(
                    "{} passes every signature through the shape gate on the same document before {} verifies it",
                    self.loc(shape_gate),
                    self.loc(verify.site)
                ),
                format!(
                    "{} propagates rejection for the {} list",
                    self.loc(site),
                    list.label()
                ),
            ];
            if let Some(cert_loop) = cert_loop {
                witness.push(format!("{} repeats verification per configured pinned certificate, a separate configuration multiplier", self.loc(cert_loop.site)));
            }
            let (verdict, message, assumptions) = match (&bound, caller) {
                (Some(bound), _) => {
                    witness.push(format!("{} bounds `{}` before the renderer reads that attribute", self.loc(bound.check), bound.value));
                    (Verdict::Proven, format!("{} supplies at most {} distinct prefixes of at most {} bytes per element", list.label(), bound.members, bound.member_bytes), vec![
                        "the reviewed Cargo selection and verifier, renderer and parser sources apply at runtime".into(),
                        "the shape gate rejects extra or namespaced attributes on the same immutable document, so both readers select the same PrefixList".into(),
                        "the accepted ASCII NCNames or #default tokenize identically in both readers".into(),
                        "the admitted same-document reference and transforms use a fast path whose node set carries no namespace filter".into(),
                    ])
                }
                (None, Caller::Uncapped) => {
                    witness.push("src/saml.rs:1028 checks the PrefixList attribute name and leaves its value unrestricted".into());
                    if matches!(list, List::SignedInfo) {
                        witness.push("SignedInfo has a fixed visible shape, but each visible visit still scales with the uncapped list. Rendering follows reference digest comparison and precedes SignatureValue verification".into());
                    } else {
                        witness.push("the reference can visit a larger signed subtree without changing its transform list".into());
                    }
                    (Verdict::Violated, format!("{} admits a request PrefixList with no cardinality or token length cap, reused across visible elements", list.label()), vec![])
                }
                (None, _) => (Verdict::Unknown, "cannot establish the accepted cardinality of the exact PrefixList the renderer reads".into(), vec![]),
            };
            witness.extend(library.witness(list));
            self.push(6, RULE, verdict, site, message, witness, assumptions);
        }
    }

    fn prefix_unknown(&mut self, site: Id, message: &str) {
        self.push(
            6,
            RULE,
            Verdict::Unknown,
            site,
            message.into(),
            vec![],
            vec![],
        );
    }
}
