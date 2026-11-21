//! Question 9 for Rust handles a function releases by hand: a C handle freed by an explicit
//! `*_destroy`/`*_free`/`*_close` call leaks when anything between its creation and that call
//! panics or returns early. A guard whose `Drop` frees it releases it on every exit.

use super::Analysis;
use crate::facts::*;
use crate::report::Verdict;
use regex::Regex;

impl<'a> Analysis<'a> {
    pub(super) fn release_on_panic(&mut self) {
        let f = self.f;
        // A C release, called through its bindings: `ffi::duckdb_appender_destroy`,
        // `libduckdb_sys::duckdb_close`. A Rust function of the same shape is not one.
        let release = Regex::new(
            r"(^|::)(ffi|sys|[a-z0-9_]+_sys)::([a-z0-9_]+::)*[a-z][a-z0-9]*_[a-z0-9_]*(destroy|free|close|release|dispose|delete)$",
        )
        .expect("release");
        // A call into C does not unwind: an `ffi::` or `sys::` path, or a function with the
        // release's C prefix (`duckdb_appender_clear` beside `duckdb_appender_destroy`).
        let c_path = Regex::new(r"(^|::)(ffi|sys)::").expect("c path");
        let at = |site: Id| &f.sites[site as usize];
        for r in &f.calls {
            let rs = at(r.site);
            let file = &f.files[rs.file as usize];
            if file.lang != Lang::Rust || file.test || !release.is_match(&r.full) {
                continue;
            }
            let Some(arg) = r.args.first() else { continue };
            let handle = arg
                .text
                .trim()
                .trim_start_matches("&mut ")
                .trim_start_matches("&mut")
                .trim_start_matches('&')
                .trim_start_matches('*')
                .trim();
            if handle.is_empty() || !handle.chars().all(|c| c.is_alphanumeric() || c == '_') {
                continue;
            }
            // The handle's creation: the latest assignment from a call before the release.
            let made = f
                .assigns
                .iter()
                .filter(|a| {
                    let s = at(a.site);
                    s.file == rs.file
                        && s.func == rs.func
                        && s.line < rs.line
                        && !a.value.calls.is_empty()
                        && a.target.trim().trim_start_matches("mut ").trim() == handle
                })
                .max_by_key(|a| at(a.site).line);
            let Some(made) = made else { continue };
            let prefix = r
                .name
                .split('_')
                .next()
                .map(|p| format!("{p}_"))
                .unwrap_or_default();
            let c_call = |c: &Call| c_path.is_match(&c.full) || c.name.starts_with(&prefix);
            // Calls that cannot panic: constructors (`Ok`, `Some`), pointer and state reads.
            let quiet = |c: &Call| {
                c.name
                    .chars()
                    .next()
                    .is_some_and(|ch| ch.is_ascii_uppercase())
                    || matches!(
                        c.name.as_str(),
                        "null"
                            | "null_mut"
                            | "as_ptr"
                            | "as_mut_ptr"
                            | "is_err"
                            | "is_ok"
                            | "is_some"
                            | "is_none"
                            | "is_null"
                            | "len"
                            | "is_empty"
                    )
            };
            let from = at(made.site).line;
            let between: Vec<&Call> = f
                .calls
                .iter()
                .filter(|c| {
                    let s = at(c.site);
                    s.file == rs.file
                        && s.func == rs.func
                        && s.line > from
                        && s.line < rs.line
                        && !c_call(c)
                        && !quiet(c)
                })
                .collect();
            let path = &file.path;
            let creator = made
                .value
                .calls
                .first()
                .and_then(|&s| self.call(s))
                .map(|c| c.full.clone())
                .unwrap_or_default();
            if between.is_empty() {
                self.push(
                    9,
                    "release-on-panic",
                    Verdict::Proven,
                    r.site,
                    format!(
                        "`{handle}` from `{creator}` (line {from}) is released by `{}` with no Rust call between them, so nothing there can panic",
                        r.full
                    ),
                    vec![],
                    vec!["calls into C do not unwind".into()],
                );
                continue;
            }
            let mut witness = vec![format!("{path}:{from} `{handle}` = `{creator}(...)`")];
            witness.extend(between.iter().take(6).map(|c| {
                format!(
                    "{path}:{} `{}` can panic before the release",
                    at(c.site).line,
                    c.full
                )
            }));
            witness.push(format!("{path}:{} `{}`", rs.line, r.full));
            self.push(
                9,
                "release-on-panic",
                Verdict::Violated,
                r.site,
                format!(
                    "`{handle}` from `{creator}` is released only by the explicit `{}`: a panic or an early return in the {} call(s) between leaks it; a guard whose Drop releases it covers every exit",
                    r.full,
                    between.len()
                ),
                witness,
                vec![],
            );
        }
    }
}
