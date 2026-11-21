//! The self-check without any outside repository: each snippet in acceptance/inject is written
//! into a small clean tree, and the scan must turn from no violation of that rule into one at the
//! snippet. A rule that cannot fail this way proves nothing.

use serde_json::Value;
use std::path::Path;
use std::process::Command;

const CLEAN: &str = r#"
import logging
import os
import re
import threading
import time
from pathlib import Path

log = logging.getLogger(__name__)
_lock = threading.Lock()

ALLOWED = re.compile(r"[a-z0-9][a-z0-9-]{0,62}")


def load(root: Path, name: str) -> bytes:
    if not ALLOWED.fullmatch(name):
        raise ValueError("bad name")
    return (root / name / "meta.json").read_bytes()


def elapsed(start: float) -> float:
    now = time.monotonic()
    return now - start


def past(deadline: float) -> bool:
    log.info("checked at %s", time.time())
    return time.time() > deadline


def save(path: Path, text: str) -> None:
    _lock.acquire()
    try:
        path.write_text(text)
    finally:
        _lock.release()


def token_length() -> int:
    token = os.environ.get("API_TOKEN", "")
    log.info("token has %d characters", len(token))
    return len(token)


class Client:
    def __init__(self, token):
        self.token = token

    def status(self):
        return "ok"


def report_status() -> None:
    client = Client(os.environ.get("API_TOKEN", ""))
    log.info("status %s from %s", client.status(), os.environ.get("API_TOKEN_FILE", ""))
"#;

const CLEAN_SH: &str = "ssh ha 'cat /config/.storage/backup' | jq '.data.password | length'\ngrep -q '^TOKEN=' .env\nchmod 600 .env\n";

const MANIFEST: &str = r#"{"domain": "demo", "name": "Demo", "version": "0.1.0"}"#;

struct Case {
    snippet: &'static str,
    /// Repo-relative file the snippet is written to.
    file: &'static str,
    question: u64,
    rule: &'static str,
}

const CASES: &[Case] = &[
    Case {
        snippet: "q10_log_env.py",
        file: "pkg/inject.py",
        question: 10,
        rule: "secret-sink",
    },
    Case {
        snippet: "q10_argv.py",
        file: "pkg/inject.py",
        question: 10,
        rule: "secret-sink",
    },
    Case {
        snippet: "q10_store_cat.sh",
        file: "pkg/run.sh",
        question: 10,
        rule: "store-printed",
    },
    Case {
        snippet: "q9_interrupted.py",
        file: "pkg/inject.py",
        question: 9,
        rule: "release-interrupted",
    },
    Case {
        snippet: "q9_on_error.py",
        file: "pkg/inject.py",
        question: 9,
        rule: "release-on-error",
    },
    Case {
        snippet: "q1_one_reading.py",
        file: "pkg/inject.py",
        question: 1,
        rule: "one-reading",
    },
    Case {
        snippet: "q1_mixed_time.py",
        file: "pkg/inject.py",
        question: 1,
        rule: "mixed-time-sources",
    },
    Case {
        snippet: "q1_double.py",
        file: "pkg/inject.py",
        question: 1,
        rule: "double-reimplements",
    },
    Case {
        snippet: "q2_suite_guard.py",
        file: "pkg/tests/conftest.py",
        question: 2,
        rule: "suite-disables-guard",
    },
    Case {
        snippet: "q2_wire.py",
        file: "pkg/tests/test_wire.py",
        question: 2,
        rule: "wire-provenance",
    },
    Case {
        snippet: "q3_reread.py",
        file: "pkg/inject.py",
        question: 3,
        rule: "reread-after-check",
    },
    Case {
        snippet: "q4_admin.py",
        file: "custom_components/demo/inject.py",
        question: 4,
        rule: "unguarded-effect",
    },
    Case {
        snippet: "q5_segment.py",
        file: "pkg/inject.py",
        question: 5,
        rule: "closed-segment",
    },
    Case {
        snippet: "q5_deny.py",
        file: "pkg/inject.py",
        question: 5,
        rule: "open-deny",
    },
    Case {
        snippet: "q6_wall_bound.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "wall-date-bound",
    },
    Case {
        snippet: "q6_retry.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "retry-limit",
    },
    Case {
        snippet: "q6_retry.rs",
        file: "pkg/inject.rs",
        question: 6,
        rule: "retry-limit",
    },
    Case {
        snippet: "q6_state_exit.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "state-exit",
    },
    Case {
        snippet: "q6_durable.py",
        file: "custom_components/demo/inject.py",
        question: 6,
        rule: "durable-exit",
    },
    Case {
        snippet: "q6_requery.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "handler-requery",
    },
    Case {
        snippet: "q6_held.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "held-state-exit",
    },
    Case {
        snippet: "q6_held.py",
        file: "pkg/inject.py",
        question: 6,
        rule: "held-run-recovery",
    },
    Case {
        snippet: "q3_stale_write.py",
        file: "pkg/inject.py",
        question: 3,
        rule: "stale-write-back",
    },
    Case {
        snippet: "q3_read_before_check.py",
        file: "pkg/inject.py",
        question: 3,
        rule: "read-before-check",
    },
    Case {
        snippet: "q4_write_before_guard.py",
        file: "pkg/inject.py",
        question: 4,
        rule: "write-before-guard",
    },
    Case {
        snippet: "q5_name_table.py",
        file: "pkg/tests/test_guard.py",
        question: 5,
        rule: "name-table-guard",
    },
    Case {
        snippet: "q7_probe.py",
        file: "pkg/inject.py",
        question: 7,
        rule: "weak-probe",
    },
];

fn write(root: &Path, rel: &str, text: &str) {
    let p = root.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

fn clean_tree(root: &Path) {
    write(root, "pkg/__init__.py", "");
    write(root, "pkg/store.py", CLEAN);
    write(root, "pkg/run.sh", CLEAN_SH);
    write(root, "pkg/tests/__init__.py", "");
    write(
        root,
        "pkg/tests/test_store.py",
        "def test_nothing():\n    assert True\n",
    );
    write(root, "custom_components/demo/manifest.json", MANIFEST);
    write(
        root,
        "custom_components/demo/__init__.py",
        "DOMAIN = \"demo\"\n",
    );
    let caps = Path::new(env!("CARGO_MANIFEST_DIR")).join("acceptance/captures/envisalink-tpi.txt");
    write(
        root,
        "captures/tpi.txt",
        &std::fs::read_to_string(caps).unwrap(),
    );
    write(
        root,
        "proofscan.toml",
        "[[q2.wire]]\nname = \"TPI keypad update\"\npattern = '^%00,'\ncaptures = [\"captures/*.txt\"]\n",
    );
}

/// (site, rule) of each violation of `question`.
fn violations(root: &Path, question: u64) -> Vec<(String, String)> {
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "--json", "-q", &question.to_string()])
        .arg(root)
        .output()
        .unwrap();
    let v: Value = serde_json::from_slice(&out.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stderr)));
    v["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["verdict"] == "violated")
        .map(|f| {
            (
                f["site"].as_str().unwrap().replace('\\', "/"),
                f["rule"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

#[test]
fn clean_tree_has_no_violation() {
    let dir = tempfile::tempdir().unwrap();
    clean_tree(dir.path());
    for q in [1, 2, 3, 4, 5, 6, 7, 9, 10] {
        assert_eq!(
            violations(dir.path(), q),
            vec![],
            "question {q} on the clean tree"
        );
    }
}

#[test]
fn retry_limit_requires_an_advancing_bound_that_exits() {
    let dir = tempfile::tempdir().unwrap();
    let sources = [
        (
            "log.py",
            "while True:\n    try:\n        work()\n    except OSError:\n        log('retry limit')\n",
            "unknown",
        ),
        (
            "unused.py",
            "attempt = 0\nwhile True:\n    attempt += 1\n    try:\n        work()\n    except OSError:\n        continue\n",
            "unknown",
        ),
        (
            "fixed.py",
            "attempt = 0\nwhile True:\n    if attempt >= 3:\n        break\n    try:\n        work()\n    except OSError:\n        continue\n",
            "unknown",
        ),
        (
            "no_exit.py",
            "attempt = 0\nwhile True:\n    attempt += 1\n    if attempt >= 3:\n        log(attempt)\n    try:\n        work()\n    except OSError:\n        continue\n",
            "unknown",
        ),
        (
            "bypass.py",
            "attempt = 0\nwhile True:\n    if skip():\n        continue\n    attempt += 1\n    if attempt >= 3:\n        break\n    try:\n        work()\n    except OSError:\n        continue\n",
            "unknown",
        ),
        (
            "reset.py",
            "attempt = 0\nwhile True:\n    attempt += 1\n    if attempt >= 3:\n        break\n    try:\n        work()\n    except OSError:\n        attempt = 0\n",
            "unknown",
        ),
        (
            "wrong_direction.py",
            "attempt = 0\nwhile True:\n    attempt += 1\n    if attempt < 0:\n        break\n    try:\n        work()\n    except OSError:\n        continue\n",
            "unknown",
        ),
        (
            "nested_exit.py",
            "import time\ndeadline = time.monotonic() + 10\nwhile True:\n    def check():\n        if time.monotonic() >= deadline:\n            return\n    try:\n        work()\n    except OSError:\n        check()\n",
            "unknown",
        ),
        (
            "bare.py",
            "while True:\n    try:\n        work()\n    except OSError:\n        continue\n",
            "violated",
        ),
        (
            "counter.py",
            "i = 0\nwhile True:\n    if i >= 3:\n        break\n    i += 1\n    try:\n        work()\n    except OSError:\n        continue\n",
            "proven",
        ),
        (
            "condition.py",
            "i = 0\nwhile i < 3:\n    i += 1\n    try:\n        work()\n    except OSError:\n        continue\n",
            "proven",
        ),
        (
            "deadline.py",
            "import time\ndeadline = time.monotonic() + 10\nwhile True:\n    if time.monotonic() >= deadline:\n        break\n    try:\n        work()\n    except OSError:\n        continue\n",
            "proven",
        ),
        (
            "range.rs",
            "fn run() { for _ in 0..3 { if let Err(_) = work() { continue; } } }",
            "proven",
        ),
        (
            "range.py",
            "for attempt in range(3):\n    try:\n        work()\n    except OSError:\n        continue\n",
            "proven",
        ),
        (
            "per_item.rs",
            "fn run() { for i in 0..3 { if let Err(_) = work(i) { continue; } } }",
            "absent",
        ),
        (
            "per_item.py",
            "for item in range(3):\n    try:\n        work(item)\n    except OSError:\n        continue\n",
            "absent",
        ),
        (
            "rust_counter.rs",
            "fn run() { let mut i = 0; loop { if i >= 3 { break; } i += 1; if let Err(_) = work() { continue; } } }",
            "proven",
        ),
        (
            "rust_propagated.rs",
            "fn run() -> Result<(), ()> { let mut i = 0; loop { if i >= 3 { Err(())?; } i += 1; if let Err(_) = work() { continue; } } }",
            "proven",
        ),
        (
            "rust_conditional_exit.rs",
            "fn run() { let mut attempt = 0; loop { if attempt >= 3 { #[cfg(feature = \"halt\")] break; } attempt += 1; if let Err(_) = work() { continue; } } }",
            "unknown",
        ),
        (
            "js_counter.js",
            "let i = 0;\nwhile (true) {\n    if (i >= 3) break;\n    i++;\n    try { work(); } catch (e) { continue; }\n}",
            "proven",
        ),
        (
            "ps_counter.ps1",
            "$i = 0\nwhile ($true) {\n    if ($i -ge 3) { break }\n    $i++\n    try { Work } catch { continue }\n}\n",
            "proven",
        ),
        (
            "ps_reset.ps1",
            "$attempt = 0\nwhile ($true) {\n    if ($attempt -ge 3) { break }\n    $attempt++\n    try { Work } catch { $Attempt = 0 }\n}\n",
            "unknown",
        ),
        (
            "sh_counter.sh",
            "i=0\nwhile true; do\n    if [ \"$i\" -ge 3 ]; then break; fi\n    i=$((i + 1))\n    work || continue\ndone\n",
            "proven",
        ),
    ];
    for (name, source, _) in sources {
        write(dir.path(), name, source);
    }
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "-q", "6", "--all", "--json"])
        .arg(dir.path())
        .output()
        .unwrap();
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    let findings = report["findings"].as_array().unwrap();
    for (name, _, verdict) in sources {
        let actual = findings.iter().find(|f| {
            f["rule"] == "retry-limit"
                && f["site"].as_str().unwrap().starts_with(&format!("{name}:"))
        });
        if verdict == "absent" {
            assert!(actual.is_none(), "{name}: {actual:?}");
            continue;
        }
        assert_eq!(
            actual.map(|f| &f["verdict"]),
            Some(&Value::from(verdict)),
            "{name}: {actual:?}"
        );
        let argument = match name {
            "deadline.py" => "deadline",
            "range.rs" | "range.py" => "range",
            _ => "counter",
        };
        let finding = actual.unwrap();
        if verdict == "proven" {
            assert!(finding["message"].as_str().unwrap().contains(argument));
            assert!(finding["assumptions"].to_string().contains(argument));
        } else if verdict == "unknown" {
            assert!(
                finding["message"]
                    .as_str()
                    .unwrap()
                    .contains("no exiting comparison")
            );
        }
    }
}

#[test]
fn rust_counter_probe_selfcheck() {
    let output = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .arg("selfcheck")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn rust_retry_shapes_need_evidence_on_every_retry_path() {
    let sources = [
        (
            "remainder",
            r"
            fn run(deadline: Instant) {
                loop {
                    let left = deadline.saturating_duration_since(Instant::now());
                    if left.is_zero() { return; }
                    if let Err(_) = work(left) { continue; }
                    return;
                }
            }",
            "proven",
            "remaining duration",
        ),
        (
            "remainder_equal_zero",
            r"
            fn run(deadline: Instant) {
                loop {
                    if deadline.saturating_duration_since(Instant::now()) == Duration::ZERO { break; }
                    if let Err(_) = work() { continue; }
                    return;
                }
            }",
            "proven",
            "remaining duration",
        ),
        (
            "checked_remainder",
            r"
            fn run(deadline: Instant) {
                loop {
                    let Some(left) = deadline.checked_duration_since(Instant::now()) else { break; };
                    if let Err(_) = work(left) { continue; }
                    return;
                }
            }",
            "proven",
            "remaining duration",
        ),
        (
            "unchecked_remainder",
            r"
            fn run(deadline: Instant) {
                loop {
                    let left = deadline.saturating_duration_since(Instant::now());
                    if let Err(_) = work(left) { continue; }
                    return;
                }
            }",
            "unknown",
            "",
        ),
        (
            "civil",
            r"
            fn run() {
                let deadline = Zoned::now().datetime() + span;
                loop {
                    if let Err(e) = work() { log(e); }
                    let t = Zoned::now().datetime();
                    if t >= deadline { break; }
                }
            }",
            "proven",
            "civil clock",
        ),
        (
            "chrono",
            r"
            fn run() {
                let deadline = Local::now().naive_local() + span;
                loop {
                    if let Err(e) = work() { log(e); }
                    if Local::now().naive_local() >= deadline { break; }
                }
            }",
            "proven",
            "civil clock",
        ),
        (
            "stale_civil",
            r"
            fn run() {
                let deadline = Zoned::now().datetime() + span;
                let t = Zoned::now().datetime();
                loop {
                    if let Err(e) = work() { log(e); }
                    if t >= deadline { break; }
                }
            }",
            "unknown",
            "",
        ),
        (
            "nested",
            r"
            fn run(deadline: Instant) {
                loop {
                    match cursor.next_for(WAIT) {
                        Err(TimedOut) => {
                            if Instant::now() >= deadline { return; }
                        }
                        Ok(Some(row)) => rows.push(row),
                        _ => return,
                    }
                }
            }",
            "proven",
            "enumerator",
        ),
        (
            "nested_bypass",
            r"
            fn run(deadline: Instant) {
                loop {
                    match cursor.next_for(WAIT) {
                        Err(Interrupted) => continue,
                        Err(TimedOut) => {
                            if Instant::now() >= deadline { return; }
                        }
                        Ok(Some(row)) => rows.push(row),
                        _ => return,
                    }
                }
            }",
            "unknown",
            "",
        ),
        (
            "growth",
            r"
            fn run() {
                let mut buffer = vec![0u64; 512];
                loop {
                    let mut used = 0u32;
                    let error = query(buffer.as_mut_ptr(), &mut used);
                    if error == ERROR_INSUFFICIENT_BUFFER && used as usize > buffer.len() * 8 {
                        buffer = vec![0u64; (used as usize).div_ceil(8)];
                        continue;
                    }
                    if error != 0 { return Err(error); }
                    return Ok(buffer);
                }
            }",
            "proven",
            "finite-width",
        ),
        (
            "growth_may_stall",
            r"
            fn run() {
                let mut buffer = vec![0u64; 512];
                loop {
                    let mut used = 0u32;
                    let error = query(buffer.as_mut_ptr(), &mut used);
                    if error == ERROR_INSUFFICIENT_BUFFER && used as usize >= buffer.len() * 8 {
                        buffer = vec![0u64; (used as usize).div_ceil(8)];
                        continue;
                    }
                    if error != 0 { return Err(error); }
                    return Ok(buffer);
                }
            }",
            "unproven",
            "",
        ),
        (
            "replay",
            r"
            fn run() {
                while let Some(mut job) = queue.pop_front() {
                    match send(&job.request) {
                        Err(Expired) if !job.replayed => {
                            job.replayed = true;
                            queue.push_back(job);
                        }
                        result => complete(job, result),
                    }
                }
            }",
            "proven",
            "replay",
        ),
        (
            "replay_marked_late",
            r"
            fn run() {
                while let Some(mut job) = queue.pop_front() {
                    match send(&job.request) {
                        Err(Expired) if !job.replayed => {
                            queue.push_back(job);
                            job.replayed = true;
                        }
                        result => complete(job, result),
                    }
                }
            }",
            "unproven",
            "",
        ),
        (
            "fresh_read",
            r"
            fn run() {
                loop {
                    let frame = match stream.read_frame() {
                        Ok(frame) => frame,
                        Err(e) => return ReadError(e),
                    };
                    consume(frame);
                }
            }",
            "absent",
            "",
        ),
        (
            "labelled_exit",
            r"
            fn run() {
                'outer: loop {
                    for _ in 0..3 {
                        if let Err(e) = work() { log(e); break 'outer; }
                    }
                }
            }",
            "absent",
            "",
        ),
        (
            "independent_cases",
            r"
            fn run() {
                for _ in 0..3 {
                    let input = next_case();
                    match (work(&input), expected(&input)) {
                        (Err(e), _) => assert_error(e),
                        _ => (),
                    }
                }
            }",
            "absent",
            "",
        ),
        (
            "pending_batch",
            r"
            fn run() {
                loop {
                    if let (Some(service), Ok(items)) = (&service, store.pending()) {
                        for (id, item) in items {
                            match send(service, &item) {
                                Ok(()) => store.finished(id),
                                Err(e) => store.failed(id, e),
                            }
                        }
                    }
                    wait();
                }
            }",
            "unknown",
            "",
        ),
        (
            "failed_delivery",
            r#"
            impl Store {
                fn pending(&self) {
                    let mut stmt = db.prepare("SELECT id,binding_id,source_id,text FROM deliveries WHERE state='pending' ORDER BY attempts,id LIMIT 100")?;
                }
                fn delivery_result(&self) {
                    db.execute("UPDATE deliveries SET state=CASE WHEN ?2 THEN 'sent' ELSE 'pending' END, attempts=attempts+1, last_error=?3 WHERE id=?1", params![id,sent,error])?;
                }
            }
            fn run() {
                loop {
                    if let (Some(service), Ok(items)) = (&service, store.pending()) {
                        for (id, item) in items {
                            match send(service, &item) {
                                Ok(()) => { let _ = store.delivery_result(id, true, ""); }
                                Err(e) => { let _ = store.delivery_result(id, false, &e); }
                            }
                        }
                    }
                    wait();
                }
            }"#,
            "violated",
            "",
        ),
        (
            "volume_inventory",
            r"
            use windows_sys::Win32::Storage::FileSystem::{FindFirstVolumeW, FindNextVolumeW};
            fn run() {
                let mut name = vec![0u16; 64];
                let find = unsafe { FindFirstVolumeW(name.as_mut_ptr(), name.len() as u32) };
                loop {
                    match probe(&name) {
                        Ok(value) => save(value),
                        Err(error) => record(error),
                    }
                    if unsafe { FindNextVolumeW(find, name.as_mut_ptr(), name.len() as u32) } == 0 {
                        break;
                    }
                }
            }",
            "absent",
            "",
        ),
        (
            "volume_probe_bypasses_advance",
            r"
            use windows_sys::Win32::Storage::FileSystem::{FindFirstVolumeW, FindNextVolumeW};
            fn run() {
                let mut name = vec![0u16; 64];
                let find = unsafe { FindFirstVolumeW(name.as_mut_ptr(), name.len() as u32) };
                loop {
                    match probe(&name) {
                        Ok(value) => save(value),
                        Err(_) => continue,
                    }
                    if unsafe { FindNextVolumeW(find, name.as_mut_ptr(), name.len() as u32) } == 0 {
                        break;
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "panic_exits",
            r#"
            fn run() {
                loop {
                    match read() {
                        Ok(0) => break,
                        Ok(n) => consume(n),
                        Err(e) => panic!("{e}"),
                    }
                }
            }"#,
            "absent",
            "",
        ),
        (
            "drains_items",
            r"
            use std::collections::VecDeque;
            struct Shell { pending: VecDeque<Request> }
            impl Shell {
                fn run(&mut self) {
                    while let Some(request) = self.pending.pop_front() {
                        if let Request::Work(input) = request {
                            match apply(&input) {
                                Ok(()) => (),
                                Err(e) => record(e),
                            }
                        } else {
                            dialogs.push_back(request);
                        }
                    }
                }
            }",
            "absent",
            "",
        ),
        (
            "requeues_item",
            r"
            use std::collections::VecDeque;
            struct Shell { pending: VecDeque<Request> }
            impl Shell {
                fn run(&mut self) {
                    while let Some(request) = self.pending.pop_front() {
                        match apply(&request) {
                            Ok(()) => (),
                            Err(_) => self.pending.push_back(request),
                        }
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "independent_error_while_draining_items",
            r"
            use std::collections::VecDeque;
            struct Shell { pending: VecDeque<Request> }
            impl Shell {
                fn run(&mut self) {
                    while let Some(request) = self.pending.pop_front() {
                        match apply(&fixed_input) {
                            Ok(()) => (),
                            Err(e) => record(e),
                        }
                        dialogs.push_back(request);
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "independent_error_in_volume_loop",
            r"
            use windows_sys::Win32::Storage::FileSystem::{FindFirstVolumeW, FindNextVolumeW};
            fn run() {
                let mut name = vec![0u16; 64];
                let find = unsafe { FindFirstVolumeW(name.as_mut_ptr(), name.len() as u32) };
                loop {
                    match {
                        log(&name);
                        poll(&fixed_input)
                    } {
                        Ok(result) => record(result),
                        Err(error) => log(error),
                    }
                    if unsafe { FindNextVolumeW(find, name.as_mut_ptr(), name.len() as u32) } == 0 {
                        break;
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "guarded_clock",
            r"
            fn run(until: Instant) {
                loop {
                    match open() {
                        Ok(file) => return Ok(file),
                        Err(e) if is_sharing(e) && Instant::now() < until => sleep(),
                        Err(e) => return Err(e),
                    }
                }
            }",
            "proven",
            "deadline",
        ),
        (
            "guarded_clock_bypass",
            r"
            fn run(until: Instant) {
                loop {
                    match open() {
                        Ok(file) => return Ok(file),
                        Err(e) if busy(e) => continue,
                        Err(e) if is_sharing(e) && Instant::now() < until => sleep(),
                        Err(e) => return Err(e),
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "finite_flags",
            r"
            fn run() {
                let mut refreshed = false;
                let mut consented = false;
                loop {
                    match request() {
                        Err(e) if denied(e) && !refreshed => { refreshed = true; renew(); }
                        Err(e) if redirected(e) && !consented => { consented = true; accept(); }
                        other => return other,
                    }
                }
            }",
            "proven",
            "one-shot flags",
        ),
        (
            "reset_flag",
            r"
            fn run() {
                let mut refreshed = false;
                loop {
                    match request() {
                        Err(e) if denied(e) && !refreshed => { refreshed = true; }
                        Err(e) if redirected(e) => { refreshed = false; }
                        other => return other,
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "accept_retries_in_select",
            r"
            fn run() {
                loop {
                    tokio::select! {
                        res = listener.accept() => {
                            let socket = match res {
                                Ok(socket) => socket,
                                Err(_) => continue,
                            };
                            serve(socket);
                        }
                        _ = stop => return,
                    }
                }
            }",
            "violated",
            "",
        ),
        (
            "accept_exits_in_select",
            r"
            fn run() {
                loop {
                    tokio::select! {
                        res = listener.accept() => {
                            let socket = match res {
                                Ok(socket) => socket,
                                Err(_) => return,
                            };
                            serve(socket);
                        }
                        _ = stop => return,
                    }
                }
            }",
            "absent",
            "",
        ),
        (
            "http_status_retries",
            r"
            fn run() {
                let mut attempts = 0;
                loop {
                    attempts += 1;
                    let status = submit()?;
                    return match status.as_u16() {
                        410 if attempts == 1 => continue,
                        _ => complete(status),
                    };
                }
            }",
            "unknown",
            "",
        ),
        (
            "batch_rearmed_after_error",
            r"
            fn run() {
                loop {
                    if ready && flag.swap(false, Ordering::Relaxed) {
                        if due {
                            for item in items {
                                if let Err(_) = run_job(item) {
                                    flag.store(true, Ordering::Relaxed);
                                }
                            }
                        }
                    }
                    poll();
                }
            }",
            "violated",
            "",
        ),
    ];
    let dir = tempfile::tempdir().unwrap();
    for (name, source, _, _) in sources {
        write(dir.path(), &format!("{name}.rs"), source);
    }
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "-q", "6", "--all", "--json"])
        .arg(dir.path())
        .output()
        .unwrap();
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    let findings = report["findings"].as_array().unwrap();
    let mut mismatches = Vec::new();
    for (name, _, expected, argument) in sources {
        let finding = findings.iter().find(|f| {
            f["rule"] == "retry-limit"
                && f["site"]
                    .as_str()
                    .unwrap()
                    .starts_with(&format!("{name}.rs:"))
        });
        let actual = finding
            .and_then(|f| f["verdict"].as_str())
            .unwrap_or("absent");
        let matches = match expected {
            "unproven" => matches!(actual, "unknown" | "violated"),
            _ => actual == expected,
        };
        if !matches {
            mismatches.push(format!("{name}: expected {expected}, got {actual}"));
        } else if expected == "proven" {
            let f = finding.unwrap();
            assert!(f["message"].as_str().unwrap().contains(argument), "{f}");
            assert!(f["assumptions"].to_string().contains(argument), "{f}");
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn rust_retry_limit_requires_strict_progress_on_every_back_edge() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let decoder = |body: &str| {
        format!(
            "fn decode(mut rest: &[u8], mut other: &[u8], n: usize) {{
                loop {{
                    match std::str::from_utf8(rest) {{
                        Ok(_) => return,
                        Err(error) => {{ {body} }}
                    }}
                }}
            }}"
        )
    };
    let sources = [
        (
            "decoder",
            "match error.error_len() {
                Some(bad) => { rest = &rest[error.valid_up_to() + bad..]; }
                None => return,
            }",
            "proven",
        ),
        ("literal", "rest = &rest[1..];", "proven"),
        (
            "split",
            "let (valid, after) = rest.split_at(error.valid_up_to());
             rest = &after[error.error_len().unwrap_or(after.len())..];",
            "proven",
        ),
        (
            "incomplete_exits",
            "let (valid, after) = rest.split_at(error.valid_up_to());
             match error.error_len() {
                 Some(bad) => { rest = &after[bad..]; }
                 None => { let partial = after.to_vec(); break; }
             }",
            "proven",
        ),
        (
            "breaks_out_of_arm_only",
            "match error.error_len() {
                 Some(bad) => { rest = &rest[bad..]; }
                 None => 'incomplete: { break 'incomplete; }
             }",
            "unknown",
        ),
        ("zero", "rest = &rest[0..];", "unknown"),
        ("variable", "rest = &rest[n..];", "unknown"),
        (
            "fallback",
            "rest = &rest[error.error_len().unwrap_or(0)..];",
            "unknown",
        ),
        (
            "wrong_split",
            "let (valid, after) = other.split_at(n);
             rest = &after[error.error_len().unwrap_or(after.len())..];",
            "unknown",
        ),
        (
            "skipped",
            "if n == 0 { continue; } rest = &rest[1..];",
            "unknown",
        ),
        (
            "shadowed",
            "let mut rest = rest; rest = &rest[1..];",
            "unknown",
        ),
        ("other", "other = &other[1..];", "violated"),
        ("plain", "continue;", "violated"),
        ("success_can_repeat", "rest = &rest[1..];", "unknown"),
    ];
    for (name, body, _) in sources {
        let mut source = decoder(body);
        if name == "success_can_repeat" {
            source = source.replace("Ok(_) => return", "Ok(_) => continue");
        }
        write(root, &format!("{name}.rs"), &source);
    }
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "-q", "6", "--all", "--json"])
        .arg(root)
        .output()
        .unwrap();
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    let findings = report["findings"].as_array().unwrap();
    for (name, _, verdict) in sources {
        let finding = findings
            .iter()
            .find(|f| f["rule"] == "retry-limit" && f["site"] == format!("{name}.rs:2"))
            .unwrap_or_else(|| panic!("no retry-limit finding for {name}"));
        assert_eq!(finding["verdict"], verdict, "{name}: {finding}");
        if verdict == "proven" {
            assert!(finding["message"].as_str().unwrap().contains("shortens"));
            let assumptions = finding["assumptions"].to_string();
            assert!(assumptions.contains("std::str::from_utf8"));
            assert_eq!(
                assumptions.contains("Utf8Error::error_len()"),
                matches!(name, "decoder" | "split" | "incomplete_exits")
            );
            assert_eq!(
                assumptions.contains("at least one byte after"),
                name == "split"
            );
        }
    }
}

#[test]
fn every_injected_defect_turns_into_a_violation() {
    let inject = Path::new(env!("CARGO_MANIFEST_DIR")).join("acceptance/inject");
    let mut failed = vec![];
    for c in CASES {
        let dir = tempfile::tempdir().unwrap();
        clean_tree(dir.path());
        let before = violations(dir.path(), c.question);
        let snippet = std::fs::read_to_string(inject.join(c.snippet)).unwrap();
        let path = dir.path().join(c.file);
        let mut text = std::fs::read_to_string(&path).unwrap_or_default();
        text.push_str(&snippet);
        write(dir.path(), c.file, &text);
        let after = violations(dir.path(), c.question);
        let new: Vec<_> = after
            .iter()
            .filter(|v| !before.contains(v) && v.1 == c.rule && v.0.starts_with(c.file))
            .collect();
        if new.is_empty() {
            failed.push(format!(
                "{} gave no new Q{} {} in {} (got {:?})",
                c.snippet, c.question, c.rule, c.file, after
            ));
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

const REQUERY_CALLER: &str = "def check(w):\n    try:\n        return w.alive()\n    except OSError:\n        w.stop()\n        return False\n";

#[test]
fn a_call_never_dispatches_to_another_language() {
    // The only `refresh` is a Rust method that reaches a query; a Python call by that name must
    // not reach it (a stale build did, and flagged 640 handler-requery chains in one repository).
    let dir = tempfile::tempdir().unwrap();
    write(
        dir.path(),
        "pkg/watch.py",
        "def check(w):\n    try:\n        return w.refresh()\n    except OSError:\n        w.refresh()\n        return False\n",
    );
    write(
        dir.path(),
        "src/lib.rs",
        "pub struct W;\nimpl W {\n    pub fn refresh(&self) -> bool {\n        self.alive()\n    }\n    pub fn alive(&self) -> bool {\n        true\n    }\n}\n",
    );
    write(
        dir.path(),
        "Cargo.toml",
        "[package]\nname = \"w\"\nversion = \"0.1.0\"\n",
    );
    assert_eq!(violations(dir.path(), 6), vec![]);
}

fn git(root: &Path, args: &[&str]) {
    let ok = Command::new("git")
        .args([
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(args)
        .current_dir(root)
        .status()
        .unwrap()
        .success();
    assert!(ok, "git {args:?}");
}

fn diff_violations(root: &Path, base: &str) -> Vec<(String, String)> {
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "--json", "-q", "6", "--diff", base])
        .arg(root)
        .output()
        .unwrap();
    let v: Value = serde_json::from_slice(&out.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stderr)));
    v["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["verdict"] == "violated")
        .map(|f| {
            (
                f["site"].as_str().unwrap().replace('\\', "/"),
                f["rule"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

#[test]
fn a_diff_keeps_only_what_the_change_brought() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    git(root, &["init", "-q"]);
    write(root, "pkg/__init__.py", "");
    write(root, "pkg/check.py", REQUERY_CALLER);
    let watch = |stop_body: &str| {
        format!(
            "class PsWatch:\n    def __init__(self, proc):\n        self.proc = proc\n\n    def alive(self):\n        return self.proc.poll() is None\n\n    def stop(self):\n{stop_body}"
        )
    };
    // The base: stop does not query, so the handler has an exit.
    write(root, "pkg/watch.py", &watch("        self.proc.kill()\n"));
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "base"]);
    // The change makes stop query: the requery in check.py is new, reached through watch.py.
    write(
        root,
        "pkg/watch.py",
        &watch("        if self.alive():\n            self.proc.kill()\n"),
    );
    git(root, &["commit", "-qam", "stop queries"]);
    let brought = diff_violations(root, "HEAD~1");
    assert!(
        brought
            .iter()
            .any(|(s, r)| s.starts_with("pkg/check.py") && r == "handler-requery"),
        "the change that adds the requery must be reported: {brought:?}"
    );
    // A later change on the same line leaves that finding as it was: not this change's.
    write(
        root,
        "pkg/watch.py",
        &watch("        if self.alive():  # unchanged behavior\n            self.proc.kill()\n"),
    );
    git(root, &["commit", "-qam", "comment"]);
    assert_eq!(diff_violations(root, "HEAD~1"), vec![]);
}

const LEAKS_LIB: &str = "pub enum LeakResult {\n    Clean,\n    Hits(Vec<String>),\n    Unavailable(String),\n}\n\npub trait Leaks {\n    fn scan(&self, code: i32) -> LeakResult;\n}\n\npub struct Gitleaks;\n\nimpl Leaks for Gitleaks {\n    fn scan(&self, code: i32) -> LeakResult {\n        match code {\n            0 => LeakResult::Clean,\n            2 => LeakResult::Hits(vec![]),\n            _ => LeakResult::Unavailable(\"gitleaks failed\".to_string()),\n        }\n    }\n}\n";

fn leaks_fake(subject: &str) -> String {
    format!(
        "use w::*;\n\npub enum Canned {{\n    Clean,\n    Hits(Vec<String>),\n    Unavailable(String),\n}}\n\npub struct FakeLeaks {{\n    pub canned: Canned,\n}}\n\nimpl Leaks for FakeLeaks {{\n    fn scan(&self, code: i32) -> LeakResult {{\n        let _ = code;\n        match {subject} {{\n            Canned::Clean => LeakResult::Clean,\n            Canned::Hits(h) => LeakResult::Hits(h.clone()),\n            Canned::Unavailable(why) => LeakResult::Unavailable(why.to_string()),\n        }}\n    }}\n}}\n"
    )
}

/// (verdict, rule) of each Q1 double finding.
fn double_verdicts(root: &Path) -> Vec<String> {
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args(["--no-cache", "scan", "--json", "--all", "-q", "1"])
        .arg(root)
        .output()
        .unwrap();
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    v["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule"] == "double-reimplements")
        .map(|f| f["verdict"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn a_canned_fake_is_no_second_source() {
    // The shape from a publishing tool's tests: a fake implementing the same trait that
    // returns what the test set, sharing only the result variants with the real scanner.
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(
        root,
        "Cargo.toml",
        "[package]\nname = \"w\"\nversion = \"0.1.0\"\n",
    );
    write(root, "src/lib.rs", LEAKS_LIB);
    write(root, "tests/common/mod.rs", &leaks_fake("&self.canned"));
    assert_eq!(double_verdicts(root), ["proven"]);
    // The same fake deciding from its input is a second copy of the rules.
    write(
        root,
        "tests/common/mod.rs",
        &leaks_fake("(code, &self.canned).1"),
    );
    assert_eq!(double_verdicts(root), ["violated"]);
}

/// Verdicts of `rule` in one file written into an otherwise empty tree.
fn rule_verdicts(file: &str, text: &str, question: u64, rule: &str) -> Vec<String> {
    rule_verdicts_tree(&[(file, text)], question, rule)
}

#[test]
fn a_sweep_answers_each_repository_alone_and_joins_them() {
    // Two copies of one service: the same handler, `crate::sso::acs`, in each.
    let rust = "fn attrs(text: &str) -> Vec<String> {\n    let mut seen: Vec<String> = Vec::new();\n    let mut it = text.split(',');\n    while let Some(name) = it.next() {\n        if !seen.iter().any(|s| s == name) {\n            seen.push(name.to_string());\n        }\n    }\n    seen\n}\npub async fn acs(body: String) -> usize {\n    attrs(&body).len()\n}\n";
    let web =
        "pub fn app() -> Router {\n    Router::new().route(\"/acs\", post(crate::sso::acs))\n}\n";
    let (a, b) = (tempfile::tempdir().unwrap(), tempfile::tempdir().unwrap());
    for dir in [&a, &b] {
        write(dir.path(), "src/sso.rs", rust);
        write(dir.path(), "src/web.rs", web);
    }
    let sweep = |extra: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
            .args(["--no-cache", "sweep", "--json", "--all", "-q", "6"])
            .args(extra)
            .arg(a.path())
            .arg(b.path())
            .output()
            .unwrap();
        let v: Value = serde_json::from_slice(&out.stdout).unwrap();
        let sites: Vec<String> = v["findings"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|f| f["rule"] == "grow-and-search" && f["verdict"] == "violated")
            .map(|f| f["site"].as_str().unwrap().to_string())
            .collect();
        (v["repos"].as_array().unwrap().len(), sites)
    };
    // Alone, each copy's handler is the one `acs` in its `sso.rs`; each site names its repository.
    let (repos, sites) = sweep(&[]);
    assert_eq!(repos, 2);
    assert_eq!(sites.len(), 2);
    for (dir, site) in [&a, &b].iter().zip(&sites) {
        let name = dir
            .path()
            .file_name()
            .unwrap()
            .to_string_lossy()
            .to_string();
        assert!(
            sites
                .iter()
                .any(|s| s.starts_with(&format!("{name}/src/sso.rs:"))),
            "{site} for {name}"
        );
    }
    // As one program a handler resolves within its own repository, so the union agrees.
    let (_, joined) = sweep(&["--one-program"]);
    assert_eq!(joined, sites);
}

fn rule_verdicts_tree(files: &[(&str, &str)], question: u64, rule: &str) -> Vec<String> {
    let dir = tempfile::tempdir().unwrap();
    for (file, text) in files {
        write(dir.path(), file, text);
    }
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args([
            "--no-cache",
            "scan",
            "--json",
            "--all",
            "-q",
            &question.to_string(),
        ])
        .arg(dir.path())
        .output()
        .unwrap();
    let v: Value = serde_json::from_slice(&out.stdout).unwrap();
    v["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule"] == rule)
        .map(|f| f["verdict"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn a_tool_error_filter_needs_a_closed_expectation() {
    let source = r#"
use std::process::Command;

fn check(expected: usize) -> Result<(), String> {
    let output = Command::new("checker").output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    let mut hidden = 0;
    let mut errors = 0;
    for line in stderr.lines() {
        if line.contains("error: missing manifest") {
            hidden += 1;
            continue;
        }
        errors += 1;
    }
    if errors > 0 { return Err("check failed".into()); }
    Ok(())
}
"#;
    let verdicts = |text| rule_verdicts("src/main.rs", text, 5, "text-filter-pass");
    assert_eq!(verdicts(source), ["violated"]);
    let regex = source
        .replace(
            "    let mut hidden",
            "    let pattern = regex::Regex::new(r\"^error: missing manifest\").unwrap();\n    let mut hidden",
        )
        .replace("line.contains(\"error: missing manifest\")", "pattern.is_match(line)");
    assert_eq!(verdicts(&regex), ["violated"]);
    let checked = source.replace(
        "    Ok(())",
        "    if hidden != expected { return Err(\"unexpected count\".into()); }\n    Ok(())",
    );
    assert_eq!(verdicts(&checked), ["proven"]);
    let checked_lines = source.replace(
        "line.contains(\"error: missing manifest\")",
        "line.contains(\"error: missing manifest\") && [\"error: missing manifest for app\"].contains(&line)",
    );
    assert_eq!(verdicts(&checked_lines), ["proven"]);
    let mutable_allowlist = checked_lines
        .replace(
            "        if line",
            "        let mut allowed = [\"error: missing manifest for app\"];\n        allowed[0] = line;\n        if line",
        )
        .replace("[\"error: missing manifest for app\"].contains", "allowed.contains");
    assert_eq!(verdicts(&mutable_allowlist), ["unknown"]);

    let opaque_count = checked
        .replace("expected: usize", "expected: impl Fn(&str) -> usize")
        .replace("hidden != expected", "hidden != expected(&stderr)");
    assert_eq!(verdicts(&opaque_count), ["unknown"]);
    let reset_count = checked.replace("    if hidden", "    hidden = 0;\n    if hidden");
    assert_eq!(verdicts(&reset_count), ["unknown"]);
    let overwritten_count =
        checked.replace("    if hidden", "    hidden.clone_from(&0);\n    if hidden");
    assert_eq!(verdicts(&overwritten_count), ["unknown"]);

    let already_counted =
        source.replace("        if line", "        errors += 1;\n        if line");
    assert!(verdicts(&already_counted).is_empty());

    let display_only = source.replace("            continue;", "");
    assert!(verdicts(&display_only).is_empty());
}

fn snippet(name: &str) -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("acceptance/inject")
            .join(name),
    )
    .unwrap()
}

#[test]
fn a_held_state_ends_on_a_refusal_or_is_violated() {
    let held = snippet("q6_held.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &held, 6, "held-state-exit"),
        ["violated"]
    );
    // The fix: a refusal that cannot pass later ends the plan.
    let ended = held.replace(
        "        if not self.ps_in_window():\n            return False",
        "        if not self.ps_in_window():\n            self.ps_plan = None\n            return False",
    );
    assert_ne!(ended, held);
    assert_eq!(
        rule_verdicts("pkg/a.py", &ended, 6, "held-state-exit"),
        ["proven"]
    );
}

#[test]
fn a_recovery_that_reads_the_holder_is_proven() {
    let held = snippet("q6_held.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &held, 6, "held-run-recovery"),
        ["violated"]
    );
    let reads = held.replace(
        "    def ps_recover(self):\n",
        "    def ps_recover(self):\n        if self.ps_plan is not None:\n            return\n",
    );
    assert_ne!(reads, held);
    assert_eq!(
        rule_verdicts("pkg/a.py", &reads, 6, "held-run-recovery"),
        ["proven"]
    );
}

#[test]
fn a_write_back_after_a_fresh_read_is_proven() {
    let stale = snippet("q3_stale_write.py");
    assert!(
        rule_verdicts("pkg/a.py", &stale, 3, "stale-write-back").contains(&"violated".to_string())
    );
    let fresh = stale.replace(
        "    raw = ps_read_state()\n    ps_commit()\n",
        "    ps_commit()\n    raw = ps_read_state()\n",
    );
    assert_ne!(fresh, stale);
    let v = rule_verdicts("pkg/a.py", &fresh, 3, "stale-write-back");
    assert!(!v.is_empty() && v.iter().all(|x| x == "proven"), "{v:?}");
}

#[test]
fn an_allow_list_guard_is_proven() {
    let open = snippet("q5_name_table.py");
    assert_eq!(
        rule_verdicts("pkg/tests/test_g.py", &open, 5, "name-table-guard"),
        ["violated"]
    );
    let closed = open.replace(
        "        if node.func.value.id not in PS_RECEIVERS:\n            continue\n        bad.append(node.lineno)",
        "        if node.func.value.id not in PS_RECEIVERS:\n            bad.append(node.lineno)",
    );
    assert_ne!(closed, open);
    assert_eq!(
        rule_verdicts("pkg/tests/test_g.py", &closed, 5, "name-table-guard"),
        ["proven"]
    );
}

#[test]
fn a_reading_taken_after_the_clock_check_is_proven() {
    let early = snippet("q3_read_before_check.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &early, 3, "read-before-check"),
        ["violated"]
    );
    let late = early.replace(
        "    now = datetime.datetime.now(datetime.UTC)\n    if ps_clock_unsynced():\n        return\n",
        "    if ps_clock_unsynced():\n        return\n    now = datetime.datetime.now(datetime.UTC)\n",
    );
    assert_ne!(late, early);
    assert_eq!(
        rule_verdicts("pkg/a.py", &late, 3, "read-before-check"),
        ["proven"]
    );
}

#[test]
fn a_store_read_after_the_clock_check_draws_no_write_before_it() {
    let early = snippet("q4_write_before_guard.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &early, 4, "write-before-guard"),
        ["violated"]
    );
    let late = early.replace(
        "    state = ps_load_state()\n    if ps_clock_unsynced():\n        return []\n",
        "    if ps_clock_unsynced():\n        return []\n    state = ps_load_state()\n",
    );
    assert_ne!(late, early);
    assert!(rule_verdicts("pkg/a.py", &late, 4, "write-before-guard").is_empty());
}

#[test]
fn a_name_table_is_judged_by_what_it_names() {
    let guard = |table: &str| {
        format!(
            "import ast\nfrom pathlib import Path\n\nWRITERS = {table}\n\n\ndef test_writers():\n    tree = ast.parse(Path(__file__).read_text())\n    bad = []\n    for node in ast.walk(tree):\n        if not isinstance(node, ast.FunctionDef):\n            continue\n        if node.name not in WRITERS:\n            continue\n        bad.append(node.name)\n    assert not bad\n"
        )
    };
    let code = "def save(doc):\n    return doc\n\n\ndef write(doc):\n    return doc\n";
    // Names this repository defines: a new writer outside the table passes unchecked.
    let own = guard(r#"{"save", "write"}"#);
    assert_eq!(
        rule_verdicts_tree(
            &[("pkg/store.py", code), ("pkg/tests/test_w.py", &own)],
            5,
            "name-table-guard"
        ),
        ["violated"]
    );
    // Outside names matched by a field an alias cannot change: a closed domain.
    let outside = guard(r#"{"pwd", "grp", "fcntl"}"#);
    assert_eq!(
        rule_verdicts_tree(
            &[("pkg/store.py", code), ("pkg/tests/test_w.py", &outside)],
            5,
            "name-table-guard"
        ),
        ["proven"]
    );
    // No production code in the scan: whose names they are is not known.
    assert_eq!(
        rule_verdicts("pkg/tests/test_w.py", &own, 5, "name-table-guard"),
        ["unknown"]
    );
    // A test on a value is no name guard.
    let value = "import ast\n\n\ndef test_status(r):\n    ast.parse('x')\n    bad = []\n    if r.status_code in (200, 201):\n        bad.append(r)\n    assert not bad\n";
    assert!(
        rule_verdicts_tree(
            &[("pkg/store.py", code), ("pkg/tests/test_v.py", value)],
            5,
            "name-table-guard"
        )
        .is_empty()
    );
}

#[test]
fn a_status_cleared_before_the_refusal_is_proven() {
    let stale = snippet("q6_stale_status.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &stale, 6, "stale-status"),
        ["violated"]
    );
    // The fix: each attempt starts clear, so a refusal names only its own reason.
    let fresh = stale.replace(
        "    def ps_attempt(self) -> bool:\n",
        "    def ps_attempt(self) -> bool:\n        self.ps_reason = None\n",
    );
    assert_ne!(fresh, stale);
    assert_eq!(
        rule_verdicts("pkg/a.py", &fresh, 6, "stale-status"),
        ["proven"]
    );
}

#[test]
fn a_window_from_the_previous_run_is_no_fixed_day() {
    let fixed = snippet("q6_fixed_day.py");
    assert_eq!(
        rule_verdicts("pkg/a.py", &fixed, 6, "fixed-day-span"),
        ["violated"]
    );
    let since = fixed.replace(
        "def ps_mine():\n    now = ps_dt.datetime.now(PS_ZONE)\n    return ps_fetch(now - ps_dt.timedelta(days=1), now)",
        "def ps_mine(since):\n    now = ps_dt.datetime.now(PS_ZONE)\n    return ps_fetch(since, now)",
    );
    assert_ne!(since, fixed);
    assert!(rule_verdicts("pkg/a.py", &since, 6, "fixed-day-span").is_empty());
    // A repository that keeps no zone: a day is 24 hours of its clock.
    let naive = fixed
        .replace("from zoneinfo import ZoneInfo\n", "")
        .replace("PS_ZONE = ZoneInfo(\"America/Chicago\")", "PS_ZONE = None");
    assert!(rule_verdicts("pkg/a.py", &naive, 6, "fixed-day-span").is_empty());
}

#[test]
fn a_piped_runner_needs_pipefail_or_pipestatus() {
    let flow = |shell: &str| {
        format!(
            "on: push\njobs:\n  test:\n    runs-on: ubuntu-latest\n    steps:\n      - name: tests\n{shell}        run: |\n          python -m pytest -q tests | tail -n 5\n"
        )
    };
    let q = |files: &[(&str, &str)]| rule_verdicts_tree(files, 7, "pipe-masks-exit");
    assert_eq!(q(&[(".gitea/workflows/ci.yml", &flow(""))]), ["violated"]);
    // An explicit `shell: bash` runs with -o pipefail.
    assert_eq!(
        q(&[(".gitea/workflows/ci.yml", &flow("        shell: bash\n"))]),
        ["proven"]
    );
    let make = "test:\n\tpytest -q | tee test.log\n";
    assert_eq!(q(&[("Makefile", make)]), ["violated"]);
    let strict = format!("SHELL := bash\n.SHELLFLAGS := -ec -o pipefail\n{make}");
    assert_eq!(q(&[("Makefile", &strict)]), ["proven"]);
    assert_eq!(
        q(&[(
            "scripts/check.sh",
            "#!/bin/bash\nset -o pipefail\ncargo test | tail -n 20\n"
        )]),
        ["proven"]
    );
    assert_eq!(
        q(&[(
            "scripts/check.sh",
            "#!/bin/bash\ncargo test | tail -n 20\nexit \"${PIPESTATUS[0]}\"\n"
        )]),
        ["proven"]
    );
    // A pipe from something that is not a runner is not judged.
    assert!(
        q(&[(
            "scripts/v.sh",
            "#!/bin/bash\nrustc --version | grep -q 1.\n"
        )])
        .is_empty()
    );
}

#[test]
fn a_crate_patched_to_a_path_hides_from_the_advisory_check() {
    let q = |files: &[(&str, &str)]| rule_verdicts_tree(files, 7, "path-patch-advisories");
    let manifest = "[package]\nname = \"x\"\n\n[patch.crates-io]\npicky = { path = \"patches/picky\" }\nrsa = \"0.10\"\n\n[patch.crates-io.sspi]\npath = \"patches/sspi\"\n";
    let deny = "#!/bin/bash\nset -e\ncargo deny --locked check\n";
    assert_eq!(
        q(&[("Cargo.toml", manifest), ("scripts/deny.sh", deny)]),
        ["violated", "violated"]
    );
    // No advisory check, or one that skips advisories: nothing is hidden from it.
    assert!(q(&[("Cargo.toml", manifest)]).is_empty());
    assert!(
        q(&[
            ("Cargo.toml", manifest),
            (
                "scripts/deny.sh",
                "#!/bin/bash\ncargo deny check licenses bans\n"
            )
        ])
        .is_empty()
    );
    // A `path` dependency outside `[patch]` is the workspace's own crate.
    assert!(
        q(&[
            ("Cargo.toml", "[dependencies]\ncore = { path = \"core\" }\n"),
            ("scripts/deny.sh", deny)
        ])
        .is_empty()
    );
    // A pwsh step running a downloaded cargo-deny is an advisory check; downloading it is not.
    let pwsh = "on: push\njobs:\n  a:\n    runs-on: windows\n    steps:\n      - shell: pwsh\n        run: |\n          Invoke-WebRequest -Uri \"https://example.com/cargo-deny-0.18.tar.gz\" -OutFile $t\n          & (Join-Path $env:RUNNER_TEMP \"$d\\cargo-deny.exe\") deny check advisories bans sources\n";
    assert_eq!(
        q(&[("Cargo.toml", manifest), (".gitea/workflows/ci.yml", pwsh)]),
        ["violated", "violated"]
    );
    let fetch_only = "on: push\njobs:\n  a:\n    runs-on: windows\n    steps:\n      - shell: pwsh\n        run: |\n          Invoke-WebRequest -Uri \"https://example.com/cargo-deny-0.18.tar.gz\" -OutFile $t\n";
    assert!(
        q(&[
            ("Cargo.toml", manifest),
            (".gitea/workflows/ci.yml", fetch_only)
        ])
        .is_empty()
    );
    // A git dependency is not checked either; a git dev-dependency does not ship.
    let git = "[dependencies]\nironrdp-pdu = { git = \"https://example.com/ironrdp\", rev = \"abc\" }\n\n[dev-dependencies]\nmock = { git = \"https://example.com/mock\" }\n";
    assert_eq!(
        q(&[("Cargo.toml", git), ("scripts/deny.sh", deny)]),
        ["violated"]
    );
    // A tool that hands cargo deny a rewritten graph, run by a step, checks the patched copies.
    let tool = "use std::process::Command;\nfn main() {\n    let mut cmd = Command::new(\"cargo-deny\");\n    cmd.arg(\"deny\").arg(\"--metadata-path\").arg(\"graph.json\");\n    cmd.args([\"check\", \"advisories\"]);\n    cmd.status().unwrap();\n}\n";
    let run = "#!/bin/bash\nset -e\ncargo deny --locked check\ncargo run --locked -q -p deny-patched -- --config deny.toml\n";
    assert_eq!(
        q(&[
            ("Cargo.toml", manifest),
            ("tools/deny-patched/src/main.rs", tool),
            ("scripts/deny.sh", run)
        ]),
        ["proven", "proven"]
    );
    // The tool alone, never run, checks nothing.
    assert_eq!(
        q(&[
            ("Cargo.toml", manifest),
            ("tools/deny-patched/src/main.rs", tool),
            ("scripts/deny.sh", deny)
        ]),
        ["violated", "violated"]
    );
    // A diff applied to another project's manifest: the added entry and the git one in context are
    // seen, the removed one is not.
    let diff = "diff --git a/Cargo.toml b/Cargo.toml\n--- a/Cargo.toml\n+++ b/Cargo.toml\n@@ -10,3 +10,4 @@\n [patch.crates-io]\n+picky = { path = \"patches/picky\" }\n-old = { path = \"patches/old\" }\n diplomat = { git = \"https://example.com/d\" }\n";
    let audit =
        "on: push\njobs:\n  a:\n    runs-on: ubuntu-latest\n    steps:\n      - run: cargo audit\n";
    assert_eq!(
        q(&[
            ("patches/up.patch", diff),
            (".gitea/workflows/audit.yml", audit)
        ]),
        ["violated", "violated"]
    );
}

#[test]
fn a_list_searched_and_grown_in_one_loop_needs_a_bound() {
    let entry = (
        "proofscan.toml",
        "[q6]\nuntrusted_function = ':(attrs|uniq)$'\n",
    );
    let q = |file: (&str, &str)| rule_verdicts_tree(&[entry, file], 6, "grow-and-search");
    let rust = "fn attrs(text: &str) -> Vec<String> {\n    let mut seen: Vec<String> = Vec::new();\n    let mut it = text.split(',');\n    while let Some(name) = it.next() {\n        if !seen.iter().any(|s| s == name) {\n            seen.push(name.to_string());\n        }\n    }\n    seen\n}\n";
    assert_eq!(q(("src/lib.rs", rust)), ["violated"]);
    let bounded = rust.replace(
        "    while let Some(name) = it.next() {\n",
        "    while let Some(name) = it.next() {\n        if seen.len() >= 256 {\n            break;\n        }\n",
    );
    assert_eq!(q(("src/lib.rs", &bounded)), ["proven"]);
    // A loop over a parameter: the bound may be at the callers, which is not followed.
    let walked = "fn attrs(input: &[(String, String)]) -> Vec<String> {\n    let mut seen = Vec::new();\n    for (name, _) in input {\n        if !seen.iter().any(|s: &String| s == name) {\n            seen.push(name.clone());\n        }\n    }\n    seen\n}\n";
    assert_eq!(q(("src/lib.rs", walked)), ["unknown"]);
    // A searched list the caller passes in is bounded, if at all, by the caller.
    let passed = "fn attrs(seen: &mut Vec<String>, text: &str) {\n    let mut it = text.split(',');\n    while let Some(name) = it.next() {\n        if !seen.iter().any(|s| s == name) {\n            seen.push(name.to_string());\n        }\n    }\n}\n";
    assert_eq!(q(("src/lib.rs", passed)), ["unknown"]);
    // A list that only gains distinct values of a literal array is never longer than the array.
    let literal = "fn attrs(text: &str) -> Result<(), ()> {\n    let mut seen: Vec<&str> = Vec::new();\n    for c in text.split(',') {\n        let Some(name) = [\"A\", \"B\", \"C\"]\n            .into_iter()\n            .find(|n| *n == c && !seen.contains(n))\n        else {\n            return Err(());\n        };\n        seen.push(name);\n    }\n    Ok(())\n}\n";
    assert_eq!(q(("src/lib.rs", literal)), ["proven"]);
    // A list made inside the loop starts empty on each step: nothing grows across steps.
    let fresh = "fn attrs(text: &str) -> usize {\n    let mut n = 0;\n    let mut it = text.split(',');\n    while let Some(name) = it.next() {\n        let mut seen: Vec<&str> = Vec::new();\n        seen.push(name);\n        if seen.iter().any(|s| s.is_empty()) {\n            n += 1;\n        }\n    }\n    n\n}\n";
    assert!(q(("src/lib.rs", fresh)).is_empty());
    let py = "def uniq(items):\n    out = []\n    for x in items:\n        if x not in out:\n            out.append(x)\n    return out\n";
    assert_eq!(q(("app/u.py", py)), ["unknown"]);
    let py_local = "def uniq(path):\n    out = []\n    for x in open(path).read().split():\n        if x not in out:\n            out.append(x)\n    return out\n";
    assert_eq!(q(("app/u.py", py_local)), ["violated"]);
    // A set is not searched from its start; test code is not judged.
    let set = py_local
        .replace("out = []", "out = set()")
        .replace("out.append", "out.add");
    assert!(q(("app/u.py", &set)).is_empty());
    assert!(q(("tests/test_u.py", py_local)).is_empty());
    // Code that no untrusted entry reaches is not asked about.
    assert!(rule_verdicts_tree(&[("src/lib.rs", rust)], 6, "grow-and-search").is_empty());
    // An axum handler is an entry, and what it calls is reached.
    let routed = format!(
        "{rust}\nasync fn acs(body: String) -> usize {{\n    attrs(&body).len()\n}}\n\npub fn app() -> Router {{\n    Router::new().route(\"/acs\", post(acs))\n}}\n"
    );
    assert_eq!(
        rule_verdicts_tree(&[("src/lib.rs", &routed)], 6, "grow-and-search"),
        ["violated"]
    );
    // A handler named by path, `post(crate::sso::acs)`, resolves in that module's file, even
    // with a second function of the same name elsewhere.
    let handler =
        format!("{rust}\npub async fn acs(body: String) -> usize {{\n    attrs(&body).len()\n}}\n");
    let web =
        "pub fn app() -> Router {\n    Router::new().route(\"/acs\", post(crate::sso::acs))\n}\n";
    let other = "pub fn acs() -> u8 {\n    0\n}\n";
    let tree = [
        ("src/sso.rs", handler.as_str()),
        ("src/web.rs", web),
        ("src/other.rs", other),
    ];
    assert_eq!(
        rule_verdicts_tree(&tree, 6, "grow-and-search"),
        ["violated"]
    );
    // `super::sso::acs` names the same module relative to the registering one.
    let relative = web.replace("crate::sso::acs", "super::sso::acs");
    let tree = [
        ("src/sso.rs", handler.as_str()),
        ("src/web.rs", relative.as_str()),
        ("src/other.rs", other),
    ];
    assert_eq!(
        rule_verdicts_tree(&tree, 6, "grow-and-search"),
        ["violated"]
    );
    let elsewhere = web.replace("crate::sso::acs", "crate::other::acs");
    let tree = [
        ("src/sso.rs", handler.as_str()),
        ("src/web.rs", elsewhere.as_str()),
        ("src/other.rs", other),
    ];
    assert!(rule_verdicts_tree(&tree, 6, "grow-and-search").is_empty());
}

#[test]
fn a_request_size_guard_must_run_before_the_permit_wait() {
    let q = |src: &str| rule_verdicts_tree(&[("src/lib.rs", src)], 4, "guard-after-wait");
    let source = |handler: &str| {
        format!(
            r#"
use axum::{{Router, extract::State}};
use axum::routing::post;
use std::sync::Arc;
use tokio::sync::Semaphore;

fn routes() -> Router {{
    Router::new().route("/upload", post(upload)).with_state(Arc::new(Semaphore::new(1)))
}}

async fn other() {{}}

async fn upload(State(permits): State<Arc<Semaphore>>, body: String) -> Result<(), ()> {{
    {handler}
    Ok(())
}}
"#
        )
    };
    let wait = "let _permit = permits.acquire().await.unwrap();";
    let guard = "if body.len() > 1024 { return Err(()); }";
    assert_eq!(q(&source(&format!("{wait}\n{guard}"))), ["violated"]);
    assert_eq!(q(&source(&format!("{guard}\n{wait}"))), ["proven"]);
    let branch = format!("if enabled() {{ {guard} }}");
    assert_eq!(
        q(&source(&format!("{branch}\n{wait}\n{guard}"))),
        ["unknown"]
    );
    assert_eq!(
        q(&source(&format!("validate(&body)?;\n{wait}\n{guard}"))),
        ["unknown"]
    );
    assert!(
        q(&source(&format!(
            "let _pending = permits.acquire();\n{guard}"
        )))
        .is_empty()
    );
    let trusted = source(&format!("{wait}\n{guard}")).replace("post(upload)", "post(other)");
    assert!(q(&trusted).is_empty());
}

#[test]
fn request_cpu_work_needs_a_permit_held_until_it_finishes() {
    let q = |src: &str| rule_verdicts_tree(&[("src/lib.rs", src)], 6, "blocking-unbounded");
    let route = r#"
static LIMIT: tokio::sync::Semaphore = tokio::sync::Semaphore::const_new(2);
fn routes() {
    Router::new().route("/login", post(login));
}
async fn login(secret: String) {
    tokio::task::spawn_blocking(move || {
        argon2::Argon2::default().hash_password(secret.as_bytes(), &salt);
    }).await.unwrap();
}
"#;
    assert_eq!(q(route), ["violated"]);
    let bounded = route.replace(
        "    tokio::task::spawn_blocking(move || {",
        "    let permit = Arc::clone(&state.limit).acquire_owned().await.unwrap();\n    tokio::task::spawn_blocking(move || {\n        let _held = permit;",
    ).replace(
        "async fn login(secret: String)",
        "struct App { limit: Arc<tokio::sync::Semaphore> }\nasync fn login(secret: String, state: &App)",
    );
    assert_eq!(q(&bounded), ["proven"]);
    assert_eq!(
        q(&bounded.replace("let _held = permit;", "drop(permit);")),
        ["unknown"]
    );
    let inline = route
        .replace(
            "tokio::task::spawn_blocking(move || {",
            "let _held = tokio::sync::Semaphore::acquire(&LIMIT).await.unwrap();",
        )
        .replace("}).await.unwrap();", "");
    assert_eq!(q(&inline), ["proven"]);
    assert_eq!(q(&inline.replace("let _held =", "let _ =")), ["unknown"]);
    assert!(q(&route.replace("post(login)", "post(other)")).is_empty());
    assert!(
        q(&route.replace(
            "argon2::Argon2::default().hash_password(secret.as_bytes(), &salt)",
            "secret.len()",
        ))
        .is_empty()
    );
}

#[test]
fn repeated_request_bytes_need_one_budget_charged_before_each_write() {
    let config = (
        "proofscan.toml",
        "[q6]\nemitted_bytes = true\nuntrusted_function = '^src/lib.rs:verify$'\n",
    );
    let q = |src: &str| rule_verdicts_tree(&[config, ("src/lib.rs", src)], 6, "emitted-bytes");
    let unbudgeted = r#"
fn verify(value: &[::std::primitive::u8], references: &[::std::primitive::u8], signed_info: &[::std::primitive::u8]) -> Result<Vec<u8>, ()> {
    let mut output = ::std::vec::Vec::new();
    for _ in references {
        output.extend_from_slice(value);
    }
    for _ in signed_info {
        output.extend_from_slice(value);
    }
    ::std::result::Result::Ok(output)
}
"#;
    assert_eq!(q(unbudgeted), ["violated"]);
    assert!(rule_verdicts("src/lib.rs", unbudgeted, 6, "emitted-bytes").is_empty());

    let reserved = unbudgeted.replace(
        "let mut output = ::std::vec::Vec::new();",
        "let mut output = ::std::vec::Vec::new();\n    let mut remaining = 16384;",
    );
    let charge = "if value.len() > remaining { return ::std::result::Result::Err(()); }\n        remaining -= value.len();";
    let write = "output.extend_from_slice(value);";
    let bounded = reserved.replace(write, &format!("{charge}\n        {write}"));
    assert_eq!(q(&bounded), ["proven"]);
    let late = reserved.replace(write, &format!("{write}\n        {charge}"));
    assert_eq!(q(&late), ["unknown"]);
    let reset = bounded.replace(
        "for _ in signed_info {",
        "remaining = 16384;\n    for _ in signed_info {",
    );
    assert_eq!(q(&reset), ["unknown"]);
    let bypass = bounded.replacen(&format!("{charge}\n        {write}"), write, 1);
    assert_eq!(q(&bypass), ["unknown"]);
    let opaque = unbudgeted
        .replace(
            "signed_info: &[::std::primitive::u8]",
            "signed_info: &[::std::primitive::u8], writer: &mut impl std::io::Write",
        )
        .replace(write, "writer.write_all(value).map_err(|_| ())?;");
    assert_eq!(q(&opaque), ["unknown"]);
    assert!(q(&unbudgeted.replace(write, "output.push(0);")).is_empty());
    assert!(
        q(&unbudgeted
            .replace(write, "output.extend_from_slice(references);")
            .replace("for _ in signed_info", "for _ in references"))
        .is_empty()
    );
}

#[test]
fn prefix_work_needs_a_rejecting_bound_on_the_consumed_list() {
    let config = (
        "proofscan.toml",
        "[q6]\nprefix_work = true\nuntrusted_function = '^src/lib.rs:render$'\n",
    );
    let q = |src: &str| rule_verdicts_tree(&[config, ("src/lib.rs", src)], 6, "prefix-work");
    let source = r#"
fn cap(prefixes: &[::std::primitive::u8]) -> ::std::result::Result<(), ()> {
    if prefixes.len() > 8 { return ::std::result::Result::Err(()); }
    ::std::result::Result::Ok(())
}
fn render(elements: &[::std::primitive::u8], prefixes: &[::std::primitive::u8], other: &[::std::primitive::u8]) -> ::std::result::Result<(), ()> {
    for _ in elements {
        for &prefix in prefixes {
            ::std::hint::black_box(prefix);
        }
    }
    ::std::result::Result::Ok(())
}
"#;
    assert_eq!(q(source), ["violated"]);
    assert!(rule_verdicts("src/lib.rs", source, 6, "prefix-work").is_empty());
    let before = |guard: &str| {
        source.replace(
            "    for _ in elements",
            &format!("    {guard}\n    for _ in elements"),
        )
    };
    assert_eq!(q(&before("cap(prefixes)?;")), ["proven"]);
    assert_eq!(
        q(&before(
            "if prefixes.len() > 8 { return ::std::result::Result::Err(()); }"
        )),
        ["proven"]
    );
    let (render, tail) = source
        .rsplit_once("    ::std::result::Result::Ok(())")
        .unwrap();
    let late = format!("{render}    cap(prefixes)?;\n    ::std::result::Result::Ok(()){tail}");
    let budget = before("let mut left = 128usize;");
    let work = "::std::hint::black_box(prefix);";
    let refuse = "if left == 0 { return ::std::result::Result::Err(()); }";
    let charged = budget.replace(work, &format!("{refuse} left -= 1; {work}"));
    assert_eq!(q(&charged), ["proven"]);
    let output_only = budget.replace(
        work,
        &format!("{refuse} {work} if prefix == 0 {{ left -= 1; }}"),
    );
    for control in [
        before("if prefixes.len() > 8 { eprintln!(\"too many prefixes\"); }"),
        before("let _ = cap(prefixes);"),
        before("cap(other)?;"),
        before("if other.len() == 0 { cap(prefixes)?; }"),
        output_only,
        late,
    ] {
        assert_eq!(q(&control), ["unknown"], "{control}");
    }
    let partitioned = source
        .replace(
            "elements: &[::std::primitive::u8]",
            "elements: &[&[::std::primitive::u8]]",
        )
        .replace("for _ in elements", "for group in elements")
        .replace("for &prefix in prefixes", "for &prefix in *group");
    assert!(q(&partitioned).is_empty());
    assert!(q(&source.replace("for &prefix in prefixes", "for &prefix in &[0] ")).is_empty());
}

#[test]
fn a_handle_released_by_hand_leaks_on_a_panic_between() {
    let q = |src: &str| rule_verdicts_tree(&[("src/lib.rs", src)], 9, "release-on-panic");
    let head = "mod ffi {\n    pub unsafe fn duckdb_appender_destroy(_: *mut *mut u8) -> i32 { 0 }\n    pub unsafe fn duckdb_appender_clear(_: *mut u8) {}\n}\nfn create_appender() -> Result<*mut u8, ()> {\n    Ok(std::ptr::null_mut())\n}\nfn column_types(_: *mut u8) -> Vec<u32> {\n    vec![1]\n}\n";
    let by_hand = format!(
        "{head}fn open() -> Result<Vec<u32>, ()> {{\n    let mut raw = create_appender()?;\n    let columns = column_types(raw);\n    unsafe {{ ffi::duckdb_appender_destroy(&mut raw) }};\n    Ok(columns)\n}}\n"
    );
    assert_eq!(q(&by_hand), ["violated"]);
    // Only calls into C, constructors and pointer reads between: nothing there unwinds.
    let quiet = format!(
        "{head}fn drop_it() -> Result<(), ()> {{\n    let mut raw = create_appender()?;\n    if !raw.is_null() {{\n        unsafe {{ ffi::duckdb_appender_clear(raw) }};\n    }}\n    unsafe {{ ffi::duckdb_appender_destroy(&mut raw) }};\n    Ok(())\n}}\n"
    );
    assert_eq!(q(&quiet), ["proven"]);
    // A guard whose Drop releases the handle covers every exit; nothing is released by hand.
    let guard = format!(
        "{head}struct Guard(*mut u8);\nimpl Drop for Guard {{\n    fn drop(&mut self) {{\n        unsafe {{ ffi::duckdb_appender_destroy(&mut self.0) }};\n    }}\n}}\nfn open() -> Result<Vec<u32>, ()> {{\n    let guard = Guard(create_appender()?);\n    Ok(column_types(guard.0))\n}}\n"
    );
    assert!(q(&guard).is_empty());
}

fn diff_verdicts(root: &Path, base: &str, question: &str, rule: &str) -> Vec<(String, String)> {
    let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
        .args([
            "--no-cache",
            "scan",
            "--json",
            "-q",
            question,
            "--diff",
            base,
        ])
        .arg(root)
        .output()
        .unwrap();
    let v: Value = serde_json::from_slice(&out.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stderr)));
    v["findings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|f| f["rule"] == rule)
        .map(|f| {
            (
                f["site"].as_str().unwrap().replace('\\', "/"),
                f["verdict"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

#[test]
fn a_new_stored_key_needs_a_test_of_the_previous_shape() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    git(root, &["init", "-q"]);
    let store = |reads: &str| {
        format!(
            "import json\nimport os\n\nSTATE = \"state.json\"\n\n\ndef load(root):\n    with open(os.path.join(root, STATE)) as fh:\n        return json.load(fh)\n\n\ndef save(root, doc):\n    with open(os.path.join(root, STATE), \"w\") as fh:\n        json.dump(doc, fh)\n\n\ndef tick(root):\n    doc = load(root)\n    return {reads}\n"
        )
    };
    let test = |docs: &[&str]| {
        let mut t = String::from("from pkg import store\n");
        for (i, d) in docs.iter().enumerate() {
            t.push_str(&format!(
                "\n\ndef test_tick_{i}(tmp_path):\n    store.save(tmp_path, {d})\n    assert store.tick(tmp_path)\n"
            ));
        }
        t
    };
    write(root, "pkg/__init__.py", "");
    write(root, "pkg/store.py", &store("doc[\"last\"]"));
    write(root, "tests/test_store.py", &test(&["{\"last\": 1}"]));
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "base"]);
    // The change reads a new key and rewrites the one test to the new shape.
    write(
        root,
        "pkg/store.py",
        &store("doc[\"last\"], doc[\"slots\"]"),
    );
    write(
        root,
        "tests/test_store.py",
        &test(&["{\"last\": 1, \"slots\": {}}"]),
    );
    let got = diff_verdicts(root, "HEAD", "2", "upgrade-shape");
    assert_eq!(
        got,
        [("pkg/store.py:19".to_string(), "violated".to_string())],
        "{got:?}"
    );
    // A test that still loads the previous release's shape proves it.
    write(
        root,
        "tests/test_store.py",
        &test(&["{\"last\": 1, \"slots\": {}}", "{\"last\": 1}"]),
    );
    let got = diff_verdicts(root, "HEAD", "2", "upgrade-shape");
    assert_eq!(
        got,
        [("pkg/store.py:19".to_string(), "proven".to_string())],
        "{got:?}"
    );
}

#[test]
fn each_operand_of_a_changed_condition_is_a_mutant() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    git(root, &["init", "-q"]);
    write(root, "pkg/m.py", "def ok(a, b, c):\n    return a\n");
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "base"]);
    write(
        root,
        "pkg/m.py",
        "def ok(a, b, c):\n    if a or b and c:\n        return True\n    return False\n",
    );
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "change"]);
    let list = |at: &[&str]| {
        let mut args = vec!["mutate", "--list", "--diff", "HEAD^"];
        for a in at {
            args.extend(["--at", a]);
        }
        let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
            .args(&args)
            .arg(root)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).replace('\\', "/")
    };
    let all = list(&[]);
    for want in [
        "pkg/m.py:2 `a` is dropped from its `or`",
        "pkg/m.py:2 `b and c` is dropped from its `or`",
        "pkg/m.py:2 `b` is dropped from its `and`",
        "pkg/m.py:2 `c` is dropped from its `and`",
        "pkg/m.py:2 `a or b and c` always holds",
    ] {
        assert!(all.contains(want), "missing {want}:\n{all}");
    }
    // --at keeps only the named lines.
    assert!(
        list(&["pkg/m.py:3"])
            .lines()
            .all(|l| l.starts_with("pkg/m.py:3 "))
    );
    assert!(list(&["pkg/m.py:9"]).trim().is_empty());
}

#[test]
fn the_gate_scans_only_an_opted_in_change() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    git(root, &["init", "-q"]);
    write(root, "pkg/__init__.py", "");
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "base"]);
    write(root, "pkg/a.py", &snippet("q6_fixed_day.py"));
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "change"]);
    let gate = |args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
            .args(["--no-cache", "gate"])
            .arg(root)
            .args(args)
            .output()
            .unwrap();
        (
            out.status.code(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
        )
    };
    // Not opted in: it passes and says so, even with a violation in the change.
    let (code, text) = gate(&["--base", "HEAD^"]);
    assert_eq!(code, Some(0));
    assert!(text.contains("not opted in"), "{text}");
    // Opted in: the change's violation fails it.
    write(root, "proofscan.toml", "");
    let (code, text) = gate(&["--base", "HEAD^"]);
    assert_eq!(code, Some(1), "{text}");
    // No upstream and no base: an error, not a pass.
    let (code, _) = gate(&[]);
    assert_eq!(code, Some(3));
}

/// A kill made only by a property test that draws new examples each run is not counted: the
/// test is set aside and the rest decide.
#[cfg(unix)]
#[test]
fn a_kill_by_a_random_draw_alone_is_no_kill() {
    let run = |decorator: &str| {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        git(root, &["init", "-q"]);
        write(root, "pkg/m.py", "def ok(a):\n    return a\n");
        write(
            root,
            "tests/test_m.py",
            &format!("{decorator}\n@given(st.integers())\ndef test_prop(x):\n    pass\n"),
        );
        // A stand-in for pytest: the property test fails on any mutant unless deselected.
        write(
            root,
            "fake-pytest.sh",
            "if grep -q '^    if a:$' pkg/m.py; then exit 0; fi\ncase \"$*\" in *--deselect*) exit 0;; esac\necho 'FAILED tests/test_m.py::test_prop - AssertionError'\nexit 1\n",
        );
        git(root, &["add", "-A"]);
        git(root, &["commit", "-qm", "base"]);
        write(
            root,
            "pkg/m.py",
            "def ok(a):\n    if a:\n        return a\n    return a\n",
        );
        git(root, &["add", "-A"]);
        git(root, &["commit", "-qm", "change"]);
        let out = Command::new(env!("CARGO_BIN_EXE_proofscan"))
            .args([
                "mutate",
                "--diff",
                "HEAD^",
                "--json",
                "--test",
                "sh fake-pytest.sh",
            ])
            .arg(root)
            .output()
            .unwrap();
        let v: Value = serde_json::from_slice(&out.stdout)
            .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stderr)));
        v["findings"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|f| f["site"] == "pkg/m.py:2")
            .map(|f| {
                (
                    f["verdict"].as_str().unwrap().to_string(),
                    f["message"].as_str().unwrap().to_string(),
                )
            })
            .collect::<Vec<_>>()
    };
    let random = run("@settings(derandomize=False)");
    assert!(!random.is_empty());
    for (verdict, message) in &random {
        assert_eq!(verdict, "violated", "{message}");
        assert!(
            message.contains("only tests/test_m.py::test_prop fails"),
            "{message}"
        );
    }
    let fixed = run("@settings(derandomize=True)");
    assert!(
        !fixed.is_empty() && fixed.iter().all(|(v, _)| v == "proven"),
        "{fixed:?}"
    );
}

#[test]
fn a_property_that_draws_anew_each_run_is_violated() {
    let drawn = snippet("q7_random_property.py");
    assert_eq!(
        rule_verdicts("pkg/tests/test_p.py", &drawn, 7, "random-property"),
        ["violated"]
    );
    let fixed = drawn.replace("derandomize=False", "derandomize=True");
    assert_ne!(fixed, drawn);
    assert_eq!(
        rule_verdicts("pkg/tests/test_p.py", &fixed, 7, "random-property"),
        ["proven"]
    );
    // No setting: CI derandomizes by default, and nothing is reported.
    let plain = drawn.replace("@settings(max_examples=50, derandomize=False)\n", "");
    assert!(rule_verdicts("pkg/tests/test_p.py", &plain, 7, "random-property").is_empty());
}

#[test]
fn request_text_needs_a_bound_before_a_store_write() {
    let q = |src: &str| rule_verdicts_tree(&[("src/lib.rs", src)], 6, "untrusted-store-size");
    let raw = r#"
async fn submit(body: String) {
    save(body).await;
}
async fn save(detail: String) {
    app.store.audit("submit", &format!("request: {detail}"));
}
fn app() -> Router {
    Router::new().route("/submit", post(submit))
}
"#;
    assert_eq!(q(raw), ["violated"]);
    let cutoff = raw.replace(
        "    app.store.audit",
        "    let detail: String = detail.chars().take(64).collect();\n    app.store.audit",
    );
    assert_eq!(q(&cutoff), ["proven"]);
    let capped = raw.replace(
        "async fn save(detail: String) {",
        "async fn save(mut detail: String) {\n    detail.truncate(64);",
    );
    assert_eq!(q(&capped), ["proven"]);
    let guarded = raw.replace(
        "async fn save(detail: String) {",
        "async fn save(detail: String) {\n    if detail.len() > 64 { return; }",
    );
    assert_eq!(q(&guarded), ["proven"]);
    let conditional = capped.replace(
        "detail.truncate(64);",
        "if enabled { detail.truncate(64); }",
    );
    assert_eq!(q(&conditional), ["violated"]);
    assert_eq!(
        q(&raw.replace("save(body)", "save(outside::change(body))")),
        ["unknown"]
    );
    assert_eq!(q(&raw.replace("{detail}", "{detail:.64}")), ["proven"]);
    assert!(q(&raw.replace("{detail}", "refused")).is_empty());
    let trusted = raw.replace("post(submit)", "post(other)");
    assert!(q(&trusted).is_empty());
    let auth = format!(
        "struct CurrentUser;\nimpl FromRequestParts for CurrentUser {{ fn from_request_parts() {{}} }}\n{}",
        raw.replace(
            "submit(body: String)",
            "submit(_: CurrentUser, body: String)"
        )
    );
    assert!(q(&auth).is_empty());
    assert_eq!(
        q(&auth.replace("_: CurrentUser", "_: Option<CurrentUser>")),
        ["violated"]
    );
    assert_eq!(
        q(&raw.replace(
            r#"&format!("request: {detail}")"#,
            r#"&format!("{short:.64} {extra}", short = detail, extra = detail)"#,
        )),
        ["violated"]
    );
}

#[test]
fn error_keeps_state_follows_the_error_path() {
    let broken = r#"
impl Buffer {
    fn append(&mut self, row: Row) -> Result<(), Error> {
        self.rows.push(row);
        self.buffered += 1;
        if self.buffered >= self.batch {
            self.rows.flush()?;
            self.buffered = 0;
        }
        Ok(())
    }
}
"#;
    let scan = |src| rule_verdicts("src/buffer.rs", src, 9, "error-keeps-state");
    assert_eq!(scan(broken), ["violated"]);
    let ordered = r#"
impl Buffer {
    fn append(&mut self, row: Row) -> Result<(), Error> {
        if self.buffered >= self.batch {
            self.rows.flush()?;
            self.buffered = 0;
        }
        self.buffered += 1;
        Ok(())
    }
}
"#;
    assert_eq!(scan(ordered), ["proven"]);

    let restore = broken
        .replace("self.rows.push(row);", "let before = self.buffered;")
        .replace(
            "self.rows.flush()?",
            "self.rows.flush().map_err(|err| { self.buffered = before; err })?",
        );
    assert_eq!(scan(&restore), ["proven"]);
    let opaque = restore.replace("self.buffered = before", "self.restore(before)");
    assert_eq!(scan(&opaque), ["unknown"]);

    let opaque_before_edit =
        ordered.replace("self.rows.flush()?", "self.refresh(); self.rows.flush()?");
    assert_eq!(scan(&opaque_before_edit), ["unknown"]);
    let opaque_argument = broken.replace("self.rows.flush()?", "flush_or_restore(self)?");
    assert_eq!(scan(&opaque_argument), ["unknown"]);

    let matched = restore.replace(
        "self.rows.flush().map_err(|err| { self.buffered = before; err })?;",
        "match self.rows.flush() { Ok(()) => (), Err(err) => { self.buffered = before; return Err(err); } }",
    );
    assert_eq!(scan(&matched), ["proven"]);
    let shadowed = matched
        .replace("Err(err) =>", "Err(before) =>")
        .replace("return Err(err)", "return Err(before)");
    assert_eq!(scan(&shadowed), ["violated"]);

    let other_branch = r#"
impl Buffer {
    fn append(&mut self, row: Row) -> Result<(), Error> {
        if self.buffered >= self.batch {
            return Err(Error::Full);
        } else {
            self.rows.flush()?;
            self.buffered = 0;
            self.buffered += 1;
        }
        Ok(())
    }
}
"#;
    assert_eq!(scan(other_branch), ["proven"]);

    let collection = r#"
impl Buffer {
    fn append(&mut self, values: &[Row]) -> Result<(), Error> {
        if flush_requested() {
            self.rows.flush()?;
        }
        let row = values.to_vec();
        self.rows.push(row);
        persist()?;
        Ok(())
    }
}
"#;
    assert_eq!(scan(collection), ["violated"]);

    let metrics = broken
        .replace("self.rows.push(row);", "")
        .replace("self.buffered", "self.metrics_count");
    assert!(scan(&metrics).is_empty());

    let budget = r#"
impl Search {
    fn apply(&mut self) -> Result<(), Error> {
        self.attempts += 1;
        if self.attempts > 100 {
            return Err(Error::Budget);
        }
        self.cache.insert("attempt", self.attempts);
        Ok(())
    }
}
"#;
    assert!(scan(budget).is_empty());

    let reporting = r#"
impl Reporter {
    fn post(&mut self) -> Result<(), Stop> {
        match exchange()? {
            Ok(()) => self.failures = 0,
            Err(_) => {
                self.failures += 1;
                if self.failures >= MAX_FAILURES {
                    self.reporting = false;
                }
            }
        }
        Ok(())
    }
}
"#;
    assert!(scan(reporting).is_empty());
}

#[test]
fn a_checked_batch_can_finish_prior_calls_before_taking_the_current_row() {
    let scan = |src: &str| rule_verdicts("src/buffer.rs", src, 9, "error-keeps-state");
    let batch = r#"
impl Batch {
    fn append(&mut self, values: &[Value]) -> Result<(), Error> {
        if self.buffered >= self.batch {
            self.pending.check_row(values)?;
            self.pending.flush()?;
            self.buffered = 0;
        }
        self.pending.append_row(values)?;
        self.buffered += 1;
        Ok(())
    }
}
"#;
    assert_eq!(scan(batch), ["proven"]);
    assert_eq!(
        scan(&batch.replace("self.pending.check_row(values)?;", "")),
        ["violated"]
    );
    let takes_input_before_flush = r#"
impl Batch {
    fn append(&mut self, values: &[Value]) -> Result<(), Error> {
        self.pending.append_row(values)?;
        self.buffered += 1;
        if self.buffered >= self.batch {
            self.pending.flush()?;
            self.buffered = 0;
        }
        Ok(())
    }
}
"#;
    assert_eq!(scan(takes_input_before_flush), ["violated"]);

    let copies_input = batch.replace(
        "        if self.buffered",
        "        let row = values.to_vec();\n        self.pending.push(row);\n        if self.buffered",
    );
    assert_eq!(scan(&copies_input), ["violated"]);
    for unknown in ["&values", "prepare(values)", "|| values.to_vec()"] {
        assert_eq!(
            scan(&copies_input.replace("values.to_vec()", unknown)),
            ["unknown"],
            "{unknown}"
        );
    }
    assert_eq!(
        scan(&batch.replace(
            "        if self.buffered",
            "        self.pending.stash(values);\n        if self.buffered",
        )),
        ["unknown"]
    );
}
