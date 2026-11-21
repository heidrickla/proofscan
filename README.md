# proofscan

proofscan checks a repository for classes of defect that pass review and tests, one question per class. Each answer is proven (with its assumptions), violated (with a witness) or unknown (naming what stopped the model). It reads Python, Rust, JavaScript, shell and PowerShell with tree-sitter, runs the facts to a fixed point in Datalog (Ascent), and compares access policies with Z3.

| # | Question | Rules |
|---|---|---|
| 1 | One source per fact | one-reading, mixed-time-sources, double-reimplements |
| 2 | Provenance of stand-ins | wire-provenance, suite-disables-guard, upgrade-shape (on a diff only) |
| 3 | Check and use together | reread-after-check, stale-write-back, read-before-check |
| 4 | Guard at the effect | unguarded-effect, write-before-guard, guard-after-wait |
| 5 | Closed sets | closed-segment, open-deny, name-table-guard, text-filter-pass |
| 6 | Bounds and exits | wall-date-bound, retry-limit, state-exit, durable-exit, handler-requery, held-state-exit, held-run-recovery, stale-status, fixed-day-span, grow-and-search, blocking-unbounded, untrusted-store-size, emitted-bytes (opt-in), prefix-work (opt-in) |
| 7 | Proof by effect | weak-probe, pipe-masks-exit, random-property, path-patch-advisories |
| 8 | Tests that can fail | mutant, operand mutants (on a diff only) |
| 9 | Release on every exit | release-interrupted, release-on-error, release-on-panic, error-keeps-state |
| 10 | Secrets never reach a sink | secret-sink, store-printed |

What each question proves, what it assumes, which rules are heuristic and what stays unknown: [docs/questions.md](docs/questions.md).

## Build

```bash
cargo install --path . --locked
```

That puts `proofscan` on the PATH (`~/.cargo/bin`), the one copy a gate should run. `proofscan --version` and the first line of every report name the commit the binary was built from, with `+dirty` when the source had uncommitted changes, so a report from a stale build shows it.

The policy comparison links the system libz3, version 4.13 or later (Debian 13: `apt-get install libz3-dev`; Ubuntu 24.04 ships 4.8.12, too old, so CI installs the official 4.15.8 build and points `Z3_LIBRARY_PATH_OVERRIDE` at it):

```bash
cargo build --release --features smt
```

`--features smt-bundled` builds Z3 from source instead (CMake and a C++ compiler).

## Use

Scan a working tree, or a commit read from git objects with nothing checked out:

```bash
proofscan scan path/to/repo
```

```bash
proofscan scan path/to/repo --rev 1a2b3c4 --scope src --question 1 --question 6
```

Keep only the findings a change brought since a base (see "Pre-push gate"), the form for a gate:

```bash
proofscan scan . --diff origin/main
```

Sweep several repositories as one program (cross-repository calls resolve through imports):

```bash
proofscan sweep --one-program ~/src/a@HEAD ~/src/b ~/src/c@v1.2
```

Without `--one-program` a sweep answers each repository alone and joins the reports, so it holds one repository in memory at a time.

Question 8 mutates the rules a diff added and runs the tests on each mutant in a pristine copy:

```bash
proofscan mutate . --diff origin/main --test "python -m pytest -q"
```

`--list` prints the mutants without running the tests; `--at path:line` keeps only those lines' mutants:

```bash
proofscan mutate . --diff origin/main --at loops/server.py:1046 --test "python -m pytest -q tests"
```

Compare two policies (feature `smt`): exit 0 when the candidate allows nothing the reference denies, 1 with a counterexample, 2 when the solver cannot decide.

```bash
proofscan policy --kind brief --candidate new-brief.txt --reference old-brief.txt
```

Review focus for a change: the unknowns are the reviewer's scope (no proof covers them), the violations are handed over, and the proven sites come with the assumptions each proof rests on, so a reviewer re-raises one only by naming the assumption that fails. With `--findings` (a `{"findings": [...]}` report, or an array of `{file, line, title}`), each finding is checked against the verdicts on its line: `confirmed-by-violation`, `contradicted-by-proof` (a rejection backed by a proof, for that question only), `unknown-here` or `no-proof` (the finding stands on its own evidence).

```bash
proofscan review . --diff origin/main --findings round3.json
```

The escaped-defect loop: a defect that got past review goes into a shared escaped-defect file, and `proofscan accept` reads that file in its own format (`clone`, `review_at`, `fix`, `files`). A defect with no `expect` is an open row: its candidates are the violations in its files that its fix clears or whose lines it changes, and "none" means the case as written does not show it. Open rows are reported, not counted; classing one means adding its `expect` to the acceptance cases file.

```bash
proofscan accept review-eval/cases.toml
```

A score per rule: the acceptance cases each rule catches, misses, holds (a precision case or a fix it gets right) and gets wrong (a precision case it fails, a violation on a clean control), and the review outcomes in a ledger, `outcomes.jsonl` beside the first cases file. Its precision is hits (cases caught and violations confirmed) over hits and false positives. A reviewed violation goes into the ledger with `--record`:

```bash
proofscan tally cases.toml
```

```bash
proofscan tally cases.toml --record stale-status "app/server.py:1290 at 5d262b2" confirmed --note "review finding D"
```

`--json` gives the full report on any command; `--all` also lists proven sites.

Facts are cached per file by its path and bytes and the build of proofscan that parsed it, in `PROOFSCAN_CACHE` or the user cache directory (`%LOCALAPPDATA%\proofscan`, `$XDG_CACHE_HOME/proofscan` or `~/.cache/proofscan`). A build's entries not used for a week are removed on the next run. `--no-cache` or `PROOFSCAN_CACHE=off` parses everything again. `PROOFSCAN_TIMING=1` prints the time of each phase and the size of each relation on stderr.

Exit status: 0 when nothing is violated or unknown, 1 on a violation, 2 on an unknown with no violation. `[report] unknown_fails = false` makes unknowns exit 0.

## Configuration

A provider pattern may start with `py:`, `rs:`, `js:`, `sh:` or `ps:` to apply in that language only (the shell `date` command is `sh:^date$`, so a Rust function named `date` is no clock read).

With no configuration the built-in defaults apply ([src/defaults.toml](src/defaults.toml)), and a framework profile is added when its marker is present ([src/profiles.toml](src/profiles.toml); Home Assistant is detected by `custom_components/*/manifest.json`). A repository adds `proofscan.toml` at its root, or passes `--config`. Tables merge, arrays append, and scalars replace. Without a declared wire or resource, the questions that need one report what they did not check, and more answers come back unknown.

```toml
[report]
unknown_fails = false

# Fixtures that stand in for a device's replies, and real captures of it.
[[q2.wire]]
name = "keypad update"
pattern = '^%00,'
capture_files = ["captures/keypad.txt"]

# A deny list kept on purpose.
[[q5.accepted_deny]]
site = "hooks/guard.py:111"
reason = "refuses known attribution lines; publishing is also checked by review"
```

## Pre-push gate

A repository opts in by adding `proofscan.toml` at its root. `proofscan gate` is the gate: with no `proofscan.toml` it passes and says the repository is not opted in, so it can run in every repository; otherwise it scans what the change from `--base` (default the upstream branch) touched and exits 1 on a violation, 2 on an unknown with `--strict`, and 3 when there is no upstream and no base:

```bash
proofscan gate .
```

`proofscan scan . --diff @{upstream}` is the same scan without the opt-in check, failing on an unknown too unless `unknown_fails = false`. A finding is the change's when its site is on a changed line, or when its witness passes a changed line and the base commit does not have the same finding (question, rule, file and message). A finding the base already had stays out even when the change edits a line its witness passes.

For a root-cause sweep after a defect is found, run its question over every repository to find the other instances:

```bash
proofscan sweep --question 5 ~/src/*/
```

## Checks

```bash
cargo fmt --check
```

```bash
cargo clippy --all-targets --features smt -- -D warnings
```

```bash
cargo nextest run --features smt
```

```bash
cargo deny check
```

The test `every_injected_defect_turns_into_a_violation` writes each snippet in `acceptance/inject/` into a clean tree and requires the scan to turn into a violation of that rule. A rule that cannot fail is caught there.
