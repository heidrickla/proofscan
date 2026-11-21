//! Names the commit a binary was built from, so a report shows which build produced it.

use std::process::Command;

fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn main() {
    let sha = git(&["rev-parse", "--short=7", "HEAD"]).unwrap_or_else(|| "unknown".into());
    // Uncommitted source makes the commit a lie; say so.
    let dirty = git(&[
        "status",
        "--porcelain",
        "--",
        "src",
        "Cargo.toml",
        "Cargo.lock",
        "build.rs",
    ])
    .is_some_and(|s| !s.is_empty());
    println!(
        "cargo:rustc-env=PROOFSCAN_COMMIT={sha}{}",
        if dirty { "+dirty" } else { "" }
    );
    if let Some(dir) = git(&["rev-parse", "--git-dir"]) {
        println!("cargo:rerun-if-changed={dir}/HEAD");
        println!("cargo:rerun-if-changed={dir}/index");
    }
    println!("cargo:rerun-if-changed=src");
}
