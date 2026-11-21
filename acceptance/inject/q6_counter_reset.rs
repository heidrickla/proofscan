use std::path::Path;

const TEMP_PREFIX: &str = "proofscan-";

fn new_in(parent: &Path) -> std::io::Result<()> {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    loop {
        NEXT.store(0, std::sync::atomic::Ordering::Relaxed);
        let index = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let path = parent.join(format!("{TEMP_PREFIX}{}-{index}", std::process::id()));
        match std::fs::create_dir(&path) {
            Ok(made) => return Ok(made),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
    }
}
