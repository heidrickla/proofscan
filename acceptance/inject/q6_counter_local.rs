use std::path::Path;

fn new_in(parent: &Path, skip_tail: bool) -> std::io::Result<()> {
    let mut index = 0u64;
    loop {
        let path = parent.join(format!("proofscan-{}", index));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(()),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                if skip_tail {
                    index += 1;
                    continue;
                }
            }
            Err(error) => return Err(error),
        }
        index += 1;
    }
}
