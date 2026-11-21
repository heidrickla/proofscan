fn read_again(rest: &[u8]) -> &str {
    loop {
        match std::str::from_utf8(rest) {
            Ok(text) => return text,
            Err(_) => continue,
        }
    }
}
