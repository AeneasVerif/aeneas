//@ [!lean] skip

fn use_range(s: &[bool]) {
    let _ = &s[0..1];
}

fn use_range_to(s: &[bool]) {
    let _ = &s[..1];
}
