//@ [!lean] skip

#[derive(Default)]
pub struct Key {
    round_keys: [[u8; 16]; 29],
}

pub fn new() {
    let _ = Key::default();
}
