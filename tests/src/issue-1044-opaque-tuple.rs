//@ [!lean] skip

//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1044

pub struct GF16 {
    pub value: u16,
}

pub fn mul2(a: u16, b: u16, c: u16) -> (u16, u16) {
    (a.wrapping_mul(b), a.wrapping_mul(c))
}

pub fn update_adjacent(a: GF16, into: &mut [GF16]) {
    let mut i: usize = 0;
    while i + 2 <= into.len() {
        (into[i].value, into[i + 1].value) = mul2(a.value, into[i].value, into[i + 1].value);
        i += 2;
    }
}
