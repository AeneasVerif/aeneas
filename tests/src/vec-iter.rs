//@ [!lean] skip

// `for x in v` — consumes the `Vec` via `IntoIterator::into_iter`.
pub fn sum_by_value(v: Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v {
        acc = acc.wrapping_add(x);
    }
    acc
}

// `for x in &v` — borrows the vector as a slice iterator (`slice::Iter`).
pub fn sum_by_ref(v: &Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v {
        acc = acc.wrapping_add(*x);
    }
    acc
}

// `step_by`
pub fn sum_step_by(v: &Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v.iter().step_by(2) {
        acc = acc.wrapping_add(*x);
    }
    acc
}

// `enumerate`
pub fn sum_enumerate(v: &Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for (i, x) in v.iter().enumerate() {
        acc = acc.wrapping_add(*x).wrapping_add(i as u32);
    }
    acc
}

// `take`
pub fn sum_take(v: &Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v.iter().take(3) {
        acc = acc.wrapping_add(*x);
    }
    acc
}

// `into_iter().step_by()` — adapters over the by-value `Vec` IntoIter.
pub fn sum_into_step_by(v: Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v.into_iter().step_by(2) {
        acc = acc.wrapping_add(x);
    }
    acc
}

// `into_iter().enumerate()`
pub fn sum_into_enumerate(v: Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for (i, x) in v.into_iter().enumerate() {
        acc = acc.wrapping_add(x).wrapping_add(i as u32);
    }
    acc
}

// `into_iter().take()`
pub fn sum_into_take(v: Vec<u32>) -> u32 {
    let mut acc: u32 = 0;
    for x in v.into_iter().take(3) {
        acc = acc.wrapping_add(x);
    }
    acc
}

// `for _ in chunks` over a `Vec` of slices
// See: https://github.com/AeneasVerif/aeneas/issues/464
pub fn for_over_vec_of_slices(chunks: Vec<&[bool]>) {
    for _c in chunks {}
}
