//@ [!lean] skip
//! Matching on an indexed place: Charon calls `Index::index` once to match on
//! the value and once again to read its fields in the branch.

pub fn array_get(a: [Option<u32>; 2], i: usize) -> u32 {
    if let Some(x) = a[i] { x } else { 0 }
}

pub fn slice_get(a: &[Option<u32>], i: usize) -> u32 {
    if let Some(x) = a[i] { x } else { 0 }
}

pub struct Links {
    pub child: [Option<u32>; 2],
}

pub fn first_child(l: &mut Links) -> u32 {
    match l.child[0] {
        Some(x) if x > 0 => x,
        Some(_) => 1,
        None => 0,
    }
}

/// The array is modified between the two uses of `a[0]`: the second `index`
/// call is not replaced.
pub fn modified(mut a: [Option<u32>; 2]) -> Option<u32> {
    let x = if let Some(x) = a[0] { x } else { 0 };
    a[0] = None;
    let y = if let Some(y) = a[0] { y } else { 1 };
    Some(x + y)
}
