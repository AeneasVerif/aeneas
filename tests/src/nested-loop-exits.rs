//@ [!lean] skip
//! Returns inside nested loops and breaks/continues to outer loops.
pub fn find(v: &[u32], x: u32) -> Option<usize> {
    let mut i = 0;
    loop {
        let mut j = 0;
        while j < 4 {
            if i + j < v.len() && v[i + j] == x {
                return Some(i + j);
            }
            j += 1;
        }
        if i >= v.len() {
            return None;
        }
        i += 4;
    }
}

pub fn outer_break(n: u32) -> u32 {
    let mut s = 0;
    'outer: for i in 0..n {
        for j in 0..n {
            if i * j > 10 {
                break 'outer;
            }
            if j > i {
                continue 'outer;
            }
            s += 1;
        }
    }
    s
}

/// An early return from a loop which also has a break, inside an `if`: the
/// statements after the loop don't end the function.
pub fn first_space(v: &[u8], b: bool) -> Option<usize> {
    if b {
        let mut i = 0;
        loop {
            if i >= v.len() {
                return None;
            }
            if v[i] == b' ' {
                break;
            }
            i += 1;
        }
        Some(i)
    } else {
        None
    }
}
