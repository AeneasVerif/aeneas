pub type Bignum = Vec<u32>;


/// Zero out a bignum
pub fn zero(x : &mut Bignum) {
    let mut i = 0;
    while i < x.len() {
        x[i] = 0;
        i += 1;
    }
}

/// Add a bignum in place.
///
/// We assume that:
/// - they have the same length
/// - there is no overflow when suming the individual thunks
pub fn add_no_overflow(x: &mut Bignum, y: &Bignum) {
    let mut i = 0;
    while i < x.len() {
        x[i] += y[i];
        i += 1;
    }
}

fn max(x : usize, y : usize) -> usize {
    if x > y { x } else { y }
}

fn get_or_zero(y : &Bignum, i : usize) -> u32 {
    if i < y.len() { y[i] } else { 0 }
}

/// Add a bignum in place.
///
/// The bignums do not necessarily have the same length.
/// We also return the carry, if there is an overflow.
pub fn add_with_carry(x: &mut Bignum, y: &Bignum) -> u8 {
    let max = max(x.len(), y.len());
    x.resize(max, 0u32);
    // now: length x >= length y
    let mut c0 = 0u8;
    let mut i = 0;
    // Remark: we have (and need) the invariant that: c0 <= 1
    while i < max {
        let yi = get_or_zero(y, i);
        let (sum, c1) = x[i].overflowing_add(c0 as u32);
        let (sum, c2) = sum.overflowing_add(yi);
        // We have: c1 as u8 + c2 as u8 <= 1
        c0 = (c1 as u8 + c2 as u8) as u8;
        x[i] = sum;
        i += 1;
    }
    c0
}

#[test]
fn test() {
    // TODO:
    // let mut x = vec![0xffffffffu32];
    // let mut y = vec![0xffffffffu32];
    let mut x = Vec::from([0xffffffffu32]);
    let mut y = Vec::from([0xffffffffu32]);
    let carry = add_with_carry(&mut x, &mut y);
    assert!(carry == 1);
    assert!(x.len() == 1);
    assert!(x[0] == 0xfffffffe);
}
