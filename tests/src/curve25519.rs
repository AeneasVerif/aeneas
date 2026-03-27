//@ [!lean] skip
//@ [lean] subdir=Curve25519
// This code is adapted from curve25519-dalek: https://github.com/dalek-cryptography/curve25519-dalek

use std::ops::Index;

pub struct Scalar52(pub [u64; 5]);

impl Index<usize> for Scalar52 {
    type Output = u64;
    fn index(&self, _index: usize) -> &u64 {
        &(self.0[_index])
    }
}

fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

pub fn mul_internal(a: &Scalar52, b: &Scalar52) -> [u128; 9] {
    let mut z = [0u128; 9];

    z[0] = m(a[0], b[0]);
    z[1] = m(a[0], b[1]) + m(a[1], b[0]);
    z[2] = m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]);
    z[3] = m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]);
    z[4] = m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]);
    z[5] = m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]);
    z[6] = m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]);
    z[7] = m(a[3], b[4]) + m(a[4], b[3]);
    z[8] = m(a[4], b[4]);

    z
}
