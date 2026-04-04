//@ [!lean] skip

fn get_b0() -> bool {
    true
}

fn get_b1() -> bool {
    true
}

fn f() {}

// === Patterns with boolean inputs ===

pub fn assert_or(b0: bool, b1: bool) {
    assert!(b0 || b1);
    f();
}

pub fn assert_and(b0: bool, b1: bool) {
    assert!(b0 && b1);
    f();
}

pub fn assert_not_or(b0: bool, b1: bool) {
    assert!(!(b0 || b1));
    f();
}

pub fn assert_not_and(b0: bool, b1: bool) {
    assert!(!(b0 && b1));
    f();
}

pub fn assert_not_b0_or_b1(b0: bool, b1: bool) {
    assert!(!b0 || b1);
    f();
}

pub fn assert_b0_or_not_b1(b0: bool, b1: bool) {
    assert!(b0 || !b1);
    f();
}

pub fn assert_not_b0_or_not_b1(b0: bool, b1: bool) {
    assert!(!b0 || !b1);
    f();
}

pub fn assert_not_b0_and_b1(b0: bool, b1: bool) {
    assert!(!b0 && b1);
    f();
}

pub fn assert_b0_and_not_b1(b0: bool, b1: bool) {
    assert!(b0 && !b1);
    f();
}

pub fn assert_not_b0_and_not_b1(b0: bool, b1: bool) {
    assert!(!b0 && !b1);
    f();
}

// === Patterns with function calls ===

pub fn assert_or_call() {
    assert!(get_b0() || get_b1());
    f();
}

pub fn assert_and_call() {
    assert!(get_b0() && get_b1());
    f();
}

pub fn assert_not_or_call() {
    assert!(!(get_b0() || get_b1()));
    f();
}

pub fn assert_not_and_call() {
    assert!(!(get_b0() && get_b1()));
    f();
}

pub fn assert_not_b0_or_b1_call() {
    assert!(!get_b0() || get_b1());
    f();
}

pub fn assert_b0_or_not_b1_call() {
    assert!(get_b0() || !get_b1());
    f();
}

pub fn assert_not_b0_or_not_b1_call() {
    assert!(!get_b0() || !get_b1());
    f();
}

pub fn assert_not_b0_and_b1_call() {
    assert!(!get_b0() && get_b1());
    f();
}

pub fn assert_b0_and_not_b1_call() {
    assert!(get_b0() && !get_b1());
    f();
}

pub fn assert_not_b0_and_not_b1_call() {
    assert!(!get_b0() && !get_b1());
    f();
}

// === Patterns with comparison-based asserts ===

pub fn assert_lt(x: u32) {
    assert!(x < 10);
    f();
}

pub fn assert_le(x: u32) {
    assert!(x <= 3494);
    f();
}

pub fn assert_gt(x: u32) {
    assert!(x > 0);
    f();
}

pub fn assert_ge(x: u32) {
    assert!(x >= 1);
    f();
}

pub fn assert_eq(x: u32) {
    assert!(x == 42);
    f();
}

pub fn assert_ne(x: u32) {
    assert!(x != 0);
    f();
}

pub fn assert_arith(x: u32, y: u32) {
    assert!(x + y < 100);
    f();
}

// === Self-contained reproduction from poly_element_mul_and_accumulate ===

const MLWE_POLYNOMIAL_COEFFICIENTS: usize = 256;
type PolyElement = [u16; MLWE_POLYNOMIAL_COEFFICIENTS];
type PolyElementAccumulator = [u32; MLWE_POLYNOMIAL_COEFFICIENTS];
const Q: u32 = 3329;
const RLOG2: u32 = 16;
const RMASK: u32 = 0xffff;
const NEG_Q_INV_MOD_R: u32 = 3327;
const MATRIX_MAX_NROWS: usize = 4;

const ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R: [u16; 128] = [
    2226, 1103, 430, 2899, 555, 2774, 843, 2486, 2078, 1251, 871, 2458, 1550, 1779, 105, 3224, 422,
    2907, 587, 2742, 177, 3152, 3094, 235, 3038, 291, 2869, 460, 1574, 1755, 1653, 1676, 3083, 246,
    778, 2551, 1159, 2170, 3182, 147, 2552, 777, 1483, 1846, 2727, 602, 1119, 2210, 1739, 1590,
    644, 2685, 2457, 872, 349, 2980, 418, 2911, 329, 3000, 3173, 156, 3254, 75, 817, 2512, 1097,
    2232, 603, 2726, 610, 2719, 1322, 2007, 2044, 1285, 1864, 1465, 384, 2945, 2114, 1215, 3193,
    136, 1218, 2111, 1994, 1335, 2455, 874, 220, 3109, 2142, 1187, 1670, 1659, 2144, 1185, 1799,
    1530, 2051, 1278, 794, 2535, 1819, 1510, 2475, 854, 2459, 870, 478, 2851, 3221, 108, 3021, 308,
    996, 2333, 991, 2338, 958, 2371, 1869, 1460, 1522, 1807, 1628, 1701,
];

fn poly_element_mul_and_accumulate(
    pe_src1: &PolyElement,
    pe_src2: &PolyElement,
    pa_dst: &mut PolyElementAccumulator,
) {
    for i in 0usize..(MLWE_POLYNOMIAL_COEFFICIENTS / 2) {
        let a0: u32 = pe_src1[2 * i].into();
        assert!(a0 < Q);
        let a1: u32 = pe_src1[2 * i + 1].into();
        assert!(a1 < Q);

        let b0: u32 = pe_src2[2 * i].into();
        assert!(b0 < Q);
        let b1: u32 = pe_src2[2 * i + 1].into();
        assert!(b1 < Q);

        let mut c0: u32 = pa_dst[2 * i];
        assert!(c0 <= 3 * ((3328 * 3328) + (3494 * 3312)));
        let mut c1: u32 = pa_dst[(2 * i) + 1];
        assert!(c1 <= 3 * ((3328 * 3328) + (3494 * 3312)));

        let mut a0b0: u32 = a0 * b0;
        let a1b1 = a1 * b1;
        let mut a0b1: u32 = a0 * b1;
        let a1b0 = a1 * b0;

        let inv: u32 = (a1b1.wrapping_mul(NEG_Q_INV_MOD_R)) & RMASK;
        let a1b1: u32 = (a1b1 + (inv * Q)) >> RLOG2;
        assert!(a1b1 <= 3494);

        let a1b1zetapow = a1b1 * (ZETA_TO_TIMES_BIT_REV_PLUS_1_TIMES_R[i] as u32);

        a0b0 += a1b1zetapow;
        assert!(a0b0 <= (3328 * 3328) + (3494 * 3312));
        a0b1 += a1b0;
        assert!(a0b1 <= 2 * 3328 * 3328);

        const { assert!(MATRIX_MAX_NROWS <= 4) }
        c0 += a0b0;
        assert!(c0 < (4 * 3328 * 3328) + (4 * 3494 * 3312));
        c1 += a0b1;
        assert!(c1 < (5 * 3328 * 3328) + (3 * 3494 * 3312));

        pa_dst[2 * i] = c0;
        pa_dst[2 * i + 1] = c1;
    }
}

fn montgomery_reduce_and_add_poly_element_accumulator_to_poly_element(
    pa_src: &mut PolyElementAccumulator,
    pe_dst: &mut PolyElement,
) {
    for i in 0usize..MLWE_POLYNOMIAL_COEFFICIENTS {
        let mut a: u32 = pa_src[i];
        assert!(a <= 4 * ((3328 * 3328) + (3494 * 3312)));
        pa_src[i] = 0;

        let mut c: u32 = pe_dst[i].into();
        assert!(c < Q);

        // montgomery reduce sum of products
        let inv = (a.wrapping_mul(NEG_Q_INV_MOD_R)) & RMASK;
        a = (a + (inv * Q)) >> RLOG2; // in range [0, 4711]
        assert!(a <= 4711);

        // add destination
        c += a;
        assert!(c <= 8039);

        // subtraction and conditional additions for constant time range reduction
        c = c.wrapping_sub(2 * Q); // in range [-2Q, 1381]
        assert!((c >= ((-2 * (Q as i32)) as u32)) || (c < 1381));
        c = c.wrapping_add(Q & (c >> 16)); // in range [-Q, Q-1]
        assert!((c >= (-(Q as i32) as u32)) || (c < Q));
        c = c.wrapping_add(Q & (c >> 16)); // in range [0, Q-1]
        assert!(c < Q);

        pe_dst[i] = c as u16;
    }
}
