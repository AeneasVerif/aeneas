//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

use std::cmp::Ordering;

pub fn compare<T: Ord>(x: &T, y: &T) -> Ordering {
    x.cmp(y)
}

pub fn u32_compare(x: u32, y: u32) -> Ordering {
    x.cmp(&y)
}

pub fn u64_partial_cmp(x: u64, y: u64) -> Option<Ordering> {
    x.partial_cmp(&y)
}

/// Exercises derived PartialOrd and Ord on a struct with scalar fields.
/// The derived impls only generate partial_cmp/cmp — the remaining methods
/// (lt, le, gt, ge, max, min, clamp) use defaults. The Lean structure
/// definitions must provide default field values for these.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Wrap(u64);

pub fn wrap_partial_cmp(x: &Wrap, y: &Wrap) -> Option<Ordering> {
    x.partial_cmp(y)
}

pub fn wrap_cmp(x: &Wrap, y: &Wrap) -> Ordering {
    x.cmp(y)
}

// ---------------------------------------------------------------------------
// exercises <, <=, >, >=, max, min and clamp on types that derive partial_cmp/cmp
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_wrap_lt() {
    assert!(Wrap(1) < Wrap(2));
    assert!(!(Wrap(2) < Wrap(2)));
    assert!(!(Wrap(2) < Wrap(1)));
}

#[verify::test]
pub fn test_wrap_le() {
    assert!(Wrap(1) <= Wrap(2));
    assert!(Wrap(2) <= Wrap(2));
    assert!(!(Wrap(2) <= Wrap(1)));
}

#[verify::test]
pub fn test_wrap_gt() {
    assert!(Wrap(2) > Wrap(1));
    assert!(!(Wrap(2) > Wrap(2)));
    assert!(!(Wrap(1) > Wrap(2)));
}

#[verify::test]
pub fn test_wrap_ge() {
    assert!(Wrap(2) >= Wrap(1));
    assert!(Wrap(2) >= Wrap(2));
    assert!(!(Wrap(1) >= Wrap(2)));
}

#[verify::test]
pub fn test_wrap_max() {
    assert!(Wrap(1).max(Wrap(2)) == Wrap(2));
    assert!(Wrap(2).max(Wrap(1)) == Wrap(2));
    assert!(Wrap(2).max(Wrap(2)) == Wrap(2));
}

#[verify::test]
pub fn test_wrap_min() {
    assert!(Wrap(1).min(Wrap(2)) == Wrap(1));
    assert!(Wrap(2).min(Wrap(1)) == Wrap(1));
    assert!(Wrap(2).min(Wrap(2)) == Wrap(2));
}

#[verify::test]
pub fn test_wrap_clamp() {
    assert!(Wrap(0).clamp(Wrap(1), Wrap(3)) == Wrap(1));
    assert!(Wrap(2).clamp(Wrap(1), Wrap(3)) == Wrap(2));
    assert!(Wrap(4).clamp(Wrap(1), Wrap(3)) == Wrap(3));
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Rank {
    Low,
    Mid,
    High,
}

#[verify::test]
pub fn test_rank_lt() {
    assert!(Rank::Low < Rank::High);
    assert!(!(Rank::Mid < Rank::Mid));
    assert!(!(Rank::High < Rank::Low));
}

// ---------------------------------------------------------------------------
// exercises the case where partial_cmp returns None where all 4 comparisons must be false.
// ---------------------------------------------------------------------------

pub enum Num {
    Val(u8),
    Nan,
}

impl PartialEq for Num {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Num::Val(a), Num::Val(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Num::Val(a), Num::Val(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

#[verify::test]
pub fn test_num_incomparable() {
    assert!(!(Num::Nan < Num::Val(1)));
    assert!(!(Num::Nan <= Num::Val(1)));
    assert!(!(Num::Nan > Num::Val(1)));
    assert!(!(Num::Nan >= Num::Val(1)));
    assert!(!(Num::Nan <= Num::Nan));
}

// ---------------------------------------------------------------------------
// exercises impl PartialOrd<&B> for &A, it's how the issue's own example (a < b on two &Foo) compiles.
// ---------------------------------------------------------------------------

#[verify::test]
pub fn test_wrap_ref_lt() {
    let a = Wrap(1);
    let b = Wrap(2);
    assert!(&a < &b);
    assert!(!(&b < &a));
}

#[verify::test]
pub fn test_wrap_ref_le() {
    let a = Wrap(1);
    let b = Wrap(2);
    assert!(&a <= &b);
    assert!(!(&b <= &a));
}

#[verify::test]
pub fn test_wrap_ref_gt() {
    let a = Wrap(1);
    let b = Wrap(2);
    assert!(&b > &a);
    assert!(!(&a > &b));
}

#[verify::test]
pub fn test_wrap_ref_ge() {
    let a = Wrap(1);
    let b = Wrap(2);
    assert!(&b >= &a);
    assert!(!(&a >= &b));
}

#[verify::test]
pub fn test_wrap_ref_partial_cmp() {
    let a = Wrap(1);
    let b = Wrap(2);
    let o = PartialOrd::partial_cmp(&&a, &&b);
    assert!(match o {
        Some(Ordering::Less) => true,
        _ => false,
    });
}

// ---------------------------------------------------------------------------
// eercises values that Ord calls equal but differ (same key, different tag).
// ---------------------------------------------------------------------------

pub struct Keyed {
    pub key: u8,
    pub tag: u8,
}

impl PartialEq for Keyed {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for Keyed {}

impl PartialOrd for Keyed {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Keyed {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

/// on tie, Rust's max returns its second argument
#[verify::test]
pub fn test_keyed_max_tie() {
    let a = Keyed { key: 1, tag: 0 };
    let b = Keyed { key: 1, tag: 1 };
    assert!(a.max(b).tag == 1);
}

/// same same but different, on tie, Rust's min retuns its first argument
#[verify::test]
pub fn test_keyed_min_tie() {
    let a = Keyed { key: 1, tag: 0 };
    let b = Keyed { key: 1, tag: 1 };
    assert!(a.min(b).tag == 0);
}

/// on tie with a bound, Rust's clamp returns self, not the bound
#[verify::test]
pub fn test_keyed_clamp_tie() {
    let x = Keyed { key: 1, tag: 0 };
    let r = x.clamp(Keyed { key: 1, tag: 1 }, Keyed { key: 3, tag: 3 });
    assert!(r.tag == 0);
    let y = Keyed { key: 3, tag: 0 };
    let r = y.clamp(Keyed { key: 1, tag: 1 }, Keyed { key: 3, tag: 3 });
    assert!(r.tag == 0);
}
