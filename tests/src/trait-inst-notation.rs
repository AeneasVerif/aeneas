//@ [!lean] skip
//@ [lean] aeneas-args=-trait-inst-notation
//! Tests for the `-trait-inst-notation` option: references to trait
//! implementations and to trait clauses are extracted to the
//! `({Trait<Args> for Type})` notation instead of using the (mangled)
//! implementation names or the clause binder paths.

pub trait ToU64 {
    fn to_u64(&self) -> u64;
}

impl ToU64 for u64 {
    fn to_u64(&self) -> u64 {
        *self
    }
}

impl<A: ToU64> ToU64 for (A, A) {
    fn to_u64(&self) -> u64 {
        self.0.to_u64() + self.1.to_u64()
    }
}

/// Reference to a clause in scope
pub fn use_clause<T: ToU64>(x: T) -> u64 {
    x.to_u64()
}

/// Reference to a generic impl instantiated at concrete types, passed as a
/// clause argument (the nested `u64` instance is resolved recursively)
pub fn use_pair_impl(x: (u64, u64)) -> u64 {
    use_clause(x)
}

pub trait Parent {
    fn name(&self) -> u64;
}

pub trait Child: Parent {
    fn child_name(&self) -> u64;
}

/// Reference to a clause through a parent-clause projection
pub fn use_parent_through_child<T: Child>(x: T) -> u64 {
    x.name()
}

impl Parent for u64 {
    fn name(&self) -> u64 {
        1
    }
}

impl Child for u64 {
    fn child_name(&self) -> u64 {
        2
    }
}

pub fn call_concrete(x: u64) -> u64 {
    use_parent_through_child(x)
}

pub trait A: ToU64 {}
pub trait B: ToU64 {}

impl A for u64 {}
impl B for u64 {}

/// Two reachable `ToU64` instances for `T` (through the parent clauses of `A`
/// and `B`): the notation would be ambiguous, so the extraction must fall
/// back to the clause binder paths
pub fn ambiguous_parents<T: A + B>(x: T) -> u64 {
    x.to_u64()
}

pub trait WithDefault {
    fn required(&self) -> u64;
    fn provided(&self) -> u64 {
        self.required()
    }
}

impl WithDefault for u64 {
    fn required(&self) -> u64 {
        *self
    }
}

pub fn call_default(x: u64) -> u64 {
    x.provided()
}

/// A trait with a type parameter and an associated constant, implemented for
/// an array type: exercises const generics and the `Array` notation
pub trait WithLen<T> {
    const LEN: usize;
    fn first(&self) -> T;
}

impl WithLen<u32> for [u32; 32] {
    const LEN: usize = 32;
    fn first(&self) -> u32 {
        self[0]
    }
}

pub fn use_with_len(x: [u32; 32]) -> u32 {
    x.first()
}

// Note: methods with their own (method-level) type parameters are not tested
// here: trait implementations providing such methods do not extract to valid
// Lean at the moment (with or without the `-trait-inst-notation` option): the
// record field is eta-expanded with an explicit binder against an implicit
// binder in the field type.
