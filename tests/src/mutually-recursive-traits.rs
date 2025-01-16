//@ [lean] known-failure
//@ [!lean] skip
pub trait Trait1 {
    type T: Trait2;
}

pub trait Trait2: Trait1 {}

pub trait T1<T: T2<Self>>: Sized {}
pub trait T2<T: T1<Self>>: Sized {}
