//@ [!lean] skip
//@ charon-args=--opaque=crate::ext
// Issue: https://github.com/AeneasVerif/aeneas/issues/765
//
// A blanket impl carrying a higher-ranked bound `for<'a> &'a T: Neg<Output = T>`
// whose body negates through a reborrow (`-&*self`). This is the shape of the
// `subtle` crate's `ConditionallyNegatable`, which used to make the interpreter
// walk a region id bound by the impl's binder and error.

use core::ops::Neg;

#[derive(Clone, Copy)]
pub struct Choice(u8);

pub trait ConditionallySelectable: Copy {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self;

    fn conditional_assign(&mut self, other: &Self, choice: Choice) {
        *self = Self::conditional_select(self, other, choice);
    }
}

#[derive(Clone, Copy)]
pub struct F;

impl ConditionallySelectable for F {
    fn conditional_select(a: &Self, _b: &Self, _choice: Choice) -> Self {
        *a
    }
}

impl<'a> Neg for &'a F {
    type Output = F;

    fn neg(self) -> F {
        F
    }
}

/// Models the external crate: the blanket impl body is opaque.
pub mod ext {
    use super::{Choice, ConditionallySelectable};
    use core::ops::Neg;

    pub trait ConditionallyNegatable {
        fn conditional_negate(&mut self, choice: Choice);
    }

    impl<T> ConditionallyNegatable for T
    where
        T: ConditionallySelectable,
        for<'a> &'a T: Neg<Output = T>,
    {
        fn conditional_negate(&mut self, choice: Choice) {
            let self_neg: T = -&*self;
            self.conditional_assign(&self_neg, choice);
        }
    }
}

/// Same blanket impl, but translated transparently.
pub mod local {
    use super::{Choice, ConditionallySelectable};
    use core::ops::Neg;

    pub trait ConditionallyNegatable {
        fn conditional_negate(&mut self, choice: Choice);
    }

    impl<T> ConditionallyNegatable for T
    where
        T: ConditionallySelectable,
        for<'a> &'a T: Neg<Output = T>,
    {
        fn conditional_negate(&mut self, choice: Choice) {
            let self_neg: T = -&*self;
            self.conditional_assign(&self_neg, choice);
        }
    }
}

pub fn call_opaque_blanket_impl(choice: Choice) -> F {
    use ext::ConditionallyNegatable;
    let mut x = F;
    x.conditional_negate(choice);
    x
}

pub fn call_transparent_blanket_impl(choice: Choice) -> F {
    use local::ConditionallyNegatable;
    let mut x = F;
    x.conditional_negate(choice);
    x
}
