//@ [coq,fstar] subdir=misc

trait Trait1 {}
trait Trait2 {
    fn foo() {}
}

// Blanket impl for Trait2
impl<T: Trait1> Trait2 for T {}
