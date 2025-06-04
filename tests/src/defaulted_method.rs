//@ [fstar,coq] subdir=misc
trait Trait {
    fn provided_method(&self) -> u32 {
        self.required_method()
    }
    fn required_method(&self) -> u32;
}

struct NoOverride;
impl Trait for NoOverride {
    fn provided_method(&self) -> u32 {
        73
    }
    fn required_method(&self) -> u32 {
        12
    }
}

struct YesOverride;
impl Trait for YesOverride {
    fn required_method(&self) -> u32 {
        42
    }
}

fn main() {
    NoOverride.provided_method();
    YesOverride.provided_method();

    // `min` is a default method of standard trait `Ord`.
    let n = 10.min(1);
    assert!(n == 1);
}
