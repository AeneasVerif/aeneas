//@ [!lean] skip
// Regression test: instantiating a generic function's output type with unit.
//
// `set_and_return` returns its generic parameter `T` and takes a mutable borrow
// (which produces a "backward" value). When `T` is instantiated with the unit
// type at a call site, the callee still returns the pair `(T, _)` (it was
// compiled generically and does not eliminate its output). The translation must
// therefore destructure the pair `(_, back)` at the call site rather than
// wrongly assuming the output was eliminated. See the discussion around
// `ignore_output` in the symbolic-to-pure translation.

fn set_and_return<T>(r: &mut u32, x: u32, t: T) -> T {
    *r = x;
    t
}

fn call_with_unit(mut n: u32) -> u32 {
    let _ = set_and_return(&mut n, 1, ());
    let _ = set_and_return(&mut n, 2, ());
    n
}
