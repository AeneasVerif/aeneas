//@ [!lean] skip
//! Regression test for issue https://github.com/AeneasVerif/aeneas/issues/1518
//! See comment below.

pub fn borrow_unit(x: &mut (i32, ())) -> &mut () {
    &mut x.1
}
pub fn loop_borrow_unit(mut n: i32) -> i32 {
    let mut x = (42, ());
    let mut ru;
    loop {
        ru = borrow_unit(&mut x);
        if n <= 0 {
            // 
            break;
        }
        x.0 += 1;
        n -= 1;
    }
    // the backwards function introduced by `borrow_unit` is still needed here.
    // But the `unit_vars_to_unit` micro-optimization would make the backward fn's
    // binder be `PIgnored`.
    *ru = ();
    // This the broke another micro-opti, `apply_beta_reduction`, which throws an
    // exception on `PIgnored` binders.
    x.0
}