//@ [!lean] skip
fn foo() -> bool {
    let y = (0, 0);
    let mut x = ((1, 2), &y);
    x.1 = &x.0;
    let xr = &x;
    let x11r = &(*(*xr).1).1;
    let vv = *x11r;
    vv == 2
}
