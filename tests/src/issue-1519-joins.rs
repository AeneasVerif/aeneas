//@ [!lean] skip
pub fn shr_and_mut<'a>(x: &'a mut i32, y: &'a mut i32) -> (&'a i32, &'a mut i32) {
    (x, y)
}
pub fn loop_shr_and_mut(mut n: i32) -> i32 {
    let mut x = 42;
    let mut y = 10;
    loop {
        let rx = &mut x;
        let ry = &mut y;
        let s = {
            let (s, r) = shr_and_mut(rx, ry);
            *r += 1;
            s
        };
        if n <= 0 {
            let v = *s;
            break v;
        }
        x += 1;
        y += 1;
        n -= 1;
    }
}