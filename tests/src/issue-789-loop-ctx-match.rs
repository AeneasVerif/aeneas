//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/789

pub struct S {
    x: u8,
    y: [u8; 4],
}

pub fn f(_r: &mut u8, _a: &[u8], _b: &mut [u8]) -> (bool, usize) {
    (true, 0)
}

pub fn the_loop(s: &mut S, next_in: &mut &[u8]) -> bool {
    loop {
        let result = f(&mut s.x, *next_in, &mut s.y);
        let n = result.1;
        let done = result.0;
        *next_in = &next_in[n..];
        if done || next_in.is_empty() {
            return done;
        }
    }
}
