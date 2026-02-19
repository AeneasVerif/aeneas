//@ [!lean] skip

pub trait WithSlice {
    const SLICE: &'static [u16];
}

/*struct S;
impl WithSlice for S {
    const SLICE : &'static [u16] = &[0, 1];
}

impl S {
    fn read(i : usize) -> u16 {
        S::SLICE[i]
    }

    fn sum() -> u16 {
        let mut s = 0;
        for x in Self::SLICE {
            s += x;
        }
        s
    }
}
*/

fn read<S: WithSlice>(_: S, i: usize) -> u16 {
    S::SLICE[i]
}

/*fn sum<S : WithSlice>(_ : S, i : usize) -> u16 {
    let mut s = 0;
    for x in S::SLICE {
        s += x;
    }
    s
}*/

fn use_static() {
    const PREFIX: &[u8; 1] = &[0];
    let _ = PREFIX;
}
