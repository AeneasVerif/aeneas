//@ [coq,fstar] skip

pub fn test(b: bool) -> () {
    let mut i = 0;
    // let mut j = 0;
    if b {
        i = 1;
    } else {
        i = 2;
    }
    i += 1;
}
