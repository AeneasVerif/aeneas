//@ [coq] skip
//@ [coq,fstar] subdir=misc
//^ note: coq gives "invalid notation for pattern"
fn match_u32(x: u32) -> u32 {
    match x {
        0 => 0,
        1 => 1,
        _ => 2,
    }
}
