//@ [lean] known-failure
//@ [coq,fstar] skip
//@ no-check-output
fn main() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
