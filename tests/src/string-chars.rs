//@ [lean] known-failure
//@ [coq,fstar] skip
fn main() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
