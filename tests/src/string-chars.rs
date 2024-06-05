//@ [lean] known-failure
//@ [!lean] skip
//@ no-check-output
fn main() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
