//@ [!lean] skip

fn collect() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
