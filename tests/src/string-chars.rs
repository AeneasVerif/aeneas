//@ [!lean] skip

fn collect() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}

fn print_vec() {
    let v = [1, 3, 2].to_vec();
    println!("{:?}", v);
}
