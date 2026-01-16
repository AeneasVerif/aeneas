//@ [!lean] skip

fn iter_array() {
    let mut v = Vec::from([1u32, 2, 3]);
    let mut x = 0;
    for i in v {
        x += 1;
    }
}
