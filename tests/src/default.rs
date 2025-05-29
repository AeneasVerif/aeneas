//@ [!lean] skip

fn f0() {
    let _: [u32; 0] = Default::default();
}

fn f1() {
    let _: [u32; 1] = Default::default();
}

fn f2() {
    let _: [u32; 2] = Default::default();
}
