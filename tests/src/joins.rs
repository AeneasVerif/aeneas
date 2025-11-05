//@ [!lean] skip

fn opt_add_1(b : bool, x : u32) -> u32 {
    let y = if b { 1 } else { 0 };
    x + y
}
