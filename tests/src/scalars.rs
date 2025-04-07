//@ [!lean] skip

fn u32_use_wrapping_add(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

fn i32_use_wrapping_add(x: i32, y: i32) -> i32 {
    x.wrapping_add(y)
}

fn u32_use_wrapping_sub(x: u32, y: u32) -> u32 {
    x.wrapping_sub(y)
}

fn i32_use_wrapping_sub(x: i32, y: i32) -> i32 {
    x.wrapping_sub(y)
}

fn u32_use_shift_right(x: u32) -> u32 {
    x >> 2
}

fn i32_use_shift_right(x: i32) -> i32 {
    x >> 2
}

fn u32_use_shift_left(x: u32) -> u32 {
    x << 2
}

fn i32_use_shift_left(x: i32) -> i32 {
    x << 2
}

fn add_and(a: u32, b: u32) -> u32 {
    (b & a) + (b & a)
}

fn u32_use_rotate_right(x: u32) -> u32 {
    x.rotate_right(2)
}

fn i32_use_rotate_right(x: i32) -> i32 {
    x.rotate_right(2)
}

fn u32_use_rotate_left(x: u32) -> u32 {
    x.rotate_left(2)
}

fn i32_use_rotate_left(x: i32) -> i32 {
    x.rotate_left(2)
}

fn u32_default() -> u32 {
    Default::default()
}

fn i32_default() -> i32 {
    Default::default()
}
