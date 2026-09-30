//@ [!lean] skip
//@ [lean] aeneas-args=-strict-joins

fn opt_add_1(b: bool, x: u32) -> u32 {
    let y = if b { 1 } else { 0 };
    x + y
}

fn opt_add_2(b: bool, x: u32) -> u32 {
    let y = if b { 1 } else { 0 };
    let z = if b { 1 } else { 0 };
    x + y + z
}

fn opt_add_1_or_panic(b: bool, x: u32) -> u32 {
    let y = if b { 1 } else { panic!() };
    x + y
}

fn opt_add_switch_1(a: u32, x: u32) -> u32 {
    let y = match a {
        0 => 0,
        1 => 1,
        _ => panic!(),
    };
    x + y
}

fn opt_add_switch_2(a: u32, x: u32) -> u32 {
    let y = match a {
        0 => 0,
        _ => panic!(),
    };
    x + y
}

enum Enum {
    V0,
    V1,
    V2,
}

fn use_enum(e: Enum, x: u32) -> u32 {
    use Enum::*;
    let y = match e {
        V0 => 0,
        V1 => 1,
        V2 => 2,
    };
    x + y
}

fn call_choose(b: bool, x: &mut u32, y: &mut u32) {
    let z = if b { x } else { y };
    *z = *z + 1;
}

struct SharedBool {
    value: bool,
}

fn shared_bool_scrutinee(k: &SharedBool, x: u32, y: u32) -> u32 {
    let f = if k.value { x } else { y };
    if x >= f {
        1
    } else {
        0
    }
}

fn shared_integer_scrutinee(n: &u8, x: u32, y: u32) -> u32 {
    let m = *n;
    let f = match m {
        0 => x,
        _ => y,
    };
    if x >= f {
        1
    } else {
        0
    }
}
