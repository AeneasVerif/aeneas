//@ [!lean] skip

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
