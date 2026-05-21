//@ [lean] aeneas-args=-test-units
//@ [!lean] skip

pub fn return_after_inner_break_outer(flag: bool, value: u32) -> u32 {
    'outer: loop {
        let mut j = 0;
        while j < 2 {
            if flag && j == 0 {
                break 'outer;
            }
            j += 1;
        }

        return value + j;
    }

    value
}

pub fn break_outer(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        let mut j = 0;
        while j < 4 {
            if i + j > 3 {
                break 'outer;
            }
            s += j;
            j += 1;
        }
        i += 1;
    }

    s + i
}

pub fn continue_outer(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        i += 1;

        let mut j = 0;
        while j < 3 {
            j += 1;
            if j == 2 {
                continue 'outer;
            }
            s += j;
        }

        s += 10;
    }

    s
}

pub fn return_nested(max: u32) -> u32 {
    let mut i = 0;
    while i < max {
        let mut j = 0;
        while j < 4 {
            if i + j > 2 {
                return i + j;
            }
            j += 1;
        }
        i += 1;
    }

    max
}

pub fn normal_and_outer_break(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        let mut j = 0;
        while j < 4 {
            if i == 3 {
                break 'outer;
            }
            if j == 2 {
                break;
            }
            s += i + j;
            j += 1;
        }
        i += 1;
    }

    s
}

pub fn outer_continue_feeds_fixed_point(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        let mut j = 0;
        while j < 2 {
            s += i + j;
            j += 1;

            if s < max {
                i += 1;
                continue 'outer;
            }
        }

        s += 100;
        i += 1;
    }

    s
}

pub fn break_outer_array_update(mut values: [usize; 4]) -> [usize; 4] {
    let mut i = 0;

    'outer: while i < 4 {
        let mut j = 0;
        while j < 4 {
            values[j] = i + j;
            if j == 2 {
                break 'outer;
            }
            j += 1;
        }
        i += 1;
    }

    values
}

pub fn continue_outer_array_update(mut values: [usize; 4]) -> [usize; 4] {
    let mut i = 0;

    'outer: while i < 4 {
        let mut j = 0;
        while j < 4 {
            values[j] = i + j;
            j += 1;

            if values[0] < 8 {
                i += 1;
                continue 'outer;
            }
        }

        values[0] = i;
        i += 1;
    }

    values
}

pub fn return_nested_mut_borrow(value: &mut u32, max: u32) -> u32 {
    let mut i = 0;
    while i < max {
        let mut j = 0;
        while j < 4 {
            let value_borrow = &mut *value;
            *value_borrow += i + j;

            if *value_borrow > max {
                return *value_borrow;
            }

            j += 1;
        }

        i += 1;
    }

    *value
}

pub fn concrete_break_outer_unit() {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < 3 {
        let mut j = 0;
        while j < 3 {
            s += 1;
            if j == 1 {
                break 'outer;
            }
            j += 1;
        }
        i += 1;
    }

    assert!(i == 0);
    assert!(s == 2);
}

pub fn concrete_continue_outer_unit() {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < 3 {
        i += 1;

        let mut j = 0;
        while j < 2 {
            j += 1;
            if j == 1 {
                continue 'outer;
            }
            s += 100;
        }

        s += 10;
    }

    assert!(i == 3);
    assert!(s == 0);
}
