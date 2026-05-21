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

pub fn continue_two_levels(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        let mut j = 0;
        while j < 2 {
            let mut k = 0;
            while k < 2 {
                s += i + j + k;
                i += 1;
                continue 'outer;
            }
            j += 1;
        }

        s += 100;
        i += 1;
    }

    s
}

pub fn return_two_levels(max: u32) -> u32 {
    let mut i = 0;

    while i < max {
        let mut j = 0;
        while j < 3 {
            let mut k = 0;
            while k < 3 {
                if i + j + k > 3 {
                    return i + j + k;
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }

    max
}

pub fn break_two_depths_same_loop(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < 3 {
        let mut j = 0;
        'middle: while j < 3 {
            let mut k = 0;
            while k < 3 {
                if max == 0 {
                    break 'middle;
                }
                if max == 1 {
                    break 'outer;
                }
                s += i + j + k;
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }

    s + i
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

pub fn concrete_return_unit_nested(flag: bool) {
    let mut i = 0;

    while i < 2 {
        let mut j = 0;
        while j < 2 {
            if flag && j == 0 {
                return;
            }
            j += 1;
        }
        i += 1;
    }

    assert!(i == 2);
}
