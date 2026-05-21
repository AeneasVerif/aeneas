//@ [lean] aeneas-args=-loops-to-rec
//@ [!lean] skip

pub fn rec_break_outer(max: u32) -> u32 {
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

pub fn rec_continue_outer(max: u32) -> u32 {
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

pub fn rec_return_nested(max: u32) -> u32 {
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

pub fn rec_break_outer_array_update(mut values: [usize; 4]) -> [usize; 4] {
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
