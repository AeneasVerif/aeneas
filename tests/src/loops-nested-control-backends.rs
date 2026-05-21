//@ [coq,fstar] subdir=misc

pub fn backend_break_outer(max: u32) -> u32 {
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

pub fn backend_continue_outer(max: u32) -> u32 {
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

pub fn backend_return_nested(max: u32) -> u32 {
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

pub fn backend_break_two_depths(max: u32) -> u32 {
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
