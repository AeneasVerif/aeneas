//@ [!lean] skip

pub fn continue_outer_only(max: u32) -> u32 {
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

pub fn continue_outer_feeds_fixed_point(max: u32) -> u32 {
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
