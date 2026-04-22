//@ [lean] known-failure
//@ [!lean] skip

// Three-level nest for focused depth-arithmetic coverage: the innermost loop
// exits two loop boundaries, so synthesis must emit PropagatedBreak 1.
pub fn break_two_levels(max: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;

    'outer: while i < max {
        let mut j = 0;
        while j < 3 {
            let mut k = 0;
            while k < 3 {
                if i + j + k > 3 {
                    break 'outer;
                }
                s += k;
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }

    s + i
}
