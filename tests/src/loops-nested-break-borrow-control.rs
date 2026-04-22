//@ [lean] known-failure
//@ [!lean] skip

// Isolated from loops-nested-control.rs so this borrow-sensitive propagated
// break case has its own known-failure boundary.
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
