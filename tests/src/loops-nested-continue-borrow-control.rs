//@ [lean] known-failure
//@ [!lean] skip

// Isolated from loops-nested-control.rs so this borrow-sensitive propagated
// continue case has its own known-failure boundary.
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
