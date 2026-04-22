//@ [!lean] skip

// Isolated from loops-nested-control.rs so this borrow-sensitive propagated
// return case has its own known-failure boundary.
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

            if j == 2 {
                break;
            }
            j += 1;
        }

        i += 1;
    }

    *value
}
