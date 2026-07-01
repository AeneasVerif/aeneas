#[allow(dead_code)]
mod basic {
    use hax_lib::*;

    #[requires(x < 100)]
    fn only_requires(x: u32) -> u32 {
        x + 1
    }

    #[ensures(|result| result == x)]
    fn only_ensures(x: u32) -> u32 {
        x
    }

    #[requires(x < 10)]
    #[ensures(|result| result > x)]
    fn both(x: u32) -> u32 {
        x + 1
    }

    // No arguments
    #[ensures(|_| true)]
    fn no_args() {
        let _x = 0;
        ()
    }

    // Unit return with a by-value argument
    #[requires(x < 10)]
    #[ensures(|_| true)]
    fn returns_unit(x: u32) {}

    // Block expression (with a `let`) inside `requires`
    #[requires({ let bound = x; bound > 10 })]
    fn block_in_requires(x: u32) -> u32 {
        x
    }

    // Pattern directly in the result closure
    #[ensures(|(a, b)| a == x && b == x)]
    fn returns_pair(x: u32) -> (u32, u32) {
        (x, x)
    }
}

#[allow(dead_code)]
mod extra_args {
    use hax_lib::*;

    // Const generic params
    #[requires(0 < x && x < N)]
    #[ensures(|result| result < N)]
    fn generic<const N: u32>(x: u32) -> u32 {
        N - x
    }

    // Trait params
    trait Val {
        fn value(&self) -> u32;
    }

    impl Val for u32 {
        fn value(&self) -> u32 {
            *self
        }
    }

    #[requires(t.value() < 1000 && x < 1000)]
    #[ensures(|result| result < 2000)]
    fn traits<T: Val>(t: T, x: u32) -> u32 {
        t.value() + x
    }
}

#[allow(dead_code)]
mod future {
    use hax_lib::*;

    #[requires(*x < 1000)]
    #[ensures(|_| *future(x) == *x + 1 )]
    fn incr(x: &mut u32) {
        *x += 1;
    }

    #[requires(i < x.len())]
    #[ensures(|_| {
            let r = future(x);
            r[i] == x[i] + 1})]
    fn incr_i(x: &mut [u32], i: usize) {
        x[i] += 1
    }

    #[requires(*x < 1000 && *y < 1000)]
    #[ensures(|r| { *future(y) == *x && *future(x) == *y && r == x + y})]
    fn swap_and_add(x: &mut u32, y: &mut u32) -> u32 {
        let tmp_x = *x;
        let tmp_y = *y;
        *x = tmp_y;
        *y = tmp_x;
        tmp_x + tmp_y
    }
}
