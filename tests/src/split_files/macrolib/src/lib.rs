//! A separate crate exporting a `macro_rules!` macro, so that `split_files` can
//! exercise items that are local to the crate under extraction but whose spans
//! point into *this* file. See `../../src/viamacro.rs`.

#[macro_export]
macro_rules! define_counter {
    ($name:ident) => {
        pub struct $name {
            pub value: u32,
        }

        impl $name {
            pub fn bump(&mut self) {
                self.value += 1;
            }
        }
    };
}
