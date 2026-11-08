//@ [!lean] skip
//@ [lean] aeneas-args=-split-files
//@ [lean] subdir=IoErrorNew

// Exercise the standard-library signatures containing `Box<dyn Error>`.
pub fn make_invalid_data(text: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, text)
}

// Exercise a trait object inside a mutable-borrow signature.
pub fn touch_dyn_error(_error: &mut dyn std::error::Error) {}
