//@ [!lean] skip
//@ [lean] aeneas-args=-split-files
//@ [lean] subdir=IoErrorNew

// Exercise the standard-library signatures containing `Box<dyn Error>`.
pub fn make_invalid_data(text: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, text)
}
