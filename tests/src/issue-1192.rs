//@ [!borrow-check] skip

pub fn zip_iter_mut_after_zip_iter(inputs: &mut [u64], scratch: &mut [u64]) {
    for _ in inputs.iter().zip(scratch.iter()) {}
    for _ in inputs.iter_mut().zip(scratch.iter_mut()) {}
}
