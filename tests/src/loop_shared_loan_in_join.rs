//@ [!lean] skip
//! Regression test: when joining a loop fixed-point context with the
//! continue context, a shared loan wrapping the data field caused the
//! left/right values to be swapped in the join's `symbolic_to_value`
//! map. As a result the loop's Continue passed the *original* data
//! instead of the potentially-transformed data.
//!
//! The bug only triggers when:
//! 1. A struct has "extra" constant fields (padding, flag) causing it
//!    to be decomposed into individual loop parameters,
//! 2. A field (data) is conditionally mutated inside a for-loop,
//! 3. The mutated field is read via a shared borrow (array index)
//!    within the same iteration, creating a shared loan that is live
//!    at the Continue point.

pub struct State {
    pub data: [u64; 4],
    pub index: u32,
    pub limit: u32,
    pub padding: u8,
    pub flag: bool,
}

fn transform(data: &mut [u64; 4]) {
    for i in 0..4 {
        data[i] = data[i].wrapping_add(1);
    }
}

impl State {
    pub fn extract(&mut self, result: &mut [u64], count: usize) {
        let mut lane_index: usize = self.index as usize;
        for i in 0usize..count {
            if self.index == self.limit {
                transform(&mut self.data);
                self.index = 0;
                lane_index = 0;
            }
            result[i] = self.data[lane_index];
            self.index += 1;
            lane_index += 1;
        }
    }
}
