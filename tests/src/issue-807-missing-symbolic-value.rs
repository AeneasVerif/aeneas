//@ [!lean] skip
// Issue: https://github.com/AeneasVerif/aeneas/issues/807

struct PortableVector {
    elements: [u8; 16],
}
fn to_bytes(x: PortableVector, bytes: &mut [u8]) {
    for i in 0..16 {
        bytes[2 * i] = x.elements[i];
    }
}
