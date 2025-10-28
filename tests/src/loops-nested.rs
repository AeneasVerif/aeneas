//@ [!lean] skip

pub fn iter(m: u32, n: u32) {
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            j += 1;
        }
        i += 1;
    }
}

pub fn sum(m: u32, n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            s += 1;
            j += 1;
        }
        i += 1;
    }
    s
}

/// This is adapted from [https://github.com/microsoft/SymCrypt/]
/// Updating the same array in the inner and outer loops.
fn update_array() {
    let mut out = [0u8; 4];

    let mut i = 0usize;
    while i < 4 {
        out[i] = 0;
        let mut j = 0usize;
        while j < 4 {
            out[j] = 1;
            j += 1;
        }
        i += 1;
    }
}

const FACTORS: [u16; 32] = [
    2285, 2571, 2970, 1812, 1493, 1422, 287, 202, 3158, 622, 1577, 182, 962, 2127, 1855, 1468, 573,
    2004, 264, 383, 2500, 1458, 1727, 3199, 2648, 1017, 732, 608, 1787, 411, 3124, 1758,
];

fn mod_add(a: u32, b: u32) -> u32 {
    (a + b) % 3329
}

fn mod_sub(a: u32, b: u32) -> u32 {
    ((a + 3329) - (b % 3329)) % 3329
}

/// This is adapted from [https://github.com/microsoft/SymCrypt/]
fn ntt_layer(a: &mut [u16; 256], mut k: usize, len: usize) {
    let mut start = 0usize;
    while start < 256 {
        let factor: u32 = FACTORS[k].into();
        k += 1;

        let mut j = 0usize;
        while j < len {
            let mut c0: u32 = a[start + j].into();
            let mut c1: u32 = a[start + j + len].into();

            let c1_factor: u32 = c1 * factor;
            c1 = mod_sub(c0, c1_factor);
            c0 = mod_add(c0, c1_factor);

            a[start + j] = c0 as u16;
            a[start + j + len] = c1 as u16;

            j += 1;
        }
        start += 2 * len;
    }
}

struct Key {
    seed: [u8; 32],
    atranspose: [u16; 32],
}

impl Key {
    fn atranspose_mut(&mut self) -> &mut [u16; 32] {
        &mut self.atranspose
    }
}

type HashState = [u8; 8];

fn shake_init(_state: &mut HashState) {}
fn shake_append(_state: &mut HashState, _data: &[u8]) {}
fn shake_state_copy(_src: &HashState, _dst: &mut HashState) {}
fn sample_ntt(_state: &mut HashState, _dst: &mut u16) {}

/// This is adapted from [https://github.com/microsoft/SymCrypt/]
fn generate_matrix_inner(key: &mut Key, state: &mut HashState) {
    let mut j = 0usize;
    while j < 4 {
        let a_transpose = key.atranspose_mut();
        sample_ntt(state, &mut a_transpose[j]);
        j += 1;
    }
}

/// This is adapted from [https://github.com/microsoft/SymCrypt/]
fn generate_matrix(key: &mut Key, state_base: &mut HashState, state_work: &mut HashState) {
    let mut coordinates = [0u8; 2];
    let n_rows = 4;

    shake_init(state_base);
    shake_append(state_base, &key.seed);

    let mut i = 0u8;
    while i < n_rows {
        coordinates[1] = i;
        let mut j = 0u8;
        while j < n_rows {
            coordinates[0] = j;
            shake_state_copy(state_base, state_work);
            shake_append(state_work, &coordinates);

            let a_transpose = key.atranspose_mut();
            sample_ntt(state_work, &mut a_transpose[(i * n_rows + j) as usize]);
            j += 1;
        }
        i += 1;
    }
}
