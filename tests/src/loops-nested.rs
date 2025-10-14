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

const FACTORS: [u16; 32] = [
    2285, 2571, 2970, 1812, 1493, 1422,  287,  202,
    3158,  622, 1577,  182,  962, 2127, 1855, 1468,
     573, 2004,  264,  383, 2500, 1458, 1727, 3199,
    2648, 1017,  732,  608, 1787,  411, 3124, 1758,
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
            let mut c0: u32 = a[start+j].into();
            let mut c1: u32 = a[start+j+len].into();

            let c1_factor: u32 = c1 * factor;
            c1 = mod_sub(c0, c1_factor);
            c0 = mod_add(c0, c1_factor);

            a[start+j]      = c0 as u16;
            a[start+j+len]  = c1 as u16;

            j += 1;
        }
        start += 2*len;
    }
}
