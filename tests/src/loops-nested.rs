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
