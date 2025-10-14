//@ [coq] aeneas-args=-use-fuel
//@ [fstar] aeneas-args=-decreases-clauses
//@ [fstar] aeneas-args=-split-files
//@ [coq,fstar] subdir=misc

pub fn iter(max: u32) -> u32 {
    let mut i = 0;
    while i < max {
        i += 1;
    }

    i
}
