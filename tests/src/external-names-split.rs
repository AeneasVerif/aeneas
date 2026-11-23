//@ charon-args=--opaque=external_names_split::Counter --opaque=external_names_split::incr
//@ [!lean] skip
//@ [lean] subdir=ExternalNamesSplit
//@ [lean] aeneas-args=-split-files -external-names tests/external-names/external-names-split.json -extra-includes=ExternalNamesModel
//! Checks that opaque items mapped through `-external-names` need no
//! hand-written model from the user: with `-split-files`, an opaque type or
//! function produces a `TypesExternal_Template` or `FunsExternal_Template` file,
//! and none must be generated here since both opaque items are mapped.

struct Counter {
    n: u32,
}

fn incr(c: Counter) -> Counter {
    Counter { n: c.n + 1 }
}

fn incr_twice(c: Counter) -> Counter {
    incr(incr(c))
}
