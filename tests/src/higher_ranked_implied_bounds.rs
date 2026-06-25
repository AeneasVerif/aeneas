//@ [!lean] skip
//@ [lean] known-failure
// A higher-ranked trait bound whose *implied bounds* relate a locally-bound
// (higher-ranked) lifetime to a free lifetime is rejected: Aeneas erases
// regions and cannot model such a constraint.

trait RefTrait<X> {
    fn get(&self) -> X;
}

// `Pair<'a, 'b: 'a>` implies `'b: 'a`. Under `for<'a>` this relates the bound
// `'a` to the free `'b` (through a region-outlives constraint).
struct Pair<'a, 'b: 'a> {
    x: &'a u8,
    y: &'b u8,
}

fn regions_outlive<'b, P>(_p: &'b P)
where
    P: for<'a> RefTrait<Pair<'a, 'b>>,
{
}

// `Holder<'a, T: 'a>` used as `Holder<'a, &'b u8>` implies `&'b u8: 'a`, i.e.
// `'b: 'a` (through a type-outlives constraint).
struct Holder<'a, T: 'a> {
    x: &'a T,
}

fn types_outlive<'b, P>(_p: &'b P)
where
    P: for<'a> RefTrait<Holder<'a, &'b u8>>,
{
}
