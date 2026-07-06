//@ [!lean] skip
//@ [lean] known-failure
// A higher-ranked trait bound whose *implied bounds* relate a locally-bound
// (higher-ranked) lifetime to a free lifetime is rejected: Aeneas erases
// regions and cannot model such a constraint.
//
// Here the constraint comes from a *type-outlives* predicate: `Holder<'a, T: 'a>`
// used as `Holder<'a, &'b u8>` implies `&'b u8: 'a`, i.e. `'b: 'a`, so under
// `for<'a>` this relates the bound `'a` to the free `'b`.

trait RefTrait<X> {
    fn get(&self) -> X;
}

struct Holder<'a, T: 'a> {
    x: &'a T,
}

fn types_outlive<'b, P>(_p: &'b P)
where
    P: for<'a> RefTrait<Holder<'a, &'b u8>>,
{
}
