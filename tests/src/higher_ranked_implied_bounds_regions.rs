//@ [!lean] skip
//@ [lean] known-failure
// A higher-ranked trait bound whose *implied bounds* relate a locally-bound
// (higher-ranked) lifetime to a free lifetime is rejected: Aeneas erases
// regions and cannot model such a constraint.
//
// Here the constraint comes from a *region-outlives* predicate: `Pair<'a, 'b: 'a>`
// implies `'b: 'a`, so under `for<'a>` this relates the bound `'a` to the free `'b`.

trait RefTrait<X> {
    fn get(&self) -> X;
}

struct Pair<'a, 'b: 'a> {
    x: &'a u8,
    y: &'b u8,
}

fn regions_outlive<'b, P>(_p: &'b P)
where
    P: for<'a> RefTrait<Pair<'a, 'b>>,
{
}
