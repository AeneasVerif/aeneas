//@ [!lean] skip
//@ [lean] known-failure
// A higher-ranked trait bound whose *implied bounds* relate a locally-bound
// (higher-ranked) lifetime to a free lifetime is rejected: Aeneas erases
// regions and cannot model such a constraint.
//
// Here the constraint comes from a *borrow*: in `&'a &'b u8` the lifetime `'a`
// of the outer borrow must be shorter than the lifetimes appearing in the
// referent, i.e. `'b: 'a`. Under `for<'a>` this relates the bound `'a` to the
// free `'b` - with no ADT involved.

trait RefTrait<X> {
    fn get(&self) -> X;
}

fn borrow_outlive<'b, P>(_p: &'b P)
where
    P: for<'a> RefTrait<&'a &'b u8>,
{
}
