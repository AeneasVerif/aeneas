# TODO

0. Priority:
  * update treatment of matches
  * remove prepass
  * update pure expressions
  * update control-flow reconstruction (Charon)

0. Improve treatments of error and state error monads. In particular, introduce
   `return` and `fail`, and remove `Return` and `Fail`.

0. replace all the `failwith` with `raise (Failure ...)`: in CPS, it messes
   up with provenance tracking

0. In SymbolicToPure we do a few simplifications on types and values (simplification
   of box type, removal of tuples which contain exactly one field - some fields
   may have been filtered for the backward functions...): there are already a
   few sanity checks, but we may to add more of them, which would type check
   entire expressions for instance.

0. merge the "read determinant" and the "switch" occurrences to "match"

0. reaggregate the ADTs

0. when going from symbolic to pure, remove the useless tuples (as some fields
   might be erased).

0. Update the high-level comments, in particular in Values.ml

0. Rename Pure -> PureAst

0. For variables pretty names: we could try to use the meta places used for the
   forward function input vars to compute pretty names for the backward functions
   output vars.

0. sanity checks in symbolic to pure!

0. update the end borrows internal to abstractions to not introduce a Bottom

0. remove AConcrete from avalue

0. remove ABottom from avalue

0. micro-passes for pure:
   - remove unused variables
   - remove useless function calls:
     - calls which don't introduce values *if* they are followed by associated
       backward calls (because they may panic!)
     - calls which don't take inputs (can happen with backward functions - for
       instance, if a rust function only returns shared borrows)
   - monadic lets to matches
   - no tuple deconstruction on returned monadic values (introduce intermediate
     variables to deconstruct in two times)
   - matching on values (ex.: `let Cons hd tl = ls in` ~~>
     `match ls with | Nil -> Panic | Cons hd tl -> ...`)

1. reorder the branches of matches

1. stateful maps/sets modules (hashtbl?)

1. Check the occurrence of visitors like visit_AEndedMutLoan: the parameters are
   sometimes inverted!

2. check types are not "infinite"

3. in MIR, erased regions are completely erased (no list of erased regions...):
  update functions like `ty_has_regions` (and rename to `ty_has_borrows`),
  `erase_regions`

4. check that no borrow_overwrites upon ending abstractions

5. add a check in function inputs: ok to take as parameters symbolic values with
  borrow parameters *if* they come from the "input abstractions".
  In order to do this, add a symbolic value kind (would make things easier than
  adding ad-hoc lookups...): `FunRet`, `FunGivenBack`, `SynthInput`, `SynthGivenBack`
  Rk.: pay attention: we can't give borrows of borrows to functions, but borrows
  are ok.

6. add `mvalue` (meta values) stored in abstractions when ending loans

8. The following doesn't work:
  ```
  fn f1<'c, T>(p : (&'c mut T, &'c mut T)) -> (&'c mut T, &'c mut T)

  fn f2<'a, 'b, T>(p: (&'a mut T, &'b mut T)) -> (&'a mut T, &'b mut T)

  let p1 = f1<'c>(p0);
  let p2 = f2<'a, 'b>(p1);
  ```
  (end borrows)
  I think we should change the proj_loans to:
  `AProjLoans of symbolic_value * (mvalue * aproj) list`
  (to accumulate the given back values)
  Then, once we collected all the borrows, we would convert it to:
  `AEndedProjLoans of (mvalue * aproj) list`
  If the list is empty, it means the value was not modified.

9. The way we currently give back symbolic values to symbolic values (inside
   abstractions) is wrong.
   We get things like :
   `AProjLoans (s0 <: &'a mut T) [AProjBorrows (s1 <: &'a mut T)]`
   while in the case of `s1` we should ignore the outer borrow (what we give
   back actually has type `T`...)
  
10. Write "bodies" for the assumed functions.

* write a function to check that the code we are about to synthesize is in the proper
  subset. In particular:
  * borrow overwrites
  * type parameters instantiation
  * uniform polymorphism
  Also, write nice debug messages which refer to the original code in case
  something fails.
* write an interesting example to study with Jonathan

* add option for: `allow_borrow_overwrites_on_input_values`
  (rather: `will_overwrite_input_borrows`)
  (but always disallow borrow overwrites on returned values)
  at the level of abstractions (not at the level of loans!)

* invariant: if there is a `proj_loans rset1 (s:rty)` where `s` contains mutable
  borrows, then:
  * either there is exactly one `s` in the current context
  * or there is exactly one `proj_borrows rset2 (s:rty<:rty')` which intersects
    the `proj_loans ...`
  However, one `proj_borrows s` may intersect several `proj_loans` (in which
  case we will need to split the value given back - for now: disallow this
  behaviour?).

* remove the rule which says that we can end a borrow under an abstraction if
  the corresponding loan is in the same abstraction.
  Actually: update the rule, rather.

* update end_borrow_get_borrow to keep track of the ignored borrows/loans as
  outer borrows, and track the ids of the ignored shared loans?
  or: make sure there are no parent abstractions when ending inner loans in
  abstractions.

* `ended_proj_loans` (with ghost value)

* make the projected shared borrows more structured? I don't think that's necessary

* add a `allow_borrow_overwrites` in the loan projectors.

* During printing, contexts are often big, with many variables containing "bottom".
  Some variables also actually never get assigned, especially when they are used
  for auxiliary assignments which don't exist anymore (because they were merged
  with other operations - for arithmetic operations, for instance).
  Maybe we should register which variable has been assigned at least once, and
  print only those (thus skipping a big part of the environment for some time).

* Some variables have the same name. It might be good to also print their id
  to disambiguate?

* it would be good to find a "core", which implements the rules (like
  "end_borrow") and on top of which we build more complex functions which
  chose in which order to apply the rules, etc. This way we would make very
  explicit where we need to insert sanity checks, what the preconditions are,
  where invariants might be broken, etc.

* intensively test with PLT-redex

* remove the config parameters when they are useless

# DONE

* update the assignment to move the destination value (which will be overriden)
  to a dummy variable, and end all the outer borrows.
  Also update pop_frame.

* Check what happens when symbolic borrows are not expanded (when looking for
  borrows/abstractions to end).

* Detect loops in end_borrow/end_abstraction

* recheck give_back_symbolic_value (use regions!)

* expand symbolic values which are primitively copyable upon using them as
  function arguments or putting them in the return value, in order to deduplicate
  those values.
  Completion: we expand those values only upon copying them (that's enough).

* invariant: if a symbolic value is present multiple times in the concrete environment,
  it means it is primitively copyable

* update the printing of mut_borrows and mut_loans ([s@0 <: ...]) and (s@0)

* add a switch to allow general symbolic values (containing references, etc.)
  or not.

* split `apply_proj_borrows` into two:
  * `apply_proj_borrows_on_input_values` : ... -> value -> rty -> avalue
  * `apply_proj_borrows_on_given_back_values` : ... -> value -> avalue -> avalue
  Actually: didn't do it: bad idea.

* Reduce projectors to `_` (ignored) when there are no region intersections

* Add a `Collections.ml` file, with `Map` and `Set`

* improve the use of [comp] for composition of functions with continuations

* derive [ord] for types

* compute the region constraints for the type definitions

* set of types with mutable borrows (what to do when type variables appear under
  shared borrows?), nested borrows...
  necessary to know what to return.

* fix the static regions (with projectors)
  Before that, introduce a sanity check to make sure we don't use static regions.

* add a meta-value in shared borrows to carry the shared value
