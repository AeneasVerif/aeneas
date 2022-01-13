* write an interesting example to study with Jonathan

* update the assignment to move the destination value (which will be overriden)
  to a dummy variable, and end all the outer borrows.
  update pop_frame

* add option for: `allow_borrow_overwrites_on_input_values`
  (but always disallow borrow overwrites on returned values)
  at the level of abstractions (not at the level of loans!)

* set of types with mutable borrows (what to do when type variables appear under
  shared borrows?)

* split `apply_proj_borrows` into two:
  * `apply_proj_borrows_on_input_values` : ... -> value -> rty -> avalue
  * `apply_proj_borrows_on_given_back_values` : ... -> value -> avalue -> avalue
  TODO: actually not sure

* remove the rule which says that we can end a borrow under an abstraction if
  the corresponding loan is in the same abstraction.

* Check what happens when symbolic borrows are not expanded (when looking for
  borrows/abstractions to end).

* Reduce projectors to `_` (ignored) when there are no region intersections

* update end_borrow_get_borrow to keep track of the ignored borrows/loans as
  outer borrows, and track the ids of the ignored shared loans?
  or: make sure there are no parent abstractions when ending inner loans in
  abstractions.

* expand symbolic values which are primitively copyable upon using them as
  function arguments or putting them in the return value, in order to deduplicate
  those values.

* invariant: if a symbolic value is present multiple times in the concrete environment,
  it means it is primitively copyable
  
* invariant: if there is a `proj_loans rset1 (s:rty)` where `s` contains mutable
  borrows, then:
  * either there is exactly one `s` in the current context
  * or there is exactly one `proj_borrows rset2 (s:rty<:rty')` which intersects
    the `proj_loans ...`
  However, one `proj_borrows s` may intersect several `proj_loans` (in which
  case we will need to split the value given back - for now: disallow this
  behaviour?).

* `ended_proj_loans` (with ghost value)

* add a check in function inputs: ok to take as parameters symbolic values with
  borrow parameters *if* they come from the "input abstractions"

* make the projected shared borrows more structured? I don't think that's necessary

* Detect loops in end_borrow/end_abstraction

* add a `allow_borrow_overwrites` in the loan projectors.

* During printing, contexts are often big, with many variables containing "bottom".
  Some variables also actually never get assigned, especially when they are used
  for auxiliary assignments which don't exist anymore (because they were merged
  with other operations - for arithmetic operations, for instance).
  Maybe we should register which variable has been assigned at least once, and
  print only those (thus skipping a big part of the environment for some time).

* Some variables have the same name. It might be good to also print their id
  to disambiguate?
