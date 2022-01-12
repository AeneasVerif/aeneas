* update assign_to_place: problem with the value to assign which is hanging in
  the air.
  Maybe: push it to a dummy variable?...
  TODO: x = move x where x contains borrows.
  I think we should move the operands to specific "temporary" variables.

* Check what happens when symbolic borrows are not expanded (when looking for
  borrows/abstractions to end).

* Detect loops in end_borrow/end_abstraction

* split `apply_proj_borrows` into two:
  * `apply_proj_borrows_on_input_values` : ... -> value -> rty -> avalue
  * `apply_proj_borrows_on_given_back_values` : ... -> value -> avalue -> avalue

* remove the rule which says that we can end a borrow under an abstraction if
  the corresponding loan is in the same abstraction

* During printing, contexts are often big, with many variables containing "bottom".
  Some variables also actually never get assigned, especially when they are used
  for auxiliary assignments which don't exist anymore (because they were merged
  with other operations - for arithmetic operations, for instance).
  Maybe we should register which variable has been assigned at least once, and
  print only those (thus skipping a big part of the environment for some time).

* Some variables have the same name. It might be good to also print their id
  to disambiguate?
