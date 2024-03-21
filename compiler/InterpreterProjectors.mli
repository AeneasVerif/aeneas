open Types
open Values
open Contexts

(** Auxiliary function.

    Apply a proj_borrows on a shared borrow.
    Note that when projecting over shared values, we generate
    {!type:Aeneas.Values.abstract_shared_borrows}, not {!type:Aeneas.Values.avalue}s.

    Parameters:
    [regions]
    [ancestor_regions]
    [see]
    [original_sv_ty]: shouldn't have erased regions
*)
val apply_proj_loans_on_symbolic_expansion :
  Meta.meta -> RegionId.Set.t -> RegionId.Set.t -> symbolic_expansion -> rty -> typed_avalue

(** Convert a symbolic expansion *which is not a borrow* to a value *)
val symbolic_expansion_non_borrow_to_value :
  Meta.meta -> symbolic_value -> symbolic_expansion -> typed_value

(** Convert a symbolic expansion *which is not a shared borrow* to a value.

    If the expansion is a mutable reference expansion, it converts it to a borrow.
    This function is meant to be used when reducing projectors over borrows,
    during a symbolic expansion.
  *)
val symbolic_expansion_non_shared_borrow_to_value :
 Meta.meta -> symbolic_value -> symbolic_expansion -> typed_value

(** Auxiliary function to prepare reborrowing operations (used when
    applying projectors).

    Returns two functions:
    - a function to generate fresh re-borrow ids, and register the reborrows
    - a function to apply the reborrows in a context
    Those functions are of course stateful.

    Parameters:
    - [config]
    - [allow_reborrows]
 *)
val prepare_reborrows :
  Meta.meta -> config -> bool -> (BorrowId.id -> BorrowId.id) * (eval_ctx -> eval_ctx)

(** Apply (and reduce) a projector over borrows to an avalue.
    We use this for instance to spread the borrows present in the inputs
    of a function into the regions introduced for this function. For instance:
    {[
      fn f<'a, 'b, T>(x: &'a T, y: &'b T)
    ]}
    If we call `f` with `x -> shared_borrow l0` and `y -> shared_borrow l1`, then
    for the region introduced for `'a` we need to project the value for `x` to
    a shared aborrow, and we need to ignore the borrow in `y`, because it belongs
    to the other region.

    Parameters:
    - [check_symbolic_no_ended]: controls whether we check or not whether
      symbolic values don't contain already ended regions.
      This check is activated when applying projectors upon calling a function
      (because we need to check that function arguments don't contain ⊥),
      but deactivated when expanding symbolic values:
      {[
        fn f<'a,'b>(x : &'a mut u32, y : &'b mut u32) -> (&'a mut u32, &'b mut u32);

        let p = f(&mut x, &mut y); // p -> @s0
        assert(x == ...); // end 'a
        let z = p.1; // HERE: the symbolic expansion of @s0 contains ended regions
      ]}
    - [ctx]

    - [fresh_reborrow]: a function which generates fresh ids for reborrows, and
      registers the reborrows (to be applied later to the context).

      When applying projections on shared values, we need to apply
      reborrows. This is a bit annoying because, with the way we compute
      the projection on borrows, we can't update the context immediately.
      Instead, we remember the list of borrows we have to insert in the
      context *afterwards*.

      See {!prepare_reborrows}

    - [regions]: the regions to project
    - [ancestor_regions]
    - [v]: the value on which to apply the projection

    - [ty]: the projection type (is used to map borrows to regions, or in other
      words to interpret the borrows as belonging to some regions). Remember that
      [v] doesn't contain region information.
      For instance, if we have:
      [v <: ty] where:
      - [v = mut_borrow l ...]
      - [ty = Ref (r, ...)]
      then we interpret the borrow [l] as belonging to region [r]
*)
val apply_proj_borrows :
  Meta.meta ->
  bool ->
  eval_ctx ->
  (BorrowId.id -> BorrowId.id) ->
  RegionId.Set.t ->
  RegionId.Set.t ->
  typed_value ->
  rty ->
  typed_avalue

(** Parameters:
    - [config]
    - [ctx]
    - [regions]: the regions to project
    - [ancestors_regions]
    - [v]: the value on which to apply the projection
    - [ty]: the type (with regions) to use for the projection (shouldn't have
      erased regions)
 *)
val apply_proj_borrows_on_input_value :
  Meta.meta ->
  config ->
  eval_ctx ->
  RegionId.Set.t ->
  RegionId.Set.t ->
  typed_value ->
  rty ->
  eval_ctx * typed_avalue
