open Types
open Values
open Contexts

(** Turn a value into a abstractions.

    We are conservative, and don't group borrows/loans into the same abstraction
    unless necessary.

    For instance:
    {[
      _ -> (mut_borrow l1 (mut_loan l2), mut_borrow l3)

      ~~>

      abs'0 { mut_borrow l1, mut_loan l2 }
      abs'1 { mut_borrow l3 }
    ]}

    Parameters:
    - [abs_kind]
    - [can_end]
    - [destructure_shared_values]: this is similar to
      [destructure_shared_values] for {!destructure_abs}.
    - [ctx]
    - [v] *)
val convert_value_to_abstractions :
  Meta.span ->
  abs_kind ->
  can_end:bool ->
  destructure_shared_values:bool ->
  eval_ctx ->
  tvalue ->
  abs list

(** See {!merge_into_abstraction}.

    Rem.: it may be more idiomatic to have a functor, but this seems a bit
    heavyweight, though. *)
type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    tavalue ->
    rty ->
    proj_marker ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [sid0]
          - [ty1]
          - [pm1]
          - [sid1] *)
  merge_amut_loans :
    loan_id ->
    rty ->
    proj_marker ->
    tavalue ->
    rty ->
    proj_marker ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_loans :
    loan_id ->
    rty ->
    proj_marker ->
    tvalue ->
    tavalue ->
    rty ->
    proj_marker ->
    tvalue ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [pm0]
          - [sv0]
          - [child0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [child1] *)
  merge_aborrow_projs :
    ty ->
    proj_marker ->
    aproj_borrows ->
    ty ->
    proj_marker ->
    aproj_borrows ->
    tavalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [loans0]
          - [ty1]
          - [pm1]
          - [proj1]
          - [loans1] *)
  merge_aloan_projs :
    ty ->
    proj_marker ->
    aproj_loans ->
    ty ->
    proj_marker ->
    aproj_loans ->
    tavalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [consumed0]
          - [borrows0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [proj_ty1]
          - [children1] *)
}

(** Merge an abstraction into another abstraction.

    We insert the result of the merge in place of the first abstraction (and in
    particular, we don't simply push the merged abstraction at the end of the
    environment: this helps preserving the structure of the environment, when
    computing loop fixed points for instance).

    When we merge two abstractions together, we remove the loans which appear in
    the *left* abstraction and whose corresponding borrows appear in the
    **right** abstraction. For instance:
    {[
      abs'0 { mut_borrow l0, mut_loan l1 }   // Rem.: mut_loan l1
      abs'1 { mut_borrow l1, mut_borrow l2 } // Rem.: mut_borrow l1

          ~~>

      abs'2 { mut_borrow l0, mut_borrow l2 }
    ]}

    We also simplify the markers, when the same value appears in both
    abstractions but with different markers. For instance:
    {[
      abs'0 { |mut_borrow l0|, mut_loan l1 }
      abs'1 { ︙mut_borrow l0︙, mut_borrow l1 }

          ~~>

      abs'2 { mut_borrow l0 }
    ]}

    Finally, we merge all their regions together. For instance, if [abs'0]
    projects region [r0] and [abs'1] projects region [r1], we pick one of the
    two, say [r0] (the one with the smallest index in practice) and substitute
    [r1] with [r0] in the whole context.

    Parameters:
    - [kind]
    - [can_end]
    - [merge_funs]: those functions are used to merge borrows/loans with the
      *same ids* but different markers. This is necessary when doing a collapse
      (see the computation of joins). If [merge_funs] are not provided, we check
      that there are no markers.
    - [ctx]
    - [abs_id0]
    - [abs_id1]

    We return the updated context as well as the id of the new abstraction which
    results from the merge. *)
val merge_into_first_abstraction :
  Meta.span ->
  abs_kind ->
  bool ->
  merge_duplicates_funcs option ->
  eval_ctx ->
  AbstractionId.id ->
  AbstractionId.id ->
  eval_ctx * AbstractionId.id

(** Reorder the fresh abstractions, as well as the loans and borrows inside
    them.

    We do this in order to enforce some structure in the environments: this
    allows us to find fixed-points. Note that this function needs to be called
    typically after we merge abstractions together (see {!reduce_ctx} and
    {!collapse_ctx} for instance).

    TODO: in the future it would be better to implement a more general matching
    algorithm, both for the joins and for checking whether two environments are
    equivalent.

    Inputs:
    - [span]
    - [allow_markers]: disables some sanity checks (which check that projection
      markers don't appear).
    - [old_abs_ids]
    - [eval_ctx] *)
val reorder_fresh_abs :
  Meta.span -> bool -> AbstractionId.Set.t -> eval_ctx -> eval_ctx
