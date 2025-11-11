open Types
open Values
open Contexts

(** Turn a value into a abstractions.

    We generally use this to turn anonymous values into region abstractions.

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
    - [ctx]
    - [v] *)
val convert_value_to_abstractions :
  Meta.span -> abs_kind -> can_end:bool -> eval_ctx -> tvalue -> abs list

(** Convert a value to a list of *output* avalues (the value should contain
    borrows but no loans), and output and input expressions, so that we can put
    it in a region abstraction.

    We use this when performing joins. *)
val convert_value_to_output_avalues :
  Meta.span ->
  eval_ctx ->
  proj_marker ->
  tvalue ->
  RegionId.Set.t ->
  ty ->
  tavalue list * tevalue

val convert_value_to_input_avalues :
  Meta.span ->
  eval_ctx ->
  proj_marker ->
  tvalue ->
  RegionId.id ->
  tavalue list * tevalue

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
    - [with_abs_conts]
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
  can_end:bool ->
  with_abs_conts:bool ->
  merge_duplicates_funcs option ->
  eval_ctx ->
  AbsId.id ->
  AbsId.id ->
  eval_ctx * AbsId.id

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
val reorder_fresh_abs : Meta.span -> bool -> AbsId.Set.t -> eval_ctx -> eval_ctx

(** Project a context to only preserve the values appearing on the left or the
    values appearing on the right.

    The [proj_marker] must be [PLeft] or [PRight]. *)
val project_context :
  Meta.span -> AbsId.Set.t -> proj_marker -> eval_ctx -> eval_ctx

(** Introduce a continuation expression to a region abstraction.

    We use this for instance for loops and joins (after branchings): in the
    joined context, we replace the abstraction continuations of the fresh
    abstractions to reflect the fact that they should be introduced by the
    loop/join. *)
val add_abs_cont_to_abs : Meta.span -> eval_ctx -> abs -> abs_fun -> abs
