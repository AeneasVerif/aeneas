open Types
open Values
open Contexts
open Cps

(** When copying values, we duplicate the shared borrows. This is tantamount to
    reborrowing the shared value. The [reborrow_shared original_id new_bid ctx]
    applies this change to an environment [ctx] by inserting a new borrow id in
    the set of borrows tracked by a shared value, referenced by the
    [original_bid] argument.  *)
val reborrow_shared : Meta.meta -> BorrowId.id -> BorrowId.id -> eval_ctx -> eval_ctx

(** End a borrow identified by its id, while preserving the invariants.

    If the borrow is inside another borrow/an abstraction or contains loans,
    [end_borrow] will end those borrows/abstractions/loans first.
  *)
val end_borrow : Meta.meta -> config -> BorrowId.id -> cm_fun

(** End a set of borrows identified by their ids, while preserving the invariants. *)
val end_borrows : Meta.meta -> config -> BorrowId.Set.t -> cm_fun

(** End an abstraction while preserving the invariants. *)
val end_abstraction : Meta.meta -> config -> AbstractionId.id -> cm_fun

(** End a set of abstractions while preserving the invariants. *)
val end_abstractions : Meta.meta -> config -> AbstractionId.Set.t -> cm_fun

(** End a borrow and return the resulting environment, ignoring synthesis *)
val end_borrow_no_synth : Meta.meta -> config -> BorrowId.id -> eval_ctx -> eval_ctx

(** End a set of borrows and return the resulting environment, ignoring synthesis *)
val end_borrows_no_synth : Meta.meta -> config -> BorrowId.Set.t -> eval_ctx -> eval_ctx

(** End an abstraction and return the resulting environment, ignoring synthesis *)
val end_abstraction_no_synth :
  Meta.meta -> config -> AbstractionId.id -> eval_ctx -> eval_ctx

(** End a set of abstractions and return the resulting environment, ignoring synthesis *)
val end_abstractions_no_synth :
  Meta.meta -> config -> AbstractionId.Set.t -> eval_ctx -> eval_ctx

(** Promote a reserved mut borrow to a mut borrow, while preserving the invariants.

    Reserved borrows are special mutable borrows which are created as shared borrows
    then promoted to mutable borrows upon their first use.

    This function replaces the reserved borrow with a mutable borrow, then replaces
    the corresponding shared loan with a mutable loan (after having ended the
    other shared borrows which point to this loan).
 *)
val promote_reserved_mut_borrow : Meta.meta -> config -> BorrowId.id -> cm_fun

(** Transform an abstraction to an abstraction where the values are not
    structured.

    For instance:
    {[
      abs {
        (mut_borrow l0, mut_borrow l1, _)
      }

          ~~>

      abs {
        mut_borrow l0
        mut_borrow l1
      }
    ]}

    Rem.: we do this to simplify the merging of abstractions. We can do this
    because for now we don't support nested borrows. In order to implement
    support for nested borrows, we will probably need to maintain the structure
    of the avalues.

    Paramters:
    - [abs_kind]
    - [can_end]
    - [destructure_shared_values]: if [true], explore shared values and whenever we find
      a shared loan, move it elsewhere by replacing it with the same value without
      the shared loan, and adding another ashared loan in the abstraction.
      For instance:
      {[
         ML {l0} (0, ML {l1} 1)

         ~~>

         ML {l0} (0, 1)
         ML {l1} 1
      ]}
    - [ctx]
    - [abs]
 *)
val destructure_abs : Meta.meta -> abs_kind -> bool -> bool -> eval_ctx -> abs -> abs

(** Return [true] if the values in an abstraction are destructured.

    We simply destructure it and check that it gives the identity.

    The input boolean is [destructure_shared_value]. See {!destructure_abs}.
 *)
val abs_is_destructured : Meta.meta -> bool -> eval_ctx -> abs -> bool

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
    - [destructure_shared_values]: this is similar to [destructure_shared_values]
      for {!destructure_abs}.
    - [ctx]
    - [v]
 *)
val convert_value_to_abstractions :
  Meta.meta -> abs_kind -> bool -> bool -> eval_ctx -> typed_value -> abs list

(** See {!merge_into_abstraction}.

    Rem.: it may be more idiomatic to have a functor, but this seems a bit
    heavyweight, though.
  *)
type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id -> rty -> typed_avalue -> rty -> typed_avalue -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [child0]
          - [ty1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_borrows : borrow_id -> rty -> rty -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [ty1]
       *)
  merge_amut_loans :
    loan_id -> rty -> typed_avalue -> rty -> typed_avalue -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [child0]
          - [ty1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_loans :
    loan_id_set ->
    rty ->
    typed_value ->
    typed_avalue ->
    rty ->
    typed_value ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [sv0]
          - [child0]
          - [ty1]
          - [sv1]
          - [child1]
       *)
}

(** Merge an abstraction into another abstraction.

    We insert the result of the merge in place of the second abstraction (and in
    particular, we don't simply push the merged abstraction at the end of the
    environment: this helps preserving the structure of the environment, when
    computing loop fixed points for instance).

    When we merge two abstractions together, we remove the loans/borrows
    which appear in one and whose associated loans/borrows appear in the
    other. For instance:
    {[
      abs'0 { mut_borrow l0, mut_loan l1 }   // Rem.: mut_loan l1
      abs'1 { mut_borrow l1, mut_borrow l2 } // Rem.: mut_borrow l1

          ~~>

      abs'01 { mut_borrow l0, mut_borrow l2 }
    ]}

    Also, we merge all their regions together. For instance, if [abs'0] projects
    region [r0] and [abs'1] projects region [r1], we pick one of the two, say [r0]
    (the one with the smallest index in practice) and substitute [r1] with [r0]
    in the whole context.

    Parameters:
    - [kind]
    - [can_end]
    - [merge_funs]: Those functions are used to merge borrows/loans with the
      *same ids*. For instance, when performing environment joins we may introduce
      abstractions which both contain loans/borrows with the same ids. When we
      later merge those abstractions together, we need to call a merge function
      to reconcile the borrows/loans. For instance, if both abstractions contain
      the same shared loan [l0], we will call {!merge_ashared_borrows} to derive
      a shared value for the merged shared loans.

      For instance, this happens for the following abstractions:
      {[
        abs'0 { mut_borrow l0, mut_loan l1 } // mut_borrow l0 !
        abs'1 { mut_borrow l0, mut_loan l2 } // mut_borrow l0 !
      ]}
      If you want to forbid this, provide [None]. In that case, [merge_into_abstraction]
      actually simply performs some sort of a union.

    - [ctx]
    - [abs_id0]
    - [abs_id1]

    We return the updated context as well as the id of the new abstraction which
    results from the merge.
 *)
val merge_into_abstraction :
  Meta.meta -> 
  abs_kind ->
  bool ->
  merge_duplicates_funcs option ->
  eval_ctx ->
  AbstractionId.id ->
  AbstractionId.id ->
  eval_ctx * AbstractionId.id
