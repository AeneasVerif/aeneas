open Values
open Contexts
open Cps
open InterpUtils

(** End a borrow identified by its id, while preserving the invariants.

    If the borrow is inside another borrow/an abstraction or contains loans,
    [end_borrow] will end those borrows/abstractions/loans first. *)
val end_borrow :
  config -> Meta.span -> ?snapshots:bool -> unique_borrow_id -> cm_fun

(** End a set of borrows identified by their ids, while preserving the
    invariants. *)
val end_borrows :
  config -> Meta.span -> ?snapshots:bool -> unique_borrow_id_set -> cm_fun

(** End a loan identified by its id, while preserving the invariants *)
val end_loan : config -> Meta.span -> ?snapshots:bool -> loan_id -> cm_fun

(** End a set of loans identified by their ids, while preserving the invariants
*)
val end_loans : config -> Meta.span -> ?snapshots:bool -> loan_id_set -> cm_fun

(** End an abstraction while preserving the invariants. *)
val end_abstraction :
  config -> Meta.span -> ?snapshots:bool -> AbsId.id -> cm_fun

(** End a set of abstractions while preserving the invariants. *)
val end_abstractions :
  config -> Meta.span -> ?snapshots:bool -> AbsId.Set.t -> cm_fun

(** End a borrow and return the resulting environment, ignoring synthesis *)
val end_borrow_no_synth :
  config ->
  Meta.span ->
  ?snapshots:bool ->
  unique_borrow_id ->
  eval_ctx ->
  eval_ctx

(** End a set of borrows and return the resulting environment, ignoring
    synthesis *)
val end_borrows_no_synth :
  config ->
  Meta.span ->
  ?snapshots:bool ->
  unique_borrow_id_set ->
  eval_ctx ->
  eval_ctx

(** End a loan and return the resulting environment, ignoring synthesis *)
val end_loan_no_synth :
  config -> Meta.span -> ?snapshots:bool -> loan_id -> eval_ctx -> eval_ctx

(** End a set of loans and return the resulting environment, ignoring synthesis
*)
val end_loans_no_synth :
  config -> Meta.span -> ?snapshots:bool -> loan_id_set -> eval_ctx -> eval_ctx

(** End a set of loans and return the resulting environment, ignoring synthesis.

    Contrary to [end_loans_no_synth], the function doesn't fail if one of the
    loan ids actually doesn't exist in the context. *)
val try_end_loans_no_synth :
  config -> Meta.span -> ?snapshots:bool -> loan_id_set -> eval_ctx -> eval_ctx

(** End an abstraction and return the resulting environment, ignoring synthesis
*)
val end_abstraction_no_synth :
  config -> Meta.span -> ?snapshots:bool -> AbsId.id -> eval_ctx -> eval_ctx

(** End a set of abstractions and return the resulting environment, ignoring
    synthesis *)
val end_abstractions_no_synth :
  config -> Meta.span -> ?snapshots:bool -> AbsId.Set.t -> eval_ctx -> eval_ctx

(** Promote a reserved mut borrow to a mut borrow, while preserving the
    invariants.

    Reserved borrows are special mutable borrows which are created as shared
    borrows then promoted to mutable borrows upon their first use.

    This function replaces the reserved borrow with a mutable borrow, then
    replaces the corresponding shared loan with a mutable loan (after having
    ended the other shared borrows which point to this loan). *)
val promote_reserved_mut_borrow :
  config -> Meta.span -> loan_id -> shared_borrow_id -> cm_fun

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
    {ul
     {- [abs_kind] }
     {- [can_end] }
     {- [destructure_shared_values]: if [true], explore shared values and
        whenever we find a shared loan, move it elsewhere by replacing it with
        the same value without the shared loan, and adding another ashared loan
        in the abstraction. For instance:
        {[
          abs { ML l0 (0, ML l1 1) }

              ~~>

          abs {
            ML l0 (0, 1),
            ML l1 1 }
        ]}
     }
     {- [ctx] }
     {- [abs] }
    } *)
val destructure_abs :
  Meta.span ->
  abs_kind ->
  can_end:bool ->
  destructure_shared_values:bool ->
  eval_ctx ->
  abs ->
  abs

(** Return [true] if the values in an abstraction are destructured.

    We simply destructure it and check that it gives the identity.

    The input boolean is [destructure_shared_value]. See {!destructure_abs}. *)
val abs_is_destructured : Meta.span -> bool -> eval_ctx -> abs -> bool

(** Attempts to eliminate useless ended shared loans.

    TODO: will not be necessary once we destructure the avalues. *)
val eliminate_ended_shared_loans : Meta.span -> eval_ctx -> eval_ctx

(** Simplify the dummy values in a context by removing as many as possible and
    ending as many borrows as possible.

    We remove all the dummy values which:
    - contain no loans/borrows.
    - contain symbolic values (including those containing borrows: it is
      tantamount to ending preemptively the outer borrows)

    We also:
    - end the borrows which are inside dummy and don't themselves contain loans
    - end the region abstractions which can be ended because they contain no
      loans
    - end the loan projectors which can be ended because the corresponding
      symbolic value doesn't appear anywhere else in the context We ignore the
      abstractions which are specified by the set of abstraction ids (we do not
      end them, nor their loans). *)
val simplify_dummy_values_useless_abs :
  config -> ?snapshots:bool -> Meta.span -> cm_fun
