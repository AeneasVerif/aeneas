open Types
open Values
open Expressions
open Contexts
open Cps

type access_kind = Read | Write | Move

(** Update the environment to be able to read a place.

    When reading a place, we may be stuck along the way because some value
    is borrowed, we reach a symbolic value, etc. This function repeatedly
    updates the environment (by ending borrows, expanding symbolic values, etc.)
    until it manages to fully access the provided place.
 *)
val update_ctx_along_read_place : Meta.meta -> config -> access_kind -> place -> cm_fun

(** Update the environment to be able to write to a place.

    See {!update_ctx_along_read_place}.
*)
val update_ctx_along_write_place : Meta.meta -> config -> access_kind -> place -> cm_fun

(** Read the value at a given place.

    This function doesn't update the environment to make sure the value is
    accessible: if needs be, you should call {!update_ctx_along_read_place} first.

    Note that we only access the value at the place, and do not check that
    the value is "well-formed" (for instance that it doesn't contain bottoms).
 *)
val read_place : Meta.meta -> access_kind -> place -> eval_ctx -> typed_value

(** Update the value at a given place.

    This function doesn't update the environment to make sure the value is
    accessible: if needs be, you should call {!update_ctx_along_write_place} first.

    This function is a helper function and is **not safe**: it will not check if
    the overwritten value contains borrows, loans, etc. and will simply
    overwrite it.
 *)
val write_place : Meta.meta -> access_kind -> place -> typed_value -> eval_ctx -> eval_ctx

(** Compute an expanded tuple ⊥ value.

    [compute_expanded_bottom_tuple_value [ty0, ..., tyn]] returns
    [(⊥:ty0, ..., ⊥:tyn)]
 *)
val compute_expanded_bottom_tuple_value : Meta.meta -> ety list -> typed_value

(** Compute an expanded ADT ⊥ value.

    The types in the generics should use erased regions.
  *)
val compute_expanded_bottom_adt_value :
  Meta.meta ->
  eval_ctx ->
  TypeDeclId.id ->
  VariantId.id option ->
  generic_args ->
  typed_value

(** Drop (end) outer loans at a given place, which should be seen as an l-value
    (we will write to it later, but need to drop the loans before writing).

    This is used to drop values when evaluating the drop statement or before
    writing to a place.

    Note that we don't do what is defined in the formalization: we move the
    value to a temporary dummy value, then explore this value and end the outer
    loans which are inside as long as we find some, then move the resulting
    value back to where it was. This shouldn't make any difference, really (note
    that the place is *inside* a borrow, if we end the borrow, we won't be able
    to reinsert the value back).
 *)
val drop_outer_loans_at_lplace : Meta.meta -> config -> place -> cm_fun

(** End the loans at a given place: read the value, if it contains a loan,
    end this loan, repeat.

    This is used when reading or borrowing values. We typically
    first call {!update_ctx_along_read_place} or {!update_ctx_along_write_place}
    to get access to the value, then call this function to "prepare" the value:
    when moving values, we can't move a value which contains loans and thus need
    to end them, etc.
 *)
val end_loans_at_place : Meta.meta -> config -> access_kind -> place -> cm_fun

(** Small utility.

    Prepare a place which is to be used as the destination of an assignment:
    update the environment along the paths, end the outer loans at this place, etc.

    Return the updated context and the (updated) value at the end of the
    place. This value should not contain any outer loan (and we check it is the
    case). Note that this value is very likely to contain ⊥ subvalues.
  *)
val prepare_lplace : Meta.meta -> config -> place -> (typed_value -> m_fun) -> m_fun
