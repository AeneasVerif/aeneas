open Expressions
open Types
open Values
open Contexts
open Cps
open InterpPaths

(** Auxiliary function.

    Prepare the access to a place in a right-value (typically an operand) by
    reorganizing the environment to end outer loans, then read the value and
    check that this value *doesn't contain any bottom nor reserved borrows*. We
    also return a loan id if the value is directly below a shared loan.

    We reorganize the environment so that:
    - we can access the place (we prepare *along* the path)
    - the value at the place itself doesn't contain loans (the [access_kind]
      controls whether we only end mutable loans, or also shared loans).

    [expand_prim_copy]: if [true], expand the symbolic values which are
    primitively copyable and contain borrows. *)
val access_rplace_reorganize_and_read :
  config ->
  Meta.span ->
  bool ->
  access_kind ->
  place ->
  eval_ctx ->
  loan_id option * tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)

(** Evaluate an operand.

    Reorganize the context, then evaluate the operand.

    **Warning**: this function shouldn't be used to evaluate a list of operands
    (for a function call, for instance): we must do *one* reorganization of the
    environment, before evaluating all the operands at once. Use
    {!eval_operands} instead. *)
val eval_operand :
  config ->
  Meta.span ->
  operand ->
  eval_ctx ->
  tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)

(** Evaluate several operands at once. *)
val eval_operands :
  config ->
  Meta.span ->
  operand list ->
  eval_ctx ->
  tvalue list * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)

(** Evaluate an rvalue which is not a global (globals are handled elsewhere).

    Transmits the computed rvalue to the received continuation.

    Note that this function fails on {!Aeneas.Expressions.rvalue.Discriminant}:
    discriminant reads should have been eliminated from the AST. *)
val eval_rvalue_not_global :
  config ->
  Meta.span ->
  rvalue ->
  eval_ctx ->
  (tvalue, eval_error) result
  * eval_ctx
  * (SymbolicAst.expr -> SymbolicAst.expr)

(** Evaluate a fake read (update the context so that we can read a place) *)
val eval_fake_read : config -> Meta.span -> place -> cm_fun

(** Retrieve information about an unsized casts.

  We handle the following cases:
  - it is possible to cast a boxed array (e.g., [Box<[T; N]>])
    to a boxed slice (e.g., [Box<[T]>])
  - it is possible to cast a boxed structure to another boxed structure
    when the structures are the same but the last field, which must be an array
    in one case and a slice in the other. For instance:
    {[
      pub struct Wrapper<T: ?Sized> {
          data: T,
      }

      fn alloc<const N : usize>() -> Box<Wrapper<[u8]>> {
          Box::new(Wrapper{data: [0; N]})
      }
    ]}

  In the structure case, we return:
  - the adt id and generics
  - the id of the last field
  - the type of the input array
  - the type of the input slice
*)
val cast_unsize_to_modified_fields :
  Meta.span ->
  eval_ctx ->
  ty ->
  ty ->
  (type_decl_id * generic_args * FieldId.id * ty * ty) option
