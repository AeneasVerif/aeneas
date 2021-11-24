open Types
open Values
open Expressions
open CfimAst
open Errors

type env_value = Var of VarId.id * typed_value | Abs of abs

type env = env_value list

type 'a eval_result = Stuck | Panic | Res of 'a

type interpreter_mode = ConcreteMode | SymbolicMode

type config = { mode : interpreter_mode; check_invariants : bool }

type stack_frame = { vars : VarId.id list }
(** A function frame

    When using the interpreter in concrete mode (i.e, non symbolic) we
    push a function frame whenever we enter a function body (and pop it
    upon leaving it).
 *)

type eval_ctx = {
  type_context : type_def TypeDefId.vector;
  fun_context : fun_def FunDefId.vector;
  type_vars : type_var TypeVarId.vector;
  vars : var VarId.Map.t;
  frames : stack_frame list;
  env : env;
  symbolic_counter : SymbolicValueId.generator;
  borrow_counter : BorrowId.generator;
}
(** Evaluation context *)

let fresh_symbolic_value_id (ctx : eval_ctx) : eval_ctx * SymbolicValueId.id =
  let id, counter' = SymbolicValueId.fresh ctx.symbolic_counter in
  ({ ctx with symbolic_counter = counter' }, id)

let fresh_borrow_id (ctx : eval_ctx) : eval_ctx * BorrowId.id =
  let id, counter' = BorrowId.fresh ctx.borrow_counter in
  ({ ctx with borrow_counter = counter' }, id)

let lookup_type_var (ctx : eval_ctx) (vid : TypeVarId.id) : type_var =
  TypeVarId.nth ctx.type_vars vid

let ctx_lookup_var (ctx : eval_ctx) (vid : VarId.id) : var =
  VarId.Map.find vid ctx.vars

(** Retrieve a variable's value in an environment *)
let env_lookup_var_value (env : env) (vid : VarId.id) : typed_value =
  let check_ev (ev : env_value) : typed_value option =
    match ev with
    | Var (vid', v) -> if vid' = vid then Some v else None
    | Abs _ -> None
  in
  match List.find_map check_ev env with
  | None -> failwith "Unreachable"
  | Some v -> v

(** Retrieve a variable's value in an evaluation context *)
let ctx_lookup_var_value (ctx : eval_ctx) (vid : VarId.id) : typed_value =
  env_lookup_var_value ctx.env vid

(** Update a variable's value in an environment

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let env_update_var_value (env : env) (vid : VarId.id) (nv : typed_value) : env =
  let update_ev (ev : env_value) : env_value =
    match ev with
    | Var (vid', v) -> if vid' = vid then Var (vid, nv) else Var (vid', v)
    | Abs abs -> Abs abs
  in
  List.map update_ev env

(** Update a variable's value in an evaluation context.

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let ctx_update_var_value (ctx : eval_ctx) (vid : VarId.id) (nv : typed_value) :
    eval_ctx =
  { ctx with env = env_update_var_value ctx.env vid nv }
