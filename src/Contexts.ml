open Types
open Values
open Expressions
open CfimAst
open Errors

(** Environment value: mapping from variable to value, abstraction (only
    used in symbolic mode) or stack frame delimiter.
    
    TODO: rename? Environment element or something?
 *)
type env_value = Var of var * typed_value | Abs of abs | Frame

type env = env_value list

type interpreter_mode = ConcreteMode | SymbolicMode

type config = { mode : interpreter_mode; check_invariants : bool }

type eval_ctx = {
  type_context : type_def TypeDefId.vector;
  fun_context : fun_def FunDefId.vector;
  type_vars : type_var TypeVarId.vector;
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
  let rec lookup env =
    match env with
    | [] ->
        raise (Invalid_argument ("Variable not found: " ^ VarId.to_string vid))
    | Var (var, _) :: env' -> if var.index = vid then var else lookup env'
    | (Abs _ | Frame) :: env' -> lookup env'
  in
  lookup ctx.env

let ctx_lookup_type_def (ctx : eval_ctx) (tid : TypeDefId.id) : type_def =
  TypeDefId.nth ctx.type_context tid

let ctx_lookup_fun_def (ctx : eval_ctx) (fid : FunDefId.id) : fun_def =
  FunDefId.nth ctx.fun_context fid

(** Retrieve a variable's value in an environment *)
let env_lookup_var_value (env : env) (vid : VarId.id) : typed_value =
  let check_ev (ev : env_value) : typed_value option =
    match ev with
    | Var (var, v) -> if var.index = vid then Some v else None
    | Abs _ | Frame -> None
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
    | Var (var, v) -> if var.index = vid then Var (var, nv) else Var (var, v)
    | Abs abs -> Abs abs
    | Frame -> Frame
  in
  List.map update_ev env

(** Update a variable's value in an evaluation context.

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let ctx_update_var_value (ctx : eval_ctx) (vid : VarId.id) (nv : typed_value) :
    eval_ctx =
  { ctx with env = env_update_var_value ctx.env vid nv }
