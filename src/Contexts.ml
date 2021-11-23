open Types
open Values
open Expressions
open CfimAst
open Print.Values
open Errors

type env_value = Var of VarId.id * typed_value | Abs of abs

type env = env_value list

let env_value_to_string (fmt : value_formatter) (ev : env_value) : string =
  match ev with
  | Var (vid, tv) ->
      var_id_to_string vid ^ " -> " ^ typed_value_to_string fmt tv
  | Abs abs -> abs_to_string fmt abs

let env_to_string (fmt : value_formatter) (env : env) : string =
  "{\n"
  ^ String.concat ";\n"
      (List.map (fun ev -> "  " ^ env_value_to_string fmt ev) env)
  ^ "\n}"

type 'a eval_result = Stuck | Panic | Res of 'a

type interpreter_mode = ConcreteMode | SymbolicMode

type config = { mode : interpreter_mode; check_invariants : bool }

type outer_borrows = Borrows of BorrowId.Set.t | Borrow of BorrowId.id

type stack_frame = { vars : var VarId.vector }
(** A function frame

    When using the interpreter in concrete mode (i.e, non symbolic) we
    push a function frame whenever we enter a function body (and pop it
    upon leaving it).
 *)

type eval_ctx = {
  type_context : type_def TypeDefId.vector;
  fun_context : fun_def FunDefId.vector;
  type_vars : type_var TypeVarId.vector;
  frames : stack_frame list;
  env : env;
  symbolic_counter : SymbolicValueId.generator;
  borrows_counter : BorrowId.generator;
}
(** Evaluation context *)
