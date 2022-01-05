module T = Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
open InterpreterUtils

(* TODO: the below functions have very "rough" signatures and do nothing: I
 * defined them so that the places where we should update the synthesized
 * program are clearly indicated in Interpreter.ml.
 * Also, some of those functions will probably be split, and their call site
 * will probably evolve.
 *
 * Small rk.: most functions should take an additional parameter for the
 * fresh symbolic value which stores the result of the computation.
 * For instance:
 *   `synthesize_binary_op Add op1 op2 s`
 * should generate:
 *   `s := op1 + op2`
 * *)

(** TODO: rename to synthesize_symbolic_expansion_{non_enum,one_variant}? *)
let synthesize_symbolic_expansion (sv : V.symbolic_value)
    (see : symbolic_expansion) : unit =
  ()

let synthesize_unary_op (unop : E.unop) (op : E.operand) : unit = ()

let synthesize_binary_op (binop : E.binop) (op1 : E.operand) (op2 : E.operand) :
    unit =
  ()

(** Actually not sure if we need this, or a synthesize_symbolic_expansion_enum *)
let synthesize_eval_rvalue_discriminant (p : E.place) : unit = ()

let synthesize_eval_rvalue_ref (p : E.place) (bkind : E.borrow_kind) : unit = ()

let synthesize_eval_rvalue_aggregate (aggregate_kind : E.aggregate_kind)
    (ops : E.operand list) : unit =
  ()

let synthesize_set_discriminant (p : E.place) (variant_id : T.VariantId.id) :
    unit =
  ()

let synthesize_non_local_function_call (fid : A.assumed_fun_id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : unit =
  ()

let synthesize_local_function_call (fid : A.FunDefId.id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : unit =
  ()
