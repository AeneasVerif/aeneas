module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open InterpreterUtils
open InterpreterProjectors
(* for symbolic_expansion definition *)

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

(** Synthesize code for a symbolic expansion which doesn't lead to branching
    (i.e., applied on a value which is not an enumeration with several variants).
 *)
let synthesize_symbolic_expansion_no_branching (_sv : V.symbolic_value)
    (_see : symbolic_expansion) : unit =
  ()

(** Synthesize code for a symbolic enum expansion (which leads to branching)
 *)
let synthesize_symbolic_expansion_enum_branching (_sv : V.symbolic_value)
    (_seel : symbolic_expansion list) : unit =
  ()

let synthesize_symbolic_expansion_if_branching (_sv : V.symbolic_value) : unit =
  ()

let synthesize_symbolic_expansion_switch_int_branching (_sv : V.symbolic_value)
    : unit =
  ()

let synthesize_unary_op (_unop : E.unop) (_op : V.typed_value)
    (_dest : V.symbolic_value) : unit =
  ()

let synthesize_binary_op (_binop : E.binop) (_op1 : V.typed_value)
    (_op2 : V.typed_value) (_dest : V.symbolic_value) : unit =
  ()

(** Actually not sure if we need this, or a synthesize_symbolic_expansion_enum *)
let synthesize_eval_rvalue_discriminant (_p : E.place) : unit = ()

let synthesize_eval_rvalue_ref (_p : E.place) (_bkind : E.borrow_kind) : unit =
  ()

let synthesize_eval_rvalue_aggregate (_aggregate_kind : E.aggregate_kind)
    (_ops : E.operand list) : unit =
  ()

let synthesize_function_call (_fid : A.fun_id)
    (_region_params : T.erased_region list) (_type_params : T.ety list)
    (_args : V.typed_value list) (_dest : E.place) (_res : V.symbolic_value) :
    unit =
  ()
