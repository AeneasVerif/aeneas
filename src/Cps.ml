(** This module defines various utilities to write the interpretation functions
    in continuation passing style. *)

module T = Types
module V = Values
module C = Contexts

(** Result of evaluating a statement *)
type statement_eval_res =
  | Unit
  | Break of int
  | Continue of int
  | Return
  | Panic

(** Synthesized expresssion - dummy for now *)
type sexpr = SOne | SList of sexpr list

type eval_result = sexpr option

type m_fun = C.eval_ctx -> eval_result
(** Monadic function *)

type cm_fun = m_fun -> m_fun
(** Monadic function with continuation *)

type typed_value_cm_fun = V.typed_value -> cm_fun
(** Monadic function with continuation and receiving a typed value *)

(** Convert a unit function to a cm function *)
let unit_to_cm_fun (f : C.eval_ctx -> unit) : cm_fun =
 fun cf ctx ->
  f ctx;
  cf ctx

(** *)
let update_to_cm_fun (f : C.eval_ctx -> C.eval_ctx) : cm_fun =
 fun cf ctx ->
  let ctx = f ctx in
  cf ctx

(** Composition of functions taking continuations as paramters.
    We tried to make this as general as possible. *)
let comp (f : 'c -> 'd -> 'e) (g : ('a -> 'b) -> 'c) : ('a -> 'b) -> 'd -> 'e =
 fun cf ctx -> f (g cf) ctx

let comp_unit (f : cm_fun) (g : C.eval_ctx -> unit) : cm_fun =
  comp f (unit_to_cm_fun g)

let comp_update (f : cm_fun) (g : C.eval_ctx -> C.eval_ctx) : cm_fun =
  comp f (update_to_cm_fun g)

(** This is just a test, to check that [comp] is general enough to handle a case
    where a function must compute a value and give it to the continuation.
    It happens for functions like [eval_operand].

    Keeping this here also makes it a good reference, when one wants to figure
    out the signatures he should use for such a composition.
 *)
let comp_ret_val (f : (V.typed_value -> m_fun) -> m_fun)
    (g : m_fun -> V.typed_value -> m_fun) : cm_fun =
  comp f g

let apply (f : cm_fun) (g : m_fun) : m_fun = fun ctx -> f g ctx

let id_cm_fun : cm_fun = fun cf ctx -> cf ctx
