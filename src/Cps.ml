(** This module defines various utilities to write the interpretation functions
    in continuation passing style. *)

module T = Types
module V = Values
module C = Contexts

(** TODO: change the name *)
type eval_error = EPanic

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
(** Continuation function *)

type cm_fun = m_fun -> m_fun
(** Continuation taking another continuation as parameter *)

type typed_value_m_fun = V.typed_value -> m_fun
(** Continuation taking a typed value as parameter - TODO: use more *)

type typed_value_cm_fun = V.typed_value -> cm_fun
(** Continuation taking another continuation as parameter and a typed
    value as parameter.
 *)

type st_m_fun = statement_eval_res -> m_fun
(** Type of a continuation used when evaluating a statement *)

type st_cm_fun = st_m_fun -> m_fun
(** Type of a continuation used when evaluating a statement *)

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

(** Composition of functions taking continuations as parameters.
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

(** If we have a list of [inputs] of type `'a list` and a function [f] which
    evaluates one element of type `'a` to compute a result of type `'b` before
    giving it to a continuation, the following function performs a fold operation:
    it evaluates all the inputs one by one by accumulating the results in a list,
    and gives the list to a continuation.
    
    Note that we make sure that the results are listed in the order in
    which they were computed (the first element of the list is the result
    of applying [f] to the first element of the inputs).
    
    See the unit test below for an illustration.
 *)
let fold_left_apply_continuation (f : 'a -> ('b -> 'c -> 'd) -> 'c -> 'd)
    (inputs : 'a list) (cf : 'b list -> 'c -> 'd) : 'c -> 'd =
  let rec eval_list (inputs : 'a list) (cf : 'b list -> 'c -> 'd)
      (outputs : 'b list) : 'c -> 'd =
   fun ctx ->
    match inputs with
    | [] -> cf (List.rev outputs) ctx
    | x :: inputs ->
        comp (f x) (fun cf v -> eval_list inputs cf (v :: outputs)) cf ctx
  in
  eval_list inputs cf []

(** Unit test/example for [fold_left_apply_continuation] *)
let _ =
  fold_left_apply_continuation
    (fun x cf (ctx : unit) -> cf (10 + x) ctx)
    [ 0; 1; 2; 3; 4 ]
    (fun values _ctx -> assert (values = [ 10; 11; 12; 13; 14 ]))
    ()

(** Composition of functions taking continuations as parameters.

    We sometimes have the following situation, where we want to compose three
    functions `send`, `transmit` and `receive` such that:
    - those three functions take continuations as parameters
    - `send` generates a value and gives it to its continuation
    - `receive` expects a value (so we can compose `send` and `receive` like
      so: `comp send receive`)
    - `transmit` doesn't expect any value and needs to be called between `send`
      and `receive`
    
    In this situation, we need to take the value given by `send` and "transmit"
    it to `receive`.

    This is what this function does (see the unit test below for an illustration).
    
    TODO: use more!
 *)
let comp_transmit (f : ('v -> 'm) -> 'n) (g : 'm -> 'm) : ('v -> 'm) -> 'n =
 fun cf -> f (fun v -> g (cf v))

let () =
  let return3 (cf : int -> unit -> unit) (ctx : unit) = cf 3 ctx in
  let do_nothing (cf : unit -> unit) (ctx : unit) = cf ctx in
  let consume3 (x : int) (ctx : unit) : unit =
    assert (x = 3);
    ctx
  in
  let cc = comp_transmit return3 do_nothing in
  let cc = cc consume3 in
  cc ()

let comp_check_value (f : ('v -> 'ctx -> 'a) -> 'ctx -> 'b)
    (g : 'v -> 'ctx -> unit) : ('v -> 'ctx -> 'a) -> 'ctx -> 'b =
 fun cf ->
  f (fun v ctx ->
      g v ctx;
      cf v ctx)

let comp_check_ctx (f : ('ctx -> 'a) -> 'ctx -> 'b) (g : 'ctx -> unit) :
    ('ctx -> 'a) -> 'ctx -> 'b =
 fun cf ->
  f (fun ctx ->
      g ctx;
      cf ctx)
