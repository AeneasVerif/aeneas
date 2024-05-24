(** This module defines various utilities to write the interpretation functions
    in continuation passing style. *)

open Values
open Contexts
open Errors

(** TODO: change the name *)
type eval_error = EPanic

(** Result of evaluating a statement *)
type statement_eval_res =
  | Unit
  | Break of int
  | Continue of int
  | Return
  | Panic
  | LoopReturn of loop_id
      (** We reached a return statement *while inside a loop* *)
  | EndEnterLoop of loop_id * typed_value SymbolicValueId.Map.t
      (** When we enter a loop, we delegate the end of the function is
          synthesized with a call to the loop translation. We use this
          evaluation result to transmit the fact that we end evaluation
          because we entered a loop.

          We provide the list of values for the translated loop function call
          (or to be more precise the input values instantiation).
       *)
  | EndContinue of loop_id * typed_value SymbolicValueId.Map.t
      (** For loop translations: we end with a continue (i.e., a recursive call
          to the translation for the loop body).

          We provide the list of values for the translated loop function call
          (or to be more precise the input values instantiation).
       *)
[@@deriving show]

type eval_result = SymbolicAst.expression option

(** Function which takes a context as input, and evaluates to:
    - a new context
    - a continuation with which to build the execution trace, provided the
      trace for the end of the execution.
  *)
type cm_fun = eval_ctx -> eval_ctx * (eval_result -> eval_result)

type st_cm_fun =
  eval_ctx -> (eval_ctx * statement_eval_res) * (eval_result -> eval_result)

(** Type of a function used when evaluating a statement *)
type stl_cm_fun =
  eval_ctx ->
  (eval_ctx * statement_eval_res) list
  * (SymbolicAst.expression list option -> eval_result)

(** Compose continuations that we use to compute execution traces *)
let cc_comp (f : 'b -> 'c) (g : 'a -> 'b) : 'a -> 'c = fun e -> f (g e)

let comp (f : 'b -> 'c) (g : 'x * ('a -> 'b)) : 'x * ('a -> 'c) =
  let x, g = g in
  (x, cc_comp f g)

let comp2 (f : 'b -> 'c) (g : 'x * 'y * ('a -> 'b)) : 'x * 'y * ('a -> 'c) =
  let x, y, g = g in
  (x, y, cc_comp f g)

(** [fold] operation for functions which thread a context and return a continuation *)
let fold_left_apply_continuation (f : 'a -> 'c -> 'c * ('e -> 'e))
    (inputs : 'a list) (ctx : 'c) : 'c * ('e -> 'e) =
  let rec eval_list (inputs : 'a list) : 'c -> 'b =
   fun ctx ->
    match inputs with
    | [] -> (ctx, fun x -> x)
    | x :: inputs ->
        let ctx, cc = f x ctx in
        comp cc (eval_list inputs ctx)
  in
  eval_list inputs ctx

(** [map] operation for functions which thread a context and return a continuation *)
let map_apply_continuation (f : 'a -> 'c -> 'b * 'c * ('e -> 'e))
    (inputs : 'a list) (ctx : 'c) : 'b list * 'c * ('e -> 'e) =
  let rec eval_list (inputs : 'a list) (ctx : 'c) : 'b list * 'c * ('e -> 'e) =
    match inputs with
    | [] -> ([], ctx, fun e -> e)
    | x :: inputs ->
        let v, ctx, cc1 = f x ctx in
        let vl, ctx, cc2 = eval_list inputs ctx in
        (v :: vl, ctx, cc_comp cc1 cc2)
  in
  eval_list inputs ctx

let opt_list_to_list_opt (len : int) (el : 'a option list) : 'a list option =
  let expr_list =
    List.rev
      (List.fold_left
         (fun acc a -> match a with Some b -> b :: acc | None -> [])
         [] el)
  in
  let _ = assert (List.length expr_list = len) in
  if Option.is_none (List.hd expr_list) then None else Some expr_list

let cc_singleton file line span cf el =
  match el with
  | Some [ e ] -> cf (Some e)
  | Some _ -> internal_error file line span
  | _ -> None

(** It happens that we need to concatenate lists of results, for
    instance when evaluating the branches of a match. When applying
    the continuations to build the symbolic expressions, we need
    to decompose the list of expressions we get to give it to the
    individual continuations for the branches.
 *)
let comp_seqs (file : string) (line : int) (span : Meta.span)
    (ls :
      ('a list
      * (SymbolicAst.expression list option -> SymbolicAst.expression option))
      list) :
    'a list
    * (SymbolicAst.expression list option -> SymbolicAst.expression list option)
    =
  (* Auxiliary function: given a list of expressions el, build the expressions
     corresponding to the different branches *)
  let rec cc_aux ls el =
    match ls with
    | [] ->
        (* End of the list of branches: there shouldn't be any expression remaining *)
        sanity_check file line (el = []) span;
        []
    | (resl, cf) :: ls ->
        (* Split the list of expressions between:
           - the expressions for the current branch
           - the expressions for the remaining branches *)
        let el0, el = Collections.List.split_at el (List.length resl) in
        (* Compute the expression for the current branch *)
        let e0 = cf (Some el0) in
        let e0 =
          match e0 with None -> internal_error file line span | Some e -> e
        in
        (* Compute the expressions for the remaining branches *)
        let e = cc_aux ls el in
        (* Concatenate *)
        e0 :: e
  in
  let cc el = match el with None -> None | Some el -> Some (cc_aux ls el) in
  (List.flatten (fst (List.split ls)), cc)
