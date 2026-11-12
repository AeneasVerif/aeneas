open Values
open LlbcAst
open Contexts
open Cps

(** Check whether ending [abs] would directly give back a mutable borrow or
    symbolic borrow projector into a frozen abstraction ([frozen_abs]). *)
val abs_borrows_loans_in_frozen :
  Meta.span -> eval_ctx -> AbsId.Set.t -> abs -> bool

(** Compute backward local-variable liveness for every statement and block exit
    in a function body. *)
val compute_liveness : block -> liveness_info

(** End any [alive_hint = Some Short] abstractions in [ctx] whose ending does
    not invalidate borrows/regions inside [live_locals] (or mutate frozen
    abstractions). *)
val end_short_abstractions :
  config -> Meta.span -> Expressions.LocalId.Set.t -> cm_fun

(** End eligible [alive_hint = Some Short] abstractions right before evaluating
    statement [st]. *)
val end_short_abstractions_before_stmt : config -> statement -> cm_fun

(** End eligible [alive_hint = Some Short] abstractions at the fallthrough exit
    of block [b]. *)
val end_short_abstractions_after_block : config -> block -> cm_fun
