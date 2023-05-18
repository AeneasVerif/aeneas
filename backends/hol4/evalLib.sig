signature evalLib =
sig
  (* This module implements [eval_conv], which supersedes EVAL_CONV by
     allowing to use custom unfolding theorems. This is particularly
     useful for divDefLib, which returns rewriting theorems to the user
     which are actually not definitional theorems.
   *)

  include Abbrev

  (* The following functions allow to register custom unfolding theorems *)
  (* TODO: permanence of theorems? *)
  val add_unfold : term * thm -> unit
  val add_unfolds : (term * thm) list -> unit
  val add_unfold_thm : thm -> unit
  val add_unfold_thms : thm list -> unit

  (* Get the unfolding theorems *)
  val get_unfold_thms : unit -> thm list

  (* The custom "eval" conversion *)
  val eval_conv : conv

  (* The custom "eval" function *)
  val eval : term -> term
end
