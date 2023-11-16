(** Some utilities for the translation *)

open Contexts

(** The local logger *)
let log = Logging.translate_log

type trans_ctx = decls_ctx [@@deriving show]
type fun_and_loops = { f : Pure.fun_decl; loops : Pure.fun_decl list }
type pure_fun_translation_no_loops = Pure.fun_decl * Pure.fun_decl list

type pure_fun_translation = {
  keep_fwd : bool;
      (** Should we extract the forward function?

          If the forward function returns `()` and there is exactly one
          backward function, we may merge the forward into the backward
          function and thus don't extract the forward function)?
       *)
  fwd : fun_and_loops;
  backs : fun_and_loops list;
}

let trans_ctx_to_fmt_env (ctx : trans_ctx) : Print.fmt_env =
  Print.Contexts.decls_ctx_to_fmt_env ctx

let trans_ctx_to_pure_fmt_env (ctx : trans_ctx) : PrintPure.fmt_env =
  PrintPure.decls_ctx_to_fmt_env ctx

let name_to_string (ctx : trans_ctx) =
  Print.Types.name_to_string (trans_ctx_to_fmt_env ctx)
