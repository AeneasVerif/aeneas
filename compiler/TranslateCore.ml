(** Some utilities for the translation *)

open Contexts
open ExtractName

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

let match_name_find_opt (ctx : trans_ctx) (name : Types.name)
    (m : 'a NameMatcherMap.t) : 'a option =
  let open Charon.NameMatcher in
  let open ExtractBuiltin in
  let mctx : ctx =
    {
      type_decls = ctx.type_ctx.type_decls;
      global_decls = ctx.global_ctx.global_decls;
      trait_decls = ctx.trait_decls_ctx.trait_decls;
    }
  in
  NameMatcherMap.find_opt mctx name m

let match_name_with_generics_find_opt (ctx : trans_ctx) (name : Types.name)
    (generics : Types.generic_args) (m : 'a NameMatcherMap.t) : 'a option =
  let open Charon.NameMatcher in
  let open ExtractBuiltin in
  let mctx : ctx =
    {
      type_decls = ctx.type_ctx.type_decls;
      global_decls = ctx.global_ctx.global_decls;
      trait_decls = ctx.trait_decls_ctx.trait_decls;
    }
  in
  NameMatcherMap.find_with_generics_opt mctx name generics m

let name_to_simple_name (ctx : trans_ctx) (n : Types.name) : string list =
  let mctx : Charon.NameMatcher.ctx =
    {
      type_decls = ctx.type_ctx.type_decls;
      global_decls = ctx.global_ctx.global_decls;
      trait_decls = ctx.trait_decls_ctx.trait_decls;
    }
  in
  name_to_simple_name mctx n

let name_with_generics_to_simple_name (ctx : trans_ctx) (n : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let mctx : Charon.NameMatcher.ctx =
    {
      type_decls = ctx.type_ctx.type_decls;
      global_decls = ctx.global_ctx.global_decls;
      trait_decls = ctx.trait_decls_ctx.trait_decls;
    }
  in
  name_with_generics_to_simple_name mctx n p g
