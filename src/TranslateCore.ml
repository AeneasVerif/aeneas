(** Some utilities for the translation *)

open Contexts
open ExtractName

(** The local logger *)
let log = Logging.translate_log

type trans_ctx = decls_ctx [@@deriving show]
type fun_and_loops = { f : Pure.fun_decl; loops : Pure.fun_decl list }
type pure_fun_translation_no_loops = Pure.fun_decl
type pure_fun_translation = fun_and_loops

let trans_ctx_to_fmt_env (ctx : trans_ctx) : Print.fmt_env =
  Print.Contexts.decls_ctx_to_fmt_env ctx

let trans_ctx_to_pure_fmt_env (ctx : trans_ctx) : PrintPure.fmt_env =
  PrintPure.decls_ctx_to_fmt_env ctx

let name_to_string (ctx : trans_ctx) =
  Print.Types.name_to_string (trans_ctx_to_fmt_env ctx)

let match_name_find_opt (ctx : trans_ctx) (name : Types.name)
    (m : 'a NameMatcherMap.t) : 'a option =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  let open ExtractBuiltin in
  NameMatcherMap.find_opt mctx name m

let match_name_with_generics_find_opt (ctx : trans_ctx) (name : Types.name)
    (generics : Types.generic_args) (m : 'a NameMatcherMap.t) : 'a option =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  let open ExtractBuiltin in
  NameMatcherMap.find_with_generics_opt mctx name generics m

let name_to_simple_name (ctx : trans_ctx) (n : Types.name) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  name_to_simple_name mctx n

let trait_name_with_generics_to_simple_name (ctx : trans_ctx)
    ?(prefix : Types.name option = None) (n : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  name_with_generics_to_simple_name mctx ~prefix n p g

let name_with_crate_to_pattern_string (crate : LlbcAst.crate) (n : Types.name) :
    string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    { tgt = TkPattern; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  let pat = Charon.NameMatcher.name_to_pattern mctx c n in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let name_with_generics_crate_to_pattern_string (crate : LlbcAst.crate)
    (n : Types.name) (params : Types.generic_params) (args : Types.generic_args)
    : string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    { tgt = TkPattern; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  let pat =
    Charon.NameMatcher.name_with_generics_to_pattern mctx c params n args
  in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let name_to_pattern_string (ctx : trans_ctx) (n : Types.name) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  let c : Charon.NameMatcher.to_pat_config =
    { tgt = TkPattern; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  let pat = Charon.NameMatcher.name_to_pattern mctx c n in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let name_with_generics_to_pattern_string (ctx : trans_ctx) (n : Types.name)
    (params : Types.generic_params) (args : Types.generic_args) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  let c : Charon.NameMatcher.to_pat_config =
    { tgt = TkPattern; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  let pat =
    Charon.NameMatcher.name_with_generics_to_pattern mctx c params n args
  in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat
