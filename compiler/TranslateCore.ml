(** Some utilities for the translation *)

open InterpreterStatements
module L = Logging
module T = Types
module A = LlbcAst
module SA = SymbolicAst
module FA = FunsAnalysis

(** The local logger *)
let log = L.translate_log

type type_context = C.type_context [@@deriving show]

type fun_context = {
  fun_decls : A.fun_decl A.FunDeclId.Map.t;
  fun_infos : FA.fun_info A.FunDeclId.Map.t;
}
[@@deriving show]

type trait_decls_context = C.trait_decls_context [@@deriving show]
type trait_impls_context = C.trait_impls_context [@@deriving show]
type global_context = C.global_context [@@deriving show]

(* TODO: we should use Contexts.decls_ctx *)
type trans_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  global_context : global_context;
  trait_decls_context : trait_decls_context;
  trait_impls_context : trait_impls_context;
}

type fun_and_loops = { f : Pure.fun_decl; loops : Pure.fun_decl list }
type pure_fun_translation_no_loops = Pure.fun_decl * Pure.fun_decl list
type pure_fun_translation = { fwd : fun_and_loops; backs : fun_and_loops list }

let trans_ctx_to_type_formatter (ctx : trans_ctx)
    (type_params : Pure.type_var list)
    (const_generic_params : Pure.const_generic_var list) :
    PrintPure.type_formatter =
  let type_decls = ctx.type_context.type_decls in
  let global_decls = ctx.global_context.global_decls in
  let trait_decls = ctx.trait_decls_context.trait_decls in
  let trait_impls = ctx.trait_impls_context.trait_impls in
  PrintPure.mk_type_formatter type_decls global_decls trait_decls trait_impls
    type_params const_generic_params

let type_decl_to_string (ctx : trans_ctx) (def : Pure.type_decl) : string =
  let generics = def.generics in
  let fmt =
    trans_ctx_to_type_formatter ctx generics.types generics.const_generics
  in
  PrintPure.type_decl_to_string fmt def

let type_id_to_string (ctx : trans_ctx) (id : Pure.TypeDeclId.id) : string =
  Print.fun_name_to_string
    (Pure.TypeDeclId.Map.find id ctx.type_context.type_decls).name

let trans_ctx_to_ast_formatter (ctx : trans_ctx)
    (type_params : Pure.type_var list)
    (const_generic_params : Pure.const_generic_var list) :
    PrintPure.ast_formatter =
  let type_decls = ctx.type_context.type_decls in
  let fun_decls = ctx.fun_context.fun_decls in
  let global_decls = ctx.global_context.global_decls in
  let trait_decls = ctx.trait_decls_context.trait_decls in
  let trait_impls = ctx.trait_impls_context.trait_impls in
  PrintPure.mk_ast_formatter type_decls fun_decls global_decls trait_decls
    trait_impls type_params const_generic_params

let fun_sig_to_string (ctx : trans_ctx) (sg : Pure.fun_sig) : string =
  let generics = sg.generics in
  let fmt =
    trans_ctx_to_ast_formatter ctx generics.types generics.const_generics
  in
  PrintPure.fun_sig_to_string fmt sg

let fun_decl_to_string (ctx : trans_ctx) (def : Pure.fun_decl) : string =
  let generics = def.signature.generics in
  let fmt =
    trans_ctx_to_ast_formatter ctx generics.types generics.const_generics
  in
  PrintPure.fun_decl_to_string fmt def

let fun_decl_id_to_string (ctx : trans_ctx) (id : A.FunDeclId.id) : string =
  Print.fun_name_to_string
    (A.FunDeclId.Map.find id ctx.fun_context.fun_decls).name
