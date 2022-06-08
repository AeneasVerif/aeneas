(** Some utilities for the translation *)

open InterpreterStatements
open FunIdentifier
module L = Logging
module T = Types
module A = LlbcAst
module M = Modules
module SA = SymbolicAst
module FA = FunsAnalysis

(** The local logger *)
let log = L.translate_log

type type_context = C.type_context [@@deriving show]

type fun_context = {
  fun_decls : A.fun_decl FunDeclId.Map.t;
  fun_infos : FA.fun_info FunDeclId.Map.t;
}
[@@deriving show]

type trans_ctx = { type_context : type_context; fun_context : fun_context }

type pure_fun_translation = Pure.fun_decl * Pure.fun_decl list

let type_decl_to_string (ctx : trans_ctx) (def : Pure.type_decl) : string =
  let type_params = def.type_params in
  let type_decls = ctx.type_context.type_decls in
  let fmt = PrintPure.mk_type_formatter type_decls type_params in
  PrintPure.type_decl_to_string fmt def

let type_id_to_string (ctx : trans_ctx) (def : Pure.type_decl) : string =
  let type_params = def.type_params in
  let type_decls = ctx.type_context.type_decls in
  let fmt = PrintPure.mk_type_formatter type_decls type_params in
  PrintPure.type_decl_to_string fmt def

let fun_sig_to_string (ctx : trans_ctx) (sg : Pure.fun_sig) : string =
  let type_params = sg.type_params in
  let type_decls = ctx.type_context.type_decls in
  let fun_decls = ctx.fun_context.fun_decls in
  let fmt = PrintPure.mk_ast_formatter type_decls fun_decls type_params in
  PrintPure.fun_sig_to_string fmt sg

let fun_decl_to_string (ctx : trans_ctx) (def : Pure.fun_decl) : string =
  let type_params = def.signature.type_params in
  let type_decls = ctx.type_context.type_decls in
  let fun_decls = ctx.fun_context.fun_decls in
  let fmt = PrintPure.mk_ast_formatter type_decls fun_decls type_params in
  PrintPure.fun_decl_to_string fmt def

let fun_decl_id_to_string (ctx : trans_ctx) (id : FunDeclId.id) : string =
  Print.fun_name_to_string
    (FunDeclId.Map.find id ctx.fun_context.fun_decls).name
