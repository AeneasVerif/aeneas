(** Some utilities for the translation *)

open InterpreterStatements
module L = Logging
module T = Types
module A = CfimAst
module M = Modules
module SA = SymbolicAst

(** The local logger *)
let log = L.translate_log

type trans_ctx = { type_context : C.type_context; fun_context : C.fun_context }

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

let fun_decl_id_to_string (ctx : trans_ctx) (id : Pure.FunDeclId.id) : string =
  Print.fun_name_to_string
    (Pure.FunDeclId.Map.find id ctx.fun_context.fun_decls).name
