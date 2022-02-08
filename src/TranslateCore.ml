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

type pure_fun_translation = Pure.fun_def * Pure.fun_def list

let type_def_to_string (ctx : trans_ctx) (def : Pure.type_def) : string =
  let type_params = def.type_params in
  let type_defs = ctx.type_context.type_defs in
  let fmt = PrintPure.mk_type_formatter type_defs type_params in
  PrintPure.type_def_to_string fmt def

let type_id_to_string (ctx : trans_ctx) (def : Pure.type_def) : string =
  let type_params = def.type_params in
  let type_defs = ctx.type_context.type_defs in
  let fmt = PrintPure.mk_type_formatter type_defs type_params in
  PrintPure.type_def_to_string fmt def

let fun_sig_to_string (ctx : trans_ctx) (sg : Pure.fun_sig) : string =
  let type_params = sg.type_params in
  let type_defs = ctx.type_context.type_defs in
  let fun_defs = ctx.fun_context.fun_defs in
  let fmt = PrintPure.mk_ast_formatter type_defs fun_defs type_params in
  PrintPure.fun_sig_to_string fmt sg

let fun_def_to_string (ctx : trans_ctx) (def : Pure.fun_def) : string =
  let type_params = def.signature.type_params in
  let type_defs = ctx.type_context.type_defs in
  let fun_defs = ctx.fun_context.fun_defs in
  let fmt = PrintPure.mk_ast_formatter type_defs fun_defs type_params in
  PrintPure.fun_def_to_string fmt def

let fun_def_id_to_string (ctx : trans_ctx) (id : Pure.FunDefId.id) : string =
  Print.name_to_string (Pure.FunDefId.Map.find id ctx.fun_context.fun_defs).name
