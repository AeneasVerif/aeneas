(** The following module defines micro-passes which operate on the pure AST *)

open Pure
open PureUtils
open TranslateCore

(** The local logger *)
let log = Logging.pure_micro_passes_log

type ctx = {
  crate : LlbcAst.crate;
  fun_decls : fun_decl FunDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  trans_ctx : trans_ctx;
  fresh_fvar_id : unit -> fvar_id;
}

let fun_decl_to_string (ctx : ctx) (def : fun_decl) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_decl_to_string fmt def

let loop_body_to_string (ctx : ctx) (x : loop_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.loop_body_to_string fmt "" "  " x

let loop_to_string (ctx : ctx) (x : loop) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.loop_to_string fmt "" "  " x

let fun_id_to_string (ctx : ctx) (fid : fun_id) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.regular_fun_id_to_string fmt fid

let fun_sig_to_string (ctx : ctx) (sg : fun_sig) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_sig_to_string fmt sg

let var_to_string (ctx : ctx) (v : var) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.var_to_string fmt v

let texpr_to_string (ctx : ctx) (x : texpr) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.texpr_to_string fmt false "" "  " x

let fvar_to_string (ctx : ctx) (x : fvar) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fvar_to_string fmt x

let generic_params_to_string (ctx : ctx) (x : generic_params) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.generic_params_to_string fmt x

let generic_args_to_string (ctx : ctx) (x : generic_args) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.generic_args_to_string fmt x

let ty_to_string (ctx : ctx) (x : ty) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.ty_to_string fmt false x

let let_to_string (ctx : ctx) monadic lv re next : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.let_to_string fmt "" "  " monadic lv re next

let fun_body_to_string (ctx : ctx) (x : fun_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.fun_body_to_string fmt x

let switch_to_string (ctx : ctx) scrut (x : switch_body) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.switch_to_string fmt "" "  " scrut x

let struct_update_to_string (ctx : ctx) supd : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.struct_update_to_string fmt "" "  " supd

let tpat_to_string (ctx : ctx) pat : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx.trans_ctx in
  PrintPure.tpat_to_string fmt pat

let lift_map_fun_decl_body (f : ctx -> fun_decl -> fun_body -> fun_body)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_all_fun_decl_body ctx.fresh_fvar_id (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor_with_state
    (obj : ctx -> fun_decl -> < visit_texpr : 'a -> texpr -> texpr ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : fun_decl =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id
    ((obj ctx def)#visit_texpr state)
    def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_map_visitor
    (obj : ctx -> fun_decl -> < visit_texpr : unit -> texpr -> texpr ; .. >)
    (ctx : ctx) (def : fun_decl) : fun_decl =
  lift_expr_map_visitor_with_state obj () ctx def

let lift_iter_fun_decl_body (f : ctx -> fun_decl -> fun_body -> unit)
    (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_all_fun_decl_body ctx.fresh_fvar_id (f ctx def) def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor_with_state
    (obj : ctx -> fun_decl -> < visit_texpr : 'a -> texpr -> unit ; .. >)
    (state : 'a) (ctx : ctx) (def : fun_decl) : unit =
  (* We open all the bound variables in the body before exploring it, then
     close them all after performing the updates - this makes it easier to
     deal with variables *)
  iter_open_all_fun_decl_body_expr ctx.fresh_fvar_id
    ((obj ctx def)#visit_texpr state)
    def

(** Lift a visitor of expressions to a function which updates a function body *)
let lift_expr_iter_visitor
    (obj : ctx -> fun_decl -> < visit_texpr : unit -> texpr -> unit ; .. >)
    (ctx : ctx) (def : fun_decl) : unit =
  lift_expr_iter_visitor_with_state obj () ctx def

let open_fun_body ctx = open_fun_body ctx.fresh_fvar_id
let open_all_fun_body ctx = open_all_fun_body ctx.fresh_fvar_id
let open_lambdas ctx = open_lambdas ctx.fresh_fvar_id
let open_binder ctx = open_binder ctx.fresh_fvar_id
let open_binders ctx = open_binders ctx.fresh_fvar_id
let open_lets ctx = open_lets ctx.fresh_fvar_id
let open_loop_body ctx = open_loop_body ctx.fresh_fvar_id
let mk_fresh_fvar ctx = mk_fresh_fvar ctx.fresh_fvar_id
let open_all_texpr ctx = open_all_texpr ctx.fresh_fvar_id

let opt_destruct_loop_result_decompose_outputs ctx =
  opt_destruct_loop_result_decompose_outputs ctx.fresh_fvar_id
