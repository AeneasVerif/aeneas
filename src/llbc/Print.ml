include Charon.PrintUtils
include Charon.PrintTypes
include Charon.PrintLlbcAst
open Values
include PrintBase
open Charon.PrintTypes
open Charon.PrintExpressions
open Charon.PrintLlbcAst.Ast
open Types
open Expressions
open LlbcAst
open Contexts
module Types = Charon.PrintTypes
module Expressions = Charon.PrintExpressions

(** Pretty-printing for contexts *)
module Contexts = struct
  include PrintBase.Env

  let decls_ctx_to_fmt_env (ctx : decls_ctx) : fmt_env =
    Crate.crate_to_fmt_env ctx.crate

  let eval_ctx_to_fmt_env (ctx : eval_ctx) : fmt_env =
    (* Below: it is always safe to omit fields - if an id can't be found at
       printing time, we print the id (in raw form) instead of the name it
       designates. *)
    (* For the locals: we retrieve the information from the environment.
       Note that the locals don't need to be ordered based on their indices.
    *)
    let rec env_to_locals (env : env) : (LocalId.id * string option) list =
      match env with
      | [] | EFrame :: _ -> []
      | EAbs _ :: env -> env_to_locals env
      | EBinding (BVar b, _) :: env -> (b.index, b.name) :: env_to_locals env
      | EBinding (BDummy _, _) :: env -> env_to_locals env
    in
    let locals = env_to_locals ctx.env in
    {
      crate = ctx.crate;
      generics =
        [
          {
            TypesUtils.empty_generic_params with
            types = ctx.type_vars;
            const_generics = ctx.const_generic_vars;
            (* The regions have been transformed to region groups *)
            regions = [];
            (* We don't need the trait clauses so we initialize them to empty *)
            trait_clauses = [];
          };
        ];
      locals;
    }

  (** Split an [env] at every occurrence of [Frame], eliminating those elements.
      Also reorders the frames and the values in the frames according to the
      following order: * frames: from the current frame to the first pushed
      (oldest frame) * values: from the first pushed (oldest) to the last pushed
  *)
  let split_env_according_to_frames (env : env) : env list =
    let rec split_aux (frames : env list) (curr_frame : env) (env : env) =
      match env with
      | [] ->
          if List.length curr_frame > 0 then curr_frame :: frames else frames
      | EFrame :: env' -> split_aux (curr_frame :: frames) [] env'
      | ev :: env' -> split_aux frames (ev :: curr_frame) env'
    in
    let frames = split_aux [] [] env in
    frames

  let eval_ctx_to_string ?(span : Meta.span option = None)
      ?(verbose : bool = false) ?(filter : bool = true)
      ?(with_var_types : bool = true) (ctx : eval_ctx) : string =
    let fmt_env = eval_ctx_to_fmt_env ctx in
    let ended_regions = RegionId.Set.to_string None ctx.ended_regions in
    let frames = split_env_according_to_frames ctx.env in
    let num_frames = List.length frames in
    let frames =
      List.mapi
        (fun i f ->
          let num_bindings = ref 0 in
          let num_dummies = ref 0 in
          let num_abs = ref 0 in
          List.iter
            (fun ev ->
              match ev with
              | EBinding (BDummy _, _) -> num_dummies := !num_abs + 1
              | EBinding (BVar _, _) -> num_bindings := !num_bindings + 1
              | EAbs _ -> num_abs := !num_abs + 1
              | _ -> [%craise_opt_span] span "Unreachable")
            f;
          "\n# Frame " ^ string_of_int i ^ ":" ^ "\n- locals: "
          ^ string_of_int !num_bindings
          ^ "\n- dummy bindings: " ^ string_of_int !num_dummies
          ^ "\n- abstractions: " ^ string_of_int !num_abs ^ "\n"
          ^ env_to_string ~span filter fmt_env verbose with_var_types
              ctx.ended_regions f
          ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames
end

(** Pretty-printing for LLBC ASTs (functions based on an evaluation context) *)
module EvalCtx = struct
  open Values
  open Contexts

  let name_to_string (ctx : eval_ctx) (n : name) : string =
    let env = eval_ctx_to_fmt_env ctx in
    name_to_string env n

  let real_var_binder_to_string (ctx : eval_ctx) (n : real_var_binder) : string
      =
    let env = eval_ctx_to_fmt_env ctx in
    real_var_binder_to_string env n

  let ty_to_string (ctx : eval_ctx) (t : ty) : string =
    let env = eval_ctx_to_fmt_env ctx in
    ty_to_string env t

  let constant_expr_to_string (ctx : eval_ctx) (c : constant_expr) : string =
    let env = eval_ctx_to_fmt_env ctx in
    constant_expr_to_string env c

  let generic_params_to_strings (ctx : eval_ctx) (x : generic_params) :
      string list * string list =
    let env = eval_ctx_to_fmt_env ctx in
    generic_params_to_strings env x

  let generic_args_to_string (ctx : eval_ctx) (x : generic_args) : string =
    let env = eval_ctx_to_fmt_env ctx in
    generic_args_to_string env x

  let trait_ref_to_string (ctx : eval_ctx) (x : trait_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_ref_to_string env x

  let trait_decl_ref_region_binder_to_string (ctx : eval_ctx)
      (x : trait_decl_ref region_binder) : string =
    let env = eval_ctx_to_fmt_env ctx in
    region_binder_to_string trait_decl_ref_to_string env x

  let trait_impl_ref_to_string (ctx : eval_ctx) (x : trait_impl_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_impl_ref_to_string env x

  let trait_decl_ref_to_string (ctx : eval_ctx) (x : trait_decl_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_decl_ref_to_string env x

  (* Note: this will fail on `Dyn` and `BuiltinOrAuto` instances, because these
     require the full `trait_ref` for printing. *)
  let trait_ref_kind_to_string (ctx : eval_ctx) (x : trait_ref_kind) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_ref_kind_to_string env None x

  let borrow_content_to_string ?(span : Meta.span option = None)
      (ctx : eval_ctx) (bc : borrow_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    borrow_content_to_string ~span env bc

  let loan_content_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (lc : loan_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    loan_content_to_string ~span env lc

  let aborrow_content_to_string ?(span : Meta.span option = None)
      (ctx : eval_ctx) (bc : aborrow_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aborrow_content_to_string ~span env bc

  let eborrow_content_to_string ?(span : Meta.span option = None)
      (ctx : eval_ctx) (ty : ty) (bc : eborrow_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    let aenv = empty_evalue_env in
    eborrow_content_to_string ~span env aenv "" "  " ty bc

  let aproj_borrows_to_string ?(with_ended = true) (ctx : eval_ctx)
      (x : aproj_borrows) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aproj_borrows_to_string ~with_ended env x

  let aproj_loans_to_string ?(with_ended = true) (ctx : eval_ctx)
      (x : aproj_loans) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aproj_loans_to_string ~with_ended env x

  let symbolic_proj_to_string ctx (proj : symbolic_proj) : string =
    let env = eval_ctx_to_fmt_env ctx in
    symbolic_proj_to_string env proj

  let aloan_content_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (lc : aloan_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aloan_content_to_string ~span env lc

  let eloan_content_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (ty : ty) (lc : eloan_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    let aenv = empty_evalue_env in
    eloan_content_to_string ~span env aenv "" "  " ty lc

  let aproj_to_string (ctx : eval_ctx) (p : aproj) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aproj_to_string env p

  let eproj_to_string (ctx : eval_ctx) (p : eproj) : string =
    let env = eval_ctx_to_fmt_env ctx in
    eproj_to_string env p

  let symbolic_value_to_string (ctx : eval_ctx) (sv : symbolic_value) : string =
    let env = eval_ctx_to_fmt_env ctx in
    symbolic_value_to_string env sv

  let tvalue_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (v : tvalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    tvalue_to_string ~span env v

  let tavalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (ctx : eval_ctx) (v : tavalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    tavalue_to_string ~span ~with_ended env v

  let tevalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (ctx : eval_ctx) (v : tevalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    let aenv = empty_evalue_env in
    tevalue_to_string ~span ~with_ended env aenv "" "  " v

  let tepat_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (v : tepat) : string =
    let env = eval_ctx_to_fmt_env ctx in
    let aenv = empty_evalue_env in
    snd (tepat_to_string ~span env aenv "" "  " v)

  let place_to_string (ctx : eval_ctx) (op : place) : string =
    let env = eval_ctx_to_fmt_env ctx in
    place_to_string env op

  let cast_kind_to_string (ctx : eval_ctx) (op : cast_kind) : string =
    let env = eval_ctx_to_fmt_env ctx in
    cast_kind_to_string env op

  let unop_to_string (ctx : eval_ctx) (op : unop) : string =
    let env = eval_ctx_to_fmt_env ctx in
    unop_to_string env op

  let operand_to_string (ctx : eval_ctx) (op : operand) : string =
    let env = eval_ctx_to_fmt_env ctx in
    operand_to_string env op

  let rvalue_to_string (ctx : eval_ctx) (rval : rvalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    rvalue_to_string env rval

  let call_to_string (ctx : eval_ctx) (call : call) : string =
    let env = eval_ctx_to_fmt_env ctx in
    call_to_string env "" call

  let fun_decl_to_string (ctx : eval_ctx) (f : fun_decl) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fun_decl_to_string env "" "  " f

  let fun_sig_to_string (ctx : eval_ctx) (x : bound_fun_sig) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fun_sig_to_string env "" "  " x

  let inst_fun_sig_to_string (ctx : eval_ctx) (x : LlbcAst.inst_fun_sig) :
      string =
    let env = eval_ctx_to_fmt_env ctx in
    inst_fun_sig_to_string env x

  let fn_ptr_kind_to_string (ctx : eval_ctx) (x : fn_ptr_kind) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fn_ptr_kind_to_string env x

  let block_to_string (ctx : eval_ctx) (indent : string) (indent_incr : string)
      (e : block) : string =
    let env = eval_ctx_to_fmt_env ctx in
    block_to_string env indent indent_incr e

  let local_to_string (ctx : eval_ctx) (x : local) : string =
    local_to_string x ^ " : " ^ ty_to_string ctx x.local_ty

  let statement_to_string (ctx : eval_ctx) (indent : string)
      (indent_incr : string) (e : statement) : string =
    let env = eval_ctx_to_fmt_env ctx in
    statement_to_string env indent indent_incr e

  let trait_impl_to_string (ctx : eval_ctx) (timpl : trait_impl) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_impl_to_string env "  " "  " timpl

  let env_elem_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (indent : string) (indent_incr : string) (ev : env_elem) : string =
    let env = eval_ctx_to_fmt_env ctx in
    env_elem_to_string ~span env false true indent indent_incr ev

  let abs_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      ?(with_ended : bool = false) (indent : string) (indent_incr : string)
      (abs : abs) : string =
    let env = eval_ctx_to_fmt_env ctx in
    abs_to_string ~span env ~with_ended false indent indent_incr abs

  let abs_cont_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      ?(with_ended : bool = false) (indent : string) (indent_incr : string)
      (cont : abs_cont) : string =
    let env = eval_ctx_to_fmt_env ctx in
    abs_cont_to_string ~span env ~with_ended indent indent_incr cont
end
