open Types
open TypesUtils
open Expressions
open Values
open LlbcAst
open SymbolicAst

let mk_mplace (span : Meta.span) (p : place) (ctx : Contexts.eval_ctx) : mplace
    =
  let rec place_to_mplace (place : place) : mplace =
    match place.kind with
    | PlaceLocal var_id ->
        PlaceLocal (Contexts.ctx_lookup_real_var_binder span ctx var_id)
    | PlaceProjection (subplace, pe) ->
        PlaceProjection (place_to_mplace subplace, pe)
    | PlaceGlobal gref -> PlaceGlobal gref
  in
  place_to_mplace p

let mk_opt_mplace (span : Meta.span) (p : place option)
    (ctx : Contexts.eval_ctx) : mplace option =
  Option.map (fun p -> mk_mplace span p ctx) p

let mk_opt_place_from_op (span : Meta.span) (op : operand)
    (ctx : Contexts.eval_ctx) : mplace option =
  match op with
  | Copy p | Move p -> Some (mk_mplace span p ctx)
  | Constant _ -> None

let mk_emeta (m : emeta) (e : expr) : expr = Meta (m, e)

let synthesize_symbolic_expansion (span : Meta.span) (sv : symbolic_value)
    (place : mplace option) (seel : symbolic_expansion option list)
    (el : expr list) : expr =
  let ls = List.combine seel el in
  (* Match on the symbolic value type to know which can of expansion happened *)
  let expansion =
    match sv.sv_ty with
    | TLiteral TBool -> (
        (* Boolean expansion: there should be two branches *)
        match ls with
        | [
         (Some (SeLiteral (VBool true)), true_exp);
         (Some (SeLiteral (VBool false)), false_exp);
        ] -> ExpandBool (true_exp, false_exp)
        | _ -> [%craise] span "Ill-formed boolean expansion")
    | TLiteral (TInt _) | TLiteral (TUInt _) ->
        let int_ty = ty_as_integer sv.sv_ty in
        (* Switch over an integer: split between the "regular" branches
           and the "otherwise" branch (which should be the last branch) *)
        let branches, otherwise = Collections.List.pop_last ls in
        (* For all the regular branches, the symbolic value should have
         * been expanded to a constant *)
        let get_scalar (see : symbolic_expansion option) : scalar_value =
          match see with
          | Some (SeLiteral (VScalar cv)) ->
              [%sanity_check] span (Scalars.get_ty cv = int_ty);
              cv
          | _ -> [%craise] span "Unreachable"
        in
        let branches =
          List.map (fun (see, exp) -> (get_scalar see, exp)) branches
        in
        (* For the otherwise branch, the symbolic value should have been left
         * unchanged *)
        let otherwise_see, otherwise = otherwise in
        [%sanity_check] span (otherwise_see = None);
        (* Return *)
        ExpandInt (int_ty, branches, otherwise)
    | TLiteral (TFloat _) ->
        [%craise] span "Float are not supported in Aeneas yet"
    | TAdt _ ->
        (* Branching: it is necessarily an enumeration expansion *)
        let get_variant (see : symbolic_expansion option) :
            VariantId.id option * symbolic_value list =
          match see with
          | Some (SeAdt (vid, fields)) -> (vid, fields)
          | _ -> [%craise] span "Ill-formed branching ADT expansion"
        in
        let exp =
          List.map
            (fun (see, exp) ->
              let vid, fields = get_variant see in
              (vid, fields, exp))
            ls
        in
        ExpandAdt exp
    | TRef (_, _, _) -> (
        (* Reference expansion: there should be one branch *)
        match ls with
        | [ (Some see, exp) ] -> ExpandNoBranch (see, exp)
        | _ -> [%craise] span "Ill-formed borrow expansion")
    | TVar _
    | TLiteral TChar
    | TNever
    | TTraitType _
    | TFnDef _
    | TFnPtr _
    | TRawPtr _
    | TDynTrait _
    | TPtrMetadata _
    | TError _ -> [%craise] span "Ill-formed symbolic expansion"
  in
  Expansion (place, sv, expansion)

let synthesize_symbolic_expansion_no_branching (span : Meta.span)
    (sv : symbolic_value) (place : mplace option) (see : symbolic_expansion)
    (e : expr) : expr =
  synthesize_symbolic_expansion span sv place [ Some see ] [ e ]

let synthesize_function_call (span : Meta.span) (call_id : call_id)
    (ctx : Contexts.eval_ctx) (sg : (fun_sig * inst_fun_sig) option)
    (abstractions : AbsId.id list) (generics : generic_args)
    (args : tvalue list) (args_places : mplace option list)
    (dest : symbolic_value) (dest_place : mplace option) (e : expr) : expr =
  let sg, inst_sg =
    match sg with
    | Some (sg, inst_sg) -> (Some sg, Some inst_sg)
    | None -> (None, None)
  in
  let call =
    {
      call_id;
      span;
      ctx;
      sg;
      inst_sg;
      abstractions;
      generics;
      args;
      dest;
      args_places;
      dest_place;
    }
  in
  FunCall (call, e)

let synthesize_global_eval (gref : global_decl_ref) (dest : symbolic_value)
    (e : expr) : expr =
  EvalGlobal (gref.id, gref.generics, dest, e)

let synthesize_regular_function_call (span : Meta.span) (fun_id : fn_ptr_kind)
    (call_id : FunCallId.id) (ctx : Contexts.eval_ctx) (sg : fun_sig)
    (inst_sg : inst_fun_sig) (abstractions : AbsId.id list)
    (generics : generic_args) (args : tvalue list)
    (args_places : mplace option list) (dest : symbolic_value)
    (dest_place : mplace option) (e : expr) : expr =
  synthesize_function_call span
    (Fun (fun_id, call_id))
    ctx
    (Some (sg, inst_sg))
    abstractions generics args args_places dest dest_place e

let synthesize_unary_op (span : Meta.span) (ctx : Contexts.eval_ctx)
    (unop : unop) (arg : tvalue) (arg_place : mplace option)
    (dest : symbolic_value) (dest_place : mplace option) (e : expr) : expr =
  let generics = empty_generic_args in
  synthesize_function_call span (Unop unop) ctx None [] generics [ arg ]
    [ arg_place ] dest dest_place e

let synthesize_binary_op (span : Meta.span) (ctx : Contexts.eval_ctx)
    (binop : binop) (arg0 : tvalue) (arg0_place : mplace option) (arg1 : tvalue)
    (arg1_place : mplace option) (dest : symbolic_value)
    (dest_place : mplace option) (e : expr) : expr =
  let generics = empty_generic_args in
  synthesize_function_call span (Binop binop) ctx None [] generics
    [ arg0; arg1 ] [ arg0_place; arg1_place ] dest dest_place e

let synthesize_end_abstraction (ctx : Contexts.eval_ctx) (abs : abs) (e : expr)
    : expr =
  EndAbs (ctx, abs, e)

let synthesize_assignment (ctx : Contexts.eval_ctx) (lplace : mplace)
    (rvalue : tvalue) (rplace : mplace option) (e : expr) : expr =
  Meta (Assignment (ctx, lplace, rvalue, rplace), e)

let synthesize_assertion (ctx : Contexts.eval_ctx) (v : tvalue) (e : expr) =
  Assertion (ctx, v, e)

let save_snapshot (ctx : Contexts.eval_ctx) : expr -> expr =
  (* Note that we take care to generate the fresh meta id immediately, so
     that we can use `-mark-ids` to stop at the moment when this function is
     called, rather than the moment when the expression is reconstructed
     (which happens at the end of the symbolic execution) *)
  let mid = ctx.fresh_meta_id () in
  fun e -> Meta (Snapshot (mid, ctx), e)
