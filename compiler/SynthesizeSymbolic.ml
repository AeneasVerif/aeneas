open Types
open TypesUtils
open Expressions
open Values
open LlbcAst
open SymbolicAst
open Errors

let mk_mplace (span : Meta.span) (p : place) (ctx : Contexts.eval_ctx) : mplace
    =
  let rec place_to_projection_and_var (place : place) :
      var_id * projection_elem list =
    match place.kind with
    | PlaceBase var_id -> (var_id, [])
    | PlaceProjection (subplace, pe) ->
        let var_id, proj = place_to_projection_and_var subplace in
        (var_id, pe :: proj)
  in
  let bv, proj = place_to_projection_and_var p in
  let bv = Contexts.ctx_lookup_var_binder span ctx bv in
  { bv; projection = proj }

let mk_opt_mplace (span : Meta.span) (p : place option)
    (ctx : Contexts.eval_ctx) : mplace option =
  Option.map (fun p -> mk_mplace span p ctx) p

let mk_opt_place_from_op (span : Meta.span) (op : operand)
    (ctx : Contexts.eval_ctx) : mplace option =
  match op with
  | Copy p | Move p -> Some (mk_mplace span p ctx)
  | Constant _ -> None

let mk_espan (m : espan) (e : expression) : expression = Meta (m, e)

let synthesize_symbolic_expansion (span : Meta.span) (sv : symbolic_value)
    (place : mplace option) (seel : symbolic_expansion option list)
    (el : expression list) : expression =
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
        | _ -> craise __FILE__ __LINE__ span "Ill-formed boolean expansion")
    | TLiteral (TInteger int_ty) ->
        (* Switch over an integer: split between the "regular" branches
           and the "otherwise" branch (which should be the last branch) *)
        let branches, otherwise = Collections.List.pop_last ls in
        (* For all the regular branches, the symbolic value should have
         * been expanded to a constant *)
        let get_scalar (see : symbolic_expansion option) : scalar_value =
          match see with
          | Some (SeLiteral (VScalar cv)) ->
              sanity_check __FILE__ __LINE__ (cv.int_ty = int_ty) span;
              cv
          | _ -> craise __FILE__ __LINE__ span "Unreachable"
        in
        let branches =
          List.map (fun (see, exp) -> (get_scalar see, exp)) branches
        in
        (* For the otherwise branch, the symbolic value should have been left
         * unchanged *)
        let otherwise_see, otherwise = otherwise in
        sanity_check __FILE__ __LINE__ (otherwise_see = None) span;
        (* Return *)
        ExpandInt (int_ty, branches, otherwise)
    | TLiteral (TFloat _) ->
        craise __FILE__ __LINE__ span "Float are not supported in Aeneas yet"
    | TAdt (_, _) ->
        (* Branching: it is necessarily an enumeration expansion *)
        let get_variant (see : symbolic_expansion option) :
            VariantId.id option * symbolic_value list =
          match see with
          | Some (SeAdt (vid, fields)) -> (vid, fields)
          | _ ->
              craise __FILE__ __LINE__ span "Ill-formed branching ADT expansion"
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
        | _ -> craise __FILE__ __LINE__ span "Ill-formed borrow expansion")
    | TVar _
    | TLiteral TChar
    | TNever | TTraitType _ | TArrow _ | TRawPtr _ | TDynTrait _ ->
        craise __FILE__ __LINE__ span "Ill-formed symbolic expansion"
  in
  Expansion (place, sv, expansion)

let synthesize_symbolic_expansion_no_branching (span : Meta.span)
    (sv : symbolic_value) (place : mplace option) (see : symbolic_expansion)
    (e : expression) : expression =
  synthesize_symbolic_expansion span sv place [ Some see ] [ e ]

let synthesize_function_call (call_id : call_id) (ctx : Contexts.eval_ctx)
    (sg : fun_sig option) (regions_hierarchy : region_var_groups)
    (abstractions : AbstractionId.id list) (generics : generic_args)
    (trait_method_generics : (generic_args * trait_instance_id) option)
    (args : typed_value list) (args_places : mplace option list)
    (dest : symbolic_value) (dest_place : mplace option) (e : expression) :
    expression =
  let call =
    {
      call_id;
      ctx;
      sg;
      regions_hierarchy;
      abstractions;
      generics;
      trait_method_generics;
      args;
      dest;
      args_places;
      dest_place;
    }
  in
  FunCall (call, e)

let synthesize_global_eval (gref : global_decl_ref) (dest : symbolic_value)
    (e : expression) : expression =
  EvalGlobal (gref.global_id, gref.global_generics, dest, e)

let synthesize_regular_function_call (fun_id : fun_id_or_trait_method_ref)
    (call_id : FunCallId.id) (ctx : Contexts.eval_ctx) (sg : fun_sig)
    (regions_hierarchy : region_var_groups)
    (abstractions : AbstractionId.id list) (generics : generic_args)
    (trait_method_generics : (generic_args * trait_instance_id) option)
    (args : typed_value list) (args_places : mplace option list)
    (dest : symbolic_value) (dest_place : mplace option) (e : expression) :
    expression =
  synthesize_function_call
    (Fun (fun_id, call_id))
    ctx (Some sg) regions_hierarchy abstractions generics trait_method_generics
    args args_places dest dest_place e

let synthesize_unary_op (ctx : Contexts.eval_ctx) (unop : unop)
    (arg : typed_value) (arg_place : mplace option) (dest : symbolic_value)
    (dest_place : mplace option) (e : expression) : expression =
  let generics = empty_generic_args in
  synthesize_function_call (Unop unop) ctx None [] [] generics None [ arg ]
    [ arg_place ] dest dest_place e

let synthesize_binary_op (ctx : Contexts.eval_ctx) (binop : binop)
    (arg0 : typed_value) (arg0_place : mplace option) (arg1 : typed_value)
    (arg1_place : mplace option) (dest : symbolic_value)
    (dest_place : mplace option) (e : expression) : expression =
  let generics = empty_generic_args in
  synthesize_function_call (Binop binop) ctx None [] [] generics None
    [ arg0; arg1 ] [ arg0_place; arg1_place ] dest dest_place e

let synthesize_end_abstraction (ctx : Contexts.eval_ctx) (abs : abs)
    (e : expression) : expression =
  EndAbstraction (ctx, abs, e)

let synthesize_assignment (ctx : Contexts.eval_ctx) (lplace : mplace)
    (rvalue : typed_value) (rplace : mplace option) (e : expression) :
    expression =
  Meta (Assignment (ctx, lplace, rvalue, rplace), e)

let synthesize_assertion (ctx : Contexts.eval_ctx) (v : typed_value)
    (e : expression) =
  Assertion (ctx, v, e)

let synthesize_forward_end (ctx : Contexts.eval_ctx)
    (loop_input_values : typed_value SymbolicValueId.Map.t option)
    (e : expression) (el : expression RegionGroupId.Map.t) =
  ForwardEnd (ctx, loop_input_values, e, el)

let synthesize_loop (loop_id : LoopId.id) (input_svalues : symbolic_value list)
    (fresh_svalues : SymbolicValueId.Set.t)
    (rg_to_given_back_tys : ty list RegionGroupId.Map.t) (end_expr : expression)
    (loop_expr : expression) (span : Meta.span) : expression =
  Loop
    {
      loop_id;
      input_svalues;
      fresh_svalues;
      rg_to_given_back_tys;
      end_expr;
      loop_expr;
      span;
    }

let save_snapshot (ctx : Contexts.eval_ctx) (e : expression) : expression =
  Meta (Snapshot ctx, e)
