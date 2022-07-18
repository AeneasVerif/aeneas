open Errors
open LlbcAstUtils
open Pure
open PureUtils
module Id = Identifiers
module M = Modules
module S = SymbolicAst
module TA = TypesAnalysis
module L = Logging
module PP = PrintPure
module FA = FunsAnalysis

(** The local logger *)
let log = L.symbolic_to_pure_log

type config = {
  filter_useless_back_calls : bool;
      (** If `true`, filter the useless calls to backward functions.
       
          The useless calls are calls to backward functions which have no outputs.
          This case happens if the original Rust function only takes *shared* borrows
          as inputs, and is thus pretty common.

          We are allowed to do this only because in this specific case,
          the backward function fails *exactly* when the forward function fails
          (they actually do exactly the same thing, the only difference being
          that the forward function can potentially return a value), and upon
          reaching the place where we should introduce a call to the backward
          function, we know we have introduced a call to the forward function.
          
          Also note that in general, backward functions "do more things" than
          forward functions, and have more opportunities to fail (even though
          in the generated code, backward functions should fail exactly when
          the forward functions fail).
          
          We might want to move this optimization to the micro-passes subsequent
          to the translation from symbolic to pure, but it is really super easy
          to do it when going from symbolic to pure.
          Note that we later filter the useless *forward* calls in the micro-passes,
          where it is more natural to do.
       *)
}

type type_context = {
  llbc_type_decls : T.type_decl TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
      (** We use this for type-checking (for sanity checks) when translating
          values and functions.
          This map is empty when we translate the types, then contains all
          the translated types when we translate the functions.
       *)
  types_infos : TA.type_infos; (* TODO: rename to type_infos *)
}

type fun_sig_named_outputs = {
  sg : fun_sig;  (** A function signature *)
  output_names : string option list;
      (** In case the signature is for a backward function, we may provides names
          for the outputs. The reason is that the outputs of backward functions
          come from (in case there are no nested borrows) borrows present in the
          inputs of the original rust function. In this situation, we can use the
          names of those inputs to name the outputs. Those names are very useful
          to generate beautiful codes (we may need to introduce temporary variables
          in the bodies of the backward functions to store the returned values, in
          which case we use those names).
       *)
}

type fun_context = {
  llbc_fun_decls : A.fun_decl A.FunDeclId.Map.t;
  fun_sigs : fun_sig_named_outputs RegularFunIdMap.t;  (** *)
  fun_infos : FA.fun_info A.FunDeclId.Map.t;
}

type global_context = {
  llbc_global_decls : A.global_decl A.GlobalDeclId.Map.t;
}

type call_info = {
  forward : S.call;
  forward_inputs : texpression list;
      (** Remember the list of inputs given to the forward function.

          Those inputs include the state input, if pertinent (in which case
          it is the last input).
       *)
  backwards : (V.abs * texpression list) T.RegionGroupId.Map.t;
      (** A map from region group id (i.e., backward function id) to
          pairs (abstraction, additional arguments received by the backward function)
       
          TODO: remove? it is also in the bs_ctx ("abstractions" field)
       *)
}
(** Whenever we translate a function call or an ended abstraction, we
    store the related information (this is useful when translating ended
    children abstractions).
 *)

type bs_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  global_context : global_context;
  fun_decl : A.fun_decl;
  bid : T.RegionGroupId.id option;  (** TODO: rename *)
  sg : fun_sig;
      (** The function signature - useful in particular to translate `Panic` *)
  sv_to_var : var V.SymbolicValueId.Map.t;
      (** Whenever we encounter a new symbolic value (introduced because of
          a symbolic expansion or upon ending an abstraction, for instance)
          we introduce a new variable (with a let-binding).
       *)
  var_counter : VarId.generator;
  state_var : VarId.id;
      (** The current state variable, in case we use a state *)
  forward_inputs : var list;
      (** The input parameters for the forward function *)
  backward_inputs : var list T.RegionGroupId.Map.t;
      (** The input parameters for the backward functions *)
  backward_outputs : var list T.RegionGroupId.Map.t;
      (** The variables that the backward functions will output *)
  calls : call_info V.FunCallId.Map.t;
      (** The function calls we encountered so far *)
  abstractions : (V.abs * texpression list) V.AbstractionId.Map.t;
      (** The ended abstractions we encountered so far, with their additional input arguments  *)
}
(** Body synthesis context *)

let type_check_pattern (ctx : bs_ctx) (v : typed_pattern) : unit =
  let env = VarId.Map.empty in
  let ctx = { PureTypeCheck.type_decls = ctx.type_context.type_decls; env } in
  let _ = PureTypeCheck.check_typed_pattern ctx v in
  ()

let type_check_texpression (ctx : bs_ctx) (e : texpression) : unit =
  let env = VarId.Map.empty in
  let ctx = { PureTypeCheck.type_decls = ctx.type_context.type_decls; env } in
  PureTypeCheck.check_texpression ctx e

(* TODO: move *)
let bs_ctx_to_ast_formatter (ctx : bs_ctx) : Print.LlbcAst.ast_formatter =
  Print.LlbcAst.fun_decl_to_ast_formatter
    ctx.type_context.llbc_type_decls
    ctx.fun_context.llbc_fun_decls
    ctx.global_context.llbc_global_decls
    ctx.fun_decl

let bs_ctx_to_pp_ast_formatter (ctx : bs_ctx) : PrintPure.ast_formatter =
  let type_params = ctx.fun_decl.signature.type_params in
  let type_decls = ctx.type_context.llbc_type_decls in
  let fun_decls = ctx.fun_context.llbc_fun_decls in
  let global_decls = ctx.global_context.llbc_global_decls in
  PrintPure.mk_ast_formatter type_decls fun_decls global_decls type_params

let ty_to_string (ctx : bs_ctx) (ty : ty) : string =
  let fmt = bs_ctx_to_pp_ast_formatter ctx in
  let fmt = PrintPure.ast_to_type_formatter fmt in
  PrintPure.ty_to_string fmt ty

let type_decl_to_string (ctx : bs_ctx) (def : type_decl) : string =
  let type_params = def.type_params in
  let type_decls = ctx.type_context.llbc_type_decls in
  let fmt = PrintPure.mk_type_formatter type_decls type_params in
  PrintPure.type_decl_to_string fmt def

let texpression_to_string (ctx : bs_ctx) (e : texpression) : string =
  let fmt = bs_ctx_to_pp_ast_formatter ctx in
  PrintPure.texpression_to_string fmt false "" "  " e

let fun_sig_to_string (ctx : bs_ctx) (sg : fun_sig) : string =
  let type_params = sg.type_params in
  let type_decls = ctx.type_context.llbc_type_decls in
  let fun_decls = ctx.fun_context.llbc_fun_decls in
  let global_decls = ctx.global_context.llbc_global_decls in
  let fmt = PrintPure.mk_ast_formatter type_decls fun_decls global_decls type_params in
  PrintPure.fun_sig_to_string fmt sg

let fun_decl_to_string (ctx : bs_ctx) (def : Pure.fun_decl) : string =
  let type_params = def.signature.type_params in
  let type_decls = ctx.type_context.llbc_type_decls in
  let fun_decls = ctx.fun_context.llbc_fun_decls in
  let global_decls = ctx.global_context.llbc_global_decls in
  let fmt = PrintPure.mk_ast_formatter type_decls fun_decls global_decls type_params in
  PrintPure.fun_decl_to_string fmt def

(* TODO: move *)
let abs_to_string (ctx : bs_ctx) (abs : V.abs) : string =
  let fmt = bs_ctx_to_ast_formatter ctx in
  let fmt = Print.LlbcAst.ast_to_value_formatter fmt in
  let indent = "" in
  let indent_incr = "  " in
  Print.Values.abs_to_string fmt indent indent_incr abs

let get_instantiated_fun_sig (fun_id : A.fun_id)
    (back_id : T.RegionGroupId.id option) (tys : ty list) (ctx : bs_ctx) :
    inst_fun_sig =
  (* Lookup the non-instantiated function signature *)
  let sg =
    (RegularFunIdMap.find (fun_id, back_id) ctx.fun_context.fun_sigs).sg
  in
  (* Create the substitution *)
  let tsubst = make_type_subst sg.type_params tys in
  (* Apply *)
  fun_sig_substitute tsubst sg

let bs_ctx_lookup_llbc_type_decl (id : TypeDeclId.id) (ctx : bs_ctx) :
    T.type_decl =
  TypeDeclId.Map.find id ctx.type_context.llbc_type_decls

let bs_ctx_lookup_llbc_fun_decl (id : A.FunDeclId.id) (ctx : bs_ctx) : A.fun_decl
    =
  A.FunDeclId.Map.find id ctx.fun_context.llbc_fun_decls

(* TODO: move *)
let bs_ctx_lookup_local_function_sig (def_id : A.FunDeclId.id)
    (back_id : T.RegionGroupId.id option) (ctx : bs_ctx) : fun_sig =
  let id = (A.Regular def_id, back_id) in
  (RegularFunIdMap.find id ctx.fun_context.fun_sigs).sg

let bs_ctx_register_forward_call (call_id : V.FunCallId.id) (forward : S.call)
    (args : texpression list) (ctx : bs_ctx) : bs_ctx =
  let calls = ctx.calls in
  assert (not (V.FunCallId.Map.mem call_id calls));
  let info =
    { forward; forward_inputs = args; backwards = T.RegionGroupId.Map.empty }
  in
  let calls = V.FunCallId.Map.add call_id info calls in
  { ctx with calls }

(** [back_args]: the *additional* list of inputs received by the backward function *)
let bs_ctx_register_backward_call (abs : V.abs) (back_args : texpression list)
    (ctx : bs_ctx) : bs_ctx * fun_id =
  (* Insert the abstraction in the call informations *)
  let back_id = abs.back_id in
  let info = V.FunCallId.Map.find abs.call_id ctx.calls in
  assert (not (T.RegionGroupId.Map.mem back_id info.backwards));
  let backwards =
    T.RegionGroupId.Map.add back_id (abs, back_args) info.backwards
  in
  let info = { info with backwards } in
  let calls = V.FunCallId.Map.add abs.call_id info ctx.calls in
  (* Insert the abstraction in the abstractions map *)
  let abstractions = ctx.abstractions in
  assert (not (V.AbstractionId.Map.mem abs.abs_id abstractions));
  let abstractions =
    V.AbstractionId.Map.add abs.abs_id (abs, back_args) abstractions
  in
  (* Retrieve the fun_id *)
  let fun_id =
    match info.forward.call_id with
    | S.Fun (fid, _) -> Regular (fid, Some abs.back_id)
    | S.Unop _ | S.Binop _ -> raise (Failure "Unreachable")
  in
  (* Update the context and return *)
  ({ ctx with calls; abstractions }, fun_id)

let rec translate_sty (ty : T.sty) : ty =
  let translate = translate_sty in
  match ty with
  | T.Adt (type_id, regions, tys) -> (
      (* Can't translate types with regions for now *)
      assert (regions = []);
      let tys = List.map translate tys in
      match type_id with
      | T.AdtId adt_id -> Adt (AdtId adt_id, tys)
      | T.Tuple -> mk_simpl_tuple_ty tys
      | T.Assumed aty -> (
          match aty with
          | T.Vec -> Adt (Assumed Vec, tys)
          | T.Option -> Adt (Assumed Option, tys)
          | T.Box -> (
              (* Eliminate the boxes *)
              match tys with
              | [ ty ] -> ty
              | _ ->
                  failwith
                    "Box/vec/option type with incorrect number of arguments")))
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> raise (Failure "Unreachable")
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty -> Array (translate ty)
  | Slice ty -> Slice (translate ty)
  | Ref (_, rty, _) -> translate rty

let translate_field (f : T.field) : field =
  let field_name = f.field_name in
  let field_ty = translate_sty f.field_ty in
  { field_name; field_ty }

let translate_fields (fl : T.field list) : field list =
  List.map translate_field fl

let translate_variant (v : T.variant) : variant =
  let variant_name = v.variant_name in
  let fields = translate_fields v.fields in
  { variant_name; fields }

let translate_variants (vl : T.variant list) : variant list =
  List.map translate_variant vl

(** Translate a type def kind to IM *)
let translate_type_decl_kind (kind : T.type_decl_kind) : type_decl_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields fields)
  | T.Enum variants -> Enum (translate_variants variants)
  | T.Opaque -> Opaque

(** Translate a type definition from IM 

    TODO: this is not symbolic to pure but IM to pure. Still, I don't see the
    point of moving this definition for now.
 *)
let translate_type_decl (def : T.type_decl) : type_decl =
  (* Translate *)
  let def_id = def.T.def_id in
  let name = def.name in
  (* Can't translate types with regions for now *)
  assert (def.region_params = []);
  let type_params = def.type_params in
  let kind = translate_type_decl_kind def.T.kind in
  { def_id; name; type_params; kind }

(** Translate a type, seen as an input/output of a forward function
    (preserve all borrows, etc.)
*)

let rec translate_fwd_ty (types_infos : TA.type_infos) (ty : 'r T.ty) : ty =
  let translate = translate_fwd_ty types_infos in
  match ty with
  | T.Adt (type_id, regions, tys) -> (
      (* Can't translate types with regions for now *)
      assert (regions = []);
      (* Translate the type parameters *)
      let t_tys = List.map translate tys in
      (* Eliminate boxes and simplify tuples *)
      match type_id with
      | AdtId _ | T.Assumed (T.Vec | T.Option) ->
          (* No general parametricity for now *)
          assert (not (List.exists (TypesUtils.ty_has_borrows types_infos) tys));
          let type_id =
            match type_id with
            | AdtId adt_id -> AdtId adt_id
            | T.Assumed T.Vec -> Assumed Vec
            | T.Assumed T.Option -> Assumed Option
            | _ -> raise (Failure "Unreachable")
          in
          Adt (type_id, t_tys)
      | Tuple ->
          (* Note that if there is exactly one type, [mk_simpl_tuple_ty] is the
             identity *)
          mk_simpl_tuple_ty t_tys
      | T.Assumed T.Box -> (
          (* We eliminate boxes *)
          (* No general parametricity for now *)
          assert (not (List.exists (TypesUtils.ty_has_borrows types_infos) tys));
          match t_tys with
          | [ bty ] -> bty
          | _ ->
              failwith
                "Unreachable: box/vec/option receives exactly one type \
                 parameter"))
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> raise (Failure "Unreachable")
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | Array ty ->
      assert (not (TypesUtils.ty_has_borrows types_infos ty));
      Array (translate ty)
  | Slice ty ->
      assert (not (TypesUtils.ty_has_borrows types_infos ty));
      Slice (translate ty)
  | Ref (_, rty, _) -> translate rty

(** Simply calls [translate_fwd_ty] *)
let ctx_translate_fwd_ty (ctx : bs_ctx) (ty : 'r T.ty) : ty =
  let types_infos = ctx.type_context.types_infos in
  translate_fwd_ty types_infos ty

(** Translate a type, when some regions may have ended.
    
    We return an option, because the translated type may be empty.
    
    [inside_mut]: are we inside a mutable borrow?
 *)
let rec translate_back_ty (types_infos : TA.type_infos)
    (keep_region : 'r -> bool) (inside_mut : bool) (ty : 'r T.ty) : ty option =
  let translate = translate_back_ty types_infos keep_region inside_mut in
  (* A small helper for "leave" types *)
  let wrap ty = if inside_mut then Some ty else None in
  match ty with
  | T.Adt (type_id, _, tys) -> (
      match type_id with
      | T.AdtId _ | Assumed (T.Vec | T.Option) ->
          (* Don't accept ADTs (which are not tuples) with borrows for now *)
          assert (not (TypesUtils.ty_has_borrows types_infos ty));
          let type_id =
            match type_id with
            | T.AdtId id -> AdtId id
            | T.Assumed T.Vec -> Assumed Vec
            | T.Assumed T.Option -> Assumed Option
            | T.Tuple | T.Assumed T.Box -> raise (Failure "Unreachable")
          in
          if inside_mut then
            let tys_t = List.filter_map translate tys in
            Some (Adt (type_id, tys_t))
          else None
      | Assumed T.Box -> (
          (* Don't accept ADTs (which are not tuples) with borrows for now *)
          assert (not (TypesUtils.ty_has_borrows types_infos ty));
          (* Eliminate the box *)
          match tys with
          | [ bty ] -> translate bty
          | _ ->
              failwith "Unreachable: boxes receive exactly one type parameter")
      | T.Tuple -> (
          (* Tuples can contain borrows (which we eliminated) *)
          let tys_t = List.filter_map translate tys in
          match tys_t with
          | [] -> None
          | _ ->
              (* Note that if there is exactly one type, [mk_simpl_tuple_ty]
               * is the identity *)
              Some (mk_simpl_tuple_ty tys_t)))
  | TypeVar vid -> wrap (TypeVar vid)
  | Bool -> wrap Bool
  | Char -> wrap Char
  | Never -> raise (Failure "Unreachable")
  | Integer int_ty -> wrap (Integer int_ty)
  | Str -> wrap Str
  | Array ty -> (
      assert (not (TypesUtils.ty_has_borrows types_infos ty));
      match translate ty with None -> None | Some ty -> Some (Array ty))
  | Slice ty -> (
      assert (not (TypesUtils.ty_has_borrows types_infos ty));
      match translate ty with None -> None | Some ty -> Some (Slice ty))
  | Ref (r, rty, rkind) -> (
      match rkind with
      | T.Shared ->
          (* Ignore shared references, unless we are below a mutable borrow *)
          if inside_mut then translate rty else None
      | T.Mut ->
          (* Dive in, remembering the fact that we are inside a mutable borrow *)
          let inside_mut = true in
          if keep_region r then
            translate_back_ty types_infos keep_region inside_mut rty
          else None)

(** Simply calls [translate_back_ty] *)
let ctx_translate_back_ty (ctx : bs_ctx) (keep_region : 'r -> bool)
    (inside_mut : bool) (ty : 'r T.ty) : ty option =
  let types_infos = ctx.type_context.types_infos in
  translate_back_ty types_infos keep_region inside_mut ty

(** List the ancestors of an abstraction *)
let list_ancestor_abstractions_ids (ctx : bs_ctx) (abs : V.abs) :
    V.AbstractionId.id list =
  (* We could do something more "elegant" without references, but it is
   * so much simpler to use references... *)
  let abs_set = ref V.AbstractionId.Set.empty in
  let rec gather (abs_id : V.AbstractionId.id) : unit =
    if V.AbstractionId.Set.mem abs_id !abs_set then ()
    else (
      abs_set := V.AbstractionId.Set.add abs_id !abs_set;
      let abs, _ = V.AbstractionId.Map.find abs_id ctx.abstractions in
      List.iter gather abs.original_parents)
  in
  List.iter gather abs.original_parents;
  let ids = !abs_set in
  (* List the ancestors, in the proper order *)
  let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
  List.filter
    (fun id -> V.AbstractionId.Set.mem id ids)
    call_info.forward.abstractions

let list_ancestor_abstractions (ctx : bs_ctx) (abs : V.abs) :
    (V.abs * texpression list) list =
  let abs_ids = list_ancestor_abstractions_ids ctx abs in
  List.map (fun id -> V.AbstractionId.Map.find id ctx.abstractions) abs_ids

(** Small utility. *)
let get_fun_effect_info (fun_infos : FA.fun_info A.FunDeclId.Map.t)
    (fun_id : A.fun_id) (gid : T.RegionGroupId.id option) : fun_effect_info =
  match fun_id with
  | A.Regular fid ->
      let info = A.FunDeclId.Map.find fid fun_infos in
      let input_state = info.stateful in
      let output_state = input_state && gid = None in
      { can_fail = info.can_fail; input_state; output_state }
  | A.Assumed aid ->
      {
        can_fail = Assumed.assumed_can_fail aid;
        input_state = false;
        output_state = false;
      }

(** Translate a function signature.

    Note that the function also takes a list of names for the inputs, and
    computes, for every output for the backward functions, a corresponding
    name (outputs for backward functions come from borrows in the inputs
    of the forward function).
 *)
let translate_fun_sig (fun_infos : FA.fun_info A.FunDeclId.Map.t)
    (fun_id : A.fun_id) (types_infos : TA.type_infos) (sg : A.fun_sig)
    (input_names : string option list) (bid : T.RegionGroupId.id option) :
    fun_sig_named_outputs =
  (* Retrieve the list of parent backward functions *)
  let gid, parents =
    match bid with
    | None -> (None, T.RegionGroupId.Set.empty)
    | Some bid ->
        let parents = list_parent_region_groups sg bid in
        (Some bid, parents)
  in
  (* List the inputs for:
   * - the forward function
   * - the parent backward functions, in proper order
   * - the current backward function (if it is a backward function)
   *)
  let fwd_inputs = List.map (translate_fwd_ty types_infos) sg.inputs in
  (* For the backward functions: for now we don't supported nested borrows,
   * so just check that there aren't parent regions *)
  assert (T.RegionGroupId.Set.is_empty parents);
  (* Small helper to translate types for backward functions *)
  let translate_back_ty_for_gid (gid : T.RegionGroupId.id) : T.sty -> ty option
      =
    let rg = T.RegionGroupId.nth sg.regions_hierarchy gid in
    let regions = T.RegionVarId.Set.of_list rg.regions in
    let keep_region r =
      match r with
      | T.Static -> raise Unimplemented
      | T.Var r -> T.RegionVarId.Set.mem r regions
    in
    let inside_mut = false in
    translate_back_ty types_infos keep_region inside_mut
  in
  (* Compute the additinal inputs for the current function, if it is a backward
   * function *)
  let back_inputs =
    match gid with
    | None -> []
    | Some gid ->
        (* For now, we don't allow nested borrows, so the additional inputs to the
         * backward function can only come from borrows that were returned like
         * in (for the backward function we introduce for 'a):
         * ```
         * fn f<'a>(...) -> &'a mut u32;
         * ```
         * Upon ending the abstraction for 'a, we need to get back the borrow
         * the function returned.
         *)
        List.filter_map (translate_back_ty_for_gid gid) [ sg.output ]
  in
  (* Does the function take a state as input, does it return a state and can
   * it fail? *)
  let effect_info = get_fun_effect_info fun_infos fun_id bid in
  (* *)
  let state_ty = if effect_info.input_state then [ mk_state_ty ] else [] in
  (* Concatenate the inputs, in the following order:
   * - forward inputs
   * - state input
   * - backward inputs
   *)
  let inputs = List.concat [ fwd_inputs; state_ty; back_inputs ] in
  (* Outputs *)
  let output_names, doutputs =
    match gid with
    | None ->
        (* This is a forward function: there is one (unnamed) output *)
        ([ None ], [ translate_fwd_ty types_infos sg.output ])
    | Some gid ->
        (* This is a backward function: there might be several outputs.
         * The outputs are the borrows inside the regions of the abstractions
         * and which are present in the input values. For instance, see:
         * ```
         * fn f<'a>(x : &'a mut u32) -> ...;
         * ```
         * Upon ending the abstraction for 'a, we give back the borrow which
         * was consumed through the `x` parameter.
         *)
        let outputs =
          List.map
            (fun (name, input_ty) ->
              (name, translate_back_ty_for_gid gid input_ty))
            (List.combine input_names sg.inputs)
        in
        (* Filter *)
        let outputs =
          List.filter (fun (_, opt_ty) -> Option.is_some opt_ty) outputs
        in
        let outputs =
          List.map (fun (name, opt_ty) -> (name, Option.get opt_ty)) outputs
        in
        List.split outputs
  in
  (* Create the return type *)
  let output =
    (* Group the outputs together *)
    let output = mk_simpl_tuple_ty doutputs in
    (* Add the output state *)
    let output =
      if effect_info.output_state then mk_simpl_tuple_ty [ mk_state_ty; output ]
      else output
    in
    (* Wrap in a result type *)
    if effect_info.can_fail then mk_result_ty output else output
  in
  (* Type parameters *)
  let type_params = sg.type_params in
  (* Return *)
  let info =
    {
      num_fwd_inputs = List.length fwd_inputs;
      num_back_inputs =
        (if bid = None then None else Some (List.length back_inputs));
      effect_info;
    }
  in
  let sg = { type_params; inputs; output; doutputs; info } in
  { sg; output_names }

let bs_ctx_fresh_state_var (ctx : bs_ctx) : bs_ctx * typed_pattern =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let var =
    { id; basename = Some ConstStrings.state_basename; ty = mk_state_ty }
  in
  let state_var = mk_typed_pattern_from_var var None in
  (* Update the context *)
  let ctx = { ctx with var_counter; state_var = id } in
  (* Return *)
  (ctx, state_var)

let fresh_named_var_for_symbolic_value (basename : string option)
    (sv : V.symbolic_value) (ctx : bs_ctx) : bs_ctx * var =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
  let var = { id; basename; ty } in
  (* Insert in the map *)
  let sv_to_var = V.SymbolicValueId.Map.add sv.sv_id var ctx.sv_to_var in
  (* Update the context *)
  let ctx = { ctx with var_counter; sv_to_var } in
  (* Return *)
  (ctx, var)

let fresh_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) :
    bs_ctx * var =
  fresh_named_var_for_symbolic_value None sv ctx

let fresh_vars_for_symbolic_values (svl : V.symbolic_value list) (ctx : bs_ctx)
    : bs_ctx * var list =
  List.fold_left_map (fun ctx sv -> fresh_var_for_symbolic_value sv ctx) ctx svl

let fresh_named_vars_for_symbolic_values
    (svl : (string option * V.symbolic_value) list) (ctx : bs_ctx) :
    bs_ctx * var list =
  List.fold_left_map
    (fun ctx (name, sv) -> fresh_named_var_for_symbolic_value name sv ctx)
    ctx svl

(** This generates a fresh variable **which is not to be linked to any symbolic value** *)
let fresh_var (basename : string option) (ty : ty) (ctx : bs_ctx) : bs_ctx * var
    =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let var = { id; basename; ty } in
  (* Update the context *)
  let ctx = { ctx with var_counter } in
  (* Return *)
  (ctx, var)

let fresh_vars (vars : (string option * ty) list) (ctx : bs_ctx) :
    bs_ctx * var list =
  List.fold_left_map (fun ctx (name, ty) -> fresh_var name ty ctx) ctx vars

let lookup_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) : var =
  V.SymbolicValueId.Map.find sv.sv_id ctx.sv_to_var

(** Peel boxes as long as the value is of the form `Box<T>` *)
let rec unbox_typed_value (v : V.typed_value) : V.typed_value =
  match (v.value, v.ty) with
  | V.Adt av, T.Adt (T.Assumed T.Box, _, _) -> (
      match av.field_values with
      | [ bv ] -> unbox_typed_value bv
      | _ -> raise (Failure "Unreachable"))
  | _ -> v

(** Translate a typed value.

    It is used, for instance, on values used as inputs for function calls.

    **IMPORTANT**: this function makes the assumption that the typed value
    doesn't contain ⊥. This means in particular that symbolic values don't
    contain ended regions.
    
    TODO: we might want to remember in the symbolic AST the set of ended
    regions, at the points where we need it, for sanity checks (though the
    sanity checks in the symbolic interpreter should be enough).
    The points where we need this set so far:
    - function call
    - end abstraction
    - return
 *)
let rec typed_value_to_texpression (ctx : bs_ctx) (v : V.typed_value) :
    texpression =
  (* We need to ignore boxes *)
  let v = unbox_typed_value v in
  let translate = typed_value_to_texpression ctx in
  (* Translate the type *)
  let ty = ctx_translate_fwd_ty ctx v.ty in
  (* Translate the value *)
  let value =
    match v.value with
    | V.Concrete cv -> { e = Const cv; ty }
    | Adt av -> (
        let variant_id = av.variant_id in
        let field_values = List.map translate av.field_values in
        (* Eliminate the tuple wrapper if it is a tuple with exactly one field *)
        match v.ty with
        | T.Adt (T.Tuple, _, _) ->
            assert (variant_id = None);
            mk_simpl_tuple_texpression field_values
        | _ ->
            (* Retrieve the type and the translated type arguments from the
             * translated type (simpler this way) *)
            let adt_id, type_args =
              match ty with
              | Adt (type_id, tys) -> (type_id, tys)
              | _ -> raise (Failure "Unreachable")
            in
            (* Create the constructor *)
            let qualif_id = AdtCons { adt_id; variant_id = av.variant_id } in
            let qualif = { id = qualif_id; type_args } in
            let cons_e = Qualif qualif in
            let field_tys =
              List.map (fun (v : texpression) -> v.ty) field_values
            in
            let cons_ty = mk_arrows field_tys ty in
            let cons = { e = cons_e; ty = cons_ty } in
            (* Apply the constructor *)
            mk_apps cons field_values)
    | Bottom -> raise (Failure "Unreachable")
    | Loan lc -> (
        match lc with
        | SharedLoan (_, v) -> translate v
        | MutLoan _ -> raise (Failure "Unreachable"))
    | Borrow bc -> (
        match bc with
        | V.SharedBorrow (mv, _) ->
            (* The meta-value stored in the shared borrow was added especially
             * for this case (because we can't use the borrow id for lookups) *)
            translate mv
        | V.InactivatedMutBorrow (mv, _) ->
            (* Same as for shared borrows. However, note that we use inactivated borrows
             * only in meta-data: a value actually *used in the translation* can't come
             * from an unpromoted inactivated borrow *)
            translate mv
        | V.MutBorrow (_, v) ->
            (* Borrows are the identity in the extraction *)
            translate v)
    | Symbolic sv ->
        let var = lookup_var_for_symbolic_value sv ctx in
        mk_texpression_from_var var
  in
  (* Debugging *)
  log#ldebug
    (lazy
      ("typed_value_to_texpression: result:" ^ "\n- input value:\n"
     ^ V.show_typed_value v ^ "\n- translated expression:\n"
     ^ show_texpression value));
  (* Sanity check *)
  type_check_texpression ctx value;
  (* Return *)
  value

(** Explore an abstraction value and convert it to a consumed value
    by collecting all the meta-values from the ended *loans*.

    Consumed values are rvalues, because when an abstraction ends, we
    introduce a call to a backward function in the synthesized program,
    which takes as inputs those consumed values:
    ```
    // Rust:
    fn choose<'a>(b: bool, x : &'a mut u32, y : &'a mut u32) -> &'a mut u32;
    
    // Synthesis:
    let ... = choose_back b x y nz in
                                ^^
    ```
 *)
let rec typed_avalue_to_consumed (ctx : bs_ctx) (av : V.typed_avalue) :
    texpression option =
  let translate = typed_avalue_to_consumed ctx in
  let value =
    match av.value with
    | AConcrete _ -> raise (Failure "Unreachable")
    | AAdt adt_v -> (
        (* Translate the field values *)
        let field_values = List.filter_map translate adt_v.field_values in
        (* For now, only tuples can contain borrows *)
        let adt_id, _, _ = TypesUtils.ty_as_adt av.ty in
        match adt_id with
        | T.AdtId _ | T.Assumed (T.Box | T.Vec | T.Option) ->
            assert (field_values = []);
            None
        | T.Tuple ->
            (* Return *)
            if field_values = [] then None
            else
              (* Note that if there is exactly one field value,
               * [mk_simpl_tuple_rvalue] is the identity *)
              let rv = mk_simpl_tuple_texpression field_values in
              Some rv)
    | ABottom -> raise (Failure "Unreachable")
    | ALoan lc -> aloan_content_to_consumed ctx lc
    | ABorrow bc -> aborrow_content_to_consumed ctx bc
    | ASymbolic aproj -> aproj_to_consumed ctx aproj
    | AIgnored -> None
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_texpression ctx value);
  (* Return *)
  value

and aloan_content_to_consumed (ctx : bs_ctx) (lc : V.aloan_content) :
    texpression option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> raise (Failure "Unreachable")
  | AEndedMutLoan { child = _; given_back = _; given_back_meta } ->
      (* Return the meta-value *)
      Some (typed_value_to_texpression ctx given_back_meta)
  | AEndedSharedLoan (_, _) ->
      (* We don't dive into shared loans: there is nothing to give back
       * inside (note that there could be a mutable borrow in the shared
       * value, pointing to a mutable loan in the child avalue, but this
       * borrow is in practice immutable) *)
      None
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      raise (Failure "Unreachable")
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      None

and aborrow_content_to_consumed (_ctx : bs_ctx) (bc : V.aborrow_content) :
    texpression option =
  match bc with
  | V.AMutBorrow (_, _, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      raise (Failure "Unreachable")
  | AEndedMutBorrow (_, _) ->
      (* We collect consumed values: ignore *)
      None
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AEndedSharedBorrow | AProjSharedBorrow _ ->
      (* Ignore *)
      None

and aproj_to_consumed (ctx : bs_ctx) (aproj : V.aproj) : texpression option =
  match aproj with
  | V.AEndedProjLoans (msv, []) ->
      (* The symbolic value was left unchanged *)
      let var = lookup_var_for_symbolic_value msv ctx in
      Some (mk_texpression_from_var var)
  | V.AEndedProjLoans (_, [ (mnv, child_aproj) ]) ->
      assert (child_aproj = AIgnoredProjBorrows);
      (* The symbolic value was updated *)
      let var = lookup_var_for_symbolic_value mnv ctx in
      Some (mk_texpression_from_var var)
  | V.AEndedProjLoans (_, _) ->
      (* The symbolic value was updated, and the given back values come from sevearl
       * abstractions *)
      raise Unimplemented
  | AEndedProjBorrows _ -> (* We consider consumed values *) None
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      raise (Failure "Unreachable")

(** Convert the abstraction values in an abstraction to consumed values.

    See [typed_avalue_to_consumed].
 *)
let abs_to_consumed (ctx : bs_ctx) (abs : V.abs) : texpression list =
  log#ldebug (lazy ("abs_to_consumed:\n" ^ abs_to_string ctx abs));
  List.filter_map (typed_avalue_to_consumed ctx) abs.avalues

let translate_mprojection_elem (pe : E.projection_elem) :
    mprojection_elem option =
  match pe with
  | Deref | DerefBox -> None
  | Field (pkind, field_id) -> Some { pkind; field_id }

let translate_mprojection (p : E.projection) : mprojection =
  List.filter_map translate_mprojection_elem p

(** Translate a "meta"-place *)
let translate_mplace (p : S.mplace) : mplace =
  let var_id = p.bv.index in
  let name = p.bv.name in
  let projection = translate_mprojection p.projection in
  { var_id; name; projection }

let translate_opt_mplace (p : S.mplace option) : mplace option =
  match p with None -> None | Some p -> Some (translate_mplace p)

(** Explore an abstraction value and convert it to a given back value
    by collecting all the meta-values from the ended *borrows*.

    Given back values are patterns, because when an abstraction ends, we
    introduce a call to a backward function in the synthesized program,
    which introduces new values:
    ```
    let (nx, ny) = f_back ... in
        ^^^^^^^^
    ```
    
    [mp]: it is possible to provide some meta-place information, to guide
    the heuristics which later find pretty names for the variables.
 *)
let rec typed_avalue_to_given_back (mp : mplace option) (av : V.typed_avalue)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  let ctx, value =
    match av.value with
    | AConcrete _ -> raise (Failure "Unreachable")
    | AAdt adt_v -> (
        (* Translate the field values *)
        (* For now we forget the meta-place information so that it doesn't get used
         * by several fields (which would then all have the same name...), but we
         * might want to do something smarter *)
        let mp = None in
        let ctx, field_values =
          List.fold_left_map
            (fun ctx fv -> typed_avalue_to_given_back mp fv ctx)
            ctx adt_v.field_values
        in
        let field_values = List.filter_map (fun x -> x) field_values in
        (* For now, only tuples can contain borrows - note that if we gave
         * something like a `&mut Vec` to a function, we give give back the
         * vector value upon visiting the "abstraction borrow" node *)
        let adt_id, _, _ = TypesUtils.ty_as_adt av.ty in
        match adt_id with
        | T.AdtId _ | T.Assumed (T.Box | T.Vec | T.Option) ->
            assert (field_values = []);
            (ctx, None)
        | T.Tuple ->
            (* Return *)
            let variant_id = adt_v.variant_id in
            assert (variant_id = None);
            if field_values = [] then (ctx, None)
            else
              (* Note that if there is exactly one field value, [mk_simpl_tuple_pattern]
               * is the identity *)
              let lv = mk_simpl_tuple_pattern field_values in
              (ctx, Some lv))
    | ABottom -> raise (Failure "Unreachable")
    | ALoan lc -> aloan_content_to_given_back mp lc ctx
    | ABorrow bc -> aborrow_content_to_given_back mp bc ctx
    | ASymbolic aproj -> aproj_to_given_back mp aproj ctx
    | AIgnored -> (ctx, None)
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with None -> () | Some value -> type_check_pattern ctx value);
  (* Return *)
  (ctx, value)

and aloan_content_to_given_back (_mp : mplace option) (lc : V.aloan_content)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> raise (Failure "Unreachable")
  | AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
  | AEndedSharedLoan (_, _) ->
      (* We consider given back values, and thus ignore those *)
      (ctx, None)
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      raise (Failure "Unreachable")
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      (ctx, None)

and aborrow_content_to_given_back (mp : mplace option) (bc : V.aborrow_content)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  match bc with
  | V.AMutBorrow (_, _, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      raise (Failure "Unreachable")
  | AEndedMutBorrow (msv, _) ->
      (* Return the meta-symbolic-value *)
      let ctx, var = fresh_var_for_symbolic_value msv ctx in
      (ctx, Some (mk_typed_pattern_from_var var mp))
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AEndedSharedBorrow | AProjSharedBorrow _ ->
      (* Ignore *)
      (ctx, None)

and aproj_to_given_back (mp : mplace option) (aproj : V.aproj) (ctx : bs_ctx) :
    bs_ctx * typed_pattern option =
  match aproj with
  | V.AEndedProjLoans (_, child_projs) ->
      (* There may be children borrow projections in case of nested borrows,
       * in which case we need to dive in - we disallow nested borrows for now *)
      assert (
        List.for_all
          (fun (_, aproj) -> aproj = V.AIgnoredProjBorrows)
          child_projs);
      (ctx, None)
  | AEndedProjBorrows mv ->
      (* Return the meta-value *)
      let ctx, var = fresh_var_for_symbolic_value mv ctx in
      (ctx, Some (mk_typed_pattern_from_var var mp))
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      raise (Failure "Unreachable")

(** Convert the abstraction values in an abstraction to given back values.

    See [typed_avalue_to_given_back].
 *)
let abs_to_given_back (mpl : mplace option list) (abs : V.abs) (ctx : bs_ctx) :
    bs_ctx * typed_pattern list =
  let avalues = List.combine mpl abs.avalues in
  let ctx, values =
    List.fold_left_map
      (fun ctx (mp, av) -> typed_avalue_to_given_back mp av ctx)
      ctx avalues
  in
  let values = List.filter_map (fun x -> x) values in
  (ctx, values)

(** Simply calls [abs_to_given_back] *)
let abs_to_given_back_no_mp (abs : V.abs) (ctx : bs_ctx) :
    bs_ctx * typed_pattern list =
  let mpl = List.map (fun _ -> None) abs.avalues in
  abs_to_given_back mpl abs ctx

(** Return the ordered list of the (transitive) parents of a given abstraction.

    Is used for instance when collecting the input values given to all the
    parent functions, in order to properly instantiate an 
 *)
let get_abs_ancestors (ctx : bs_ctx) (abs : V.abs) :
    S.call * (V.abs * texpression list) list =
  let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
  let abs_ancestors = list_ancestor_abstractions ctx abs in
  (call_info.forward, abs_ancestors)

let rec translate_expression (config : config) (e : S.expression) (ctx : bs_ctx)
    : texpression =
  match e with
  | S.Return opt_v -> translate_return opt_v ctx
  | Panic -> translate_panic ctx
  | FunCall (call, e) -> translate_function_call config call e ctx
  | EndAbstraction (abs, e) -> translate_end_abstraction config abs e ctx
  | Expansion (p, sv, exp) -> translate_expansion config p sv exp ctx
  | Meta (meta, e) -> translate_meta config meta e ctx

and translate_panic (ctx : bs_ctx) : texpression =
  (* Here we use the function return type - note that it is ok because
   * we don't match on panics which happen inside the function body -
   * but it won't be true anymore once we translate individual blocks *)
  (* If we use a state monad, we need to add a lambda for the state variable *)
  (* Note that only forward functions return a state *)
  let output_ty = mk_simpl_tuple_ty ctx.sg.doutputs in
  if ctx.sg.info.effect_info.output_state then
    (* Create the `Fail` value *)
    let ret_ty = mk_simpl_tuple_ty [ mk_state_ty; output_ty ] in
    let ret_v = mk_result_fail_texpression ret_ty in
    ret_v
  else mk_result_fail_texpression output_ty

and translate_return (opt_v : V.typed_value option) (ctx : bs_ctx) : texpression
    =
  (* There are two cases:
     - either we are translating a forward function, in which case the optional
       value should be `Some` (it is the returned value)
     - or we are translating a backward function, in which case it should be `None`
  *)
  match ctx.bid with
  | None ->
      (* Forward function *)
      let v = Option.get opt_v in
      let v = typed_value_to_texpression ctx v in
      (* We may need to return a state
       * - error-monad: Return x
       * - state-error: Return (state, x)
       * *)
      if ctx.sg.info.effect_info.output_state then
        let state_var =
          {
            id = ctx.state_var;
            basename = Some ConstStrings.state_basename;
            ty = mk_state_ty;
          }
        in
        let state_rvalue = mk_texpression_from_var state_var in
        mk_result_return_texpression
          (mk_simpl_tuple_texpression [ state_rvalue; v ])
      else mk_result_return_texpression v
  | Some bid ->
      (* Backward function *)
      (* Sanity check *)
      assert (opt_v = None);
      assert (not ctx.sg.info.effect_info.output_state);
      (* We simply need to return the variables in which we stored the values
       * we need to give back.
       * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
      let backward_outputs =
        T.RegionGroupId.Map.find bid ctx.backward_outputs
      in
      let field_values = List.map mk_texpression_from_var backward_outputs in
      (* Backward functions never return a state *)
      (* TODO: we should use a `fail` function, it would be cleaner *)
      let ret_value = mk_simpl_tuple_texpression field_values in
      let ret_value = mk_result_return_texpression ret_value in
      ret_value

and translate_function_call (config : config) (call : S.call) (e : S.expression)
    (ctx : bs_ctx) : texpression =
  (* Translate the function call *)
  let type_args = List.map (ctx_translate_fwd_ty ctx) call.type_params in
  let args =
    let args = List.map (typed_value_to_texpression ctx) call.args in
    let args_mplaces = List.map translate_opt_mplace call.args_places in
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
      (List.combine args args_mplaces)
  in
  let dest_mplace = translate_opt_mplace call.dest_place in
  let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
  (* Retrieve the function id, and register the function call in the context
   * if necessary. *)
  let ctx, fun_id, effect_info, args, out_state =
    match call.call_id with
    | S.Fun (fid, call_id) ->
        (* Regular function call *)
        let func = Regular (fid, None) in
        (* Retrieve the effect information about this function (can fail,
         * takes a state as input, etc.) *)
        let effect_info =
          get_fun_effect_info ctx.fun_context.fun_infos fid None
        in
        (* Add the state input argument *)
        let args =
          if effect_info.input_state then
            let state_var = { e = Var ctx.state_var; ty = mk_state_ty } in
            List.append args [ state_var ]
          else args
        in
        (* Generate a fresh state variable if the function call introduces
         * a new variable *)
        let ctx, out_state =
          if effect_info.input_state then
            let ctx, var = bs_ctx_fresh_state_var ctx in
            (ctx, Some var)
          else (ctx, None)
        in
        (* Register the function call *)
        let ctx = bs_ctx_register_forward_call call_id call args ctx in
        (ctx, func, effect_info, args, out_state)
    | S.Unop E.Not ->
        let effect_info =
          { can_fail = false; input_state = false; output_state = false }
        in
        (ctx, Unop Not, effect_info, args, None)
    | S.Unop E.Neg -> (
        match args with
        | [ arg ] ->
            let int_ty = ty_as_integer arg.ty in
            (* Note that negation can lead to an overflow and thus fail (it
             * is thus monadic) *)
            let effect_info =
              { can_fail = true; input_state = false; output_state = false }
            in
            (ctx, Unop (Neg int_ty), effect_info, args, None)
        | _ -> raise (Failure "Unreachable"))
    | S.Unop (E.Cast (src_ty, tgt_ty)) ->
        (* Note that cast can fail *)
        let effect_info =
          { can_fail = true; input_state = false; output_state = false }
        in
        (ctx, Unop (Cast (src_ty, tgt_ty)), effect_info, args, None)
    | S.Binop binop -> (
        match args with
        | [ arg0; arg1 ] ->
            let int_ty0 = ty_as_integer arg0.ty in
            let int_ty1 = ty_as_integer arg1.ty in
            assert (int_ty0 = int_ty1);
            let effect_info =
              {
                can_fail = ExpressionsUtils.binop_can_fail binop;
                input_state = false;
                output_state = false;
              }
            in
            (ctx, Binop (binop, int_ty0), effect_info, args, None)
        | _ -> raise (Failure "Unreachable"))
  in
  let dest_v =
    let dest = mk_typed_pattern_from_var dest dest_mplace in
    match out_state with
    | None -> dest
    | Some out_state -> mk_simpl_tuple_pattern [ out_state; dest ]
  in
  let func = { id = Func fun_id; type_args } in
  let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
  let ret_ty =
    if effect_info.can_fail then mk_result_ty dest_v.ty else dest_v.ty
  in
  let func_ty = mk_arrows input_tys ret_ty in
  let func = { e = Qualif func; ty = func_ty } in
  let call = mk_apps func args in
  (* Translate the next expression *)
  let next_e = translate_expression config e ctx in
  (* Put together *)
  mk_let effect_info.can_fail dest_v call next_e

and translate_end_abstraction (config : config) (abs : V.abs) (e : S.expression)
    (ctx : bs_ctx) : texpression =
  log#ldebug
    (lazy
      ("translate_end_abstraction: abstraction kind: "
     ^ V.show_abs_kind abs.kind));
  match abs.kind with
  | V.SynthInput ->
      (* When we end an input abstraction, this input abstraction gets back
       * the borrows which it introduced in the context through the input
       * values: by listing those values, we get the values which are given
       * back by one of the backward functions we are synthesizing. *)
      (* Note that we don't support nested borrows for now: if we find
       * an ended synthesized input abstraction, it must be the one corresponding
       * to the backward function wer are synthesizing, it can't be the one
       * for a parent backward function.
       *)
      let bid = Option.get ctx.bid in
      assert (abs.back_id = bid);

      (* The translation is done as follows:
       * - for a given backward function, we choose a set of variables `v_i`
       * - when we detect the ended input abstraction which corresponds
       *   to the backward function, and which consumed the values `consumed_i`,
       *   we introduce:
       *   ```
       *   let v_i = consumed_i in
       *   ...
       *   ```
       *   Then, when we reach the `Return` node, we introduce:
       *   ```
       *   (v_i)
       *   ```
       * *)
      (* First, get the given back variables *)
      let given_back_variables =
        T.RegionGroupId.Map.find bid ctx.backward_outputs
      in
      (* Get the list of values consumed by the abstraction upon ending *)
      let consumed_values = abs_to_consumed ctx abs in
      (* Group the two lists *)
      let variables_values =
        List.combine given_back_variables consumed_values
      in
      (* Sanity check: the two lists match (same types) *)
      List.iter
        (fun (var, v) -> assert ((var : var).ty = (v : texpression).ty))
        variables_values;
      (* Translate the next expression *)
      let next_e = translate_expression config e ctx in
      (* Generate the assignemnts *)
      let monadic = false in
      List.fold_right
        (fun (var, value) (e : texpression) ->
          mk_let monadic (mk_typed_pattern_from_var var None) value e)
        variables_values next_e
  | V.FunCall ->
      let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
      let call = call_info.forward in
      let type_args = List.map (ctx_translate_fwd_ty ctx) call.type_params in
      (* Retrieve the original call and the parent abstractions *)
      let _forward, backwards = get_abs_ancestors ctx abs in
      (* Retrieve the values consumed when we called the forward function and
       * ended the parent backward functions: those give us part of the input
       * values (rmk: for now, as we disallow nested lifetimes, there can't be
       * parent backward functions).
       * Note that the forward inputs include the input state (if there is one). *)
      let fwd_inputs = call_info.forward_inputs in
      let back_ancestors_inputs =
        List.concat (List.map (fun (_abs, args) -> args) backwards)
      in
      (* Retrieve the values consumed upon ending the loans inside this
       * abstraction: those give us the remaining input values *)
      let back_inputs = abs_to_consumed ctx abs in
      let inputs =
        List.concat [ fwd_inputs; back_ancestors_inputs; back_inputs ]
      in
      (* Retrieve the values given back by this function: those are the output
       * values. We rely on the fact that there are no nested borrows to use the
       * meta-place information from the input values given to the forward function
       * (we need to add `None` for the return avalue) *)
      let output_mpl =
        List.append (List.map translate_opt_mplace call.args_places) [ None ]
      in
      let ctx, outputs = abs_to_given_back output_mpl abs ctx in
      (* Group the output values together (note that for now, backward functions
       * never return an output state) *)
      let output = mk_simpl_tuple_pattern outputs in
      (* Sanity check: the inputs and outputs have the proper number and the proper type *)
      let fun_id =
        match call.call_id with
        | S.Fun (fun_id, _) -> fun_id
        | Unop _ | Binop _ ->
            (* Those don't have backward functions *)
            raise (Failure "Unreachable")
      in

      let inst_sg =
        get_instantiated_fun_sig fun_id (Some abs.back_id) type_args ctx
      in
      log#ldebug
        (lazy
          ("\n- fun_id: " ^ A.show_fun_id fun_id ^ "\n- inputs ("
          ^ string_of_int (List.length inputs)
          ^ "): "
          ^ String.concat ", " (List.map show_texpression inputs)
          ^ "\n- inst_sg.inputs ("
          ^ string_of_int (List.length inst_sg.inputs)
          ^ "): "
          ^ String.concat ", " (List.map show_ty inst_sg.inputs)));
      List.iter
        (fun (x, ty) -> assert ((x : texpression).ty = ty))
        (List.combine inputs inst_sg.inputs);
      log#ldebug
        (lazy
          ("\n- outputs: "
          ^ string_of_int (List.length outputs)
          ^ "\n- expected outputs: "
          ^ string_of_int (List.length inst_sg.doutputs)));
      List.iter
        (fun (x, ty) -> assert ((x : typed_pattern).ty = ty))
        (List.combine outputs inst_sg.doutputs);
      (* Retrieve the function id, and register the function call in the context
       * if necessary *)
      let ctx, func = bs_ctx_register_backward_call abs back_inputs ctx in
      (* Translate the next expression *)
      let next_e = translate_expression config e ctx in
      (* Put everything together *)
      let args_mplaces = List.map (fun _ -> None) inputs in
      let args =
        List.map
          (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
          (List.combine inputs args_mplaces)
      in
      let effect_info =
        get_fun_effect_info ctx.fun_context.fun_infos fun_id (Some abs.back_id)
      in
      let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
      let ret_ty =
        if effect_info.can_fail then mk_result_ty output.ty else output.ty
      in
      let func_ty = mk_arrows input_tys ret_ty in
      let func = { id = Func func; type_args } in
      let func = { e = Qualif func; ty = func_ty } in
      let call = mk_apps func args in
      (* **Optimization**:
       * =================
       * We do a small optimization here: if the backward function doesn't
       * have any output, we don't introduce any function call.
       * See the comment in [config].
       *)
      if config.filter_useless_back_calls && outputs = [] then (
        (* No outputs - we do a small sanity check: the backward function
         * should have exactly the same number of inputs as the forward:
         * this number can be different only if the forward function returned
         * a value containing mutable borrows, which can't be the case... *)
        assert (List.length inputs = List.length fwd_inputs);
        next_e)
      else mk_let effect_info.can_fail output call next_e
  | V.SynthRet ->
      (* If we end the abstraction which consumed the return value of the function
       * we are synthesizing, we get back the borrows which were inside. Those borrows
       * are actually input arguments of the backward function we are synthesizing.
       * So we simply need to introduce proper let bindings.
       * 
       * For instance:
       * ```
       * fn id<'a>(x : &'a mut u32) -> &'a mut u32 {
       *   x
       * }
       * ```
       *
       * Upon ending the return abstraction for 'a, we get back the borrow for `x`.
       * This new value is the second argument of the backward function:
       * ```
       * let id_back x nx = nx
       * ```
       *
       * In practice, upon ending this abstraction we introduce a useless
       * let-binding:
       * ```
       * let id_back x nx =
       *   let s = nx in // the name `s` is not important (only collision matters)
       *   ...
       * ```
       *
       * This let-binding later gets inlined, during a micro-pass.
       * 
       * *)
      (* First, retrieve the list of variables used for the inputs for the
       * backward function *)
      let inputs = T.RegionGroupId.Map.find abs.back_id ctx.backward_inputs in
      (* Retrieve the values consumed upon ending the loans inside this
       * abstraction: as there are no nested borrows, there should be none. *)
      let consumed = abs_to_consumed ctx abs in
      assert (consumed = []);
      (* Retrieve the values given back upon ending this abstraction - note that
       * we don't provide meta-place information, because those assignments will
       * be inlined anyway... *)
      log#ldebug (lazy ("abs: " ^ abs_to_string ctx abs));
      let ctx, given_back = abs_to_given_back_no_mp abs ctx in
      (* Link the inputs to those given back values - note that this also
       * checks we have the same number of values, of course *)
      let given_back_inputs = List.combine given_back inputs in
      (* Sanity check *)
      List.iter
        (fun ((given_back, input) : typed_pattern * var) ->
          log#ldebug
            (lazy
              ("\n- given_back ty: "
              ^ ty_to_string ctx given_back.ty
              ^ "\n- sig input ty: " ^ ty_to_string ctx input.ty));
          assert (given_back.ty = input.ty))
        given_back_inputs;
      (* Translate the next expression *)
      let next_e = translate_expression config e ctx in
      (* Generate the assignments *)
      let monadic = false in
      List.fold_right
        (fun (given_back, input_var) e ->
          mk_let monadic given_back (mk_texpression_from_var input_var) e)
        given_back_inputs next_e

and translate_expansion (config : config) (p : S.mplace option)
    (sv : V.symbolic_value) (exp : S.expansion) (ctx : bs_ctx) : texpression =
  (* Translate the scrutinee *)
  let scrutinee_var = lookup_var_for_symbolic_value sv ctx in
  let scrutinee = mk_texpression_from_var scrutinee_var in
  let scrutinee_mplace = translate_opt_mplace p in
  (* Translate the branches *)
  match exp with
  | ExpandNoBranch (sexp, e) -> (
      match sexp with
      | V.SeConcrete _ ->
          (* Actually, we don't *register* symbolic expansions to constant
           * values in the symbolic ADT *)
          raise (Failure "Unreachable")
      | SeMutRef (_, nsv) | SeSharedRef (_, nsv) ->
          (* The (mut/shared) borrow type is extracted to identity: we thus simply
           * introduce an reassignment *)
          let ctx, var = fresh_var_for_symbolic_value nsv ctx in
          let next_e = translate_expression config e ctx in
          let monadic = false in
          mk_let monadic
            (mk_typed_pattern_from_var var None)
            (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
            next_e
      | SeAdt _ ->
          (* Should be in the [ExpandAdt] case *)
          raise (Failure "Unreachable"))
  | ExpandAdt branches -> (
      (* We don't do the same thing if there is a branching or not *)
      match branches with
      | [] -> raise (Failure "Unreachable")
      | [ (variant_id, svl, branch) ] -> (
          (* There is exactly one branch: no branching *)
          let type_id, _, _ = TypesUtils.ty_as_adt sv.V.sv_ty in
          let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
          let branch = translate_expression config branch ctx in
          match type_id with
          | T.AdtId adt_id ->
              (* Detect if this is an enumeration or not *)
              let tdef = bs_ctx_lookup_llbc_type_decl adt_id ctx in
              let is_enum = type_decl_is_enum tdef in
              if is_enum then
                (* This is an enumeration: introduce an [ExpandEnum] let-binding *)
                let variant_id = Option.get variant_id in
                let lvars =
                  List.map (fun v -> mk_typed_pattern_from_var v None) vars
                in
                let lv = mk_adt_pattern scrutinee.ty variant_id lvars in
                let monadic = false in

                mk_let monadic lv
                  (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
                  branch
              else
                (* This is not an enumeration: introduce let-bindings for every
                 * field.
                 * We use the [dest] variable in order not to have to recompute
                 * the type of the result of the projection... *)
                let adt_id, type_args =
                  match scrutinee.ty with
                  | Adt (adt_id, tys) -> (adt_id, tys)
                  | _ -> raise (Failure "Unreachable")
                in
                let gen_field_proj (field_id : FieldId.id) (dest : var) :
                    texpression =
                  let proj_kind = { adt_id; field_id } in
                  let qualif = { id = Proj proj_kind; type_args } in
                  let proj_e = Qualif qualif in
                  let proj_ty = mk_arrow scrutinee.ty dest.ty in
                  let proj = { e = proj_e; ty = proj_ty } in
                  mk_app proj scrutinee
                in
                let id_var_pairs = FieldId.mapi (fun fid v -> (fid, v)) vars in
                let monadic = false in
                List.fold_right
                  (fun (fid, var) e ->
                    let field_proj = gen_field_proj fid var in
                    mk_let monadic
                      (mk_typed_pattern_from_var var None)
                      field_proj e)
                  id_var_pairs branch
          | T.Tuple ->
              let vars =
                List.map (fun x -> mk_typed_pattern_from_var x None) vars
              in
              let monadic = false in
              mk_let monadic
                (mk_simpl_tuple_pattern vars)
                (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
                branch
          | T.Assumed T.Box ->
              (* There should be exactly one variable *)
              let var =
                match vars with
                | [ v ] -> v
                | _ -> raise (Failure "Unreachable")
              in
              (* We simply introduce an assignment - the box type is the
               * identity when extracted (`box a == a`) *)
              let monadic = false in
              mk_let monadic
                (mk_typed_pattern_from_var var None)
                (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
                branch
          | T.Assumed T.Vec ->
              (* We can't expand vector values: we can access the fields only
               * through the functions provided by the API (note that we don't
               * know how to expand a vector, because it has a variable number
               * of fields!) *)
              failwith "Can't expand a vector value"
          | T.Assumed T.Option ->
              (* We shouldn't get there in the "one-branch" case: options have
               * two variants *)
              raise (Failure "Unreachable"))
      | branches ->
          let translate_branch (variant_id : T.VariantId.id option)
              (svl : V.symbolic_value list) (branch : S.expression) :
              match_branch =
            (* There *must* be a variant id - otherwise there can't be several branches *)
            let variant_id = Option.get variant_id in
            let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
            let vars =
              List.map (fun x -> mk_typed_pattern_from_var x None) vars
            in
            let pat_ty = scrutinee.ty in
            let pat = mk_adt_pattern pat_ty variant_id vars in
            let branch = translate_expression config branch ctx in
            { pat; branch }
          in
          let branches =
            List.map (fun (vid, svl, e) -> translate_branch vid svl e) branches
          in
          let e =
            Switch
              ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
                Match branches )
          in
          (* There should be at least one branch *)
          let branch = List.hd branches in
          let ty = branch.branch.ty in
          (* Sanity check *)
          assert (List.for_all (fun br -> br.branch.ty = ty) branches);
          (* Return *)
          { e; ty })
  | ExpandBool (true_e, false_e) ->
      (* We don't need to update the context: we don't introduce any
       * new values/variables *)
      let true_e = translate_expression config true_e ctx in
      let false_e = translate_expression config false_e ctx in
      let e =
        Switch
          ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
            If (true_e, false_e) )
      in
      let ty = true_e.ty in
      assert (ty = false_e.ty);
      { e; ty }
  | ExpandInt (int_ty, branches, otherwise) ->
      let translate_branch ((v, branch_e) : V.scalar_value * S.expression) :
          match_branch =
        (* We don't need to update the context: we don't introduce any
         * new values/variables *)
        let branch = translate_expression config branch_e ctx in
        let pat = mk_typed_pattern_from_constant_value (V.Scalar v) in
        { pat; branch }
      in
      let branches = List.map translate_branch branches in
      let otherwise = translate_expression config otherwise ctx in
      let pat_ty = Integer int_ty in
      let otherwise_pat : typed_pattern = { value = PatDummy; ty = pat_ty } in
      let otherwise : match_branch =
        { pat = otherwise_pat; branch = otherwise }
      in
      let all_branches = List.append branches [ otherwise ] in
      let e =
        Switch
          ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
            Match all_branches )
      in
      let ty = otherwise.branch.ty in
      assert (
        List.for_all (fun (br : match_branch) -> br.branch.ty = ty) branches);
      { e; ty }

and translate_meta (config : config) (meta : S.meta) (e : S.expression)
    (ctx : bs_ctx) : texpression =
  let next_e = translate_expression config e ctx in
  let meta =
    match meta with
    | S.Assignment (lp, rv, rp) ->
        let lp = translate_mplace lp in
        let rv = typed_value_to_texpression ctx rv in
        let rp = translate_opt_mplace rp in
        Assignment (lp, rv, rp)
  in
  let e = Meta (meta, next_e) in
  let ty = next_e.ty in
  { e; ty }

let translate_fun_decl (config : config) (ctx : bs_ctx)
    (body : S.expression option) : fun_decl =
  (* Translate *)
  let def = ctx.fun_decl in
  let bid = ctx.bid in
  log#ldebug
    (lazy
      ("SymbolicToPure.translate_fun_decl: "
      ^ Print.fun_name_to_string def.A.name
      ^ " ("
      ^ Print.option_to_string T.RegionGroupId.to_string bid
      ^ ")"));

  (* Translate the declaration *)
  let def_id = def.A.def_id in
  let basename = def.name in
  (* Lookup the signature *)
  let signature = bs_ctx_lookup_local_function_sig def_id bid ctx in
  (* Translate the body, if there is *)
  let body =
    match body with
    | None -> None
    | Some body ->
        let body = translate_expression config body ctx in
        (* Sanity check *)
        type_check_texpression ctx body;
        (* Introduce the input state, if necessary *)
        let effect_info =
          get_fun_effect_info ctx.fun_context.fun_infos (Regular def_id) bid
        in
        let input_state =
          if effect_info.input_state then
            [
              {
                id = ctx.state_var;
                basename = Some ConstStrings.state_basename;
                ty = mk_state_ty;
              };
            ]
          else []
        in
        (* Compute the list of (properly ordered) input variables *)
        let backward_inputs : var list =
          match bid with
          | None -> []
          | Some back_id ->
              let parents_ids =
                list_ordered_parent_region_groups def.signature back_id
              in
              let backward_ids = List.append parents_ids [ back_id ] in
              List.concat
                (List.map
                   (fun id -> T.RegionGroupId.Map.find id ctx.backward_inputs)
                   backward_ids)
        in
        let inputs =
          List.concat [ ctx.forward_inputs; input_state; backward_inputs ]
        in
        let inputs_lvs =
          List.map (fun v -> mk_typed_pattern_from_var v None) inputs
        in
        (* Sanity check *)
        log#ldebug
          (lazy
            ("SymbolicToPure.translate_fun_decl:" ^ "\n- forward_inputs: "
            ^ String.concat ", " (List.map show_var ctx.forward_inputs)
            ^ "\n- input_state: "
            ^ String.concat ", " (List.map show_var input_state)
            ^ "\n- backward_inputs: "
            ^ String.concat ", " (List.map show_var backward_inputs)
            ^ "\n- signature.inputs: "
            ^ String.concat ", " (List.map show_ty signature.inputs)));
        assert (
          List.for_all
            (fun (var, ty) -> (var : var).ty = ty)
            (List.combine inputs signature.inputs));
        Some { inputs; inputs_lvs; body }
  in
  (* Assemble the declaration *)
  let def = { def_id; back_id = bid; basename; signature; is_global_body = def.is_global_body; body } in
  (* Debugging *)
  log#ldebug
    (lazy
      ("SymbolicToPure.translate_fun_decl: translated:\n"
     ^ fun_decl_to_string ctx def));
  (* return *)
  def

let translate_type_decls (type_decls : T.type_decl list) : type_decl list =
  List.map translate_type_decl type_decls

(** Translates function signatures.

    Takes as input a list of function information containing:
    - the function id
    - a list of optional names for the inputs
    - the function signature
    
    Returns a map from forward/backward functions identifiers to:
    - translated function signatures
    - optional names for the outputs values (we derive them for the backward
      functions)
 *)
let translate_fun_signatures (fun_infos : FA.fun_info A.FunDeclId.Map.t)
    (types_infos : TA.type_infos)
    (functions : (A.fun_id * string option list * A.fun_sig) list) :
    fun_sig_named_outputs RegularFunIdMap.t =
  (* For every function, translate the signatures of:
     - the forward function
     - the backward functions
  *)
  let translate_one (fun_id : A.fun_id) (input_names : string option list)
      (sg : A.fun_sig) : (regular_fun_id * fun_sig_named_outputs) list =
    (* The forward function *)
    let fwd_sg =
      translate_fun_sig fun_infos fun_id types_infos sg input_names None
    in
    let fwd_id = (fun_id, None) in
    (* The backward functions *)
    let back_sgs =
      List.map
        (fun (rg : T.region_var_group) ->
          let tsg =
            translate_fun_sig fun_infos fun_id types_infos sg input_names
              (Some rg.id)
          in
          let id = (fun_id, Some rg.id) in
          (id, tsg))
        sg.regions_hierarchy
    in
    (* Return *)
    (fwd_id, fwd_sg) :: back_sgs
  in
  let translated =
    List.concat
      (List.map (fun (id, names, sg) -> translate_one id names sg) functions)
  in
  List.fold_left
    (fun m (id, sg) -> RegularFunIdMap.add id sg m)
    RegularFunIdMap.empty translated
