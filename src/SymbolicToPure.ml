open Errors
open Pure
open CfimAstUtils
module Id = Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module M = Modules
module S = SymbolicAst
module TA = TypesAnalysis
module L = Logging

(** The local logger *)
let log = L.symbolic_to_pure_log

(** TODO: move this, it is not useful for symbolic -> pure *)
type name =
  | FunName of A.FunDefId.id * T.RegionVarId.id option
  | TypeName of T.TypeDefId.id
[@@deriving show, ord]

let name_to_string (n : name) : string = show_name n

module NameOrderedType = struct
  type t = name

  let compare = compare_name

  let to_string = name_to_string

  let pp_t = pp_name

  let show_t = show_name
end

module NameMap = Collections.MakeMapInj (NameOrderedType) (Id.NameOrderedType)
(** Notice that we use the *injective* map to map identifiers to names.

    Of course, even if those names (which are string lists) don't collide,
    when converting them to strings we can still introduce collisions: we
    check that later.
    
    Note that we use injective maps for sanity: though we write the name
    generation with collision in mind, it is always good to have such checks.
 *)

let translate_fun_name (fdef : A.fun_def) (bid : T.RegionGroupId.id option) :
    Id.name =
  let sg = fdef.signature in
  (* General function to generate a suffix for a region group
   * (i.e., an abstraction)*)
  let rg_to_string (rg : T.region_var_group) : string =
    (* We are just a little bit smart:
       - if there is exactly one region id in the region group and this region
         has a name, we use this name
       - otherwise, we use the region number (note that region names shouldn't
         start with numbers)
    *)
    match rg.T.regions with
    | [ rid ] -> (
        let rvar = T.RegionVarId.nth sg.region_params rid in
        match rvar.name with
        | None -> T.RegionGroupId.to_string rg.T.id
        | Some name -> name)
    | _ -> T.RegionGroupId.to_string rg.T.id
  in
  (* There are several cases:
     - this is a forward function: we add "_fwd"
     - this is a backward function:
       - this function has one backward function: we add "_back"
       - this function has several backward function: we add "_back" and an
         additional suffix to identify the precise backward function
  *)
  let suffix =
    match bid with
    | None -> "_fwd"
    | Some bid -> (
        match sg.regions_hierarchy with
        | [] ->
            failwith "Unreachable"
            (* we can't get there if we ask for a back function *)
        | [ _ ] ->
            (* Exactly one backward function *)
            "_back"
        | _ ->
            (* Several backward functions *)
            let rg = T.RegionGroupId.nth sg.regions_hierarchy bid in
            "_back" ^ rg_to_string rg)
  in
  (* Final name *)
  let rec add_to_last (n : Id.name) : Id.name =
    match n with
    | [] -> failwith "Unreachable"
    | [ x ] -> [ x ^ suffix ]
    | x :: n -> x :: add_to_last n
  in
  add_to_last fdef.name

(** Generates a name for a type (simply reuses the name in the definition) *)
let translate_type_name (def : T.type_def) : Id.name = def.T.name

(* TODO: move *)
let mk_place_from_var (v : var) : place = { var = v.id; projection = [] }

let mk_typed_rvalue_from_var (v : var) : typed_rvalue =
  let value = RvPlace (mk_place_from_var v) in
  let ty = v.ty in
  { value; ty }

(* TODO: move *)
let mk_typed_lvalue_from_var (v : var) : typed_lvalue =
  let value = LvVar (Var v) in
  let ty = v.ty in
  { value; ty }

let ty_as_integer (t : ty) : T.integer_type =
  match t with Integer int_ty -> int_ty | _ -> failwith "Unreachable"

(* TODO: move *)
let type_def_is_enum (def : T.type_def) : bool =
  match def.kind with T.Struct _ -> false | Enum _ -> true

(** Type substitution *)
let ty_substitute (tsubst : TypeVarId.id -> ty) (ty : ty) : ty =
  let obj =
    object
      inherit [_] map_ty

      method! visit_TypeVar _ var_id = tsubst var_id
    end
  in
  obj#visit_ty () ty

let make_type_subst (vars : type_var list) (tys : ty list) : TypeVarId.id -> ty
    =
  let ls = List.combine vars tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TypeVarId.Map.add (k : type_var).index v mp)
      TypeVarId.Map.empty ls
  in
  fun id -> TypeVarId.Map.find id mp

let fun_sig_substitute (tsubst : TypeVarId.id -> ty) (sg : fun_sig) :
    inst_fun_sig =
  let subst = ty_substitute tsubst in
  let inputs = List.map subst sg.inputs in
  let outputs = List.map subst sg.outputs in
  { inputs; outputs }

type regular_fun_id = A.fun_id * T.RegionGroupId.id option
[@@deriving show, ord]
(** We use this type as a key for lookups *)

module RegularFunIdOrderedType = struct
  type t = regular_fun_id

  let compare = compare_regular_fun_id

  let to_string = show_regular_fun_id

  let pp_t = pp_regular_fun_id

  let show_t = show_regular_fun_id
end

module RegularFunIdMap = Collections.MakeMap (RegularFunIdOrderedType)

type type_context = {
  types_infos : TA.type_infos;
  cfim_type_defs : T.type_def TypeDefId.Map.t;
}

type fun_context = {
  cfim_fun_defs : A.fun_def FunDefId.Map.t;
  fun_sigs : fun_sig RegularFunIdMap.t;
}

type call_info = {
  forward : S.call;
  backwards : V.abs T.RegionGroupId.Map.t;
      (** TODO: not sure we need this anymore *)
}
(** Whenever we translate a function call or an ended abstraction, we
    store the related information (this is useful when translating ended
    children abstractions)
 *)

type bs_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  bid : T.RegionGroupId.id option;  (** TODO: rename *)
  sv_to_var : var V.SymbolicValueId.Map.t;
      (** Whenever we encounter a new symbolic value (introduced because of
          a symbolic expansion or upon ending an abstraction, for instance)
          we introduce a new variable (with a let-binding).
   *)
  var_counter : VarId.generator;
  forward_inputs : var list;
      (** The input parameters for the forward function *)
  backward_inputs : var list T.RegionGroupId.Map.t;
      (** The input parameters for the backward functions *)
  backward_outputs : var list T.RegionGroupId.Map.t;
      (** The variables that the backward functions will output *)
  calls : call_info V.FunCallId.Map.t;
      (** The function calls we encountered so far *)
  abstractions : V.abs V.AbstractionId.Map.t;
      (** The ended abstractions we encountered so far *)
}
(** Body synthesis context *)

type fs_ctx = {
  fun_def : A.fun_def;
  bid : T.RegionGroupId.id option;
  type_context : type_context;
  fun_context : fun_context;
  forward_inputs : var list;
      (** The input parameters for the forward function *)
  backward_inputs : var list T.RegionGroupId.Map.t;
      (** The input parameters for the backward functions *)
  backward_outputs : var list T.RegionGroupId.Map.t;
      (** The variables that the backward functions will output *)
}
(** Function synthesis context

    TODO: remove
 *)

let fs_ctx_to_bs_ctx (fs_ctx : fs_ctx) : bs_ctx =
  let {
    fun_def;
    bid;
    type_context;
    fun_context;
    forward_inputs;
    backward_inputs;
    backward_outputs;
  } =
    fs_ctx
  in
  let sv_to_var = V.SymbolicValueId.Map.empty in
  let var_counter = VarId.generator_zero in
  let calls = V.FunCallId.Map.empty in
  let abstractions = V.AbstractionId.Map.empty in
  {
    bid;
    sv_to_var;
    var_counter;
    type_context;
    fun_context;
    forward_inputs;
    backward_inputs;
    backward_outputs;
    calls;
    abstractions;
  }

let get_instantiated_fun_sig (fun_id : A.fun_id)
    (back_id : T.RegionGroupId.id option) (tys : ty list) (ctx : bs_ctx) :
    inst_fun_sig =
  (* Lookup the non-instantiated function signature *)
  let sg = RegularFunIdMap.find (fun_id, back_id) ctx.fun_context.fun_sigs in
  (* Create the substitution *)
  let tsubst = make_type_subst sg.type_params tys in
  (* Apply *)
  fun_sig_substitute tsubst sg

let bs_ctx_lookup_cfim_type_def (id : TypeDefId.id) (ctx : bs_ctx) : T.type_def
    =
  TypeDefId.Map.find id ctx.type_context.cfim_type_defs

let bs_ctx_lookup_cfim_fun_def (id : FunDefId.id) (ctx : bs_ctx) : A.fun_def =
  FunDefId.Map.find id ctx.fun_context.cfim_fun_defs

(* TODO: move *)
let bs_ctx_lookup_local_function_sig (def_id : FunDefId.id)
    (back_id : T.RegionGroupId.id option) (ctx : bs_ctx) : fun_sig =
  let id = (A.Local def_id, back_id) in
  RegularFunIdMap.find id ctx.fun_context.fun_sigs

let bs_ctx_register_forward_call (call_id : V.FunCallId.id) (forward : S.call)
    (ctx : bs_ctx) : bs_ctx =
  let calls = ctx.calls in
  assert (not (V.FunCallId.Map.mem call_id calls));
  let info = { forward; backwards = T.RegionGroupId.Map.empty } in
  let calls = V.FunCallId.Map.add call_id info calls in
  { ctx with calls }

let bs_ctx_register_backward_call (abs : V.abs) (ctx : bs_ctx) : bs_ctx * fun_id
    =
  (* Insert the abstraction in the call informations *)
  let back_id = abs.back_id in
  let info = V.FunCallId.Map.find abs.call_id ctx.calls in
  assert (not (T.RegionGroupId.Map.mem back_id info.backwards));
  let backwards = T.RegionGroupId.Map.add back_id abs info.backwards in
  let info = { info with backwards } in
  let calls = V.FunCallId.Map.add abs.call_id info ctx.calls in
  (* Insert the abstraction in the abstractions map *)
  let abstractions = ctx.abstractions in
  assert (not (V.AbstractionId.Map.mem abs.abs_id abstractions));
  let abstractions = V.AbstractionId.Map.add abs.abs_id abs abstractions in
  (* Retrieve the fun_id *)
  let fun_id =
    match info.forward.call_id with
    | S.Fun (fid, _) -> Regular (fid, Some abs.back_id)
    | S.Unop _ | S.Binop _ -> failwith "Unreachable"
  in
  (* Update the context and return *)
  ({ ctx with calls; abstractions }, fun_id)

let rec translate_sty (ty : T.sty) : ty =
  let translate = translate_sty in
  match ty with
  | T.Adt (type_id, regions, tys) ->
      (* Can't translate types with regions for now *)
      assert (regions = []);
      let tys = List.map translate tys in
      Adt (type_id, tys)
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> failwith "Unreachable"
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
let translate_type_def_kind (kind : T.type_def_kind) : type_def_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields fields)
  | T.Enum variants -> Enum (translate_variants variants)

(** Translate a type definition from IM 

    TODO: this is not symbolic to pure but IM to pure. Still, I don't see the
    point of moving this definition for now.
 *)
let translate_type_def (def : T.type_def) : type_def =
  (* Translate *)
  let def_id = def.T.def_id in
  let name = translate_type_name def in
  (* Can't translate types with regions for now *)
  assert (def.region_params = []);
  let type_params = def.type_params in
  let kind = translate_type_def_kind def.T.kind in
  { def_id; name; type_params; kind }

(** Translate a type, seen as an input/output of a forward function
    (preserve all borrows, etc.)
*)

let rec translate_fwd_ty (types_infos : TA.type_infos) (ty : 'r T.ty) : ty =
  let translate = translate_fwd_ty types_infos in
  match ty with
  | T.Adt (type_id, regions, tys) ->
      (* Can't translate types with regions for now *)
      assert (regions = []);
      (* No general parametricity for now *)
      assert (not (List.exists (TypesUtils.ty_has_borrows types_infos) tys));
      (* Translate the type parameters *)
      let tys = List.map translate tys in
      Adt (type_id, tys)
  | TypeVar vid -> TypeVar vid
  | Bool -> Bool
  | Char -> Char
  | Never -> failwith "Unreachable"
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
      | T.AdtId _ | Assumed _ ->
          (* Don't accept ADTs (which are not tuples) with borrows for now *)
          assert (not (TypesUtils.ty_has_borrows types_infos ty));
          None
      | T.Tuple -> (
          (* Tuples can contain borrows (which we eliminated) *)
          let tys_t = List.filter_map translate tys in
          match tys_t with [] -> None | _ -> Some (Adt (T.Tuple, tys_t))))
  | TypeVar vid -> wrap (TypeVar vid)
  | Bool -> wrap Bool
  | Char -> wrap Char
  | Never -> failwith "Unreachable"
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

let list_ancestor_abstractions_ids (ctx : bs_ctx) (abs : V.abs) :
    V.AbstractionId.id list =
  (* We could do something more "elegant" without references, but it is
   * so much simpler to use references... *)
  let abs_set = ref V.AbstractionId.Set.empty in
  let rec gather (abs_id : V.AbstractionId.id) : unit =
    if V.AbstractionId.Set.mem abs_id !abs_set then ()
    else (
      abs_set := V.AbstractionId.Set.add abs_id !abs_set;
      let abs = V.AbstractionId.Map.find abs_id ctx.abstractions in
      List.iter gather abs.original_parents)
  in
  gather abs.abs_id;
  let ids = !abs_set in
  (* List the ancestors, in the proper order *)
  let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
  List.filter
    (fun id -> V.AbstractionId.Set.mem id ids)
    call_info.forward.abstractions

let list_ancestor_abstractions (ctx : bs_ctx) (abs : V.abs) : V.abs list =
  let abs_ids = list_ancestor_abstractions_ids ctx abs in
  List.map (fun id -> V.AbstractionId.Map.find id ctx.abstractions) abs_ids

let translate_fun_sig (types_infos : TA.type_infos) (sg : A.fun_sig)
    (bid : T.RegionGroupId.id option) : fun_sig =
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
  let inputs = List.append fwd_inputs back_inputs in
  (* Outputs *)
  let outputs : ty list =
    match gid with
    | None ->
        (* This is a forward function: there is one output *)
        [ translate_fwd_ty types_infos sg.output ]
    | Some gid ->
        (* This is a backward function: there might be several outputs.
         * The outputs are the borrows inside the regions of the abstractions
         * and which are present in the input values. For instance, see:
         * ```
         * fn f<'a>(x : 'a mut u32) -> ...;
         * ```
         * Upon ending the abstraction for 'a, we give back the borrow which
         * was consumed through the `x` parameter.
         *)
        List.filter_map (translate_back_ty_for_gid gid) sg.inputs
  in
  (* Type parameters *)
  let type_params = sg.type_params in
  (* Return *)
  { type_params; inputs; outputs }

let fresh_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) :
    bs_ctx * var =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
  let var = { id; ty } in
  (* Insert in the map *)
  let sv_to_var = V.SymbolicValueId.Map.add sv.sv_id var ctx.sv_to_var in
  (* Update the context *)
  let ctx = { ctx with var_counter; sv_to_var } in
  (* Return *)
  (ctx, var)

let fresh_vars_for_symbolic_values (svl : V.symbolic_value list) (ctx : bs_ctx)
    : bs_ctx * var list =
  List.fold_left_map (fun ctx sv -> fresh_var_for_symbolic_value sv ctx) ctx svl

(** This generates a fresh variable **which is not to be linked to any symbolic value** *)
let fresh_var (ty : ty) (ctx : bs_ctx) : bs_ctx * var =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let var = { id; ty } in
  (* Update the context *)
  let ctx = { ctx with var_counter } in
  (* Return *)
  (ctx, var)

let fresh_vars (tys : ty list) (ctx : bs_ctx) : bs_ctx * var list =
  List.fold_left_map (fun ctx ty -> fresh_var ty ctx) ctx tys

let lookup_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) : var =
  V.SymbolicValueId.Map.find sv.sv_id ctx.sv_to_var

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
let rec typed_value_to_rvalue (ctx : bs_ctx) (v : V.typed_value) : typed_rvalue
    =
  let translate = typed_value_to_rvalue ctx in
  let value =
    match v.value with
    | V.Concrete cv -> RvConcrete cv
    | Adt av ->
        let variant_id = av.variant_id in
        let field_values = List.map translate av.field_values in
        RvAdt { variant_id; field_values }
    | Bottom -> failwith "Unreachable"
    | Loan lc -> (
        match lc with
        | SharedLoan (_, v) -> (translate v).value
        | MutLoan _ -> failwith "Unreachable")
    | Borrow bc -> (
        match bc with
        | V.SharedBorrow (mv, _) ->
            (* The meta-value stored in the shared borrow was added especially
             * for this case (because we can't use the borrow id for lookups) *)
            (translate mv).value
        | V.InactivatedMutBorrow _ -> failwith "Unreachable"
        | V.MutBorrow (_, v) ->
            (* Borrows are the identity in the extraction *)
            (translate v).value)
    | Symbolic sv ->
        let var = lookup_var_for_symbolic_value sv ctx in
        (mk_typed_rvalue_from_var var).value
  in
  let ty = ctx_translate_fwd_ty ctx v.ty in
  { value; ty }

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
    typed_rvalue option =
  let translate = typed_avalue_to_consumed ctx in
  match av.value with
  | AConcrete _ -> failwith "Unreachable"
  | AAdt adt_v -> (
      (* Translate the field values *)
      let field_values = List.filter_map translate adt_v.field_values in
      (* For now, only tuples can contain borrows *)
      let adt_id, _, _ = TypesUtils.ty_as_adt av.ty in
      match adt_id with
      | T.AdtId _ | T.Assumed T.Box ->
          assert (field_values = []);
          None
      | T.Tuple ->
          (* Return *)
          let variant_id = adt_v.variant_id in
          if field_values = [] then None
          else
            let value = RvAdt { variant_id; field_values } in
            let ty = ctx_translate_fwd_ty ctx av.ty in
            let rv = { value; ty } in
            Some rv)
  | ABottom -> failwith "Unreachable"
  | ALoan lc -> aloan_content_to_consumed ctx lc
  | ABorrow bc -> aborrow_content_to_consumed ctx bc
  | ASymbolic aproj -> aproj_to_consumed ctx aproj
  | AIgnored -> None

and aloan_content_to_consumed (ctx : bs_ctx) (lc : V.aloan_content) :
    typed_rvalue option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> failwith "Unreachable"
  | AEndedMutLoan { child = _; given_back = _; given_back_meta } ->
      (* Return the meta-value *)
      Some (typed_value_to_rvalue ctx given_back_meta)
  | AEndedSharedLoan (_, _) ->
      (* We don't dive into shared loans: there is nothing to give back
       * inside (note that there could be a mutable borrow in the shared
       * value, pointing to a mutable loan in the child avalue, but this
       * borrow is in practice immutable) *)
      None
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      failwith "Unreachable"
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      None

and aborrow_content_to_consumed (_ctx : bs_ctx) (bc : V.aborrow_content) :
    typed_rvalue option =
  match bc with
  | V.AMutBorrow (_, _, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      failwith "Unreachable"
  | AEndedMutBorrow (_, _) ->
      (* We collect consumed values: ignore *)
      None
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AProjSharedBorrow _ ->
      (* Ignore *)
      None

and aproj_to_consumed (ctx : bs_ctx) (aproj : V.aproj) : typed_rvalue option =
  match aproj with
  | V.AEndedProjLoans (msv, []) ->
      (* The symbolic value was left unchanged *)
      let var = lookup_var_for_symbolic_value msv ctx in
      Some (mk_typed_rvalue_from_var var)
  | V.AEndedProjLoans (_, [ (mnv, child_aproj) ]) ->
      assert (child_aproj = AIgnoredProjBorrows);
      (* The symbolic value was updated *)
      let var = lookup_var_for_symbolic_value mnv ctx in
      Some (mk_typed_rvalue_from_var var)
  | V.AEndedProjLoans (_, _) ->
      (* The symbolic value was updated, and the given back values come from sevearl
       * abstractions *)
      raise Unimplemented
  | AEndedProjBorrows _ -> (* We consider consumed values *) None
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      failwith "Unreachable"

(** Convert the abstraction values in an abstraction to consumed values.

    See [typed_avalue_to_consumed].
 *)
let abs_to_consumed (ctx : bs_ctx) (abs : V.abs) : typed_rvalue list =
  List.filter_map (typed_avalue_to_consumed ctx) abs.avalues

(** Explore an abstraction value and convert it to a given back value
    by collecting all the meta-values from the ended *borrows*.

    Given back values are lvalues, because when an abstraction ends, we
    introduce a call to a backward function in the synthesized program,
    which introduces new values:
    ```
    let (nx, ny) = f_back ... in
        ^^^^^^^^
    ```
 *)
let rec typed_avalue_to_given_back (av : V.typed_avalue) (ctx : bs_ctx) :
    bs_ctx * typed_lvalue option =
  match av.value with
  | AConcrete _ -> failwith "Unreachable"
  | AAdt adt_v -> (
      (* Translate the field values *)
      let ctx, field_values =
        List.fold_left_map
          (fun ctx fv -> typed_avalue_to_given_back fv ctx)
          ctx adt_v.field_values
      in
      let field_values = List.filter_map (fun x -> x) field_values in
      (* For now, only tuples can contain borrows *)
      let adt_id, _, _ = TypesUtils.ty_as_adt av.ty in
      match adt_id with
      | T.AdtId _ | T.Assumed T.Box ->
          assert (field_values = []);
          (ctx, None)
      | T.Tuple ->
          (* Return *)
          let variant_id = adt_v.variant_id in
          assert (variant_id = None);
          if field_values = [] then (ctx, None)
          else
            let value = LvTuple field_values in
            let ty = ctx_translate_fwd_ty ctx av.ty in
            let lv : typed_lvalue = { value; ty } in
            (ctx, Some lv))
  | ABottom -> failwith "Unreachable"
  | ALoan lc -> aloan_content_to_given_back lc ctx
  | ABorrow bc -> aborrow_content_to_given_back bc ctx
  | ASymbolic aproj -> aproj_to_given_back aproj ctx
  | AIgnored -> (ctx, None)

and aloan_content_to_given_back (lc : V.aloan_content) (ctx : bs_ctx) :
    bs_ctx * typed_lvalue option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> failwith "Unreachable"
  | AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
  | AEndedSharedLoan (_, _) ->
      (* We consider given back values, and thus ignore those *)
      (ctx, None)
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      failwith "Unreachable"
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      (ctx, None)

and aborrow_content_to_given_back (bc : V.aborrow_content) (ctx : bs_ctx) :
    bs_ctx * typed_lvalue option =
  match bc with
  | V.AMutBorrow (_, _, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      failwith "Unreachable"
  | AEndedMutBorrow (mv, _) ->
      (* Return the meta-value *)
      let ctx, var = fresh_var_for_symbolic_value mv ctx in
      (ctx, Some (mk_typed_lvalue_from_var var))
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AProjSharedBorrow _ ->
      (* Ignore *)
      (ctx, None)

and aproj_to_given_back (aproj : V.aproj) (ctx : bs_ctx) :
    bs_ctx * typed_lvalue option =
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
      (ctx, Some (mk_typed_lvalue_from_var var))
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      failwith "Unreachable"

(** Convert the abstraction values in an abstraction to given back values.

    See [typed_avalue_to_given_back].
 *)
let abs_to_given_back (abs : V.abs) (ctx : bs_ctx) : bs_ctx * typed_lvalue list
    =
  let ctx, values =
    List.fold_left_map
      (fun ctx av -> typed_avalue_to_given_back av ctx)
      ctx abs.avalues
  in
  let values = List.filter_map (fun x -> x) values in
  (ctx, values)

(** Return the ordered list of the (transitive) parents of a given abstraction.

    Is used for instance when collecting the input values given to all the
    parent functions, in order to properly instantiate an 
 *)
let get_abs_ancestors (ctx : bs_ctx) (abs : V.abs) : S.call * V.abs list =
  let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
  let abs_ancestors = list_ancestor_abstractions ctx abs in
  (call_info.forward, abs_ancestors)

let rec translate_expression (e : S.expression) (ctx : bs_ctx) : expression =
  match e with
  | S.Return opt_v -> translate_return opt_v ctx
  | Panic -> Panic
  | FunCall (call, e) -> translate_function_call call e ctx
  | EndAbstraction (abs, e) -> translate_end_abstraction abs e ctx
  | Expansion (sv, exp) -> translate_expansion sv exp ctx
  | Meta (_, e) ->
      (* We ignore the meta information *)
      translate_expression e ctx

and translate_return (opt_v : V.typed_value option) (ctx : bs_ctx) : expression
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
      let v = typed_value_to_rvalue ctx v in
      Return v
  | Some bid ->
      (* Backward function *)
      (* Sanity check *)
      assert (opt_v = None);
      (* We simply need to return the variables in which we stored the values
       * we need to give back.
       * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
      let backward_outputs =
        T.RegionGroupId.Map.find bid ctx.backward_outputs
      in
      let field_values = List.map mk_typed_rvalue_from_var backward_outputs in
      let ret_value = RvAdt { variant_id = None; field_values } in
      let ret_tys = List.map (fun (v : typed_rvalue) -> v.ty) field_values in
      let ret_ty = Adt (T.Tuple, ret_tys) in
      let ret_value : typed_rvalue = { value = ret_value; ty = ret_ty } in
      Return ret_value

and translate_function_call (call : S.call) (e : S.expression) (ctx : bs_ctx) :
    expression =
  (* Translate the function call *)
  let type_params = List.map (ctx_translate_fwd_ty ctx) call.type_params in
  let args = List.map (typed_value_to_rvalue ctx) call.args in
  let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
  (* Retrieve the function id, and register the function call in the context
   * if necessary. *)
  let ctx, func =
    match call.call_id with
    | S.Fun (fid, call_id) ->
        let ctx = bs_ctx_register_forward_call call_id call ctx in
        let func = Regular (fid, None) in
        (ctx, func)
    | S.Unop E.Not -> (ctx, Unop Not)
    | S.Unop E.Neg -> (
        match args with
        | [ arg ] ->
            let int_ty = ty_as_integer arg.ty in
            (ctx, Unop (Neg int_ty))
        | _ -> failwith "Unreachable")
    | S.Binop binop -> (
        match args with
        | [ arg0; arg1 ] ->
            let int_ty0 = ty_as_integer arg0.ty in
            let int_ty1 = ty_as_integer arg1.ty in
            assert (int_ty0 = int_ty1);
            (ctx, Binop (binop, int_ty0))
        | _ -> failwith "Unreachable")
  in
  let call = { func; type_params; args } in
  (* Translate the next expression *)
  let e = translate_expression e ctx in
  (* Put together *)
  Let (Call ([ mk_typed_lvalue_from_var dest ], call), e)

and translate_end_abstraction (abs : V.abs) (e : S.expression) (ctx : bs_ctx) :
    expression =
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
        (fun (var, v) -> assert ((var : var).ty = (v : typed_rvalue).ty))
        variables_values;
      (* Translate the next expression *)
      let e = translate_expression e ctx in
      (* Generate the assignemnts *)
      List.fold_right
        (fun (var, value) e ->
          Let (Assign (mk_typed_lvalue_from_var var, value), e))
        variables_values e
  | V.FunCall ->
      let call_info = V.FunCallId.Map.find abs.call_id ctx.calls in
      let call = call_info.forward in
      let type_params = List.map (ctx_translate_fwd_ty ctx) call.type_params in
      (* Retrive the orignal call and the parent abstractions *)
      let forward, backwards = get_abs_ancestors ctx abs in
      (* Retrieve the values consumed when we called the forward function and
       * ended the parent backward functions: those give us part of the input
       * values *)
      let fwd_inputs = List.map (typed_value_to_rvalue ctx) forward.args in
      let back_ancestors_inputs =
        List.concat (List.map (abs_to_consumed ctx) backwards)
      in
      (* Retrieve the values consumed upon ending the loans inside this
       * abstraction: those give us the remaining input values *)
      let back_inputs = abs_to_consumed ctx abs in
      let inputs =
        List.concat [ fwd_inputs; back_ancestors_inputs; back_inputs ]
      in
      (* Retrieve the values given back by this function: those are the output
       * values *)
      let ctx, outputs = abs_to_given_back abs ctx in
      (* Sanity check: the inputs and outputs have the proper number and the proper type *)
      let fun_id =
        match call.call_id with
        | S.Fun (fun_id, _) -> fun_id
        | Unop _ | Binop _ ->
            (* Those don't have backward functions *) failwith "Unreachable"
      in

      let inst_sg =
        get_instantiated_fun_sig fun_id (Some abs.back_id) type_params ctx
      in
      List.iter
        (fun (x, ty) -> assert ((x : typed_rvalue).ty = ty))
        (List.combine inputs inst_sg.inputs);
      List.iter
        (fun (x, ty) -> assert ((x : typed_lvalue).ty = ty))
        (List.combine outputs inst_sg.outputs);
      (* Retrieve the function id, and register the function call in the context
       * if necessary *)
      let ctx, func = bs_ctx_register_backward_call abs ctx in
      (* Translate the next expression *)
      let e = translate_expression e ctx in
      (* Put everything together *)
      let call = { func; type_params; args = inputs } in
      Let (Call (outputs, call), e)
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
      (* Retrieve the values given back upon ending this abstraction *)
      let ctx, given_back = abs_to_given_back abs ctx in
      (* Link the inputs to those given back values - note that this also
       * checks we have the same number of values, of course *)
      let given_back_inputs = List.combine given_back inputs in
      (* Sanity check *)
      List.iter
        (fun ((given_back, input) : typed_lvalue * var) ->
          assert (given_back.ty = input.ty))
        given_back_inputs;
      (* Translate the next expression *)
      let e = translate_expression e ctx in
      (* Generate the assignments *)
      List.fold_right
        (fun (given_back, input_var) e ->
          Let (Assign (given_back, mk_typed_rvalue_from_var input_var), e))
        given_back_inputs e

and translate_expansion (sv : V.symbolic_value) (exp : S.expansion)
    (ctx : bs_ctx) : expression =
  (* Translate the scrutinee *)
  let scrutinee_var = lookup_var_for_symbolic_value sv ctx in
  let scrutinee = mk_typed_rvalue_from_var scrutinee_var in
  (* Translate the branches *)
  match exp with
  | ExpandNoBranch (sexp, e) -> (
      match sexp with
      | V.SeConcrete _ ->
          (* Actually, we don't *register* symbolic expansions to constant
           * values in the symbolic ADT *)
          failwith "Unreachable"
      | SeMutRef (_, sv) | SeSharedRef (_, sv) ->
          (* The (mut/shared) borrow type is extracted to identity: we thus simply
           * introduce an reassignment *)
          let ctx, var = fresh_var_for_symbolic_value sv ctx in
          let e = translate_expression e ctx in
          Let (Assign (mk_typed_lvalue_from_var var, scrutinee), e)
      | SeAdt _ ->
          (* Should be in the [ExpandAdt] case *)
          failwith "Unreachable")
  | ExpandAdt branches -> (
      (* We don't do the same thing if there is a branching or not *)
      match branches with
      | [] -> failwith "Unreachable"
      | [ (variant_id, svl, branch) ] -> (
          let type_id, _, _ = TypesUtils.ty_as_adt sv.V.sv_ty in
          let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
          let branch = translate_expression branch ctx in
          match type_id with
          | T.AdtId adt_id ->
              (* Detect if this is an enumeration or not *)
              let tdef = bs_ctx_lookup_cfim_type_def adt_id ctx in
              let is_enum = type_def_is_enum tdef in
              if is_enum then
                (* This is an enumeration: introduce an [ExpandEnum] let-binding *)
                let variant_id = Option.get variant_id in
                let vars = List.map (fun x -> Var x) vars in
                Let
                  ( Deconstruct (vars, Some (adt_id, variant_id), scrutinee),
                    branch )
              else
                (* This is not an enumeration: introduce let-bindings for every
                 * field.
                 * We use the [dest] variable in order not to have to recompute
                 * the type of the result of the projection... *)
                let gen_field_proj (field_id : FieldId.id) (dest : var) :
                    typed_rvalue =
                  let pkind = E.ProjAdt (adt_id, None) in
                  let pe : projection_elem = { pkind; field_id } in
                  let projection = [ pe ] in
                  let place = { var = scrutinee_var.id; projection } in
                  let value = RvPlace place in
                  let ty = dest.ty in
                  { value; ty }
                in
                let id_var_pairs = FieldId.mapi (fun fid v -> (fid, v)) vars in
                List.fold_right
                  (fun (fid, var) e ->
                    let field_proj = gen_field_proj fid var in
                    Let (Assign (mk_typed_lvalue_from_var var, field_proj), e))
                  id_var_pairs branch
          | T.Tuple ->
              let vars = List.map (fun x -> Var x) vars in
              Let (Deconstruct (vars, None, scrutinee), branch)
          | T.Assumed T.Box ->
              (* There should be exactly one variable *)
              let var =
                match vars with [ v ] -> v | _ -> failwith "Unreachable"
              in
              (* We simply introduce an assignment - the box type is the
               * identity when extracted (`box a == a`) *)
              Let (Assign (mk_typed_lvalue_from_var var, scrutinee), branch))
      | branches ->
          let translate_branch (variant_id : T.VariantId.id option)
              (svl : V.symbolic_value list) (branch : S.expression) :
              match_branch =
            (* There *must* be a variant id - otherwise there can't be several branches *)
            let variant_id = Option.get variant_id in
            let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
            let vars = List.map (fun x -> Var x) vars in
            let branch = translate_expression branch ctx in
            { variant_id; vars; branch }
          in
          let branches =
            List.map (fun (vid, svl, e) -> translate_branch vid svl e) branches
          in
          Switch (scrutinee, Match branches))
  | ExpandBool (true_e, false_e) ->
      (* We don't need to update the context: we don't introduce any
       * new values/variables *)
      let true_e = translate_expression true_e ctx in
      let false_e = translate_expression false_e ctx in
      Switch (scrutinee, If (true_e, false_e))
  | ExpandInt (int_ty, branches, otherwise) ->
      let translate_branch ((v, branch_e) : V.scalar_value * S.expression) :
          scalar_value * expression =
        (* We don't need to update the context: we don't introduce any
         * new values/variables *)
        let branch_e = translate_expression branch_e ctx in
        (v, branch_e)
      in
      let branches = List.map translate_branch branches in
      let otherwise = translate_expression otherwise ctx in
      Switch (scrutinee, SwitchInt (int_ty, branches, otherwise))

let translate_fun_def (def : A.fun_def) (ctx : bs_ctx) (body : S.expression) :
    fun_def =
  let bid = ctx.bid in
  (* Translate the function *)
  let def_id = def.A.def_id in
  let basename = def.name in
  let signature = bs_ctx_lookup_local_function_sig def_id bid ctx in
  let body = translate_expression body ctx in
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
  let inputs = List.append ctx.forward_inputs backward_inputs in
  (* Sanity check *)
  assert (
    List.for_all
      (fun (var, ty) -> (var : var).ty = ty)
      (List.combine inputs signature.inputs));
  { def_id; basename; signature; inputs; body }

let translate_type_defs (type_defs : T.type_def list) : type_def TypeDefId.Map.t
    =
  List.fold_left
    (fun tdefs def ->
      let tdef = translate_type_def def in
      TypeDefId.Map.add def.def_id tdef tdefs)
    TypeDefId.Map.empty type_defs

let translate_fun_signatures (types_infos : TA.type_infos)
    (functions : (A.fun_id * A.fun_sig) list) : fun_sig RegularFunIdMap.t =
  (* For every function, translate the signatures of:
     - the forward function
     - the backward functions
  *)
  let translate_one (fun_id : A.fun_id) (sg : A.fun_sig) :
      (regular_fun_id * fun_sig) list =
    (* The forward function *)
    let fwd_sg = translate_fun_sig types_infos sg None in
    let fwd_id = (fun_id, None) in
    (* The backward functions *)
    let back_sgs =
      List.map
        (fun (rg : T.region_var_group) ->
          let tsg = translate_fun_sig types_infos sg (Some rg.id) in
          let id = (fun_id, Some rg.id) in
          (id, tsg))
        sg.regions_hierarchy
    in
    (* Return *)
    (fwd_id, fwd_sg) :: back_sgs
  in
  let translated =
    List.concat (List.map (fun (id, sg) -> translate_one id sg) functions)
  in
  List.fold_left
    (fun m (id, sg) -> RegularFunIdMap.add id sg m)
    RegularFunIdMap.empty translated
