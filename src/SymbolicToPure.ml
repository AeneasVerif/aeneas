open Errors
module Id = Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module M = Modules
module S = SymbolicAst
module TA = TypesAnalysis
open Pure

(** TODO: move this, it is not useful for symbolic -> pure *)
type name =
  | FunName of A.FunDefId.id * V.BackwardFunctionId.id option
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

let translate_fun_name (fdef : A.fun_def) (bid : V.BackwardFunctionId.id option)
    : Id.name =
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
            (* Several backward functions - note that **we use the backward function id
             * as if it were a region group id** (there is a direct mapping between the
             * two - TODO: merge them) *)
            let rg = V.BackwardFunctionId.nth sg.regions_hierarchy bid in
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

type type_context = {
  types_infos : TA.type_infos;
  type_defs : type_def TypeDefId.Map.t;
}

type fun_context = { fun_defs : fun_def FunDefId.Map.t }

(* TODO: do we really need that actually? *)
type synth_ctx = {
  names : NameMap.t;
  (* TODO: remove? *)
  type_context : type_context;
  fun_context : fun_context;
  declarations : M.declaration_group list;
}

type bs_ctx = {
  type_context : type_context;
  fun_def : A.fun_def;
  bid : V.BackwardFunctionId.id option;
}
(** Body synthesis context *)

let bs_ctx_lookup_type_def (id : TypeDefId.id) (ctx : bs_ctx) : type_def =
  TypeDefId.Map.find id ctx.type_context.type_defs

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

let rec translate_fwd_ty (ctx : bs_ctx) (ty : 'r T.ty) : ty =
  let translate = translate_fwd_ty ctx in
  let types_infos = ctx.type_context.types_infos in
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

(** Translate a type, when some regions may have ended.
    
    We return an option, because the translated type may be empty.
    
    [inside_mut]: are we inside a mutable borrow?
 *)
let rec translate_back_ty (ctx : bs_ctx) (keep_region : 'r -> bool)
    (inside_mut : bool) (ty : 'r T.ty) : ty option =
  let translate = translate_back_ty ctx keep_region inside_mut in
  let types_infos = ctx.type_context.types_infos in
  (* A small helper for "leave" types *)
  let wrap ty = if inside_mut then Some ty else None in
  match ty with
  | T.Adt (type_id, regions, tys) -> (
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
          if keep_region r then translate_back_ty ctx keep_region inside_mut rty
          else None)

(** Small utility: list the transitive parents of a region var group.
    We don't do that in an efficient manner, but it doesn't matter.
 *)
let rec list_parent_region_groups (def : A.fun_def) (gid : T.RegionGroupId.id) :
    T.RegionGroupId.Set.t =
  let rg = T.RegionGroupId.nth def.signature.regions_hierarchy gid in
  let parents =
    List.fold_left
      (fun s gid ->
        (* Compute the parents *)
        let parents = list_parent_region_groups def gid in
        (* Parents U current region *)
        let parents = T.RegionGroupId.Set.add gid parents in
        (* Make the union with the accumulator *)
        T.RegionGroupId.Set.union s parents)
      T.RegionGroupId.Set.empty rg.parents
  in
  parents

(** Small utility: same as [list_parent_region_groups], but returns an ordered list *)
let list_ordered_parent_region_groups (def : A.fun_def)
    (gid : T.RegionGroupId.id) : T.RegionGroupId.id list =
  let pset = list_parent_region_groups def gid in
  let parents =
    List.filter
      (fun (rg : T.region_var_group) -> T.RegionGroupId.Set.mem rg.id pset)
      def.signature.regions_hierarchy
  in
  let parents = List.map (fun (rg : T.region_var_group) -> rg.id) parents in
  parents

let translate_fun_sig (ctx : bs_ctx) (def : A.fun_def)
    (bid : V.BackwardFunctionId.id option) : fun_sig =
  let sg = def.signature in
  (* Retrieve the list of parent backward functions *)
  let gid, parents =
    match bid with
    | None -> (None, T.RegionGroupId.Set.empty)
    | Some bid ->
        let gid = T.RegionGroupId.of_int (V.BackwardFunctionId.to_int bid) in
        let parents = list_parent_region_groups def gid in
        (Some gid, parents)
  in
  (* List the inputs for:
   * - the forward function
   * - the parent backward functions, in proper order
   * - the current backward function (if it is a backward function)
   *)
  let fwd_inputs = List.map (translate_fwd_ty ctx) sg.inputs in
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
    translate_back_ty ctx keep_region inside_mut
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
        [ translate_fwd_ty ctx sg.output ]
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

(** Translate a typed value.

    **IMPORTANT**: this function makes the assumption that the typed value
    doesn't contain ⊥. This means in particular that symbolic values don't
    contain ended regions.
    
    TODO: we might want to remember in the symbolic AST the set of ended
    regions, at the points where we need it, for sanity checks.
    The points where we need this set so far:
    - function call
    - end abstraction
    - return
 *)
let translate_typed_value (ctx : bs_ctx) (v : V.typed_value) : typed_value =
  raise Unimplemented

let fresh_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) :
    bs_ctx * var =
  raise Unimplemented

let fresh_vars_for_symbolic_values (svl : V.symbolic_value list) (ctx : bs_ctx)
    : bs_ctx * var list =
  List.fold_left_map (fun ctx sv -> fresh_var_for_symbolic_value sv ctx) ctx svl

let get_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) : var =
  raise Unimplemented

(* TODO: move *)
let mk_place_from_var (v : var) : place = { var = v.id; projection = [] }

(* TODO: move *)
let type_def_is_enum (def : type_def) : bool =
  match def.kind with Struct _ -> false | Enum _ -> true

let typed_avalue_to_consumed (ctx : bs_ctx) (av : V.typed_avalue) :
    typed_value option =
  raise Unimplemented

let typed_avalue_to_given_back (ctx : bs_ctx) (av : V.typed_avalue) :
    typed_value option =
  raise Unimplemented

let abs_to_consumed (ctx : bs_ctx) (abs : V.abs) : typed_value list =
  List.filter_map (typed_avalue_to_consumed ctx) abs.avalues

let abs_to_given_back (ctx : bs_ctx) (abs : V.abs) : typed_value list =
  List.filter_map (typed_avalue_to_given_back ctx) abs.avalues

(** Return the ordered list of the (transitive) parents of a given abstraction.

    Is used for instance when collecting the input values given to all the
    parent functions, in order to properly instantiate an 
 *)
let get_abs_ordered_parents (ctx : bs_ctx) (call_id : S.call_id)
    (gid : T.RegionGroupId.id) : S.call * V.abs list =
  raise Unimplemented

let rec translate_expression (e : S.expression) (ctx : bs_ctx) : expression =
  match e with
  | S.Return v ->
      let v = translate_typed_value ctx v in
      Return (Value v)
  | Panic -> Panic
  | FunCall (call, e) ->
      (* Translate the function call *)
      let type_params = List.map (translate_fwd_ty ctx) call.type_params in
      let args = List.map (translate_typed_value ctx) call.args in
      let args = List.map (fun v -> Value v) args in
      let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
      let func =
        match call.call_id with
        | S.Fun (A.Local fid, _) -> Local (fid, None)
        | S.Fun (A.Assumed fid, _) -> Assumed fid
        | S.Unop unop -> Unop unop
        | S.Binop binop -> Binop binop
      in
      let call = { func; type_params; args } in
      (* Translate the next expression *)
      let e = translate_expression e ctx in
      (* Put together *)
      Let (Call ([ Var dest ], call), e)
  | EndAbstraction (abs, e) -> translate_end_abstraction abs e
  | Expansion (sv, exp) -> translate_expansion sv exp ctx
  | Meta (_, e) ->
      (* We ignore the meta information *)
      translate_expression e ctx

and translate_end_abstraction (abs : V.abs) (e : S.expression) : expression =
  match abs.kind with
  | V.SynthInput ->
      (* There are no nested borrows for now: we shouldn't get there *)
      raise Unimplemented
  | V.FunCall ->
      (* Retrive the orignal call and the parent abstractions *)
      (* Retrieve the values consumed when we called the forward function and
       * ended the parent backward functions: those give us part of the input
       * values *)
      (* Retrieve the values consumed upon ending the loans inside this
       * abstraction: those give us the remaining input values *)
      (* Retrieve the values given back by this function: those are the output
       * values *)
      (* Put everything together *)
      raise Unimplemented
  | V.SynthRet ->
      (* *)
      raise Unimplemented

and translate_expansion (sv : V.symbolic_value) (exp : S.expansion)
    (ctx : bs_ctx) : expression =
  (* Translate the scrutinee *)
  let scrutinee_var = get_var_for_symbolic_value sv ctx in
  let scrutinee = Place (mk_place_from_var scrutinee_var) in
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
          Let (Assignment (var, scrutinee), e)
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
              let tdef = bs_ctx_lookup_type_def adt_id ctx in
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
                 * field *)
                let gen_field_proj (field_id : FieldId.id) : operand =
                  let pkind = E.ProjAdt (adt_id, None) in
                  let pe : projection_elem = { pkind; field_id } in
                  let projection = [ pe ] in
                  let place = { var = scrutinee_var.id; projection } in
                  Place place
                in
                let id_var_pairs = FieldId.mapi (fun fid v -> (fid, v)) vars in
                List.fold_right
                  (fun (fid, var) e ->
                    let field_proj = gen_field_proj fid in
                    Let (Assignment (var, field_proj), e))
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
              Let (Assignment (var, scrutinee), branch))
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

let translate_fun_def (type_context : type_context) (def : A.fun_def)
    (bid : V.BackwardFunctionId.id option) (body : S.expression) : fun_def =
  let bs_ctx = { type_context; fun_def = def; bid } in
  (* Translate the function *)
  let def_id = def.A.def_id in
  let name = translate_fun_name def bid in
  let signature = translate_fun_sig bs_ctx def bid in
  let body = translate_expression body bs_ctx in
  { def_id; name; signature; body }
