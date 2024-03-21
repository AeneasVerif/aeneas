open Types
open LlbcAst
open Errors

type subtype_info = {
  under_borrow : bool;  (** Are we inside a borrow? *)
  under_mut_borrow : bool;  (** Are we inside a mut borrow? *)
}
[@@deriving show]

(** See {!type_decl_info} *)
type type_param_info = subtype_info [@@deriving show]

type expl_info = subtype_info [@@deriving show]

type type_borrows_info = {
  contains_static : bool;
      (** Does the type (transitively) contain a static borrow? *)
  contains_borrow : bool;  (** Does the type (transitively) contain a borrow? *)
  contains_nested_borrows : bool;
      (** Does the type (transitively) contain nested borrows? *)
  contains_borrow_under_mut : bool;
}
[@@deriving show]

(** Generic definition *)
type 'p g_type_info = {
  borrows_info : type_borrows_info;
      (** Various informations about the borrows *)
  param_infos : 'p;  (** Gives information about the type parameters *)
  is_tuple_struct : bool;
      (** If true, it means the type is a record that we should extract as a tuple.
          This field is only valid for type declarations.
       *)
}
[@@deriving show]

(** Information about a type definition. *)
type type_decl_info = type_param_info list g_type_info [@@deriving show]

(** Information about a type. *)
type ty_info = type_borrows_info [@@deriving show]

(** Helper definition.

    Allows us to factorize code: {!analyze_full_ty} is used both to analyze
    type definitions and types. *)
type partial_type_info = type_param_info list option g_type_info
[@@deriving show]

type type_infos = type_decl_info TypeDeclId.Map.t [@@deriving show]

let expl_info_init = { under_borrow = false; under_mut_borrow = false }

let type_borrows_info_init : type_borrows_info =
  {
    contains_static = false;
    contains_borrow = false;
    contains_nested_borrows = false;
    contains_borrow_under_mut = false;
  }

(** Return true if a type declaration is a structure with unnamed fields.

    Note that there are two possibilities:
    - either all the fields are named
    - or none of the fields are named
 *)
let type_decl_is_tuple_struct (x : type_decl) : bool =
  match x.kind with
  | Struct fields -> List.for_all (fun f -> f.field_name = None) fields
  | _ -> false

let initialize_g_type_info (is_tuple_struct : bool) (param_infos : 'p) :
    'p g_type_info =
  { borrows_info = type_borrows_info_init; is_tuple_struct; param_infos }

let initialize_type_decl_info (is_rec : bool) (def : type_decl) : type_decl_info
    =
  let param_info = { under_borrow = false; under_mut_borrow = false } in
  let param_infos = List.map (fun _ -> param_info) def.generics.types in
  let is_tuple_struct =
    !Config.use_tuple_structs && (not is_rec) && type_decl_is_tuple_struct def
  in
  initialize_g_type_info is_tuple_struct param_infos

let type_decl_info_to_partial_type_info (info : type_decl_info) :
    partial_type_info =
  {
    borrows_info = info.borrows_info;
    is_tuple_struct = info.is_tuple_struct;
    param_infos = Some info.param_infos;
  }

let partial_type_info_to_type_decl_info (info : partial_type_info) :
    type_decl_info =
  {
    borrows_info = info.borrows_info;
    is_tuple_struct = info.is_tuple_struct;
    param_infos = Option.get info.param_infos;
  }

let partial_type_info_to_ty_info (info : partial_type_info) : ty_info =
  info.borrows_info

let analyze_full_ty (updated : bool ref) (infos : type_infos)
    (ty_info : partial_type_info) (ty : ty) : partial_type_info =
  (* Small utility *)
  let check_update_bool (original : bool) (nv : bool) : bool =
    if nv && not original then (
      updated := true;
      nv)
    else original
  in
  let r_is_static (r : region) : bool = r = RStatic in

  (* Update a partial_type_info, while registering if we actually performed an update *)
  let update_ty_info (ty_info : partial_type_info)
      (ty_b_info : type_borrows_info) : partial_type_info =
    let original = ty_info.borrows_info in
    let contains_static =
      check_update_bool original.contains_static ty_b_info.contains_static
    in
    let contains_borrow =
      check_update_bool original.contains_borrow ty_b_info.contains_borrow
    in
    let contains_nested_borrows =
      check_update_bool original.contains_nested_borrows
        ty_b_info.contains_nested_borrows
    in
    let contains_borrow_under_mut =
      check_update_bool original.contains_borrow_under_mut
        ty_b_info.contains_borrow_under_mut
    in
    let updated_borrows_info =
      {
        contains_static;
        contains_borrow;
        contains_nested_borrows;
        contains_borrow_under_mut;
      }
    in
    { ty_info with borrows_info = updated_borrows_info }
  in

  (* The recursive function which explores the type *)
  let rec analyze (expl_info : expl_info) (ty_info : partial_type_info)
      (ty : ty) : partial_type_info =
    match ty with
    | TLiteral _ | TNever | TTraitType _ -> ty_info
    | TVar var_id -> (
        (* Update the information for the proper parameter, if necessary *)
        match ty_info.param_infos with
        | None -> ty_info
        | Some param_infos ->
            let param_info = TypeVarId.nth param_infos var_id in
            (* Set [under_borrow] *)
            let under_borrow =
              check_update_bool param_info.under_borrow expl_info.under_borrow
            in
            (* Set [under_nested_borrows] *)
            let under_mut_borrow =
              check_update_bool param_info.under_mut_borrow
                expl_info.under_mut_borrow
            in
            (* Update param_info *)
            let param_info = { under_borrow; under_mut_borrow } in
            let param_infos =
              TypeVarId.update_nth param_infos var_id param_info
            in
            let param_infos = Some param_infos in
            { ty_info with param_infos })
    | TRef (r, rty, rkind) ->
        (* Update the type info *)
        let contains_static = r_is_static r in
        let contains_borrow = true in
        let contains_nested_borrows = expl_info.under_borrow in
        let contains_borrow_under_mut = expl_info.under_mut_borrow in
        let ty_b_info =
          {
            contains_static;
            contains_borrow;
            contains_nested_borrows;
            contains_borrow_under_mut;
          }
        in
        let ty_info = update_ty_info ty_info ty_b_info in
        (* Update the exploration info *)
        let expl_info =
          {
            under_borrow = true;
            under_mut_borrow = expl_info.under_mut_borrow || rkind = RMut;
          }
        in
        (* Continue exploring *)
        analyze expl_info ty_info rty
    | TRawPtr (rty, _) ->
        (* TODO: not sure what to do here *)
        analyze expl_info ty_info rty
    | TAdt ((TTuple | TAssumed (TBox | TSlice | TArray | TStr)), generics) ->
        (* Nothing to update: just explore the type parameters *)
        List.fold_left
          (fun ty_info ty -> analyze expl_info ty_info ty)
          ty_info generics.types
    | TAdt (TAdtId adt_id, generics) ->
        (* Lookup the information for this type definition *)
        let adt_info = TypeDeclId.Map.find adt_id infos in
        (* Update the type info with the information from the adt *)
        let ty_info = update_ty_info ty_info adt_info.borrows_info in
        (* Check if 'static appears in the region parameters *)
        let found_static = List.exists r_is_static generics.regions in
        let borrows_info = ty_info.borrows_info in
        let borrows_info =
          {
            borrows_info with
            contains_static =
              check_update_bool borrows_info.contains_static found_static;
          }
        in
        let ty_info = { ty_info with borrows_info } in
        (* For every instantiated type parameter: update the exploration info
         * then explore the type *)
        let params_tys = List.combine adt_info.param_infos generics.types in
        let ty_info =
          List.fold_left
            (fun ty_info (param_info, ty) ->
              (* Update the type info *)
              (* Below: we use only the information which we learn only
               * by taking the type parameter into account. *)
              let contains_static = false in
              let contains_borrow = param_info.under_borrow in
              let contains_nested_borrows =
                expl_info.under_borrow && param_info.under_borrow
              in
              let contains_borrow_under_mut =
                expl_info.under_mut_borrow && param_info.under_borrow
              in
              let ty_b_info =
                {
                  contains_static;
                  contains_borrow;
                  contains_nested_borrows;
                  contains_borrow_under_mut;
                }
              in
              let ty_info = update_ty_info ty_info ty_b_info in
              (* Update the exploration info *)
              let expl_info =
                {
                  under_borrow =
                    expl_info.under_borrow || param_info.under_borrow;
                  under_mut_borrow =
                    expl_info.under_mut_borrow || param_info.under_mut_borrow;
                }
              in
              (* Continue exploring *)
              analyze expl_info ty_info ty)
            ty_info params_tys
        in
        (* Return *)
        ty_info
    | TArrow (_regions, inputs, output) ->
        (* Just dive into the arrow *)
        let ty_info =
          List.fold_left
            (fun ty_info ty -> analyze expl_info ty_info ty)
            ty_info inputs
        in
        analyze expl_info ty_info output
  in
  (* Explore *)
  analyze expl_info_init ty_info ty

let type_decl_is_opaque (d : type_decl) : bool =
  match d.kind with Struct _ | Enum _ -> false | Opaque -> true

let analyze_type_decl (updated : bool ref) (infos : type_infos)
    (def : type_decl) : type_infos =
  (* We analyze the type declaration only if it is not opaque (we need to explore
   * the variants of the ADTs *)
  if type_decl_is_opaque def then infos
  else
    (* Retrieve all the types of all the fields of all the variants *)
    let fields_tys : ty list =
      match def.kind with
      | Struct fields -> List.map (fun f -> f.field_ty) fields
      | Enum variants ->
          List.concat
            (List.map
               (fun v -> List.map (fun f -> f.field_ty) v.fields)
               variants)
      | Opaque -> craise def.meta "unreachable"
    in
    (* Explore the types and accumulate information *)
    let type_decl_info = TypeDeclId.Map.find def.def_id infos in
    let type_decl_info = type_decl_info_to_partial_type_info type_decl_info in
    let type_decl_info =
      List.fold_left
        (fun type_decl_info ty ->
          analyze_full_ty updated infos type_decl_info ty)
        type_decl_info fields_tys
    in
    let type_decl_info = partial_type_info_to_type_decl_info type_decl_info in
    (* Update the information for the type definition we explored *)
    let infos = TypeDeclId.Map.add def.def_id type_decl_info infos in
    (* Return *)
    infos

let analyze_type_declaration_group (type_decls : type_decl TypeDeclId.Map.t)
    (infos : type_infos) (decl : type_declaration_group) : type_infos =
  (* Collect the identifiers used in the declaration group *)
  let is_rec, ids =
    match decl with
    | NonRecGroup id -> (false, [ id ])
    | RecGroup ids -> (true, ids)
  in
  (* Retrieve the type definitions *)
  let decl_defs = List.map (fun id -> TypeDeclId.Map.find id type_decls) ids in
  (* Initialize the type information for the current definitions *)
  let infos =
    List.fold_left
      (fun infos (def : type_decl) ->
        TypeDeclId.Map.add def.def_id
          (initialize_type_decl_info is_rec def)
          infos)
      infos decl_defs
  in
  (* Analyze the types - this function simply computes a fixed-point *)
  let updated : bool ref = ref false in
  let rec analyze (infos : type_infos) : type_infos =
    let infos =
      List.fold_left
        (fun infos def -> analyze_type_decl updated infos def)
        infos decl_defs
    in
    if !updated then (
      updated := false;
      analyze infos)
    else infos
  in
  analyze infos

(** Compute the type information for every *type definition* in a list of
    declarations. This type definition information is later used to easily
    compute the information of arbitrary types.
    
    Rk.: pay attention to the difference between type definitions and types!
 *)
let analyze_type_declarations (type_decls : type_decl TypeDeclId.Map.t)
    (decls : type_declaration_group list) : type_infos =
  List.fold_left
    (fun infos decl -> analyze_type_declaration_group type_decls infos decl)
    TypeDeclId.Map.empty decls

(** Analyze a type to check whether it contains borrows, etc., provided
    we have already analyzed the type definitions in the context.
 *)
let analyze_ty (infos : type_infos) (ty : ty) : ty_info =
  (* We don't use [updated] but need to give it as parameter *)
  let updated = ref false in
  (* We don't need to compute whether the type contains 'static or not *)
  let ty_info = initialize_g_type_info false None in
  let ty_info = analyze_full_ty updated infos ty_info ty in
  (* Convert the ty_info *)
  partial_type_info_to_ty_info ty_info
