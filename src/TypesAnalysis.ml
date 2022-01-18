open Types
open Modules

type subtype_info = {
  under_borrow : bool;  (** Are we inside a borrow? *)
  under_nested_borrows : bool;  (** Are we inside nested borrows? *)
}
[@@deriving show]

type type_param_info = subtype_info [@@deriving show]
(** See [type_def_info] *)

type expl_info = subtype_info [@@deriving show]

type 'p g_type_info = {
  contains_static : bool;
      (** Does the type (transitively) contains a static borrow? *)
  contains_borrow : bool;
      (** Does the type (transitively) contains a borrow? *)
  contains_nested_borrows : bool;
      (** Does the type (transitively) contains nested borrows? *)
  param_infos : 'p;  (** Gives information about the type parameters *)
}
[@@deriving show]
(** Generic definition *)

type type_def_info = type_param_info list g_type_info [@@deriving show]
(** Information about a type definition. *)

type ty_info = unit g_type_info [@@deriving show]
(** Information about a type. *)

type partial_type_info = type_param_info list option g_type_info
[@@deriving show]
(** Helper definition.

    Allows us to factorize code: [analyze_full_ty] is used both to analyze
    type definitions and types. *)

type type_infos = type_def_info TypeDefId.Map.t [@@deriving show]

let expl_info_init = { under_borrow = false; under_nested_borrows = false }

let initialize_g_type_info (param_infos : 'p) : 'p g_type_info =
  {
    contains_static = false;
    contains_borrow = false;
    contains_nested_borrows = false;
    param_infos;
  }

let initialize_type_def_info (def : type_def) : type_def_info =
  let param_info = { under_borrow = false; under_nested_borrows = false } in
  let param_infos = List.map (fun _ -> param_info) def.type_params in
  initialize_g_type_info param_infos

let type_def_info_to_partial_type_info (info : type_def_info) :
    partial_type_info =
  {
    contains_static = info.contains_static;
    contains_borrow = info.contains_borrow;
    contains_nested_borrows = info.contains_nested_borrows;
    param_infos = Some info.param_infos;
  }

let partial_type_info_to_type_def_info (info : partial_type_info) :
    type_def_info =
  {
    contains_static = info.contains_static;
    contains_borrow = info.contains_borrow;
    contains_nested_borrows = info.contains_nested_borrows;
    param_infos = Option.get info.param_infos;
  }

let partial_type_info_to_ty_info (info : partial_type_info) : ty_info =
  {
    contains_static = info.contains_static;
    contains_borrow = info.contains_borrow;
    contains_nested_borrows = info.contains_nested_borrows;
    param_infos = ();
  }

let analyze_full_ty (updated : bool ref) (infos : type_infos)
    (ty_info : partial_type_info) (ty : 'r gr_ty) : partial_type_info =
  (* Small utility *)
  let check_update_bool (original : bool) (nv : bool) : bool =
    if nv && not original then (
      updated := true;
      nv)
    else original
  in

  let update_ty_info_from_expl_info (ty_info : partial_type_info)
      (expl_info : expl_info) : partial_type_info =
    (* Set `contains_borrow` *)
    let contains_borrow =
      check_update_bool ty_info.contains_borrow expl_info.under_borrow
    in
    (* Set `contains_nested_borrows` *)
    let contains_nested_borrows =
      check_update_bool ty_info.contains_nested_borrows
        expl_info.under_nested_borrows
    in
    (* Update ty_info *)
    { ty_info with contains_borrow; contains_nested_borrows }
  in

  (* The recursive function which explores the type *)
  let rec analyze (expl_info : expl_info) (ty_info : partial_type_info)
      (ty : 'r gr_ty) : partial_type_info =
    match ty with
    | Bool | Char | Never | Integer _ | Str -> ty_info
    | TypeVar var_id -> (
        (* Update the information for the proper parameter, if necessary *)
        match ty_info.param_infos with
        | None -> ty_info
        | Some param_infos ->
            let param_info = TypeVarId.nth param_infos var_id in
            (* Set `under_borrow` *)
            let under_borrow =
              check_update_bool param_info.under_borrow expl_info.under_borrow
            in
            (* Set `under_nested_borrows` *)
            let under_nested_borrows =
              check_update_bool param_info.under_nested_borrows
                expl_info.under_nested_borrows
            in
            (* Update param_info *)
            let param_info = { under_borrow; under_nested_borrows } in
            let param_infos =
              TypeVarId.update_nth param_infos var_id param_info
            in
            let param_infos = Some param_infos in
            { ty_info with param_infos })
    | Array ty | Slice ty ->
        (* Just dive in *)
        analyze expl_info ty_info ty
    | Ref (r, rty, _) ->
        (* Update the exploration info *)
        let expl_info =
          { under_borrow = true; under_nested_borrows = expl_info.under_borrow }
        in
        (* Set `contains_static` *)
        let contains_static =
          check_update_bool ty_info.contains_static (r = Static)
        in
        let ty_info = { ty_info with contains_static } in
        (* Update the type info *)
        let ty_info = update_ty_info_from_expl_info ty_info expl_info in
        (* Continue exploring *)
        analyze expl_info ty_info rty
    | Adt ((Tuple | Assumed Box), _, tys) ->
        (* Nothing to update: just explore the type parameters *)
        List.fold_left
          (fun ty_info ty -> analyze expl_info ty_info ty)
          ty_info tys
    | Adt (AdtId adt_id, regions, tys) ->
        (* Lookup the information for this type definition *)
        let adt_info = TypeDefId.Map.find adt_id infos in
        (* Check if 'static appears *)
        let ty_info =
          List.fold_left
            (fun ty_info r ->
              {
                ty_info with
                contains_static =
                  check_update_bool ty_info.contains_static (r = Static);
              })
            ty_info regions
        in
        (* For every instantiated type parameter: update the exploration info
         * then explore the type *)
        let params_tys = List.combine adt_info.param_infos tys in
        let ty_info =
          List.fold_left
            (fun ty_info (param_info, ty) ->
              (* Update the exploration info *)
              let expl_info =
                {
                  under_borrow =
                    expl_info.under_borrow || param_info.under_borrow;
                  under_nested_borrows =
                    expl_info.under_nested_borrows
                    || param_info.under_nested_borrows;
                }
              in
              (* Propagate the updates to the ty info *)
              let ty_info = update_ty_info_from_expl_info ty_info expl_info in
              (* Continue exploring *)
              analyze expl_info ty_info ty)
            ty_info params_tys
        in
        (* Return *)
        ty_info
  in
  (* Explore *)
  analyze expl_info_init ty_info ty

let analyze_type_def (updated : bool ref) (infos : type_infos) (def : type_def)
    : type_infos =
  (* Retrieve all the types of all the fields of all the variants *)
  let fields_tys : sty list =
    match def.kind with
    | Struct fields -> List.map (fun f -> f.field_ty) fields
    | Enum variants ->
        List.concat
          (List.map (fun v -> List.map (fun f -> f.field_ty) v.fields) variants)
  in
  (* Explore the types and accumulate information *)
  let type_def_info = TypeDefId.Map.find def.def_id infos in
  let type_def_info = type_def_info_to_partial_type_info type_def_info in
  let type_def_info =
    List.fold_left
      (fun type_def_info ty -> analyze_full_ty updated infos type_def_info ty)
      type_def_info fields_tys
  in
  let type_def_info = partial_type_info_to_type_def_info type_def_info in
  (* Update the information for the type definition we explored *)
  let infos = TypeDefId.Map.add def.def_id type_def_info infos in
  (* Return *)
  infos

let analyze_type_declaration_group (type_defs : type_def TypeDefId.Map.t)
    (infos : type_infos) (decl : type_declaration_group) : type_infos =
  (* Collect the identifiers used in the declaration group *)
  let ids = match decl with NonRec id -> [ id ] | Rec ids -> ids in
  (* Retrieve the type definitions *)
  let decl_defs = List.map (fun id -> TypeDefId.Map.find id type_defs) ids in
  (* Initialize the type information for the current definitions *)
  let infos =
    List.fold_left
      (fun infos def ->
        TypeDefId.Map.add def.def_id (initialize_type_def_info def) infos)
      infos decl_defs
  in
  (* Analyze the types - this function simply computes a fixed-point *)
  let updated : bool ref = ref false in
  let rec analyze (infos : type_infos) : type_infos =
    let infos =
      List.fold_left
        (fun infos def -> analyze_type_def updated infos def)
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
let analyze_type_declarations (type_defs : type_def TypeDefId.Map.t)
    (decls : type_declaration_group list) : type_infos =
  List.fold_left
    (fun infos decl -> analyze_type_declaration_group type_defs infos decl)
    TypeDefId.Map.empty decls

(** Analyze a type to check whether it contains borrows, etc., provided
    we have already analyzed the type definitions in the context.
 *)
let analyze_ty (infos : type_infos) (ty : 'r gr_ty) : ty_info =
  (* We don't use `updated` but need to give it as parameter *)
  let updated = ref false in
  let ty_info = initialize_g_type_info None in
  let ty_info = analyze_full_ty updated infos ty_info ty in
  (* Convert the ty_info *)
  partial_type_info_to_ty_info ty_info
