(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module V = Values

(** Substitute types variables and regions in a type *)
let rec ty_subst (rsubst : 'r1 -> 'r2) (tsubst : T.TypeVarId.id -> 'r2 T.ty)
    (ty : 'r1 T.ty) : 'r2 T.ty =
  let open T in
  let subst = ty_subst rsubst tsubst in
  (* helper *)
  match ty with
  | Adt (def_id, regions, tys) ->
      Adt (def_id, List.map rsubst regions, List.map subst tys)
  | Tuple tys -> Tuple (List.map subst tys)
  | Array aty -> Array (subst aty)
  | Slice sty -> Slice (subst sty)
  | Ref (r, ref_ty, ref_kind) -> Ref (rsubst r, subst ref_ty, ref_kind)
  | Assumed (aty, regions, tys) ->
      Assumed (aty, List.map rsubst regions, List.map subst tys)
      (* Below variants: we technically return the same value, but because
         one has type ['r1 ty] and the other has type ['r2 ty] we need to
         deconstruct then reconstruct *)
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str

(** Erase the regions in a type and substitute the type variables *)
let erase_regions_substitute_types (tsubst : T.TypeVarId.id -> T.ety)
    (ty : T.rty) : T.ety =
  let rsubst (r : T.RegionVarId.id T.region) : T.erased_region = T.Erased in
  ty_subst rsubst tsubst ty

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids *)
let make_type_subst (var_ids : T.TypeVarId.id list) (tys : 'r T.ty list) :
    T.TypeVarId.id -> 'r T.ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TypeVarId.Map.add k v mp)
      T.TypeVarId.Map.empty ls
  in
  fun id -> T.TypeVarId.Map.find id mp

(** Retrieve the list of fields for the given variant of a [type_def].

    Raises [Invalid_argument] if the arguments are incorrect.

    TODO: move
 *)
let type_def_get_fields (def : T.type_def)
    (opt_variant_id : T.VariantId.id option) : T.field T.FieldId.vector =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id ->
      (T.VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      raise
        (Invalid_argument
           "The variant id should be [Some] if and only if the definition is \
            an enumeration")

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_def_get_instantiated_field_type (def : T.type_def)
    (opt_variant_id : T.VariantId.id option) (types : T.ety list) :
    T.ety T.FieldId.vector =
  (*  let indices = List.mapi (fun i _ -> TypeVarId.of_int i) def.type_params in*)
  let ty_subst =
    make_type_subst
      (List.map
         (fun x -> x.T.tv_index)
         (T.TypeVarId.vector_to_list def.T.type_params))
      types
  in
  let fields = type_def_get_fields def opt_variant_id in
  T.FieldId.map
    (fun f -> erase_regions_substitute_types ty_subst f.T.field_ty)
    fields
