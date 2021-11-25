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
  | Bool | Char | Never | Integer _ | Str -> (* no change *) ty
  | Array aty -> Array (subst aty)
  | Slice sty -> Slice (subst sty)
  | Ref (r, ref_ty, ref_kind) -> Ref (rsubst r, subst ref_ty, ref_kind)
  | Assumed (aty, regions, tys) ->
      Assumed (aty, List.map rsubst regions, List.map subst tys)

(*(** Works *)
let ty_subst2 (rsubst : 'r1 -> T.erased_region)
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty) (ty : 'r1 T.ty) :
    T.erased_region T.ty =
  ty_subst rsubst tsubst ty

let ty_subst3 (rsubst : int -> T.erased_region)
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty) (ty : int T.ty) :
    T.erased_region T.ty =
  ty_subst rsubst tsubst ty*)

(*(** Doesn't work *)
let ty_subst3 (rsubst : T.RegionVarId.id T.region -> T.erased_region)
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty)
    (ty : T.RegionVarId.id T.region T.ty) : T.erased_region T.ty =
  ty_subst2 rsubst tsubst ty*)

(*
(** Erase the regions in a type and substitute the type variables *)
let erase_regions_substitute_types
    (rsubst : T.RegionVarId.id T.region -> T.erased_region)
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty)
    (t : T.RegionVarId.id T.region T.ty) =
  ty_subst rsubst tsubst t*)

(*let erase_regions_substitute_types
    (rsubst : T.RegionVarId.id T.region -> T.erased_region)
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty)
    (ty : T.RegionVarId.id T.region T.ty) : T.erased_region T.ty =
  ty_subst rsubst tsubst ty*)

(*let erase_regions_substitute_types
    (tsubst : T.TypeVarId.id -> T.erased_region T.ty)
    (ty : T.RegionVarId.id T.region T.ty) : T.erased_region T.ty =
  let rsubst (r : T.RegionVarId.id T.region) : T.erased_region = T.Erased in
  ty_subst rsubst tsubst ty*)

(*let erase_regions_substitute_types (tsubst : T.TypeVarId.id -> T.ety)
    (ty : T.rty) : T.ety =
  let rsubst (r : T.RegionVarId.id T.region) : T.erased_region = T.Erased in
  ty_subst rsubst tsubst ty*)

(*(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let get_adt_instantiated_field_type
      (def : T.type_def)
      (opt_variant_id : T.VariantId.id option) (types : T.ety list) :
      ety list =*)
