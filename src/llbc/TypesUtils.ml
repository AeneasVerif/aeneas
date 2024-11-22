open Types
open Utils
include Charon.TypesUtils

(** Retuns true if the type contains borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!type:Types.ty},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_borrows (span : Meta.span option) (infos : TypesAnalysis.type_infos)
    (ty : ty) : bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_borrow

(** Checks that a type is copyable.
  *
  * This used to recursively traverse the type to ensure all its fields were
  * `Copy`. Instead we trust rustc's typechecking like we do for other marker
  * traits.
  *)
let ty_is_copyable (_ty : ty) : bool = true

let ty_has_adt_with_borrows span (infos : TypesAnalysis.type_infos) (ty : ty) :
    bool =
  let visitor =
    object
      inherit [_] iter_ty as super

      method! visit_ty env ty =
        match ty with
        | TAdt (type_id, _) when type_id <> TTuple ->
            let info = TypesAnalysis.analyze_ty span infos ty in
            if info.TypesAnalysis.contains_borrow then raise Found
            else super#visit_ty env ty
        | _ -> super#visit_ty env ty
    end
  in
  try
    visitor#visit_ty () ty;
    false
  with Found -> true

(** Retuns true if the type contains nested borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!type:Types.ty},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_nested_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (ty : ty) : bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_nested_borrows

(** Retuns true if the type decl contains nested borrows. *)
let type_decl_has_nested_borrows (span : Meta.span option)
    (infos : TypesAnalysis.type_infos) (type_decl : type_decl) : bool =
  let generics =
    Substitute.generic_args_of_params_erase_regions span type_decl.generics
  in
  let ty = TAdt (TAdtId type_decl.def_id, generics) in
  ty_has_nested_borrows span infos ty

(** Retuns true if the type contains a borrow under a mutable borrow *)
let ty_has_borrow_under_mut span (infos : TypesAnalysis.type_infos) (ty : ty) :
    bool =
  let info = TypesAnalysis.analyze_ty span infos ty in
  info.TypesAnalysis.contains_borrow_under_mut

(** Check if a {!type:Charon.Types.ty} contains a mutable borrow which uses a
    region from a given set. *)
let ty_has_mut_borrow_for_region_in_pred (infos : TypesAnalysis.type_infos)
    (pred : region -> bool) (ty : ty) : bool =
  let obj =
    object
      inherit [_] iter_ty as super

      method! visit_TRef env r ty rkind =
        begin
          match rkind with
          | RMut -> if pred r then raise Found
          | RShared -> ()
        end;
        super#visit_TRef env r ty rkind

      method! visit_TAdt env type_id generics =
        (* Lookup the information for this ADT *)
        begin
          match type_id with
          | TTuple | TBuiltin (TBox | TArray | TSlice | TStr) -> ()
          | TAdtId adt_id ->
              let info = TypeDeclId.Map.find adt_id infos in
              RegionVarId.iteri
                (fun adt_rid r ->
                  if RegionVarId.Set.mem adt_rid info.mut_regions && pred r then
                    raise Found
                  else ())
                generics.regions
        end;
        super#visit_TAdt env type_id generics
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Small helper *)
let raise_if_not_rty_visitor =
  object
    inherit [_] iter_ty

    method! visit_region _ r =
      match r with
      | RBVar _ | RErased -> raise Found
      | RStatic | RFVar _ -> ()
  end

(** Return [true] if the type is a region type (i.e., it doesn't contain erased
    regions), and only contains free regions) *)
let ty_is_rty (ty : ty) : bool =
  try
    raise_if_not_rty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Small helper *)
let raise_if_not_erased_ty_visitor =
  object
    inherit [_] iter_ty

    method! visit_region _ r =
      match r with
      | RStatic | RBVar _ | RFVar _ -> raise Found
      | RErased -> ()
  end

(** Return [true] if the type is a region type (i.e., it doesn't contain erased regions) *)
let ty_is_ety (ty : ty) : bool =
  try
    raise_if_not_erased_ty_visitor#visit_ty () ty;
    true
  with Found -> false

let generic_args_only_erased_regions (x : generic_args) : bool =
  try
    raise_if_not_erased_ty_visitor#visit_generic_args () x;
    true
  with Found -> false

(** Small helper *)
let raise_if_region_ty_visitor =
  object
    inherit [_] iter_ty
    method! visit_region _ _ = raise Found
  end

(** Return [true] if the type doesn't contain regions (including erased regions) *)
let ty_no_regions (ty : ty) : bool =
  try
    raise_if_region_ty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Return [true] if the trait ref doesn't contain regions (including erased regions) *)
let trait_ref_no_regions (x : trait_ref) : bool =
  try
    raise_if_region_ty_visitor#visit_trait_ref () x;
    true
  with Found -> false

(** Return [true] if the trait instance id doesn't contain regions (including erased regions) *)
let trait_instance_id_no_regions (x : trait_instance_id) : bool =
  try
    raise_if_region_ty_visitor#visit_trait_instance_id () x;
    true
  with Found -> false

(** Return [true] if the generic args don't contain regions (including erased regions) *)
let generic_args_no_regions (x : generic_args) : bool =
  try
    raise_if_region_ty_visitor#visit_generic_args () x;
    true
  with Found -> false

(** Return [true] if the trait type constraint doesn't contain regions (including erased regions) *)
let trait_type_constraint_no_regions (x : trait_type_constraint) : bool =
  try
    let { trait_ref; type_name = _; ty } = x in
    raise_if_region_ty_visitor#visit_trait_ref () trait_ref;
    raise_if_region_ty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Return true if a type declaration should be extracted as a tuple, because
    it is a non-recursive structure with unnamed fields. *)
let type_decl_from_decl_id_is_tuple_struct (ctx : TypesAnalysis.type_infos)
    (id : TypeDeclId.id) : bool =
  let info = TypeDeclId.Map.find id ctx in
  info.is_tuple_struct

(** Return true if a type declaration should be extracted as a tuple, because
    it is a non-recursive structure with unnamed fields. *)
let type_decl_from_type_id_is_tuple_struct (ctx : TypesAnalysis.type_infos)
    (id : type_id) : bool =
  match id with
  | TTuple -> true
  | TAdtId id ->
      let info = TypeDeclId.Map.find id ctx in
      info.is_tuple_struct
  | TBuiltin _ -> false
