open Types
open Utils
include Charon.TypesUtils
module TA = TypesAnalysis

(** Retuns true if the type contains borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!Types.ety},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_borrows (infos : TA.type_infos) (ty : ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow

(** Retuns true if the type contains nested borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!Types.ety},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_nested_borrows (infos : TA.type_infos) (ty : ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_nested_borrows

(** Retuns true if the type contains a borrow under a mutable borrow *)
let ty_has_borrow_under_mut (infos : TA.type_infos) (ty : ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow_under_mut

(** Small helper *)
let raise_if_erased_ty_visitor =
  object
    inherit [_] iter_ty
    method! visit_RErased _ = raise Found
  end

(** Return [true] if the type is a region type (i.e., it doesn't contain erased regions) *)
let ty_is_rty (ty : ty) : bool =
  try
    raise_if_erased_ty_visitor#visit_ty () ty;
    true
  with Found -> false

(** Small helper *)
let raise_if_not_erased_ty_visitor =
  object
    inherit [_] iter_ty
    method! visit_RStatic _ = raise Found
    method! visit_RVar _ = raise Found
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
    let { trait_ref; generics; type_name = _; ty } = x in
    raise_if_region_ty_visitor#visit_trait_ref () trait_ref;
    raise_if_region_ty_visitor#visit_generic_args () generics;
    raise_if_region_ty_visitor#visit_ty () ty;
    true
  with Found -> false
