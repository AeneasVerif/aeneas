open Types
include Charon.TypesUtils
module TA = TypesAnalysis

(** Retuns true if the type contains borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!Types.ety},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_borrows (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow

(** Retuns true if the type contains nested borrows.

    Note that we can't simply explore the type and look for regions: sometimes
    we erase the lists of regions (by replacing them with [[]] when using {!Types.ety},
    and when a type uses 'static this region doesn't appear in the region parameters.
 *)
let ty_has_nested_borrows (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_nested_borrows

(** Retuns true if the type contains a borrow under a mutable borrow *)
let ty_has_borrow_under_mut (infos : TA.type_infos) (ty : 'r ty) : bool =
  let info = TA.analyze_ty infos ty in
  info.TA.contains_borrow_under_mut
