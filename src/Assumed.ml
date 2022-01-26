module T = Types
(** This module contains various utilities for the assumed functions.

    Note that `Box::free` is peculiar: we don't really handle it as a function,
    because it is legal to free a box whose boxed value is `⊥` (it often
    happens that we move a value out of a box before freeing this box).
    Semantically speaking, we thus handle `Box::free` as a value drop and
    not as a function call, and thus never need its signature.
 *)

module A = CfimAst
open TypesUtils

(** `T -> Box<T>` *)
let box_new_sig : A.fun_sig =
  let tvar_id_0 = T.TypeVarId.of_int 0 in
  let tvar_0 = T.TypeVar tvar_id_0 in
  {
    region_params = [];
    num_early_bound_regions = 0;
    regions_hierarchy = [];
    type_params = [ { index = tvar_id_0; name = "T" } ];
    inputs = [ tvar_0 (* T *) ];
    output = mk_box_ty tvar_0 (* Box<T> *);
  }

(** Helper for `Box::deref_shared` and `Box::deref_mut`.
    Returns:
    `&'a (mut) Box<T> -> &'a (mut) T`
 *)
let box_deref_sig (is_mut : bool) : A.fun_sig =
  let rvar_id_0 = T.RegionVarId.of_int 0 in
  let rvar_0 = T.Var rvar_id_0 in
  let rg_id_0 = T.RegionGroupId.of_int 0 in
  let tvar_id_0 = T.TypeVarId.of_int 0 in
  let tvar_0 = T.TypeVar tvar_id_0 in
  let ref_kind = if is_mut then T.Mut else T.Shared in
  (* The signature fields *)
  let region_params = [ { T.index = rvar_id_0; name = Some "'a" } ] in
  let regions_hierarchy =
    [ { T.id = rg_id_0; regions = [ rvar_id_0 ]; parents = [] } ]
    (* <'a> *)
  in
  {
    region_params;
    num_early_bound_regions = 0;
    regions_hierarchy;
    type_params = [ { index = tvar_id_0; name = "T" } ] (* <T> *);
    inputs =
      [ mk_ref_ty rvar_0 (mk_box_ty tvar_0) ref_kind (* &'a (mut) Box<T> *) ];
    output = mk_ref_ty rvar_0 tvar_0 ref_kind (* &'a (mut) T *);
  }

(** `&'a Box<T> -> &'a T` *)
let box_deref_shared_sig = box_deref_sig false

(** `&'a mut Box<T> -> &'a mut T` *)
let box_deref_mut_sig = box_deref_sig true
