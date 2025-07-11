open Types
open Values
open TypesUtils
open ValuesUtils
open Errors

let rec typed_avalue_to_abs_toutput (span : Meta.span option)
    (regions : region_id_set) (av : typed_avalue) : abs_toutput =
  let ty = normalize_proj_ty regions av.ty in
  match av.value with
  | AAdt adt -> adt_avalue_to_abs_toutput span regions ty adt
  | ABottom ->
      (* The function shouldn't be called on bottom values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ALoan _ ->
      (* The function shouldn't be called on loan values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ABorrow b -> aborrow_content_to_abs_toutput span regions ty b
  | ASymbolic (marker, proj) ->
      cassert_opt_span __FILE__ __LINE__ (marker = PNone) span "Unexpected";
      aproj_to_abs_toutput span regions proj
  | AIgnored _ ->
      (* The empty output is a unit *)
      abs_toutput_unit

and adt_avalue_to_abs_toutput (span : Meta.span option)
    (regions : region_id_set) (ty : ty) (av : adt_avalue) : abs_toutput =
  let fields =
    List.map (typed_avalue_to_abs_toutput span regions) av.field_values
  in
  let id, generics = ty_as_adt ty in
  let opat = OAdt (av.variant_id, fields) in
  let opat_ty = TAdt { id; generics } in
  { opat; opat_ty }

and aborrow_content_to_abs_toutput (span : Meta.span option)
    (regions : region_id_set) (ty : ty) (bc : aborrow_content) : abs_toutput =
  match bc with
  | AMutBorrow (marker, bid, child) ->
      sanity_check_opt_span __FILE__ __LINE__ (marker = PNone) span;
      sanity_check_opt_span __FILE__ __LINE__ (is_aignored child.value) span;
      let opat = OBorrow bid in
      let opat_ty = normalize_proj_ty regions ty in
      { opat; opat_ty }
  | ASharedBorrow _ | AProjSharedBorrow _ -> abs_toutput_unit
  | AIgnoredMutBorrow (_, av) -> typed_avalue_to_abs_toutput span regions av
  | AEndedMutBorrow _ | AEndedSharedBorrow | AEndedIgnoredMutBorrow _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

and aproj_to_abs_toutput (span : Meta.span option) (regions : region_id_set)
    (proj : aproj) : abs_toutput =
  match proj with
  | AProjBorrows (sv_id, proj_ty, children) ->
      sanity_check_opt_span __FILE__ __LINE__ (children = []) span;
      let opat = OSymbolic sv_id in
      let opat_ty = normalize_proj_ty regions proj_ty in
      { opat; opat_ty }
  | AEmpty -> abs_toutput_unit
  | AProjLoans _ | AEndedProjBorrows _ | AEndedProjLoans _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

let rec typed_avalue_to_abs_texpr (span : Meta.span option)
    (regions : region_id_set) (av : typed_avalue) : abs_texpr =
  let ty = normalize_proj_ty regions av.ty in
  let e =
    match av.value with
    | AAdt adt -> adt_avalue_to_abs_expr span regions adt
    | ABottom ->
        (* The function shouldn't be called on bottom values *)
        internal_error_opt_span __FILE__ __LINE__ span
    | ALoan l -> aloan_content_to_abs_expr span regions l
    | ABorrow _ ->
        (* The function shouldn't be called on borrow values *)
        internal_error_opt_span __FILE__ __LINE__ span
    | ASymbolic (marker, proj) ->
        cassert_opt_span __FILE__ __LINE__ (marker = PNone) span "Unexpected";
        aproj_to_abs_expr span proj
    | AIgnored _ ->
        (* The empty output is a unit pattern *)
        abs_expr_unit
  in
  { e; ty }

and adt_avalue_to_abs_expr (span : Meta.span option) (regions : region_id_set)
    (av : adt_avalue) : abs_expr =
  let fields =
    List.map (typed_avalue_to_abs_texpr span regions) av.field_values
  in
  EAdt (av.variant_id, fields)

and aloan_content_to_abs_expr (span : Meta.span option)
    (regions : region_id_set) (lc : aloan_content) : abs_expr =
  match lc with
  | AMutLoan (marker, bid, child) ->
      sanity_check_opt_span __FILE__ __LINE__ (marker = PNone) span;
      sanity_check_opt_span __FILE__ __LINE__ (is_aignored child.value) span;
      ELoan bid
  | ASharedLoan _ | AIgnoredSharedLoan _ -> abs_expr_unit
  | AIgnoredMutLoan (_, av) -> (typed_avalue_to_abs_texpr span regions av).e
  | AEndedMutLoan _ | AEndedSharedLoan _ | AEndedIgnoredMutLoan _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

and aproj_to_abs_expr (span : Meta.span option) (proj : aproj) : abs_expr =
  match proj with
  | AProjLoans (sv_id, _, children) ->
      sanity_check_opt_span __FILE__ __LINE__ (children = []) span;
      ESymbolic sv_id
  | AEmpty -> abs_expr_unit
  | AProjBorrows _ | AEndedProjBorrows _ | AEndedProjLoans _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

let typed_avalues_to_abs_texpr (span : Meta.span option)
    (regions : region_id_set) (avl : typed_avalue list) : abs_texpr =
  let exprs = List.map (typed_avalue_to_abs_texpr span regions) avl in
  let generics =
    {
      regions = [];
      types = List.map (fun (av : typed_avalue) -> av.ty) avl;
      const_generics = [];
      trait_refs = [];
    }
  in
  { e = EAdt (None, exprs); ty = TAdt { id = TTuple; generics } }
