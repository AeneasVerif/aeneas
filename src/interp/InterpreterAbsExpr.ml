open Types
open Values
open TypesUtils
open ValuesUtils
open Errors

let rec typed_avalue_to_abs_output_pat (span : Meta.span option)
    (av : typed_avalue) : abs_output_pat =
  match av.value with
  | AAdt adt -> adt_avalue_to_abs_output_pat span av.ty adt
  | ABottom ->
      (* The function shouldn't be called on bottom values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ALoan _ ->
      (* The function shouldn't be called on loan values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ABorrow b -> aborrow_content_to_abs_output_pat span b
  | ASymbolic (marker, proj) ->
      cassert_opt_span __FILE__ __LINE__ (marker = PNone) span "Unexpected";
      aproj_to_abs_output_pat span proj
  | AIgnored _ ->
      (* The empty output is a unit pattern *)
      abs_output_pat_unit

and adt_avalue_to_abs_output_pat (span : Meta.span option) (ty : ty)
    (av : adt_avalue) : abs_output_pat =
  let fields = List.map (typed_avalue_to_abs_output_pat span) av.field_values in
  let id, generics = ty_as_adt ty in
  OAdt ({ id; generics }, av.variant_id, fields)

and aborrow_content_to_abs_output_pat (span : Meta.span option)
    (bc : aborrow_content) : abs_output_pat =
  match bc with
  | AMutBorrow (marker, bid, child) ->
      sanity_check_opt_span __FILE__ __LINE__ (marker = PNone) span;
      sanity_check_opt_span __FILE__ __LINE__ (is_aignored child.value) span;
      OBorrow bid
  | ASharedBorrow _ | AProjSharedBorrow _ -> abs_output_pat_unit
  | AIgnoredMutBorrow (_, av) -> typed_avalue_to_abs_output_pat span av
  | AEndedMutBorrow _ | AEndedSharedBorrow | AEndedIgnoredMutBorrow _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

and aproj_to_abs_output_pat (span : Meta.span option) (proj : aproj) :
    abs_output_pat =
  match proj with
  | AProjBorrows (sv_id, proj_ty, children) ->
      sanity_check_opt_span __FILE__ __LINE__ (children = []) span;
      OSymbolic (sv_id, proj_ty)
  | AEmpty -> abs_output_pat_unit
  | AProjLoans _ | AEndedProjBorrows _ | AEndedProjLoans _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

let typed_avalue_to_abs_output (span : Meta.span option) (av : typed_avalue) :
    abs_output =
  mk_abs_output_no_marker (typed_avalue_to_abs_output_pat span av) av.ty

let rec typed_avalue_to_abs_expr (span : Meta.span option)
    (regions : region_id_set) (av : typed_avalue) : abs_expr =
  match av.value with
  | AAdt adt -> adt_avalue_to_abs_expr span regions av.ty adt
  | ABottom ->
      (* The function shouldn't be called on bottom values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ALoan _ ->
      (* The function shouldn't be called on loan values *)
      internal_error_opt_span __FILE__ __LINE__ span
  | ABorrow b -> aborrow_content_to_abs_expr span regions b
  | ASymbolic (marker, proj) ->
      cassert_opt_span __FILE__ __LINE__ (marker = PNone) span "Unexpected";
      aproj_to_abs_expr span regions proj
  | AIgnored _ ->
      (* The empty output is a unit pattern *)
      abs_expr_unit

and adt_avalue_to_abs_expr (span : Meta.span option) (regions : region_id_set)
    (ty : ty) (av : adt_avalue) : abs_expr =
  let fields =
    List.map (typed_avalue_to_abs_expr span regions) av.field_values
  in
  let id, generics = ty_as_adt ty in
  EAdt ({ id; generics }, av.variant_id, fields)

and aborrow_content_to_abs_expr (span : Meta.span option)
    (regions : region_id_set) (bc : aborrow_content) : abs_expr =
  match bc with
  | AMutBorrow (marker, bid, child) ->
      sanity_check_opt_span __FILE__ __LINE__ (marker = PNone) span;
      sanity_check_opt_span __FILE__ __LINE__ (is_aignored child.value) span;
      EBorrow bid
  | ASharedBorrow _ | AProjSharedBorrow _ -> abs_expr_unit
  | AIgnoredMutBorrow (_, av) -> typed_avalue_to_abs_expr span regions av
  | AEndedMutBorrow _ | AEndedSharedBorrow | AEndedIgnoredMutBorrow _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span

and aproj_to_abs_expr (span : Meta.span option) (regions : region_id_set)
    (proj : aproj) : abs_expr =
  match proj with
  | AProjBorrows (sv_id, proj_ty, children) ->
      sanity_check_opt_span __FILE__ __LINE__ (children = []) span;
      ESymbolic (sv_id, proj_ty, regions)
  | AEmpty -> abs_expr_unit
  | AProjLoans _ | AEndedProjBorrows _ | AEndedProjLoans _ ->
      (* The function shouldn't be called on this kind of values *)
      internal_error_opt_span __FILE__ __LINE__ span
