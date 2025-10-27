open Utils
open TypesUtils
open Types
open Values
include Charon.ValuesUtils

(** Utility exception *)
exception FoundSymbolicValue of symbolic_value

let mk_unit_value : tvalue =
  { value = VAdt { variant_id = None; fields = [] }; ty = mk_unit_ty }

let mk_bool_value (b : bool) : tvalue =
  { value = VLiteral (VBool b); ty = TLiteral TBool }

let mk_true : tvalue = mk_bool_value true
let mk_false : tvalue = mk_bool_value false

let mk_tvalue (span : Meta.span) (ty : ty) (value : value) : tvalue =
  [%sanity_check] span (ty_is_ety ty);
  { value; ty }

let mk_tavalue (span : Meta.span) (ty : ty) (value : avalue) : tavalue =
  [%sanity_check] span (ty_is_rty ty);
  { value; ty }

let mk_bottom (span : Meta.span) (ty : ty) : tvalue =
  [%sanity_check] span (ty_is_ety ty);
  { value = VBottom; ty }

let mk_ebottom (ty : ty) : tevalue = { value = EBottom; ty }

let mk_aignored (span : Meta.span) (ty : ty) (v : tvalue option) : tavalue =
  [%sanity_check] span (ty_is_rty ty);
  { value = AIgnored v; ty }

let mk_eignored (ty : ty) : tevalue = { value = EIgnored; ty }
let mk_epat_ignored (ty : ty) : tepat = { pat = PIgnored; ty }

let mk_evalue (env : env) (ty : ty) (v : tvalue) : tevalue =
  { value = EValue (env, v); ty }

let value_as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic v -> v
  | _ -> [%craise] span "Unexpected"

let tvalue_as_symbolic (span : Meta.span) (v : tvalue) : symbolic_value =
  value_as_symbolic span v.value

let mk_etuple (vl : tevalue list) : tevalue =
  let tys = List.map (fun (v : tevalue) -> v.ty) vl in
  let generics = mk_generic_args_from_types tys in
  {
    value = EAdt { variant_id = None; fields = vl };
    ty = TAdt { id = TTuple; generics };
  }

let mk_epat_tuple (vl : tepat list) : tepat =
  let tys = List.map (fun (v : tepat) -> v.ty) vl in
  let generics = mk_generic_args_from_types tys in
  { pat = PAdt (None, vl); ty = TAdt { id = TTuple; generics } }

let mk_simpl_etuple (vl : tevalue list) : tevalue =
  match vl with
  | [ v ] -> v
  | _ -> mk_etuple vl

(** Peel boxes as long as the value is of the form [Box<T>] *)
let rec unbox_tvalue (span : Meta.span) (v : tvalue) : tvalue =
  match (v.value, v.ty) with
  | VAdt av, TAdt { id = TBuiltin TBox; _ } -> (
      match av.fields with
      | [ bv ] -> unbox_tvalue span bv
      | _ -> [%internal_error] span)
  | _ -> v

(** Create a typed value from a symbolic value. *)
let mk_tvalue_from_symbolic_value (svalue : symbolic_value) : tvalue =
  let av = VSymbolic svalue in
  let av : tvalue =
    { value = av; ty = Substitute.erase_regions svalue.sv_ty }
  in
  av

(** Box a value *)
let mk_box_value (span : Meta.span) (v : tvalue) : tvalue =
  let box_ty = mk_box_ty v.ty in
  let box_v = VAdt { variant_id = None; fields = [ v ] } in
  mk_tvalue span box_ty box_v

let is_bottom (v : value) : bool =
  match v with
  | VBottom -> true
  | _ -> false

let is_aignored (v : avalue) : bool =
  match v with
  | AIgnored _ -> true
  | _ -> false

let is_eignored (v : evalue) : bool =
  match v with
  | EIgnored -> true
  | _ -> false

let is_symbolic (v : value) : bool =
  match v with
  | VSymbolic _ -> true
  | _ -> false

let as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic s -> s
  | _ -> [%craise] span "Unexpected"

let as_mut_borrow (span : Meta.span) (v : tvalue) : BorrowId.id * tvalue =
  match v.value with
  | VBorrow (VMutBorrow (bid, bv)) -> (bid, bv)
  | _ -> [%craise] span "Unexpected"

let is_unit (v : tvalue) : bool =
  ty_is_unit v.ty
  &&
  match v.value with
  | VAdt av -> av.variant_id = None && av.fields = []
  | _ -> false

let mk_aproj_borrows (pm : proj_marker) (sv_id : symbolic_value_id)
    (proj_ty : ty) : tavalue =
  {
    value =
      ASymbolic (pm, AProjBorrows { proj = { sv_id; proj_ty }; loans = [] });
    ty = proj_ty;
  }

let mk_aproj_loans (pm : proj_marker) (sv_id : symbolic_value_id) (proj_ty : ty)
    : tavalue =
  {
    value =
      ASymbolic
        ( pm,
          AProjLoans { proj = { sv_id; proj_ty }; consumed = []; borrows = [] }
        );
    ty = proj_ty;
  }

let mk_eproj_borrows (pm : proj_marker) (sv_id : symbolic_value_id)
    (proj_ty : ty) : tevalue =
  {
    value =
      ESymbolic (pm, EProjBorrows { proj = { sv_id; proj_ty }; loans = [] });
    ty = proj_ty;
  }

let mk_eproj_loans (pm : proj_marker) (sv_id : symbolic_value_id) (proj_ty : ty)
    : tevalue =
  {
    value =
      ESymbolic
        ( pm,
          EProjLoans { proj = { sv_id; proj_ty }; consumed = []; borrows = [] }
        );
    ty = proj_ty;
  }

let proj_markers_intersect (pm0 : proj_marker) (pm1 : proj_marker) : bool =
  match (pm0, pm1) with
  | PNone, _ | _, PNone | PLeft, PLeft | PRight, PRight -> true
  | _ -> false

let symbolic_proj_to_esymbolic_proj (p : symbolic_proj) : esymbolic_proj =
  let { sv_id; proj_ty } : symbolic_proj = p in
  { sv_id; proj_ty }

(** Check if a value contains a *concrete* borrow (i.e., a [Borrow] value - we
    don't check if there are borrows hidden in symbolic values). *)
let concrete_borrows_in_value (v : tvalue) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

(** Check if a value contains reserved mutable borrows (which are necessarily
    *concrete*: a symbolic value can't "hide" reserved borrows). *)
let reserved_in_value (v : tvalue) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_VReservedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

(** Check if a value contains a loan (which is necessarily *concrete*: symbolic
    values can't "hide" loans). *)
let concrete_loans_in_value (v : tvalue) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

(** Check if a value contains concrete borrows or loans *)
let concrete_borrows_loans_in_value (v : value) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _env _ = raise Found
      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value contains outer loans (i.e., loans which are not in borrwed
    values. *)
let outer_loans_in_value (v : tvalue) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _env _ = raise Found

      method! visit_borrow_content _ _ =
        (* Do nothing so as *not to dive* in borrowed values *) ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

let symbolic_value_is_greedily_expandable (span : Meta.span option)
    (type_decls : type_decl TypeDeclId.Map.t)
    (type_infos : TypesAnalysis.type_infos) (sv : symbolic_value) : bool =
  if ty_has_borrows span type_infos sv.sv_ty then
    (* Ignore arrays and slices, as we can't expand them *)
    match sv.sv_ty with
    | TAdt { id = TBuiltin (TArray | TSlice); _ } -> false
    | TAdt { id = TAdtId id; _ } ->
        (* Lookup the type of the ADT to check if we can expand it *)
        let def = TypeDeclId.Map.find id type_decls in
        begin
          match def.kind with
          | Struct _ | Enum ([] | [ _ ]) ->
              (* Structure or enumeration with <= 1 variant *)
              true
          | Enum (_ :: _) | Alias _ | Opaque | TDeclError _ | Union _ ->
              (* Enumeration with > 1 variants *)
              false
        end
    | _ -> true
  else false

let find_first_expandable_sv_with_borrows (span : Meta.span option)
    (type_decls : type_decl TypeDeclId.Map.t)
    (type_infos : TypesAnalysis.type_infos) (v : tvalue) : symbolic_value option
    =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_tvalue

      method! visit_VSymbolic _ sv =
        if symbolic_value_is_greedily_expandable span type_decls type_infos sv
        then raise (FoundSymbolicValue sv)
        else ()
    end
  in
  (* Small helper *)
  try
    obj#visit_tvalue () v;
    None
  with FoundSymbolicValue sv -> Some sv

(** Strip the outer shared loans in a value. Ex.:
    [shared_loan {l0, l1} (3 : u32, shared_loan {l2} (4 : u32))] ~~>
    [(3 : u32, shared_loan {l2} (4 : u32))] *)
let rec value_strip_shared_loans (v : tvalue) : tvalue =
  match v.value with
  | VLoan (VSharedLoan (_, v')) -> value_strip_shared_loans v'
  | _ -> v

(** Check if a symbolic value has borrows *)
let symbolic_value_has_borrows span (infos : TypesAnalysis.type_infos)
    (sv : symbolic_value) : bool =
  ty_has_borrows span infos sv.sv_ty

(** Check if a value has borrows in **a general sense**.

    It checks if:
    - there are concrete borrows
    - there are symbolic values which may contain borrows *)
let value_has_borrows span (infos : TypesAnalysis.type_infos) (v : value) : bool
    =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if symbolic_value_has_borrows span infos sv then raise Found else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

let value_has_non_ended_borrows_or_loans (ended_regions : RegionId.Set.t)
    (v : value) : bool =
  let ty_visitor =
    object
      inherit [_] iter_ty

      method! visit_RVar _ region =
        match region with
        | Free rid ->
            if not (RegionId.Set.mem rid ended_regions) then raise Found else ()
        | Bound _ -> ()
    end
  in
  let value_visitor =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _ _ = raise Found
      method! visit_loan_content _ _ = raise Found
      method! visit_symbolic_value _ sv = ty_visitor#visit_ty () sv.sv_ty
    end
  in
  (* We use exceptions *)
  try
    value_visitor#visit_value () v;
    false
  with Found -> true

(** Check if a value has loans.

    Note that loans are necessarily concrete (there can't be loans hidden inside
    symbolic values). *)
let value_has_loans (v : value) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value contains outer loans.

    Note that loans are necessarily concrete (there can't be loans hidden inside
    symbolic values). *)
let value_has_outer_loans (v : value) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _env _ = raise Found

      method! visit_borrow_content _ _ =
        (* Don't dive inside of borrows *)
        ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value contains mutable loans.

    Note that loans are necessarily concrete (there can't be loans hidden inside
    symbolic values). *)
let value_has_mutable_loans (v : value) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_VMutLoan _ _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Check if a value has loans or borrows in **a general sense**.

    It checks if:
    - there are concrete loans or concrete borrows
    - there are symbolic values which may contain borrows (symbolic values can't
      contain loans). *)
let value_has_loans_or_borrows span (infos : TypesAnalysis.type_infos)
    (v : value) : bool =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _env _ = raise Found
      method! visit_loan_content _env _ = raise Found

      method! visit_symbolic_value _ sv =
        if ty_has_borrow_under_mut span infos sv.sv_ty then raise Found else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_value () v;
    false
  with Found -> true

(** Remove the shared loans in a value *)
let value_remove_shared_loans (v : tvalue) : tvalue =
  let visitor =
    object (self : 'self)
      inherit [_] map_tvalue as super

      method! visit_tvalue env v =
        match v.value with
        | VLoan (VSharedLoan (_, sv)) -> self#visit_tvalue env sv
        | _ -> super#visit_tvalue env v
    end
  in
  visitor#visit_tvalue () v

(** An iter visitor for abstraction expressions where the environment is the
    current scope/level (we increment it whenever we enter a binder) *)
class ['self] scoped_iter_tevalue =
  object (self : 'self)
    inherit [_] iter_tavalue

    method! visit_ELet scope _ pat bound next =
      let scope' = scope + 1 in
      self#visit_tepat scope pat;
      self#visit_tevalue scope bound;
      self#visit_tevalue scope' next
  end

(** A map visitor for expressions where the environment is the current
    scope/level (we increment it whenever we enter a binder) *)
class ['self] scoped_map_tevalue =
  object (self : 'self)
    inherit [_] map_tavalue

    method! visit_ELet scope rid_set pat bound next =
      let scope' = scope + 1 in
      let pat = self#visit_tepat scope pat in
      let bound = self#visit_tevalue scope bound in
      let next = self#visit_tevalue scope' next in
      ELet (rid_set, pat, bound, next)
  end

(** Open a typed expression pattern by introducing fresh free variables for the
    bound variables. *)
let open_tepat (span : Meta.span) (fresh_fvar_id : unit -> abs_fvar_id)
    (pat : tepat) : tepat =
  let visitor =
    object
      inherit [_] map_tavalue
      method! visit_POpen _ _ = [%internal_error] span
      method! visit_PBound _ = POpen (fresh_fvar_id ())
    end
  in
  visitor#visit_tepat () pat

(** Close a typed expression pattern by replacing its free variables with bound
    variables. We also return the map from free variable ids to bound variables.
*)
let close_tepat (span : Meta.span) (pat : tepat) :
    AbsBVarId.id AbsFVarId.Map.t * tepat =
  let _, fresh_bvar_id = AbsBVarId.fresh_stateful_generator () in
  let map = ref AbsFVarId.Map.empty in
  let visitor =
    object
      inherit [_] map_tavalue

      method! visit_POpen _ id =
        let bid = fresh_bvar_id () in
        map := AbsFVarId.Map.add id bid !map;
        PBound

      method! visit_PBound _ = [%internal_error] span
    end
  in
  let pat = visitor#visit_tepat () pat in
  (!map, pat)

(** Open a binder in an abstraction expression.

    Return the opened binder (where the bound variables have been replaced with
    fresh free variables). *)
let open_binder (span : Meta.span) (pat : tepat) (e : tevalue) : tepat * tevalue
    =
  (* We start by introducing the free variables in the pattern *)
  (* The map from bound var ids to freshly introduced fvar ids *)
  let m = ref AbsBVarId.Map.empty in
  (* We need to count the bound vars *)
  let _, fresh_abs_bvar_id = AbsBVarId.fresh_stateful_generator () in
  let fresh_fvar_id _ =
    let bid = fresh_abs_bvar_id () in
    let fid = fresh_abs_fvar_id () in
    m := AbsBVarId.Map.add bid fid !m;
    fid
  in
  let pat = open_tepat span fresh_fvar_id pat in
  (* We can now open the expression *)
  let visitor =
    object
      inherit [_] scoped_map_tevalue

      method! visit_EBVar scope (var : abs_bvar) =
        if var.scope = scope then EFVar (AbsBVarId.Map.find var.bvar_id !m)
        else (
          [%sanity_check] span (var.scope < scope);
          EBVar var)
    end
  in
  let e = visitor#visit_tevalue 0 e in
  (pat, e)

(** Helper visitor to close a binder.

    Return the closed binder (where the free variables have been replaced with
    bound variables). *)
let close_binder_visitor (span : Meta.span) (pat : tepat) =
  (* Close the pattern *)
  let map, pat = close_tepat span pat in
  (* Use the map to update the expression *)
  (* We can now open the expression *)
  let visitor =
    object
      inherit [_] scoped_map_tevalue

      method! visit_EFVar scope fid =
        match AbsFVarId.Map.find_opt fid map with
        | None -> EFVar fid
        | Some bvar_id -> EBVar { scope; bvar_id }

      method! visit_EBVar scope var =
        (* We may need to increment the scope *)
        if var.scope >= scope then EBVar { var with scope = var.scope + 1 }
        else EBVar var
    end
  in
  (pat, visitor)

(** Close a binder in an expression.

    Return the closed binder (where the free variables have been replaced with
    bound variables). *)
let close_binder (span : Meta.span) (pat : tepat) (e : tevalue) :
    tepat * tevalue =
  let pat, visitor = close_binder_visitor span pat in
  let e = visitor#visit_tevalue 0 e in
  (pat, e)

let mk_fresh_abs_fvar (ty : ty) : tevalue =
  let id = fresh_abs_fvar_id () in
  { value = EFVar id; ty }

let mk_epat_from_fvar (fv : tevalue) : tepat =
  match fv.value with
  | EFVar id -> { pat = POpen id; ty = fv.ty }
  | _ -> raise (Failure "Unexpected")

let tevalue_has_fvars (e : tevalue) : bool =
  let visitor =
    object
      inherit [_] iter_tevalue
      method! visit_EFVar _ _ = raise Found
    end
  in
  try
    visitor#visit_tevalue () e;
    false
  with Found -> true

(** Create a let-binding.

    The pattern should be open (it should contain free variables): this helper
    will close it by replacing the free variables with bound variables. *)
let mk_let (span : Meta.span) (rid_set : region_id_set) (pat : tepat)
    (bound : tevalue) (e : tevalue) : tevalue =
  (* Close the pattern *)
  let pat, e = close_binder span pat e in
  (* Create the let-binding *)
  let value = ELet (rid_set, pat, bound, e) in
  let ty = e.ty in
  { value; ty }
