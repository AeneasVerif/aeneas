open Utils
open TypesUtils
open Types
open Values
open Errors
include Charon.ValuesUtils

(** Utility exception *)
exception FoundSymbolicValue of symbolic_value

let mk_unit_value : typed_value =
  { value = VAdt { variant_id = None; field_values = [] }; ty = mk_unit_ty }

let mk_bool_value (b : bool) : typed_value =
  { value = VLiteral (VBool b); ty = TLiteral TBool }

let mk_true : typed_value = mk_bool_value true
let mk_false : typed_value = mk_bool_value false

let mk_typed_value (span : Meta.span) (ty : ty) (value : value) : typed_value =
  sanity_check __FILE__ __LINE__ (ty_is_ety ty) span;
  { value; ty }

let mk_typed_avalue (span : Meta.span) (ty : ty) (value : avalue) : typed_avalue
    =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value; ty }

let mk_bottom (span : Meta.span) (ty : ty) : typed_value =
  sanity_check __FILE__ __LINE__ (ty_is_ety ty) span;
  { value = VBottom; ty }

let mk_abottom (span : Meta.span) (ty : ty) : typed_avalue =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value = ABottom; ty }

let mk_aignored (span : Meta.span) (ty : ty) (v : typed_value option) :
    typed_avalue =
  sanity_check __FILE__ __LINE__ (ty_is_rty ty) span;
  { value = AIgnored v; ty }

let value_as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic v -> v
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

(** Create a typed value from a symbolic value. *)
let mk_typed_value_from_symbolic_value (svalue : symbolic_value) : typed_value =
  let av = VSymbolic svalue in
  let av : typed_value =
    { value = av; ty = Substitute.erase_regions svalue.sv_ty }
  in
  av

(** Box a value *)
let mk_box_value (span : Meta.span) (v : typed_value) : typed_value =
  let box_ty = mk_box_ty v.ty in
  let box_v = VAdt { variant_id = None; field_values = [ v ] } in
  mk_typed_value span box_ty box_v

let is_bottom (v : value) : bool =
  match v with
  | VBottom -> true
  | _ -> false

let is_aignored (v : avalue) : bool =
  match v with
  | AIgnored _ -> true
  | _ -> false

let is_symbolic (v : value) : bool =
  match v with
  | VSymbolic _ -> true
  | _ -> false

let as_symbolic (span : Meta.span) (v : value) : symbolic_value =
  match v with
  | VSymbolic s -> s
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

let as_mut_borrow (span : Meta.span) (v : typed_value) :
    BorrowId.id * typed_value =
  match v.value with
  | VBorrow (VMutBorrow (bid, bv)) -> (bid, bv)
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

let is_unit (v : typed_value) : bool =
  ty_is_unit v.ty
  &&
  match v.value with
  | VAdt av -> av.variant_id = None && av.field_values = []
  | _ -> false

let mk_aproj_borrows (pm : proj_marker) (sv_id : symbolic_value_id)
    (proj_ty : ty) =
  { value = ASymbolic (pm, AProjBorrows (sv_id, proj_ty, [])); ty = proj_ty }

let mk_aproj_loans (pm : proj_marker) (sv_id : symbolic_value_id) (proj_ty : ty)
    =
  { value = ASymbolic (pm, AProjLoans (sv_id, proj_ty, [])); ty = proj_ty }

(** Check if a value contains a *concrete* borrow (i.e., a [Borrow] value - we
    don't check if there are borrows hidden in symbolic values). *)
let concrete_borrows_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains reserved mutable borrows (which are necessarily
    *concrete*: a symbolic value can't "hide" reserved borrows). *)
let reserved_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_VReservedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan (which is necessarily *concrete*: symbolic
    values can't "hide" loans). *)
let concrete_loans_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains concrete borrows or loans *)
let concrete_borrows_loans_in_value (v : value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
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
let outer_loans_in_value (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _env _ = raise Found

      method! visit_borrow_content _ _ =
        (* Do nothing so as *not to dive* in borrowed values *) ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
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
    (type_infos : TypesAnalysis.type_infos) (v : typed_value) :
    symbolic_value option =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_VSymbolic _ sv =
        if symbolic_value_is_greedily_expandable span type_decls type_infos sv
        then raise (FoundSymbolicValue sv)
        else ()
    end
  in
  (* Small helper *)
  try
    obj#visit_typed_value () v;
    None
  with FoundSymbolicValue sv -> Some sv

(** Strip the outer shared loans in a value. Ex.:
    [shared_loan {l0, l1} (3 : u32, shared_loan {l2} (4 : u32))] ~~>
    [(3 : u32, shared_loan {l2} (4 : u32))] *)
let rec value_strip_shared_loans (v : typed_value) : typed_value =
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
      inherit [_] iter_typed_value
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
      inherit [_] iter_typed_value
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
      inherit [_] iter_typed_value
      method! visit_loan_content _env _ = raise Found
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
      inherit [_] iter_typed_value
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
let value_remove_shared_loans (v : typed_value) : typed_value =
  let visitor =
    object (self : 'self)
      inherit [_] map_typed_value as super

      method! visit_typed_value env v =
        match v.value with
        | VLoan (VSharedLoan (_, sv)) -> self#visit_typed_value env sv
        | _ -> super#visit_typed_value env v
    end
  in
  visitor#visit_typed_value () v

let mk_abs_toutput (opat : abs_output) (opat_ty : ty) : abs_toutput =
  { opat; opat_ty }

let abs_output_unit : abs_output = OAdt (None, [])

let abs_toutput_unit : abs_toutput =
  mk_abs_toutput abs_output_unit
    (TAdt { id = TTuple; generics = empty_generic_args })

let rec abs_toutput_is_empty (output : abs_toutput) : bool =
  match output.opat with
  | OAdt (_, []) -> true
  | OAdt (_, fields) -> List.for_all abs_toutput_is_empty fields
  | _ -> false

let abs_toutput_mk_tuple (el : abs_toutput list) : abs_toutput =
  let tys = List.map (fun (e : abs_toutput) -> e.opat_ty) el in
  let opat = OAdt (None, el) in
  let opat_ty = TAdt { id = TTuple; generics = mk_generic_args_from_types tys } in
  { opat; opat_ty }

let abs_expr_unit : abs_expr = EAdt (None, [])

let abs_texpr_unit : abs_texpr =
  {
    e = abs_expr_unit;
    ty = TAdt { id = TTuple; generics = empty_generic_args };
  }

let abs_texpr_mk_tuple (el : abs_texpr list) : abs_texpr =
  let tys = List.map (fun (e : abs_texpr) -> e.ty) el in
  let e = EAdt (None, el) in
  let ty = TAdt { id = TTuple; generics = mk_generic_args_from_types tys } in
  { e; ty }

let abs_expr_tpat_mk_tuple (pats : abs_expr_tpat list) : abs_expr_tpat =
  let tys = List.map (fun (pat : abs_expr_tpat) -> pat.epat_ty) pats in
  let epat = PAdt (None, pats) in
  let epat_ty =
    TAdt { id = TTuple; generics = mk_generic_args_from_types tys }
  in
  { epat; epat_ty }

(** Substitute the input bound variables with fresh free variables *)
let abs_texpr_free_vars (bvars : abs_bound_var_id list)
    (fresh_fvar_id : unit -> abs_free_var_id) (e : abs_texpr) :
    abs_texpr * (abs_bound_var_id * abs_free_var_id) list =
  (* Initialize the map from bound variable to  *)
  let bound_to_free_list =
    List.map (fun bvar_id -> (bvar_id, fresh_fvar_id ())) bvars
  in
  let bound_to_free =
    AbsBoundVarId.Map.of_list
      (List.map
         (fun (bvar_id, fvar_id) -> (bvar_id, EFVar fvar_id))
         bound_to_free_list)
  in

  (* Optionally substitute a free variable *)
  let subst_bound_var (scope : int) (bv : abs_bound_var) : abs_expr =
    if scope = bv.db_scope_id then
      AbsBoundVarId.Map.find bv.bvar_id bound_to_free
    else EBVar bv
  in

  let visitor =
    object (self)
      inherit [_] map_abs_expr as super

      method! visit_EBVar scope bv =
        (* Optionally replace the bound var *)
        subst_bound_var scope bv

      method! visit_ELambda scope bvars expr =
        (* Increase the depth and continue *)
        super#visit_ELambda (scope + 1) bvars expr

      method! visit_ELet scope pat bexpr expr =
        (* Visit the bound expression *)
        let bexpr = self#visit_abs_texpr scope bexpr in
        (* Push a new scope and visit the inner expression *)
        let expr = self#visit_abs_texpr (scope + 1) expr in
        (* Put everything together *)
        ELet (pat, bexpr, expr)
    end
  in

  (visitor#visit_abs_texpr 0 e, bound_to_free_list)

(** Compute some helpers to bind variables.

    Introduce unique bound var ids (starting from 0) for the list of free
    variables given as input, and return:
    - a function to substitute the free variables with their corresponding bound
      variables in an abs expression
    - the list of pairs (free variable id, bound variable id) *)
let abs_texpr_prepare_bind_vars (fvars : abs_free_var_id list) :
    (abs_texpr -> abs_texpr) * (abs_free_var_id * abs_bound_var_id) list =
  let _, fresh_bvar_id = AbsBoundVarId.fresh_stateful_generator () in

  let free_to_bound_list =
    List.map (fun fv_id -> (fv_id, fresh_bvar_id ())) fvars
  in
  let free_to_bound = AbsFreeVarId.Map.of_list free_to_bound_list in

  (* Substitute a free variable *)
  let subst_free_var (scope : int) (fv_id : abs_free_var_id) : abs_expr =
    match AbsFreeVarId.Map.find_opt fv_id free_to_bound with
    | None -> EFVar fv_id
    | Some bvar_id -> EBVar { db_scope_id = scope; bvar_id }
  in

  let visitor =
    object (self)
      inherit [_] map_abs_expr as super

      method! visit_EFVar scope fv =
        (* Optionally replace the bound var *)
        subst_free_var scope fv

      method! visit_ELambda scope bvars expr =
        (* Increase the depth and continue *)
        super#visit_ELambda (scope + 1) bvars expr

      method! visit_ELet scope pat bexpr expr =
        (* Visit the bound expression *)
        let bexpr = self#visit_abs_texpr scope bexpr in
        (* Push a new scope and visit the inner expression *)
        let expr = self#visit_abs_texpr (scope + 1) expr in
        (* Put everything together *)
        ELet (pat, bexpr, expr)
    end
  in

  (* Visit *)
  (visitor#visit_abs_texpr 0, free_to_bound_list)

(** Replace the input list of free variables with bound variables, in
    preparation of the introducing of, e.g., a let-binding. *)
let abs_texpr_bind_vars (fvars : abs_free_var_id list) (e : abs_texpr) :
    abs_texpr * (abs_free_var_id * abs_bound_var_id) list =
  let subst, free_to_bound_list = abs_texpr_prepare_bind_vars fvars in
  (subst e, free_to_bound_list)

let abs_texpr_no_free_vars (e : abs_texpr) : bool =
  let free_vars = ref AbsFreeVarId.Set.empty in
  let visitor =
    object
      inherit [_] iter_abs_expr

      method! visit_abs_free_var_id _ fv_id =
        free_vars := AbsFreeVarId.Set.add fv_id !free_vars
    end
  in
  visitor#visit_abs_texpr () e;
  AbsFreeVarId.Set.is_empty !free_vars

module AbsExprOrderedType = struct
  type t = abs_expr

  let compare = compare_abs_expr
  let to_string = show_abs_expr
  let pp_t = pp_abs_expr
  let show_t = show_abs_expr
end

module AbsExprMap = struct
  include Collections.MakeMap (AbsExprOrderedType)

  let to_opt_subst (m : abs_expr t) : abs_expr -> abs_expr =
   fun e ->
    match find_opt e m with
    | None -> e
    | Some e -> e
end

module AbsExprSet = Collections.MakeSet (AbsExprOrderedType)

module AbsTExprOrderedType = struct
  type t = abs_texpr

  let compare = compare_abs_texpr
  let to_string = show_abs_texpr
  let pp_t = pp_abs_texpr
  let show_t = show_abs_texpr
end

module AbsTExprMap = struct
  include Collections.MakeMap (AbsTExprOrderedType)

  let to_opt_subst (m : abs_texpr t) : abs_texpr -> abs_texpr =
   fun e ->
    match find_opt e m with
    | None -> e
    | Some e -> e
end

module AbsTExprSet = Collections.MakeSet (AbsTExprOrderedType)

module AbsTOutputOrderedType = struct
  type t = abs_toutput

  let compare = compare_abs_toutput
  let to_string = show_abs_toutput
  let pp_t = pp_abs_toutput
  let show_t = show_abs_toutput
end

module AbsTOutputMap = struct
  include Collections.MakeMap (AbsTOutputOrderedType)

  let to_subst (m : 'a t) : abs_toutput -> 'a = fun e -> find e m
end

module AbsTOutputSet = Collections.MakeSet (AbsTOutputOrderedType)

(** Helper function.

    This function allows to define in a generic way a comparison of **region
    types**. See [projections_intersect] for instance.

    Important: the regions in the types mustn't be erased.

    [default]: default boolean to return, when comparing types with no regions
    [combine]: how to combine booleans [compare_regions]: how to compare regions

    TODO: is there a way of deriving such a comparison? TODO: rename *)
let rec compare_rtys (span : Meta.span) (default : bool)
    (combine : bool -> bool -> bool)
    (compare_regions : region -> region -> bool) (ty1 : rty) (ty2 : rty) : bool
    =
  let compare = compare_rtys span default combine compare_regions in
  (* Sanity check - TODO: don't do this at every recursive call *)
  sanity_check __FILE__ __LINE__ (ty_is_rty ty1 && ty_is_rty ty2) span;
  (* Normalize the associated types *)
  match (ty1, ty2) with
  | TLiteral lit1, TLiteral lit2 ->
      sanity_check __FILE__ __LINE__ (lit1 = lit2) span;
      default
  | TAdt tref1, TAdt tref2 ->
      let generics1 = tref1.generics in
      let generics2 = tref2.generics in
      sanity_check __FILE__ __LINE__ (tref1.id = tref2.id) span;
      (* There are no regions in the const generics, so we ignore them,
         but we still check they are the same, for sanity *)
      sanity_check __FILE__ __LINE__
        (generics1.const_generics = generics2.const_generics)
        span;

      (* We also ignore the trait refs *)

      (* The check for the ADTs is very crude: we simply compare the arguments
       * two by two.
       *
       * For instance, when checking if some projections intersect, we simply
       * check if some arguments intersect. As all the type and region
       * parameters should be used somewhere in the ADT (otherwise rustc
       * generates an error), it means that it should be equivalent to checking
       * whether two fields intersect (and anyway comparing the field types is
       * difficult in case of enumerations...).
       * If we didn't have the above property enforced by the rust compiler,
       * this check would still be a reasonable conservative approximation. *)

      (* Check the region parameters *)
      let regions = List.combine generics1.regions generics2.regions in
      let params_b =
        List.fold_left
          (fun b (r1, r2) -> combine b (compare_regions r1 r2))
          default regions
      in
      (* Check the type parameters *)
      let tys = List.combine generics1.types generics2.types in
      let tys_b =
        List.fold_left
          (fun b (ty1, ty2) -> combine b (compare ty1 ty2))
          default tys
      in
      (* Combine *)
      combine params_b tys_b
  | TRef (r1, ty1, kind1), TRef (r2, ty2, kind2) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (kind1 = kind2) span;
      (* Explanation for the case where we check if projections intersect:
       * the projections intersect if the borrows intersect or their contents
       * intersect. *)
      let regions_b = compare_regions r1 r2 in
      let tys_b = compare ty1 ty2 in
      combine regions_b tys_b
  | TVar id1, TVar id2 ->
      sanity_check __FILE__ __LINE__ (id1 = id2) span;
      default
  | TTraitType _, TTraitType _ ->
      (* The types should have been normalized. If after normalization we
         get trait types, we can consider them as variables *)
      sanity_check __FILE__ __LINE__ (ty1 = ty2) span;
      default
  | _ ->
      log#ltrace
        (lazy
          ("compare_rtys: unexpected inputs:" ^ "\n- ty1: " ^ show_ty ty1
         ^ "\n- ty2: " ^ show_ty ty2));
      internal_error __FILE__ __LINE__ span

(** Check if two different projections intersect. This is necessary when giving
    a symbolic value to an abstraction: we need to check that the regions which
    are already ended inside the abstraction don't intersect the regions over
    which we project in the new abstraction. Note that the two abstractions have
    different views (in terms of regions) of the symbolic value (hence the two
    region types). *)
let projections_intersect (span : Meta.span) (ty1 : rty)
    (rset1 : RegionId.Set.t) (ty2 : rty) (rset2 : RegionId.Set.t) : bool =
  let default = false in
  let combine b1 b2 = b1 || b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 && region_in_set r2 rset2
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** Check if the first projection contains the second projection. We use this
    function when checking invariants.

    The regions in the types shouldn't be erased (this function will raise an
    exception otherwise). *)
let projection_contains (span : Meta.span) (ty1 : rty) (rset1 : RegionId.Set.t)
    (ty2 : rty) (rset2 : RegionId.Set.t) : bool =
  let default = true in
  let combine b1 b2 = b1 && b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 || not (region_in_set r2 rset2)
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** A marked borrow id *)
type marked_borrow_id = proj_marker * BorrowId.id [@@deriving show, ord]

module MarkedBorrowIdOrd = struct
  type t = marked_borrow_id

  let compare = compare_marked_borrow_id
  let to_string = show_marked_borrow_id
  let pp_t = pp_marked_borrow_id
  let show_t = show_marked_borrow_id
end

module MarkedBorrowIdSet = Collections.MakeSet (MarkedBorrowIdOrd)
module MarkedBorrowIdMap = Collections.MakeMap (MarkedBorrowIdOrd)

module MarkedBorrowId : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = marked_borrow_id = struct
  type t = marked_borrow_id

  let to_string = show_marked_borrow_id

  module Set = MarkedBorrowIdSet
  module Map = MarkedBorrowIdMap
end

(** A marked and normalized symbolic value (loan/borrow) projection.

    A normalized symbolic value projection is a projection of a symoblic value
    for which the projection type has been normalized in the following way: the
    projected regions have the identifier 0, and the non-projected regions are
    erased.

    For instance, if we consider the region abstractions below:
    {[
      abs0 {'a} { s <: S<'a, 'b> }
      abs1 {'b} { s <: S<'a, 'b> }
    ]}

    Then normalizing (the type of) the symbolic value [s] for ['a] gives
    [S<'0, '_>], while normalizing it for ['b] gives [S<'_, '0>].

    We use normalized types to compare loan/borrow projections of symbolic
    values, and for lookups (normalized types can easily be used as keys in
    maps). *)
type marked_norm_symb_proj = {
  pm : proj_marker;
  sv_id : symbolic_value_id;
  norm_proj_ty : ty;
}
[@@deriving show, ord]

module MarkedNormSymbProjOrd = struct
  type t = marked_norm_symb_proj

  let compare = compare_marked_norm_symb_proj
  let to_string = show_marked_norm_symb_proj
  let pp_t = pp_marked_norm_symb_proj
  let show_t = show_marked_norm_symb_proj
end

module MarkedNormSymbProjSet = Collections.MakeSet (MarkedNormSymbProjOrd)
module MarkedNormSymbProjMap = Collections.MakeMap (MarkedNormSymbProjOrd)

module MarkedNormSymbProj : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = marked_norm_symb_proj = struct
  type t = marked_norm_symb_proj

  let to_string = show_marked_norm_symb_proj

  module Set = MarkedNormSymbProjSet
  module Map = MarkedNormSymbProjMap
end

type norm_symb_proj = { sv_id : symbolic_value_id; norm_proj_ty : ty }
[@@deriving show, ord]

module NormSymbProjOrd = struct
  type t = norm_symb_proj

  let compare = compare_norm_symb_proj
  let to_string = show_norm_symb_proj
  let pp_t = pp_norm_symb_proj
  let show_t = show_norm_symb_proj
end

module NormSymbProjSet = Collections.MakeSet (NormSymbProjOrd)
module NormSymbProjMap = Collections.MakeMap (NormSymbProjOrd)

module NormSymbProj : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = norm_symb_proj = struct
  type t = norm_symb_proj

  let to_string = show_norm_symb_proj

  module Set = NormSymbProjSet
  module Map = NormSymbProjMap
end

let marked_norm_symb_proj_to_unmarked (m : marked_norm_symb_proj) :
    norm_symb_proj =
  { sv_id = m.sv_id; norm_proj_ty = m.norm_proj_ty }

(** Normalize a projection type by replacing the projected regions with ['0] and
    the non-projected ones with ['_].

    For instance, when normalizing the projection type [S<'a, 'b>] for the
    projection region ['a]. *)
let normalize_proj_ty (regions : RegionId.Set.t) (ty : rty) : rty =
  let visitor =
    object
      inherit [_] map_ty

      method! visit_region _ r =
        match r with
        | RVar (Free r) ->
            if RegionId.Set.mem r regions then RVar (Free (RegionId.of_int 0))
            else RErased
        | RVar (Bound _) | RStatic | RErased -> r
    end
  in
  visitor#visit_ty () ty

(** Compute the union of two normalized projection types *)
let rec norm_proj_tys_union (span : Meta.span) (ty1 : rty) (ty2 : rty) : rty =
  match (ty1, ty2) with
  | TAdt tref1, TAdt tref2 ->
      sanity_check __FILE__ __LINE__ (tref1.id = tref2.id) span;
      TAdt
        {
          id = tref1.id;
          generics =
            norm_proj_generic_args_union span tref1.generics tref2.generics;
        }
  | TVar id1, TVar id2 ->
      sanity_check __FILE__ __LINE__ (id1 = id2) span;
      TVar id1
  | TLiteral lit1, TLiteral lit2 ->
      sanity_check __FILE__ __LINE__ (lit1 = lit2) span;
      TLiteral lit1
  | TNever, TNever -> TNever
  | TRef (r1, ty1, rk1), TRef (r2, ty2, rk2) ->
      sanity_check __FILE__ __LINE__ (rk1 = rk2) span;
      TRef
        ( norm_proj_regions_union span r1 r2,
          norm_proj_tys_union span ty1 ty2,
          rk1 )
  | TRawPtr (ty1, rk1), TRawPtr (ty2, rk2) ->
      sanity_check __FILE__ __LINE__ (rk1 = rk2) span;
      TRawPtr (norm_proj_tys_union span ty1 ty2, rk1)
  | TTraitType (tr1, item1), TTraitType (tr2, item2) ->
      sanity_check __FILE__ __LINE__ (item1 = item2) span;
      TTraitType (norm_proj_trait_refs_union span tr1 tr2, item1)
  | TDynTrait (), TDynTrait () -> TDynTrait ()
  | ( TFnPtr
        { binder_regions = binder_regions1; binder_value = inputs1, output1 },
      TFnPtr
        { binder_regions = binder_regions2; binder_value = inputs2, output2 } )
    ->
      (* TODO: general case *)
      sanity_check __FILE__ __LINE__ (binder_regions1 = []) span;
      sanity_check __FILE__ __LINE__ (binder_regions2 = []) span;
      let binder_value =
        ( List.map2 (norm_proj_tys_union span) inputs1 inputs2,
          norm_proj_tys_union span output1 output2 )
      in
      TFnPtr { binder_regions = []; binder_value }
  | _ -> internal_error __FILE__ __LINE__ span

and norm_proj_generic_args_union span (generics1 : generic_args)
    (generics2 : generic_args) : generic_args =
  let {
    regions = regions1;
    types = types1;
    const_generics = const_generics1;
    trait_refs = trait_refs1;
  } =
    generics1
  in
  let {
    regions = regions2;
    types = types2;
    const_generics = const_generics2;
    trait_refs = trait_refs2;
  } =
    generics2
  in
  {
    regions = List.map2 (norm_proj_regions_union span) regions1 regions2;
    types = List.map2 (norm_proj_tys_union span) types1 types2;
    const_generics =
      List.map2
        (norm_proj_const_generics_union span)
        const_generics1 const_generics2;
    trait_refs =
      List.map2 (norm_proj_trait_refs_union span) trait_refs1 trait_refs2;
  }

and norm_proj_regions_union (span : Meta.span) (r1 : region) (r2 : region) :
    region =
  match (r1, r2) with
  | RVar (Free _), RVar (Free _) ->
      (* There is an intersection: the regions should be disjoint *)
      internal_error __FILE__ __LINE__ span
  | RVar (Free rid), RErased | RErased, RVar (Free rid) ->
      sanity_check __FILE__ __LINE__ (rid = RegionId.zero) span;
      RVar (Free rid)
  | _ -> internal_error __FILE__ __LINE__ span

and norm_proj_trait_refs_union (span : Meta.span) (tr1 : trait_ref)
    (tr2 : trait_ref) : trait_ref =
  let { trait_id = trait_id1; trait_decl_ref = decl_ref1 } = tr1 in
  let { trait_id = trait_id2; trait_decl_ref = decl_ref2 } = tr2 in
  sanity_check __FILE__ __LINE__ (trait_id1 = trait_id2) span;
  (* There might be regions but let's ignore this for now... *)
  sanity_check __FILE__ __LINE__ (decl_ref1 = decl_ref2) span;
  tr1

and norm_proj_const_generics_union (span : Meta.span) (cg1 : const_generic)
    (cg2 : const_generic) : const_generic =
  sanity_check __FILE__ __LINE__ (cg1 = cg2) span;
  cg1

let norm_proj_ty_contains span (ty1 : rty) (ty2 : rty) : bool =
  let set = RegionId.Set.singleton RegionId.zero in
  projection_contains span ty1 set ty2 set

let subst_abs_texpr (subst : abs_texpr -> abs_texpr) (e : abs_texpr) : abs_texpr
    =
  let visitor =
    object
      inherit [_] map_abs_expr as super
      method! visit_abs_texpr env e = super#visit_abs_texpr env (subst e)
    end
  in
  visitor#visit_abs_texpr () e

let abs_texpr_map_to_subst (m : abs_texpr AbsTExprMap.t) :
    abs_texpr -> abs_texpr =
 fun e ->
  match AbsTExprMap.find_opt e m with
  | None -> e
  | Some e -> e

(** Small helper which allows us, given an abstraction continuation of
    expression [e] and with outputs [outputs], to create the expression:
    {[
      let outputs = e in ...
    ]}
    This is useful when merging region abstractions together: we need to compose
    their continuations, and we do so by binding the outputs of the first
    continuation, so that the second continuation can refer to them (and we also
    bind the outputs of the second one, because the outputs of the composition
    is actually a combination of the outputs of both continuations). *)
let let_bind_abs_cont_outputs (span : Meta.span)
    (fresh_fvar_id : unit -> AbsFreeVarId.id) (cont : abs_cont) :
    (abs_texpr -> abs_texpr) * (abs_texpr * abs_texpr) list =
  (* Convert the outputs to expressions that we will substitute with variables. *)
  let output_to_subst_texpr ((out, _) : abs_toutput * proj_marker) : abs_texpr =
    let e =
      match out.opat with
      | OBorrow bid -> ELoan bid
      | OSymbolic sv_id -> ESymbolic sv_id
      | OAdt _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    { e; ty = out.opat_ty }
  in
  let abs_output_fvars = List.map (fun _ -> fresh_fvar_id ()) cont.outputs in
  let abs_output_fvars_tys =
    List.combine abs_output_fvars
      (List.map (fun (o, _) -> o.opat_ty) cont.outputs)
  in
  let abs_outputs = List.map output_to_subst_texpr cont.outputs in
  (* Map from expression to expression *)
  let emap =
    List.combine abs_outputs
      (List.map
         (fun (fv_id, ty) -> { e = EFVar fv_id; ty })
         abs_output_fvars_tys)
  in
  let mk_let (next : abs_texpr) : abs_texpr =
    let next, free_to_bound = abs_texpr_bind_vars abs_output_fvars next in
    let bvars = List.map snd free_to_bound in
    let bvars_tys =
      List.combine bvars
        (List.map (fun (v : abs_toutput * _) -> (fst v).opat_ty) cont.outputs)
    in
    let pat =
      abs_expr_tpat_mk_tuple
        (List.map
           (fun (vid, ty) -> { epat = PVar vid; epat_ty = ty })
           bvars_tys)
    in
    { e = ELet (pat, cont.expr, next); ty = next.ty }
  in
  (mk_let, emap)
