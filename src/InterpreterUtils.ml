(* TODO: most of the definitions in this file need to be moved elsewhere *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils
open Utils

(** Some utilities *)

let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string

let ety_to_string = Print.EvalCtxCfimAst.ety_to_string

let typed_value_to_string = Print.EvalCtxCfimAst.typed_value_to_string

let place_to_string = Print.EvalCtxCfimAst.place_to_string

let operand_to_string = Print.EvalCtxCfimAst.operand_to_string

let statement_to_string ctx =
  Print.EvalCtxCfimAst.statement_to_string ctx "" "  "

let same_symbolic_id (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) : bool =
  sv0.V.sv_id = sv1.V.sv_id

let mk_var (index : V.VarId.id) (name : string option) (var_ty : T.ety) : A.var
    =
  { A.index; name; var_ty }

(** Small helper - TODO: move *)
let mk_place_from_var_id (var_id : V.VarId.id) : E.place =
  { var_id; projection = [] }

(** Create a fresh symbolic proj comp *)
let mk_fresh_symbolic_proj_comp (ended_regions : T.RegionId.set_t) (ty : T.rty)
    (ctx : C.eval_ctx) : C.eval_ctx * V.symbolic_proj_comp =
  let ctx, sv_id = C.fresh_symbolic_value_id ctx in
  let svalue = { V.sv_id; V.sv_ty = ty } in
  let sv = { V.svalue; rset_ended = ended_regions } in
  (ctx, sv)

(** Create a fresh symbolic value (as a complementary projector) *)
let mk_fresh_symbolic_proj_comp_value (ended_regions : T.RegionId.set_t)
    (ty : T.rty) (ctx : C.eval_ctx) : C.eval_ctx * V.typed_value =
  let ctx, sv = mk_fresh_symbolic_proj_comp ended_regions ty ctx in
  let value : V.value = V.Symbolic sv in
  let ty : T.ety = Subst.erase_regions ty in
  let sv : V.typed_value = { V.value; ty } in
  (ctx, sv)

let mk_typed_value_from_proj_comp (sv : V.symbolic_proj_comp) : V.typed_value =
  let ty = Subst.erase_regions sv.V.svalue.V.sv_ty in
  let value = V.Symbolic sv in
  { V.value; ty }

let mk_typed_value_from_symbolic_value (svalue : V.symbolic_value) :
    V.typed_value =
  let spc = { V.svalue; rset_ended = T.RegionId.Set.empty } in
  mk_typed_value_from_proj_comp spc

let mk_aproj_loans_from_proj_comp (sv : V.symbolic_proj_comp) : V.typed_avalue =
  let ty = sv.V.svalue.V.sv_ty in
  let proj = V.AProjLoans sv.V.svalue in
  let value = V.ASymbolic proj in
  { V.value; ty }

(** TODO: move *)
let borrow_is_asb (bid : V.BorrowId.id) (asb : V.abstract_shared_borrow) : bool
    =
  match asb with
  | V.AsbBorrow bid' -> bid' = bid
  | V.AsbProjReborrows _ -> false

(** TODO: move *)
let borrow_in_asb (bid : V.BorrowId.id) (asb : V.abstract_shared_borrows) : bool
    =
  List.exists (borrow_is_asb bid) asb

(** TODO: move *)
let remove_borrow_from_asb (bid : V.BorrowId.id)
    (asb : V.abstract_shared_borrows) : V.abstract_shared_borrows =
  let removed = ref 0 in
  let asb =
    List.filter
      (fun asb ->
        if not (borrow_is_asb bid asb) then true
        else (
          removed := !removed + 1;
          false))
      asb
  in
  assert (!removed = 1);
  asb

(** We sometimes need to return a value whose type may vary depending on
    whether we find it in a "concrete" value or an abstraction (ex.: loan
    contents when we perform environment lookups by using borrow ids) *)
type ('a, 'b) concrete_or_abs = Concrete of 'a | Abstract of 'b

type g_loan_content = (V.loan_content, V.aloan_content) concrete_or_abs
(** Generic loan content: concrete or abstract *)

type g_borrow_content = (V.borrow_content, V.aborrow_content) concrete_or_abs
(** Generic borrow content: concrete or abstract *)

type abs_or_var_id = AbsId of V.AbstractionId.id | VarId of V.VarId.id

exception FoundBorrowContent of V.borrow_content
(** Utility exception *)

exception FoundLoanContent of V.loan_content
(** Utility exception *)

exception FoundABorrowContent of V.aborrow_content
(** Utility exception *)

exception FoundGBorrowContent of g_borrow_content
(** Utility exception *)

exception FoundGLoanContent of g_loan_content
(** Utility exception *)

(** Check if a value contains a borrow *)
let borrows_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains inactivated mutable borrows *)
let inactivated_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_InactivatedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan *)
let loans_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

let symbolic_value_id_in_ctx (sv_id : V.SymbolicValueId.id) (ctx : C.eval_ctx) :
    bool =
  let obj =
    object
      inherit [_] C.iter_eval_ctx

      method! visit_Symbolic _ sv =
        if sv.V.svalue.V.sv_id = sv_id then raise Found else ()

      method! visit_ASymbolic _ aproj =
        match aproj with
        | AProjLoans sv | AProjBorrows (sv, _) ->
            if sv.V.sv_id = sv_id then raise Found else ()

      method! visit_abstract_shared_borrows _ asb =
        let visit (asb : V.abstract_shared_borrow) : unit =
          match asb with
          | V.AsbBorrow _ -> ()
          | V.AsbProjReborrows (sv, _) ->
              if sv.V.sv_id = sv_id then raise Found else ()
        in
        List.iter visit asb
    end
  in
  (* We use exceptions *)
  try
    obj#visit_eval_ctx () ctx;
    false
  with Found -> true

(** TODO: move to InterpreterSymbolic or sth *)
type symbolic_expansion =
  | SeConcrete of V.constant_value
  | SeAdt of (T.VariantId.id option * V.symbolic_proj_comp list)
  | SeMutRef of V.BorrowId.id * V.symbolic_proj_comp
  | SeSharedRef of V.BorrowId.set_t * V.symbolic_proj_comp

(** Check if two different projections intersect. This is necessary when
    giving a symbolic value to an abstraction: we need to check that
    the regions which are already ended inside the abstraction don't
    intersect the regions over which we project in the new abstraction.
    Note that the two abstractions have different views (in terms of regions)
    of the symbolic value (hence the two region types).
*)
let rec projections_intersect (ty1 : T.rty) (rset1 : T.RegionId.set_t)
    (ty2 : T.rty) (rset2 : T.RegionId.set_t) : bool =
  match (ty1, ty2) with
  | T.Bool, T.Bool | T.Char, T.Char | T.Str, T.Str -> false
  | T.Integer int_ty1, T.Integer int_ty2 ->
      assert (int_ty1 = int_ty2);
      false
  | T.Adt (id1, regions1, tys1), T.Adt (id2, regions2, tys2) ->
      assert (id1 = id2);
      (* The intersection check for the ADTs is very crude: 
       * we check if some arguments intersect. As all the type and region
       * parameters should be used somewhere in the ADT (otherwise rustc
       * generates an error), it means that it should be equivalent to checking
       * whether two fields intersect (and anyway comparing the field types is
       * difficult in case of enumerations...).
       * If we didn't have the above property enforced by the rust compiler,
       * this check would still be a reasonable conservative approximation. *)
      let regions = List.combine regions1 regions2 in
      let tys = List.combine tys1 tys2 in
      List.exists
        (fun (r1, r2) -> region_in_set r1 rset1 && region_in_set r2 rset2)
        regions
      || List.exists
           (fun (ty1, ty2) -> projections_intersect ty1 rset1 ty2 rset2)
           tys
  | T.Array ty1, T.Array ty2 | T.Slice ty1, T.Slice ty2 ->
      projections_intersect ty1 rset1 ty2 rset2
  | T.Ref (r1, ty1, kind1), T.Ref (r2, ty2, kind2) ->
      (* Sanity check *)
      assert (kind1 = kind2);
      (* The projections intersect if the borrows intersect or their contents
       * intersect *)
      (region_in_set r1 rset1 && region_in_set r2 rset2)
      || projections_intersect ty1 rset1 ty2 rset2
  | _ -> failwith "Unreachable"

(** Check if the ended regions of a comp projector over a symbolic value
    intersect the regions listed in another projection *)
let symbolic_proj_comp_ended_regions_intersect_proj (s : V.symbolic_proj_comp)
    (ty : T.rty) (regions : T.RegionId.set_t) : bool =
  projections_intersect s.V.svalue.V.sv_ty s.V.rset_ended ty regions

(** Check that a symbolic value doesn't contain ended regions.

    Note that we don't check that the set of ended regions is empty: we
    check that the set of ended regions doesn't intersect the set of
    regions used in the type (this is more general).
*)
let symbolic_proj_comp_ended_regions (s : V.symbolic_proj_comp) : bool =
  let regions = rty_regions s.V.svalue.V.sv_ty in
  not (T.RegionId.Set.disjoint regions s.rset_ended)

(** Check if a [value] contains ⊥.

    Note that this function is very general: it also checks wether
    symbolic values contain already ended regions.
 *)
let bottom_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_Bottom _ = raise Found

      method! visit_symbolic_proj_comp _ s =
        if symbolic_proj_comp_ended_regions s then raise Found else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if an [avalue] contains ⊥.

    Note that this function is very general: it also checks wether
    symbolic values contain already ended regions.
    
    TODO: remove?
*)
let bottom_in_avalue (v : V.typed_avalue) (_abs_regions : T.RegionId.set_t) :
    bool =
  let obj =
    object
      inherit [_] V.iter_typed_avalue

      method! visit_Bottom _ = raise Found

      method! visit_symbolic_proj_comp _ sv =
        if symbolic_proj_comp_ended_regions sv then raise Found else ()

      method! visit_aproj _ ap =
        (* Nothing to do actually *)
        match ap with
        | V.AProjLoans _sv -> ()
        | V.AProjBorrows (_sv, _rty) -> ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_avalue () v;
    false
  with Found -> true

(** Return true if a type is "primitively copyable".
  *
  * "primitively copyable" means that copying instances of this type doesn't
  * require calling dedicated functions defined through the Copy trait. It
  * is the case for types like integers, shared borrows, etc.
  *)
let rec type_is_primitively_copyable (ty : T.ety) : bool =
  match ty with
  | T.Adt ((T.AdtId _ | T.Assumed _), _, _) -> false
  | T.Adt (T.Tuple, _, tys) -> List.for_all type_is_primitively_copyable tys
  | T.TypeVar _ | T.Never | T.Str | T.Array _ | T.Slice _ -> false
  | T.Bool | T.Char | T.Integer _ -> true
  | T.Ref (_, _, T.Mut) -> false
  | T.Ref (_, _, T.Shared) -> true
