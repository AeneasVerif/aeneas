module T = Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils

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

(* TODO: move *)
let mk_var (index : V.VarId.id) (name : string option) (var_ty : T.ety) : A.var
    =
  { A.index; name; var_ty }

(** Small helper *)
let mk_place_from_var_id (var_id : V.VarId.id) : E.place =
  { var_id; projection = [] }

(** Deconstruct a type of the form `Box<T>` to retrieve the `T` inside *)
let ty_get_box (box_ty : T.ety) : T.ety =
  match box_ty with
  | T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) -> boxed_ty
  | _ -> failwith "Not a boxed type"

(** Deconstruct a type of the form `&T` or `&mut T` to retrieve the `T` (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : T.ety) : T.erased_region * T.ety * T.ref_kind =
  match ty with
  | T.Ref (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> failwith "Not a ref type"

(** Box a value *)
let mk_box_value (v : V.typed_value) : V.typed_value =
  let box_ty = T.Adt (T.Assumed T.Box, [], [ v.V.ty ]) in
  let box_v = V.Adt { variant_id = None; field_values = [ v ] } in
  mk_typed_value box_ty box_v

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

let mk_aproj_loans_from_proj_comp (sv : V.symbolic_proj_comp) : V.typed_avalue =
  let ty = sv.V.svalue.V.sv_ty in
  let proj = V.AProjLoans sv.V.svalue in
  let value = V.ASymbolic proj in
  { V.value; ty }
