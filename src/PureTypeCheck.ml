(** Module to perform type checking on the pure AST - we use this for sanity checks only *)

open Pure
open PureUtils

(** Utility function, used for type checking *)
let get_adt_field_types (type_decls : type_decl TypeDeclId.Map.t)
    (type_id : type_id) (variant_id : VariantId.id option) (tys : ty list) :
    ty list =
  match type_id with
  | Tuple ->
      (* Tuple *)
      assert (variant_id = None);
      tys
  | AdtId def_id ->
      (* "Regular" ADT *)
      let def = TypeDeclId.Map.find def_id type_decls in
      type_decl_get_instantiated_fields_types def variant_id tys
  | Assumed aty -> (
      (* Assumed type *)
      match aty with
      | State ->
          (* `State` is opaque *)
          raise (Failure "Unreachable: `State` values are opaque")
      | Result ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then [ ty ]
          else if variant_id = result_fail_id then []
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | Option ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = option_some_id then [ ty ]
          else if variant_id = option_none_id then []
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | Vec -> raise (Failure "Unreachable: `Vector` values are opaque"))

type tc_ctx = {
  type_decls : type_decl TypeDeclId.Map.t;  (** The type declarations *)
  env : ty VarId.Map.t;  (** Environment from variables to types *)
}

let check_constant_value (v : constant_value) (ty : ty) : unit =
  match (ty, v) with
  | Integer int_ty, V.Scalar sv -> assert (int_ty = sv.V.int_ty)
  | Bool, Bool _ | Char, Char _ | Str, String _ -> ()
  | _ -> raise (Failure "Inconsistent type")

let rec check_typed_pattern (ctx : tc_ctx) (v : typed_pattern) : tc_ctx =
  log#ldebug (lazy ("check_typed_pattern: " ^ show_typed_pattern v));
  match v.value with
  | PatConcrete cv ->
      check_constant_value cv v.ty;
      ctx
  | PatDummy -> ctx
  | PatVar (var, _) ->
      assert (var.ty = v.ty);
      let env = VarId.Map.add var.id var.ty ctx.env in
      { ctx with env }
  | PatAdt av ->
      (* Compute the field types *)
      let type_id, tys =
        match v.ty with
        | Adt (type_id, tys) -> (type_id, tys)
        | _ -> raise (Failure "Inconsistently typed value")
      in
      let field_tys =
        get_adt_field_types ctx.type_decls type_id av.variant_id tys
      in
      let check_value (ctx : tc_ctx) (ty : ty) (v : typed_pattern) : tc_ctx =
        if ty <> v.ty then (
          log#serror
            ("check_typed_pattern: not the same types:" ^ "\n- ty: "
           ^ show_ty ty ^ "\n- v.ty: " ^ show_ty v.ty);
          raise (Failure "Inconsistent types"));
        check_typed_pattern ctx v
      in
      (* Check the field types: check that the field patterns have the expected
       * types, and check that the field patterns themselves are well-typed *)
      List.fold_left
        (fun ctx (ty, v) -> check_value ctx ty v)
        ctx
        (List.combine field_tys av.field_values)

let rec check_texpression (ctx : tc_ctx) (e : texpression) : unit =
  match e.e with
  | Var var_id -> (
      (* Lookup the variable - note that the variable may not be there,
       * if we type-check a subexpression (i.e.: if the variable is introduced
       * "outside" of the expression) - TODO: this won't happen once
       * we use a locally nameless representation *)
      match VarId.Map.find_opt var_id ctx.env with
      | None -> ()
      | Some ty -> assert (ty = e.ty))
  | Const cv -> check_constant_value cv e.ty
  | App (app, arg) ->
      let input_ty, output_ty = destruct_arrow app.ty in
      assert (input_ty = arg.ty);
      assert (output_ty = e.ty);
      check_texpression ctx app;
      check_texpression ctx arg
  | Abs (pat, body) ->
      let pat_ty, body_ty = destruct_arrow e.ty in
      assert (pat.ty = pat_ty);
      assert (body.ty = body_ty);
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_typed_pattern ctx pat in
      check_texpression ctx body
  | Qualif qualif -> (
      match qualif.id with
      | Func _ | Global _ -> () (* TODO *)
      | Proj { adt_id = proj_adt_id; field_id } ->
          (* Note we can only project fields of structures (not enumerations) *)
          (* Deconstruct the projector type *)
          let adt_ty, field_ty = destruct_arrow e.ty in
          let adt_id, adt_type_args =
            match adt_ty with
            | Adt (type_id, tys) -> (type_id, tys)
            | _ -> raise (Failure "Unreachable")
          in
          (* Check the ADT type *)
          assert (adt_id = proj_adt_id);
          assert (adt_type_args = qualif.type_args);
          (* Retrieve and check the expected field type *)
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types ctx.type_decls proj_adt_id variant_id
              qualif.type_args
          in
          let expected_field_ty = FieldId.nth expected_field_tys field_id in
          assert (expected_field_ty = field_ty)
      | AdtCons id -> (
          let expected_field_tys =
            get_adt_field_types ctx.type_decls id.adt_id id.variant_id
              qualif.type_args
          in
          let field_tys, adt_ty = destruct_arrows e.ty in
          assert (expected_field_tys = field_tys);
          match adt_ty with
          | Adt (type_id, tys) ->
              assert (type_id = id.adt_id);
              assert (tys = qualif.type_args)
          | _ -> raise (Failure "Unreachable")))
  | Let (monadic, pat, re, e_next) ->
      let expected_pat_ty = if monadic then destruct_result re.ty else re.ty in
      assert (pat.ty = expected_pat_ty);
      assert (e.ty = e_next.ty);
      (* Check the right-expression *)
      check_texpression ctx re;
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_typed_pattern ctx pat in
      (* Check the next expression *)
      check_texpression ctx e_next
  | Switch (scrut, switch_body) -> (
      check_texpression ctx scrut;
      match switch_body with
      | If (e_then, e_else) ->
          assert (scrut.ty = Bool);
          assert (e_then.ty = e.ty);
          assert (e_else.ty = e.ty);
          check_texpression ctx e_then;
          check_texpression ctx e_else
      | Match branches ->
          let check_branch (br : match_branch) : unit =
            assert (br.pat.ty = scrut.ty);
            let ctx = check_typed_pattern ctx br.pat in
            check_texpression ctx br.branch
          in
          List.iter check_branch branches)
  | Meta (_, e_next) ->
      assert (e_next.ty = e.ty);
      check_texpression ctx e_next
