(** Module to perform type checking on the pure AST - we use this for sanity checks only *)

open Pure
open PureUtils

(** Utility function, used for type checking.

    This function should only be used for "regular" ADTs, where the number
    of fields is fixed: it shouldn't be used for arrays, slices, etc.
 *)
let get_adt_field_types (type_decls : type_decl TypeDeclId.Map.t)
    (type_id : type_id) (variant_id : VariantId.id option) (tys : ty list)
    (cgs : const_generic list) : ty list =
  match type_id with
  | Tuple ->
      (* Tuple *)
      assert (variant_id = None);
      tys
  | AdtId def_id ->
      (* "Regular" ADT *)
      let def = TypeDeclId.Map.find def_id type_decls in
      type_decl_get_instantiated_fields_types def variant_id tys cgs
  | Assumed aty -> (
      (* Assumed type *)
      match aty with
      | State ->
          (* This type is opaque *)
          raise (Failure "Unreachable: opaque type")
      | Result ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then [ ty ]
          else if variant_id = result_fail_id then [ mk_error_ty ]
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | Error ->
          assert (tys = []);
          let variant_id = Option.get variant_id in
          assert (
            variant_id = error_failure_id || variant_id = error_out_of_fuel_id);
          []
      | Fuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then []
          else if variant_id = fuel_succ_id then [ mk_fuel_ty ]
          else raise (Failure "Unreachable: improper variant id for fuel type")
      | Option ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = option_some_id then [ ty ]
          else if variant_id = option_none_id then []
          else
            raise (Failure "Unreachable: improper variant id for option type")
      | Range ->
          let ty = Collections.List.to_cons_nil tys in
          assert (variant_id = None);
          [ ty; ty ]
      | Vec | Array | Slice | Str ->
          (* Array: when not symbolic values (for instance, because of aggregates),
             the array expressions are introduced as struct updates *)
          raise (Failure "Attempting to access the fields of an opaque type"))

type tc_ctx = {
  type_decls : type_decl TypeDeclId.Map.t;  (** The type declarations *)
  global_decls : A.global_decl A.GlobalDeclId.Map.t;
      (** The global declarations *)
  env : ty VarId.Map.t;  (** Environment from variables to types *)
  const_generics : ty T.ConstGenericVarId.Map.t;
      (** The types of the const generics *)
}

let check_literal (v : literal) (ty : literal_type) : unit =
  match (ty, v) with
  | Integer int_ty, PV.Scalar sv -> assert (int_ty = sv.PV.int_ty)
  | Bool, Bool _ | Char, Char _ -> ()
  | _ -> raise (Failure "Inconsistent type")

let rec check_typed_pattern (ctx : tc_ctx) (v : typed_pattern) : tc_ctx =
  log#ldebug (lazy ("check_typed_pattern: " ^ show_typed_pattern v));
  match v.value with
  | PatConstant cv ->
      check_literal cv (ty_as_literal v.ty);
      ctx
  | PatDummy -> ctx
  | PatVar (var, _) ->
      assert (var.ty = v.ty);
      let env = VarId.Map.add var.id var.ty ctx.env in
      { ctx with env }
  | PatAdt av ->
      (* Compute the field types *)
      let type_id, tys, cgs = ty_as_adt v.ty in
      let field_tys =
        get_adt_field_types ctx.type_decls type_id av.variant_id tys cgs
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
  | CVar cg_id ->
      let ty = T.ConstGenericVarId.Map.find cg_id ctx.const_generics in
      assert (ty = e.ty)
  | Const cv -> check_literal cv (ty_as_literal e.ty)
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
      | FunOrOp _ -> () (* TODO *)
      | Global _ -> () (* TODO *)
      | Proj { adt_id = proj_adt_id; field_id } ->
          (* Note we can only project fields of structures (not enumerations) *)
          (* Deconstruct the projector type *)
          let adt_ty, field_ty = destruct_arrow e.ty in
          let adt_id, adt_type_args, adt_cg_args = ty_as_adt adt_ty in
          (* Check the ADT type *)
          assert (adt_id = proj_adt_id);
          assert (adt_type_args = qualif.type_args);
          assert (adt_cg_args = qualif.const_generic_args);
          (* Retrieve and check the expected field type *)
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types ctx.type_decls proj_adt_id variant_id
              qualif.type_args qualif.const_generic_args
          in
          let expected_field_ty = FieldId.nth expected_field_tys field_id in
          assert (expected_field_ty = field_ty)
      | AdtCons id -> (
          let expected_field_tys =
            get_adt_field_types ctx.type_decls id.adt_id id.variant_id
              qualif.type_args qualif.const_generic_args
          in
          let field_tys, adt_ty = destruct_arrows e.ty in
          assert (expected_field_tys = field_tys);
          match adt_ty with
          | Adt (type_id, tys, cgs) ->
              assert (type_id = id.adt_id);
              assert (tys = qualif.type_args);
              assert (cgs = qualif.const_generic_args)
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
          assert (scrut.ty = Literal Bool);
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
  | Loop loop ->
      assert (loop.fun_end.ty = e.ty);
      (* If we translate forward functions, the type of the loop is the same
         as the type of the parent expression - in case of backward functions,
         the loop doesn't necessarily give back the same values as the parent
         function
      *)
      assert (Option.is_some loop.back_output_tys || loop.loop_body.ty = e.ty);
      check_texpression ctx loop.fun_end;
      check_texpression ctx loop.loop_body
  | StructUpdate supd -> (
      (* Check the init value *)
      (if Option.is_some supd.init then
         match VarId.Map.find_opt (Option.get supd.init) ctx.env with
         | None -> ()
         | Some ty -> assert (ty = e.ty));
      (* Check the fields *)
      (* Retrieve and check the expected field type *)
      let adt_id, adt_type_args, adt_cg_args = ty_as_adt e.ty in
      assert (adt_id = supd.struct_id);
      (* The id can only be: a custom type decl or an array *)
      match adt_id with
      | AdtId _ ->
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types ctx.type_decls adt_id variant_id adt_type_args
              adt_cg_args
          in
          List.iter
            (fun (fid, fe) ->
              let expected_field_ty = FieldId.nth expected_field_tys fid in
              assert (expected_field_ty = fe.ty);
              check_texpression ctx fe)
            supd.updates
      | Assumed Array ->
          let expected_field_ty = Collections.List.to_cons_nil adt_type_args in
          List.iter
            (fun (_, fe) ->
              assert (expected_field_ty = fe.ty);
              check_texpression ctx fe)
            supd.updates
      | _ -> raise (Failure "Unexpected"))
  | Meta (_, e_next) ->
      assert (e_next.ty = e.ty);
      check_texpression ctx e_next
