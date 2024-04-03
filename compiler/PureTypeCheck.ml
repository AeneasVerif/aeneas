(** Module to perform type checking on the pure AST - we use this for sanity checks only *)

open Pure
open PureUtils
open Errors

(** Utility function, used for type checking.

    This function should only be used for "regular" ADTs, where the number
    of fields is fixed: it shouldn't be used for arrays, slices, etc.
 *)
let get_adt_field_types (meta : Meta.meta)
    (type_decls : type_decl TypeDeclId.Map.t) (type_id : type_id)
    (variant_id : VariantId.id option) (generics : generic_args) : ty list =
  match type_id with
  | TTuple ->
      (* Tuple *)
      sanity_check __FILE__ __LINE__ (generics.const_generics = []) meta;
      sanity_check __FILE__ __LINE__ (generics.trait_refs = []) meta;
      sanity_check __FILE__ __LINE__ (variant_id = None) meta;
      generics.types
  | TAdtId def_id ->
      (* "Regular" ADT *)
      let def = TypeDeclId.Map.find def_id type_decls in
      type_decl_get_instantiated_fields_types def variant_id generics
  | TAssumed aty -> (
      (* Assumed type *)
      match aty with
      | TState ->
          (* This type is opaque *)
          craise __FILE__ __LINE__ meta "Unreachable: opaque type"
      | TResult ->
          let ty = Collections.List.to_cons_nil generics.types in
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then [ ty ]
          else if variant_id = result_fail_id then [ mk_error_ty ]
          else
            craise __FILE__ __LINE__ meta
              "Unreachable: improper variant id for result type"
      | TError ->
          sanity_check __FILE__ __LINE__ (generics = empty_generic_args) meta;
          let variant_id = Option.get variant_id in
          sanity_check __FILE__ __LINE__
            (variant_id = error_failure_id || variant_id = error_out_of_fuel_id)
            meta;
          []
      | TFuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then []
          else if variant_id = fuel_succ_id then [ mk_fuel_ty ]
          else
            craise __FILE__ __LINE__ meta
              "Unreachable: improper variant id for fuel type"
      | TArray | TSlice | TStr | TRawPtr _ ->
          (* Array: when not symbolic values (for instance, because of aggregates),
             the array expressions are introduced as struct updates *)
          craise __FILE__ __LINE__ meta
            "Attempting to access the fields of an opaque type")

type tc_ctx = {
  type_decls : type_decl TypeDeclId.Map.t;  (** The type declarations *)
  global_decls : A.global_decl A.GlobalDeclId.Map.t;
      (** The global declarations *)
  env : ty VarId.Map.t;  (** Environment from variables to types *)
  const_generics : ty T.ConstGenericVarId.Map.t;
      (** The types of the const generics *)
      (* TODO: add trait type constraints *)
}

let check_literal (meta : Meta.meta) (v : literal) (ty : literal_type) : unit =
  match (ty, v) with
  | TInteger int_ty, VScalar sv ->
      sanity_check __FILE__ __LINE__ (int_ty = sv.int_ty) meta
  | TBool, VBool _ | TChar, VChar _ -> ()
  | _ -> craise __FILE__ __LINE__ meta "Inconsistent type"

let rec check_typed_pattern (meta : Meta.meta) (ctx : tc_ctx)
    (v : typed_pattern) : tc_ctx =
  log#ldebug (lazy ("check_typed_pattern: " ^ show_typed_pattern v));
  match v.value with
  | PatConstant cv ->
      check_literal meta cv (ty_as_literal meta v.ty);
      ctx
  | PatDummy -> ctx
  | PatVar (var, _) ->
      sanity_check __FILE__ __LINE__ (var.ty = v.ty) meta;
      let env = VarId.Map.add var.id var.ty ctx.env in
      { ctx with env }
  | PatAdt av ->
      (* Compute the field types *)
      let type_id, generics = ty_as_adt meta v.ty in
      let field_tys =
        get_adt_field_types meta ctx.type_decls type_id av.variant_id generics
      in
      let check_value (ctx : tc_ctx) (ty : ty) (v : typed_pattern) : tc_ctx =
        if ty <> v.ty then (
          (* TODO: we need to normalize the types *)
          log#serror
            ("check_typed_pattern: not the same types:" ^ "\n- ty: "
           ^ show_ty ty ^ "\n- v.ty: " ^ show_ty v.ty);
          craise __FILE__ __LINE__ meta "Inconsistent types");
        check_typed_pattern meta ctx v
      in
      (* Check the field types: check that the field patterns have the expected
       * types, and check that the field patterns themselves are well-typed *)
      List.fold_left
        (fun ctx (ty, v) -> check_value ctx ty v)
        ctx
        (List.combine field_tys av.field_values)

let rec check_texpression (meta : Meta.meta) (ctx : tc_ctx) (e : texpression) :
    unit =
  match e.e with
  | Var var_id -> (
      (* Lookup the variable - note that the variable may not be there,
       * if we type-check a subexpression (i.e.: if the variable is introduced
       * "outside" of the expression) - TODO: this won't happen once
       * we use a locally nameless representation *)
      match VarId.Map.find_opt var_id ctx.env with
      | None -> ()
      | Some ty -> sanity_check __FILE__ __LINE__ (ty = e.ty) meta)
  | CVar cg_id ->
      let ty = T.ConstGenericVarId.Map.find cg_id ctx.const_generics in
      sanity_check __FILE__ __LINE__ (ty = e.ty) meta
  | Const cv -> check_literal meta cv (ty_as_literal meta e.ty)
  | App (app, arg) ->
      let input_ty, output_ty = destruct_arrow meta app.ty in
      sanity_check __FILE__ __LINE__ (input_ty = arg.ty) meta;
      sanity_check __FILE__ __LINE__ (output_ty = e.ty) meta;
      check_texpression meta ctx app;
      check_texpression meta ctx arg
  | Lambda (pat, body) ->
      let pat_ty, body_ty = destruct_arrow meta e.ty in
      sanity_check __FILE__ __LINE__ (pat.ty = pat_ty) meta;
      sanity_check __FILE__ __LINE__ (body.ty = body_ty) meta;
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_typed_pattern meta ctx pat in
      check_texpression meta ctx body
  | Qualif qualif -> (
      match qualif.id with
      | FunOrOp _ -> () (* TODO *)
      | Global _ -> () (* TODO *)
      | TraitConst _ -> () (* TODO *)
      | Proj { adt_id = proj_adt_id; field_id } ->
          (* Note we can only project fields of structures (not enumerations) *)
          (* Deconstruct the projector type *)
          let adt_ty, field_ty = destruct_arrow meta e.ty in
          let adt_id, adt_generics = ty_as_adt meta adt_ty in
          (* Check the ADT type *)
          sanity_check __FILE__ __LINE__ (adt_id = proj_adt_id) meta;
          sanity_check __FILE__ __LINE__ (adt_generics = qualif.generics) meta;
          (* Retrieve and check the expected field type *)
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types meta ctx.type_decls proj_adt_id variant_id
              qualif.generics
          in
          let expected_field_ty = FieldId.nth expected_field_tys field_id in
          sanity_check __FILE__ __LINE__ (expected_field_ty = field_ty) meta
      | AdtCons id -> (
          let expected_field_tys =
            get_adt_field_types meta ctx.type_decls id.adt_id id.variant_id
              qualif.generics
          in
          let field_tys, adt_ty = destruct_arrows e.ty in
          sanity_check __FILE__ __LINE__ (expected_field_tys = field_tys) meta;
          match adt_ty with
          | TAdt (type_id, generics) ->
              sanity_check __FILE__ __LINE__ (type_id = id.adt_id) meta;
              sanity_check __FILE__ __LINE__ (generics = qualif.generics) meta
          | _ -> craise __FILE__ __LINE__ meta "Unreachable"))
  | Let (monadic, pat, re, e_next) ->
      let expected_pat_ty =
        if monadic then destruct_result meta re.ty else re.ty
      in
      sanity_check __FILE__ __LINE__ (pat.ty = expected_pat_ty) meta;
      sanity_check __FILE__ __LINE__ (e.ty = e_next.ty) meta;
      (* Check the right-expression *)
      check_texpression meta ctx re;
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_typed_pattern meta ctx pat in
      (* Check the next expression *)
      check_texpression meta ctx e_next
  | Switch (scrut, switch_body) -> (
      check_texpression meta ctx scrut;
      match switch_body with
      | If (e_then, e_else) ->
          sanity_check __FILE__ __LINE__ (scrut.ty = TLiteral TBool) meta;
          sanity_check __FILE__ __LINE__ (e_then.ty = e.ty) meta;
          sanity_check __FILE__ __LINE__ (e_else.ty = e.ty) meta;
          check_texpression meta ctx e_then;
          check_texpression meta ctx e_else
      | Match branches ->
          let check_branch (br : match_branch) : unit =
            sanity_check __FILE__ __LINE__ (br.pat.ty = scrut.ty) meta;
            let ctx = check_typed_pattern meta ctx br.pat in
            check_texpression meta ctx br.branch
          in
          List.iter check_branch branches)
  | Loop loop ->
      sanity_check __FILE__ __LINE__ (loop.fun_end.ty = e.ty) meta;
      check_texpression meta ctx loop.fun_end;
      check_texpression meta ctx loop.loop_body
  | StructUpdate supd -> (
      (* Check the init value *)
      (if Option.is_some supd.init then
         match VarId.Map.find_opt (Option.get supd.init) ctx.env with
         | None -> ()
         | Some ty -> sanity_check __FILE__ __LINE__ (ty = e.ty) meta);
      (* Check the fields *)
      (* Retrieve and check the expected field type *)
      let adt_id, adt_generics = ty_as_adt meta e.ty in
      sanity_check __FILE__ __LINE__ (adt_id = supd.struct_id) meta;
      (* The id can only be: a custom type decl or an array *)
      match adt_id with
      | TAdtId _ ->
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types meta ctx.type_decls adt_id variant_id
              adt_generics
          in
          List.iter
            (fun ((fid, fe) : _ * texpression) ->
              let expected_field_ty = FieldId.nth expected_field_tys fid in
              sanity_check __FILE__ __LINE__ (expected_field_ty = fe.ty) meta;
              check_texpression meta ctx fe)
            supd.updates
      | TAssumed TArray ->
          let expected_field_ty =
            Collections.List.to_cons_nil adt_generics.types
          in
          List.iter
            (fun ((_, fe) : _ * texpression) ->
              sanity_check __FILE__ __LINE__ (expected_field_ty = fe.ty) meta;
              check_texpression meta ctx fe)
            supd.updates
      | _ -> craise __FILE__ __LINE__ meta "Unexpected")
  | Meta (_, e_next) ->
      sanity_check __FILE__ __LINE__ (e_next.ty = e.ty) meta;
      check_texpression meta ctx e_next
  | EError (meta, msg) -> craise_opt_meta __FILE__ __LINE__ meta msg
