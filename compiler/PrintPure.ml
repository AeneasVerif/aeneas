(** This module defines printing functions for the types defined in Pure.ml *)

open Pure
open PureUtils

(** The formatting context for pure definitions uses non-pure definitions
    to lookup names. The main reason is that when building the pure definitions
    like in [SymbolicToPure] we don't have a pure context available, while
    at every stage we have the original LLBC definitions at hand.
 *)
type fmt_env = {
  type_decls : Types.type_decl TypeDeclId.Map.t;
  fun_decls : LlbcAst.fun_decl FunDeclId.Map.t;
  global_decls : LlbcAst.global_decl GlobalDeclId.Map.t;
  trait_decls : LlbcAst.trait_decl TraitDeclId.Map.t;
  trait_impls : LlbcAst.trait_impl TraitImplId.Map.t;
  generics : generic_params;
  locals : (VarId.id * string option) list;
}

let var_id_to_pretty_string (id : var_id) : string = "v@" ^ VarId.to_string id

let type_var_id_to_string (env : fmt_env) (id : type_var_id) : string =
  (* Note that the types are not necessarily ordered following their indices *)
  match
    List.find_opt (fun (x : type_var) -> x.index = id) env.generics.types
  with
  | None -> Print.Types.type_var_id_to_pretty_string id
  | Some x -> Print.Types.type_var_to_string x

let const_generic_var_id_to_string (env : fmt_env) (id : const_generic_var_id) :
    string =
  (* Note that the regions are not necessarily ordered following their indices *)
  match
    List.find_opt
      (fun (x : const_generic_var) -> x.index = id)
      env.generics.const_generics
  with
  | None -> Print.Types.const_generic_var_id_to_pretty_string id
  | Some x -> Print.Types.const_generic_var_to_string x

let var_id_to_string (env : fmt_env) (id : VarId.id) : string =
  match List.find_opt (fun (i, _) -> i = id) env.locals with
  | None -> var_id_to_pretty_string id
  | Some (_, name) -> (
      match name with
      | None -> var_id_to_pretty_string id
      | Some name -> name ^ "^" ^ VarId.to_string id)

let trait_clause_id_to_string = Print.Types.trait_clause_id_to_string

let fmt_env_to_llbc_fmt_env (env : fmt_env) : Print.fmt_env =
  {
    type_decls = env.type_decls;
    fun_decls = env.fun_decls;
    global_decls = env.global_decls;
    trait_decls = env.trait_decls;
    trait_impls = env.trait_impls;
    regions = [];
    types = [];
    const_generics = [];
    trait_clauses = [];
    preds = TypesUtils.empty_predicates;
    locals = [];
  }

let decls_ctx_to_fmt_env (ctx : Contexts.decls_ctx) : fmt_env =
  {
    type_decls = ctx.type_ctx.type_decls;
    fun_decls = ctx.fun_ctx.fun_decls;
    global_decls = ctx.global_ctx.global_decls;
    trait_decls = ctx.trait_decls_ctx.trait_decls;
    trait_impls = ctx.trait_impls_ctx.trait_impls;
    generics = empty_generic_params;
    locals = [];
  }

let name_to_string (env : fmt_env) =
  Print.Types.name_to_string (fmt_env_to_llbc_fmt_env env)

let type_decl_id_to_string (env : fmt_env) =
  Print.Types.type_decl_id_to_string (fmt_env_to_llbc_fmt_env env)

let global_decl_id_to_string (env : fmt_env) =
  Print.Types.global_decl_id_to_string (fmt_env_to_llbc_fmt_env env)

let fun_decl_id_to_string (env : fmt_env) =
  Print.Expressions.fun_decl_id_to_string (fmt_env_to_llbc_fmt_env env)

let trait_decl_id_to_string (env : fmt_env) =
  Print.Types.trait_decl_id_to_string (fmt_env_to_llbc_fmt_env env)

let trait_impl_id_to_string (env : fmt_env) =
  Print.Types.trait_impl_id_to_string (fmt_env_to_llbc_fmt_env env)

let adt_field_to_string (env : fmt_env) =
  Print.Types.adt_field_to_string (fmt_env_to_llbc_fmt_env env)

let adt_variant_from_type_decl_id_to_string (env : fmt_env) =
  Print.Types.adt_variant_to_string (fmt_env_to_llbc_fmt_env env)

let adt_field_names (env : fmt_env) =
  Print.Types.adt_field_names (fmt_env_to_llbc_fmt_env env)

let option_to_string = Print.option_to_string
let type_var_to_string = Print.Types.type_var_to_string
let const_generic_var_to_string = Print.Types.const_generic_var_to_string
let integer_type_to_string = Print.Values.integer_type_to_string
let literal_type_to_string = Print.Values.literal_type_to_string
let scalar_value_to_string = Print.Values.scalar_value_to_string
let literal_to_string = Print.Values.literal_to_string

let assumed_ty_to_string (aty : assumed_ty) : string =
  match aty with
  | TState -> "State"
  | TResult -> "Result"
  | TError -> "Error"
  | TFuel -> "Fuel"
  | TArray -> "Array"
  | TSlice -> "Slice"
  | TStr -> "Str"
  | TRawPtr Mut -> "MutRawPtr"
  | TRawPtr Const -> "ConstRawPtr"

let type_id_to_string (env : fmt_env) (id : type_id) : string =
  match id with
  | TAdtId id -> type_decl_id_to_string env id
  | TTuple -> ""
  | TAssumed aty -> assumed_ty_to_string aty

(* TODO: duplicates  Charon.PrintTypes.const_generic_to_string *)
let const_generic_to_string (env : fmt_env) (cg : const_generic) : string =
  match cg with
  | CgGlobal id -> global_decl_id_to_string env id
  | CgVar id -> const_generic_var_id_to_string env id
  | CgValue lit -> literal_to_string lit

let rec ty_to_string (env : fmt_env) (inside : bool) (ty : ty) : string =
  match ty with
  | TAdt (id, generics) -> (
      match id with
      | TTuple ->
          let generics = generic_args_to_strings env false generics in
          "(" ^ String.concat " * " generics ^ ")"
      | TAdtId _ | TAssumed _ ->
          let generics = generic_args_to_strings env true generics in
          let generics_s =
            if generics = [] then "" else " " ^ String.concat " " generics
          in
          let ty_s = type_id_to_string env id ^ generics_s in
          if generics <> [] && inside then "(" ^ ty_s ^ ")" else ty_s)
  | TVar tv -> type_var_id_to_string env tv
  | TLiteral lty -> literal_type_to_string lty
  | TArrow (arg_ty, ret_ty) ->
      let ty =
        ty_to_string env true arg_ty ^ " -> " ^ ty_to_string env false ret_ty
      in
      if inside then "(" ^ ty ^ ")" else ty
  | TTraitType (trait_ref, generics, type_name) ->
      let trait_ref = trait_ref_to_string env false trait_ref in
      let s =
        if generics = empty_generic_args then trait_ref ^ "::" ^ type_name
        else
          let generics = generic_args_to_string env generics in
          "(" ^ trait_ref ^ " " ^ generics ^ ")::" ^ type_name
      in
      if inside then "(" ^ s ^ ")" else s

and generic_args_to_strings (env : fmt_env) (inside : bool)
    (generics : generic_args) : string list =
  let tys = List.map (ty_to_string env inside) generics.types in
  let cgs = List.map (const_generic_to_string env) generics.const_generics in
  let trait_refs =
    List.map (trait_ref_to_string env inside) generics.trait_refs
  in
  List.concat [ tys; cgs; trait_refs ]

and generic_args_to_string (env : fmt_env) (generics : generic_args) : string =
  String.concat " " (generic_args_to_strings env true generics)

and trait_ref_to_string (env : fmt_env) (inside : bool) (tr : trait_ref) :
    string =
  let trait_id = trait_instance_id_to_string env false tr.trait_id in
  let generics = generic_args_to_string env tr.generics in
  let s = trait_id ^ generics in
  if tr.generics = empty_generic_args || not inside then s else "(" ^ s ^ ")"

and trait_instance_id_to_string (env : fmt_env) (inside : bool)
    (id : trait_instance_id) : string =
  match id with
  | Self -> "Self"
  | TraitImpl id -> trait_impl_id_to_string env id
  | Clause id -> trait_clause_id_to_string env id
  | ParentClause (inst_id, _decl_id, clause_id) ->
      let inst_id = trait_instance_id_to_string env false inst_id in
      let clause_id = trait_clause_id_to_string env clause_id in
      "parent(" ^ inst_id ^ ")::" ^ clause_id
  | ItemClause (inst_id, _decl_id, item_name, clause_id) ->
      let inst_id = trait_instance_id_to_string env false inst_id in
      let clause_id = trait_clause_id_to_string env clause_id in
      "(" ^ inst_id ^ ")::" ^ item_name ^ "::[" ^ clause_id ^ "]"
  | TraitRef tr -> trait_ref_to_string env inside tr
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

let trait_clause_to_string (env : fmt_env) (clause : trait_clause) : string =
  let clause_id = trait_clause_id_to_string env clause.clause_id in
  let trait_id = trait_decl_id_to_string env clause.trait_id in
  let generics = generic_args_to_strings env true clause.generics in
  let generics =
    if generics = [] then "" else " " ^ String.concat " " generics
  in
  "[" ^ clause_id ^ "]: " ^ trait_id ^ generics

let generic_params_to_strings (env : fmt_env) (generics : generic_params) :
    string list =
  let tys = List.map type_var_to_string generics.types in
  let cgs = List.map const_generic_var_to_string generics.const_generics in
  let trait_clauses =
    List.map (trait_clause_to_string env) generics.trait_clauses
  in
  List.concat [ tys; cgs; trait_clauses ]

let field_to_string env inside (f : field) : string =
  match f.field_name with
  | None -> ty_to_string env inside f.field_ty
  | Some field_name ->
      let s = field_name ^ " : " ^ ty_to_string env false f.field_ty in
      if inside then "(" ^ s ^ ")" else s

let variant_to_string env (v : variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string env false) v.fields)
  ^ ")"

let type_decl_to_string (env : fmt_env) (def : type_decl) : string =
  let env = { env with generics = def.generics } in
  let name = def.name in
  let params =
    if def.generics = empty_generic_params then ""
    else " " ^ String.concat " " (generic_params_to_strings env def.generics)
  in
  match def.kind with
  | Struct fields ->
      if List.length fields > 0 then
        let fields =
          String.concat ","
            (List.map (fun f -> "\n  " ^ field_to_string env false f) fields)
        in
        "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
      else "struct " ^ name ^ params ^ "{}"
  | Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string env v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ " =\n" ^ variants
  | Opaque -> "opaque type " ^ name ^ params

let var_to_varname (v : var) : string =
  match v.basename with
  | Some name -> name ^ "^" ^ VarId.to_string v.id
  | None -> "^" ^ VarId.to_string v.id

let var_to_string (env : fmt_env) (v : var) : string =
  let varname = var_to_varname v in
  "(" ^ varname ^ " : " ^ ty_to_string env false v.ty ^ ")"

let rec mprojection_to_string (env : fmt_env) (inside : string)
    (p : mprojection) : string =
  match p with
  | [] -> inside
  | pe :: p' -> (
      let s = mprojection_to_string env inside p' in
      match pe.pkind with
      | E.ProjTuple _ -> "(" ^ s ^ ")." ^ T.FieldId.to_string pe.field_id
      | E.ProjAdt (adt_id, opt_variant_id) -> (
          let field_name =
            match adt_field_to_string env adt_id opt_variant_id pe.field_id with
            | Some field_name -> field_name
            | None -> T.FieldId.to_string pe.field_id
          in
          match opt_variant_id with
          | None -> "(" ^ s ^ ")." ^ field_name
          | Some variant_id ->
              let variant_name =
                adt_variant_from_type_decl_id_to_string env adt_id variant_id
              in
              "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name))

let mplace_to_string (env : fmt_env) (p : mplace) : string =
  let name = match p.name with None -> "" | Some name -> name in
  (* We add the "llbc" suffix to the variable index, because meta-places
   * use indices of the variables in the original LLBC program, while
   * regular places use indices for the pure variables: we want to make
   * this explicit, otherwise it is confusing. *)
  let name = name ^ "^" ^ E.VarId.to_string p.var_id ^ "llbc" in
  mprojection_to_string env name p.projection

let adt_variant_to_string (env : fmt_env) (adt_id : type_id)
    (variant_id : VariantId.id option) : string =
  match adt_id with
  | TTuple -> "Tuple"
  | TAdtId def_id -> (
      (* "Regular" ADT *)
      match variant_id with
      | Some vid -> adt_variant_from_type_decl_id_to_string env def_id vid
      | None -> type_decl_id_to_string env def_id)
  | TAssumed aty -> (
      (* Assumed type *)
      match aty with
      | TState | TArray | TSlice | TStr | TRawPtr _ ->
          (* Those types are opaque: we can't get there *)
          raise (Failure "Unreachable")
      | TResult ->
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then "@Result::Return"
          else if variant_id = result_fail_id then "@Result::Fail"
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | TError ->
          let variant_id = Option.get variant_id in
          if variant_id = error_failure_id then "@Error::Failure"
          else if variant_id = error_out_of_fuel_id then "@Error::OutOfFuel"
          else raise (Failure "Unreachable: improper variant id for error type")
      | TFuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then "@Fuel::Zero"
          else if variant_id = fuel_succ_id then "@Fuel::Succ"
          else raise (Failure "Unreachable: improper variant id for fuel type"))

let adt_field_to_string (env : fmt_env) (adt_id : type_id)
    (field_id : FieldId.id) : string =
  match adt_id with
  | TTuple ->
      raise (Failure "Unreachable")
      (* Tuples don't use the opaque field id for the field indices, but [int] *)
  | TAdtId def_id -> (
      (* "Regular" ADT *)
      let fields = adt_field_names env def_id None in
      match fields with
      | None -> FieldId.to_string field_id
      | Some fields -> FieldId.nth fields field_id)
  | TAssumed aty -> (
      (* Assumed type *)
      match aty with
      | TState | TFuel | TArray | TSlice | TStr ->
          (* Opaque types: we can't get there *)
          raise (Failure "Unreachable")
      | TResult | TError | TRawPtr _ ->
          (* Enumerations: we can't get there *)
          raise (Failure "Unreachable"))

(** TODO: we don't need a general function anymore (it is now only used for
    patterns)
 *)
let adt_g_value_to_string (env : fmt_env) (value_to_string : 'v -> string)
    (variant_id : VariantId.id option) (field_values : 'v list) (ty : ty) :
    string =
  let field_values = List.map value_to_string field_values in
  match ty with
  | TAdt (TTuple, _) ->
      (* Tuple *)
      "(" ^ String.concat ", " field_values ^ ")"
  | TAdt (TAdtId def_id, _) ->
      (* "Regular" ADT *)
      let adt_ident =
        match variant_id with
        | Some vid -> adt_variant_from_type_decl_id_to_string env def_id vid
        | None -> type_decl_id_to_string env def_id
      in
      if field_values <> [] then
        match adt_field_names env def_id variant_id with
        | None ->
            let field_values = String.concat ", " field_values in
            adt_ident ^ " (" ^ field_values ^ ")"
        | Some field_names ->
            let field_values = List.combine field_names field_values in
            let field_values =
              List.map
                (fun (field, value) -> field ^ " = " ^ value ^ ";")
                field_values
            in
            let field_values = String.concat " " field_values in
            adt_ident ^ " { " ^ field_values ^ " }"
      else adt_ident
  | TAdt (TAssumed aty, _) -> (
      (* Assumed type *)
      match aty with
      | TState | TRawPtr _ ->
          (* This type is opaque: we can't get there *)
          raise (Failure "Unreachable")
      | TResult ->
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then
            match field_values with
            | [ v ] -> "@Result::Return " ^ v
            | _ -> raise (Failure "Result::Return takes exactly one value")
          else if variant_id = result_fail_id then
            match field_values with
            | [ v ] -> "@Result::Fail " ^ v
            | _ -> raise (Failure "Result::Fail takes exactly one value")
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | TError ->
          assert (field_values = []);
          let variant_id = Option.get variant_id in
          if variant_id = error_failure_id then "@Error::Failure"
          else if variant_id = error_out_of_fuel_id then "@Error::OutOfFuel"
          else raise (Failure "Unreachable: improper variant id for error type")
      | TFuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then (
            assert (field_values = []);
            "@Fuel::Zero")
          else if variant_id = fuel_succ_id then
            match field_values with
            | [ v ] -> "@Fuel::Succ " ^ v
            | _ -> raise (Failure "@Fuel::Succ takes exactly one value")
          else raise (Failure "Unreachable: improper variant id for fuel type")
      | TArray | TSlice | TStr ->
          assert (variant_id = None);
          let field_values =
            List.mapi (fun i v -> string_of_int i ^ " -> " ^ v) field_values
          in
          let id = assumed_ty_to_string aty in
          id ^ " [" ^ String.concat "; " field_values ^ "]")
  | _ ->
      raise
        (Failure
           ("Inconsistently typed value: expected ADT type but found:"
          ^ "\n- ty: " ^ ty_to_string env false ty ^ "\n- variant_id: "
           ^ Print.option_to_string VariantId.to_string variant_id))

let rec typed_pattern_to_string (env : fmt_env) (v : typed_pattern) : string =
  match v.value with
  | PatConstant cv -> literal_to_string cv
  | PatVar (v, None) -> var_to_string env v
  | PatVar (v, Some mp) ->
      let mp = "[@mplace=" ^ mplace_to_string env mp ^ "]" in
      "(" ^ var_to_varname v ^ " " ^ mp ^ " : "
      ^ ty_to_string env false v.ty
      ^ ")"
  | PatDummy -> "_"
  | PatAdt av ->
      adt_g_value_to_string env
        (typed_pattern_to_string env)
        av.variant_id av.field_values v.ty

let fun_sig_to_string (env : fmt_env) (sg : fun_sig) : string =
  let env = { env with generics = sg.generics } in
  let generics = generic_params_to_strings env sg.generics in
  let inputs = List.map (ty_to_string env false) sg.inputs in
  let output = ty_to_string env false sg.output in
  let all_types = List.concat [ generics; inputs; [ output ] ] in
  String.concat " -> " all_types

let inst_fun_sig_to_string (env : fmt_env) (sg : inst_fun_sig) : string =
  let inputs = List.map (ty_to_string env false) sg.inputs in
  let output = ty_to_string env false sg.output in
  let all_types = List.append inputs [ output ] in
  String.concat " -> " all_types

let fun_suffix (lp_id : LoopId.id option) (rg_id : T.RegionGroupId.id option) :
    string =
  let lp_suff =
    match lp_id with
    | None -> ""
    | Some lp_id -> "^loop" ^ LoopId.to_string lp_id
  in

  let rg_suff =
    match rg_id with
    | None -> ""
    | Some rg_id -> "@" ^ T.RegionGroupId.to_string rg_id
  in

  lp_suff ^ rg_suff

let llbc_assumed_fun_id_to_string (fid : A.assumed_fun_id) : string =
  match fid with
  | BoxNew -> "alloc::boxed::Box::new"
  | BoxFree -> "alloc::alloc::box_free"
  | ArrayIndexShared -> "@ArrayIndexShared"
  | ArrayIndexMut -> "@ArrayIndexMut"
  | ArrayToSliceShared -> "@ArrayToSliceShared"
  | ArrayToSliceMut -> "@ArrayToSliceMut"
  | ArrayRepeat -> "@ArrayRepeat"
  | SliceIndexShared -> "@SliceIndexShared"
  | SliceIndexMut -> "@SliceIndexMut"

let llbc_fun_id_to_string (env : fmt_env) (fid : A.fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FAssumed fid -> llbc_assumed_fun_id_to_string fid

let pure_assumed_fun_id_to_string (fid : pure_assumed_fun_id) : string =
  match fid with
  | Return -> "return"
  | Fail -> "fail"
  | Assert -> "assert"
  | FuelDecrease -> "fuel_decrease"
  | FuelEqZero -> "fuel_eq_zero"

let regular_fun_id_to_string (env : fmt_env) (fun_id : fun_id) : string =
  match fun_id with
  | FromLlbc (fid, lp_id, rg_id) ->
      let f =
        match fid with
        | FunId (FRegular fid) -> fun_decl_id_to_string env fid
        | FunId (FAssumed fid) -> llbc_assumed_fun_id_to_string fid
        | TraitMethod (trait_ref, method_name, _) ->
            trait_ref_to_string env true trait_ref ^ "." ^ method_name
      in
      f ^ fun_suffix lp_id rg_id
  | Pure fid -> pure_assumed_fun_id_to_string fid

let unop_to_string (unop : unop) : string =
  match unop with
  | Not -> "¬"
  | Neg _ -> "-"
  | Cast (src, tgt) ->
      "cast<" ^ literal_type_to_string src ^ "," ^ literal_type_to_string tgt
      ^ ">"

let binop_to_string = Print.Expressions.binop_to_string

let fun_or_op_id_to_string (env : fmt_env) (fun_id : fun_or_op_id) : string =
  match fun_id with
  | Fun fun_id -> regular_fun_id_to_string env fun_id
  | Unop unop -> unop_to_string unop
  | Binop (binop, int_ty) ->
      binop_to_string binop ^ "<" ^ integer_type_to_string int_ty ^ ">"

(** [inside]: controls the introduction of parentheses *)
let rec texpression_to_string (env : fmt_env) (inside : bool) (indent : string)
    (indent_incr : string) (e : texpression) : string =
  match e.e with
  | Var var_id -> var_id_to_string env var_id
  | CVar cg_id -> const_generic_var_id_to_string env cg_id
  | Const cv -> literal_to_string cv
  | App _ ->
      (* Recursively destruct the app, to have a pair (app, arguments list) *)
      let app, args = destruct_apps e in
      (* Convert to string *)
      app_to_string env inside indent indent_incr app args
  | Lambda _ ->
      let xl, e = destruct_lambdas e in
      let e = lambda_to_string env indent indent_incr xl e in
      if inside then "(" ^ e ^ ")" else e
  | Qualif _ ->
      (* Qualifier without arguments *)
      app_to_string env inside indent indent_incr e []
  | Let (monadic, lv, re, e) ->
      let e = let_to_string env indent indent_incr monadic lv re e in
      if inside then "(" ^ e ^ ")" else e
  | Switch (scrutinee, body) ->
      let e = switch_to_string env indent indent_incr scrutinee body in
      if inside then "(" ^ e ^ ")" else e
  | Loop loop ->
      let e = loop_to_string env indent indent_incr loop in
      if inside then "(" ^ e ^ ")" else e
  | StructUpdate supd -> (
      let s =
        match supd.init with
        | None -> ""
        | Some vid -> " " ^ var_id_to_string env vid ^ " with"
      in
      let indent1 = indent ^ indent_incr in
      let indent2 = indent1 ^ indent_incr in
      (* The id should be a custom type decl id or an array *)
      match supd.struct_id with
      | TAdtId aid ->
          let field_names = Option.get (adt_field_names env aid None) in
          let fields =
            List.map
              (fun (fid, fe) ->
                let field = FieldId.nth field_names fid in
                let fe =
                  texpression_to_string env false indent2 indent_incr fe
                in
                "\n" ^ indent1 ^ field ^ " := " ^ fe ^ ";")
              supd.updates
          in
          let bl = if fields = [] then "" else "\n" ^ indent in
          "{" ^ s ^ String.concat "" fields ^ bl ^ "}"
      | TAssumed TArray ->
          let fields =
            List.map
              (fun (_, fe) ->
                texpression_to_string env false indent2 indent_incr fe)
              supd.updates
          in
          "[ " ^ String.concat ", " fields ^ " ]"
      | _ -> raise (Failure "Unexpected"))
  | Meta (meta, e) -> (
      let meta_s = emeta_to_string env meta in
      let e = texpression_to_string env inside indent indent_incr e in
      match meta with
      | Assignment _ | SymbolicAssignment _ | Tag _ ->
          let e = meta_s ^ "\n" ^ indent ^ e in
          if inside then "(" ^ e ^ ")" else e
      | MPlace _ -> "(" ^ meta_s ^ " " ^ e ^ ")")

and app_to_string (env : fmt_env) (inside : bool) (indent : string)
    (indent_incr : string) (app : texpression) (args : texpression list) :
    string =
  (* There are two possibilities: either the [app] is an instantiated,
   * top-level qualifier (function, ADT constructore...), or it is a "regular"
   * expression *)
  let app, generics =
    match app.e with
    | Qualif qualif ->
        (* Qualifier case *)
        (* Convert the qualifier identifier *)
        let qualif_s =
          match qualif.id with
          | FunOrOp fun_id -> fun_or_op_id_to_string env fun_id
          | Global global_id -> global_decl_id_to_string env global_id
          | AdtCons adt_cons_id ->
              let variant_s =
                adt_variant_to_string env adt_cons_id.adt_id
                  adt_cons_id.variant_id
              in
              ConstStrings.constructor_prefix ^ variant_s
          | Proj { adt_id; field_id } ->
              let adt_s = adt_variant_to_string env adt_id None in
              let field_s = adt_field_to_string env adt_id field_id in
              (* Adopting an F*-like syntax *)
              ConstStrings.constructor_prefix ^ adt_s ^ "?." ^ field_s
          | TraitConst (trait_ref, generics, const_name) ->
              let trait_ref = trait_ref_to_string env true trait_ref in
              let generics_s = generic_args_to_string env generics in
              if generics <> empty_generic_args then
                "(" ^ trait_ref ^ generics_s ^ ")." ^ const_name
              else trait_ref ^ "." ^ const_name
        in
        (* Convert the type instantiation *)
        let generics = generic_args_to_strings env true qualif.generics in
        (* *)
        (qualif_s, generics)
    | _ ->
        (* "Regular" expression case *)
        let inside = args <> [] || (args = [] && inside) in
        (texpression_to_string env inside indent indent_incr app, [])
  in
  (* Convert the arguments.
   * The arguments are expressions, so indentation might get weird... (though
   * those expressions will in most cases just be values) *)
  let arg_to_string =
    let inside = true in
    let indent1 = indent ^ indent_incr in
    texpression_to_string env inside indent1 indent_incr
  in
  let args = List.map arg_to_string args in
  let all_args = List.append generics args in
  (* Put together *)
  let e =
    if all_args = [] then app else app ^ " " ^ String.concat " " all_args
  in
  (* Add parentheses *)
  if all_args <> [] && inside then "(" ^ e ^ ")" else e

and lambda_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (xl : typed_pattern list) (e : texpression) : string =
  let xl = List.map (typed_pattern_to_string env) xl in
  let e = texpression_to_string env false indent indent_incr e in
  "λ " ^ String.concat " " xl ^ ". " ^ e

and let_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (monadic : bool) (lv : typed_pattern) (re : texpression) (e : texpression) :
    string =
  let indent1 = indent ^ indent_incr in
  let inside = false in
  let re = texpression_to_string env inside indent1 indent_incr re in
  let e = texpression_to_string env inside indent indent_incr e in
  let lv = typed_pattern_to_string env lv in
  if monadic then lv ^ " <-- " ^ re ^ ";\n" ^ indent ^ e
  else "let " ^ lv ^ " = " ^ re ^ " in\n" ^ indent ^ e

and switch_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (scrutinee : texpression) (body : switch_body) : string =
  let indent1 = indent ^ indent_incr in
  (* Printing can mess up on the scrutinee, because it is an expression - but
   * in most situations it will be a value or a function call, so it should be
   * ok*)
  let scrut = texpression_to_string env true indent1 indent_incr scrutinee in
  let e_to_string = texpression_to_string env false indent1 indent_incr in
  match body with
  | If (e_true, e_false) ->
      let e_true = e_to_string e_true in
      let e_false = e_to_string e_false in
      "if " ^ scrut ^ "\n" ^ indent ^ "then\n" ^ indent1 ^ e_true ^ "\n"
      ^ indent ^ "else\n" ^ indent1 ^ e_false
  | Match branches ->
      let branch_to_string (b : match_branch) : string =
        let pat = typed_pattern_to_string env b.pat in
        indent ^ "| " ^ pat ^ " ->\n" ^ indent1 ^ e_to_string b.branch
      in
      let branches = List.map branch_to_string branches in
      "match " ^ scrut ^ " with\n" ^ String.concat "\n" branches

and loop_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (loop : loop) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let loop_inputs =
    "fresh_vars: ["
    ^ String.concat "; " (List.map (var_to_string env) loop.inputs)
    ^ "]"
  in
  let back_output_tys =
    let tys =
      match loop.back_output_tys with
      | None -> ""
      | Some tys -> String.concat "; " (List.map (ty_to_string env false) tys)
    in
    "back_output_tys: [" ^ tys ^ "]"
  in
  let fun_end =
    texpression_to_string env false indent2 indent_incr loop.fun_end
  in
  let loop_body =
    texpression_to_string env false indent2 indent_incr loop.loop_body
  in
  "loop {\n" ^ indent1 ^ loop_inputs ^ "\n" ^ indent1 ^ back_output_tys ^ "\n"
  ^ indent1 ^ "fun_end: {\n" ^ indent2 ^ fun_end ^ "\n" ^ indent1 ^ "}\n"
  ^ indent1 ^ "loop_body: {\n" ^ indent2 ^ loop_body ^ "\n" ^ indent1 ^ "}\n"
  ^ indent ^ "}"

and emeta_to_string (env : fmt_env) (meta : emeta) : string =
  let meta =
    match meta with
    | Assignment (lp, rv, rp) ->
        let rp =
          match rp with
          | None -> ""
          | Some rp -> " [@src=" ^ mplace_to_string env rp ^ "]"
        in
        "@assign(" ^ mplace_to_string env lp ^ " := "
        ^ texpression_to_string env false "" "" rv
        ^ rp ^ ")"
    | SymbolicAssignment (var_id, rv) ->
        "@symb_assign(" ^ VarId.to_string var_id ^ " := "
        ^ texpression_to_string env false "" "" rv
        ^ ")"
    | MPlace mp -> "@mplace=" ^ mplace_to_string env mp
    | Tag msg -> "@tag \"" ^ msg ^ "\""
  in
  "@meta[" ^ meta ^ "]"

let fun_decl_to_string (env : fmt_env) (def : fun_decl) : string =
  let env = { env with generics = def.signature.generics } in
  let name = def.name ^ fun_suffix def.loop_id def.back_id in
  let signature = fun_sig_to_string env def.signature in
  match def.body with
  | None -> "val " ^ name ^ " :\n  " ^ signature
  | Some body ->
      let inside = false in
      let indent = "  " in
      let inputs = List.map (var_to_string env) body.inputs in
      let inputs =
        if inputs = [] then indent
        else "  fun " ^ String.concat " " inputs ^ " ->\n" ^ indent
      in
      let body = texpression_to_string env inside indent indent body.body in
      "let " ^ name ^ " :\n  " ^ signature ^ " =\n" ^ inputs ^ body
