(** This module defines printing functions for the types defined in Pure.ml *)

open Pure
open PureUtils
open Errors

(** The formatting context for pure definitions uses non-pure definitions
    to lookup names. The main reason is that when building the pure definitions
    like in [SymbolicToPure] we don't have a pure context available, while
    at every stage we have the original LLBC definitions at hand.
 *)
type fmt_env = {
  crate : LlbcAst.crate;
  (* We need a list of params because we have nested binding levels for trait methods. *)
  generics : generic_params list;
  vars : string VarId.Map.t;
}

let fmt_env_push_var (env : fmt_env) (var : var) : fmt_env =
  (* Only push the binding if the name is not [None] *)
  match var.basename with
  | None -> env
  | Some name -> { env with vars = VarId.Map.add var.id name env.vars }

let fmt_env_push_locals (env : fmt_env) (vars : var list) : fmt_env =
  List.fold_left fmt_env_push_var env vars

let var_id_to_pretty_string (id : var_id) : string = "^" ^ VarId.to_string id

let lookup_var_in_env (env : fmt_env)
    (find_in : generic_params -> 'id -> 'b option) (var : 'id de_bruijn_var) :
    'b option =
  if List.length env.generics == 0 then None
  else
    let dbid, varid =
      match var with
      | Bound (dbid, varid) -> (dbid, varid)
      | Free varid ->
          let len = List.length env.generics in
          let dbid = len - 1 in
          (dbid, varid)
    in
    match List.nth_opt env.generics dbid with
    | None -> None
    | Some generics -> begin
        match find_in generics varid with
        | None -> None
        | Some r -> Some r
      end

let type_db_var_to_string (env : fmt_env) (var : type_var_id de_bruijn_var) :
    string =
  (* Note that the types are not necessarily ordered following their indices *)
  let find (generics : generic_params) varid =
    List.find_opt (fun (v : type_var) -> v.index = varid) generics.types
  in
  match lookup_var_in_env env find var with
  | None -> Print.Types.type_db_var_to_pretty_string var
  | Some x -> Print.Types.type_var_to_string x

let const_generic_db_var_to_string (env : fmt_env)
    (var : const_generic_var_id de_bruijn_var) : string =
  let find (generics : generic_params) varid =
    List.find_opt
      (fun (v : const_generic_var) -> v.index = varid)
      generics.const_generics
  in
  match lookup_var_in_env env find var with
  | None -> Print.Types.const_generic_db_var_to_pretty_string var
  | Some x -> Print.Types.const_generic_var_to_string x

let var_id_to_string (env : fmt_env) (id : VarId.id) : string =
  match VarId.Map.find_opt id env.vars with
  | None -> var_id_to_pretty_string id
  | Some name -> name ^ "^" ^ VarId.to_string id

let trait_clause_id_to_string = Print.Types.trait_clause_id_to_string

let fmt_env_to_llbc_fmt_env (env : fmt_env) : Print.fmt_env =
  Charon.PrintLlbcAst.Crate.crate_to_fmt_env env.crate

let decls_ctx_to_fmt_env (ctx : Contexts.decls_ctx) : fmt_env =
  {
    crate = ctx.crate;
    generics = [ empty_generic_params ];
    vars = VarId.Map.empty;
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
let literal_type_to_string = Print.Values.literal_type_to_string
let type_var_to_string (v : type_var) = "(" ^ v.name ^ ": Type)"

let const_generic_var_to_string (v : const_generic_var) =
  "(" ^ v.name ^ " : " ^ literal_type_to_string v.ty ^ ")"

let integer_type_to_string = Print.Values.integer_type_to_string
let scalar_value_to_string = Print.Values.scalar_value_to_string
let literal_to_string = Print.Values.literal_to_string

let builtin_ty_to_string (aty : builtin_ty) : string =
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
  | TBuiltin aty -> builtin_ty_to_string aty

let const_generic_to_string (env : fmt_env) (cg : const_generic) : string =
  match cg with
  | CgGlobal id -> global_decl_id_to_string env id
  | CgVar var -> const_generic_db_var_to_string env var
  | CgValue lit -> literal_to_string lit

let rec ty_to_string (env : fmt_env) (inside : bool) (ty : ty) : string =
  match ty with
  | TAdt (id, generics) -> (
      match id with
      | TTuple ->
          let generics = generic_args_to_strings env false generics in
          "(" ^ String.concat " * " generics ^ ")"
      | TAdtId _ | TBuiltin _ ->
          let generics = generic_args_to_strings env true generics in
          let generics_s =
            if generics = [] then "" else " " ^ String.concat " " generics
          in
          let ty_s = type_id_to_string env id ^ generics_s in
          if generics <> [] && inside then "(" ^ ty_s ^ ")" else ty_s)
  | TVar tv -> type_db_var_to_string env tv
  | TLiteral lty -> literal_type_to_string lty
  | TArrow (arg_ty, ret_ty) ->
      let ty =
        ty_to_string env true arg_ty ^ " -> " ^ ty_to_string env false ret_ty
      in
      if inside then "(" ^ ty ^ ")" else ty
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = trait_ref_to_string env false trait_ref in
      let s = trait_ref ^ "::" ^ type_name in
      if inside then "(" ^ s ^ ")" else s
  | Error -> "@Error"

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
  let trait_id = trait_instance_id_to_string env tr.trait_id in
  let generics_are_empty =
    match tr.trait_id with
    | TraitImpl (_, generics) -> generics = empty_generic_args
    | _ -> true
  in
  if generics_are_empty || not inside then trait_id else "(" ^ trait_id ^ ")"

and trait_decl_ref_to_string (env : fmt_env) (inside : bool)
    (tr : trait_decl_ref) : string =
  let trait_id = trait_decl_id_to_string env tr.trait_decl_id in
  let generics = generic_args_to_string env tr.decl_generics in
  let space = if tr.decl_generics = empty_generic_args then "" else " " in
  if tr.decl_generics = empty_generic_args || not inside then
    trait_id ^ space ^ generics
  else "(" ^ trait_id ^ space ^ generics ^ ")"

and trait_instance_id_to_string (env : fmt_env) (id : trait_instance_id) :
    string =
  match id with
  | Self -> "Self"
  | TraitImpl (impl_id, generics) ->
      let generics = generic_args_to_string env generics in
      let impl_id = trait_impl_id_to_string env impl_id in
      impl_id ^ generics
  | Clause var -> Print.Types.trait_db_var_to_pretty_string var
  | ParentClause (inst_id, _decl_id, clause_id) ->
      let inst_id = trait_instance_id_to_string env inst_id in
      let clause_id = trait_clause_id_to_string env clause_id in
      "parent(" ^ inst_id ^ ")::" ^ clause_id
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

let trait_clause_to_string (env : fmt_env) (clause : trait_clause) : string =
  let trait_id = trait_decl_id_to_string env clause.trait_id in
  let generics = generic_args_to_strings env true clause.generics in
  let generics =
    if generics = [] then "" else " " ^ String.concat " " generics
  in
  trait_id ^ generics

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
  let env = { env with generics = [ def.generics ] } in
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

let mprojection_elem_to_string (env : fmt_env) (inside : string)
    (pe : mprojection_elem) : string =
  match pe.pkind with
  | E.ProjTuple _ -> "(" ^ inside ^ ")." ^ T.FieldId.to_string pe.field_id
  | E.ProjAdt (adt_id, opt_variant_id) -> (
      let field_name =
        match adt_field_to_string env adt_id opt_variant_id pe.field_id with
        | Some field_name -> field_name
        | None -> T.FieldId.to_string pe.field_id
      in
      match opt_variant_id with
      | None -> "(" ^ inside ^ ")." ^ field_name
      | Some variant_id ->
          let variant_name =
            adt_variant_from_type_decl_id_to_string env adt_id variant_id
          in
          "(" ^ inside ^ " as " ^ variant_name ^ ")." ^ field_name)

let rec mplace_to_string (env : fmt_env) (p : mplace) : string =
  match p with
  | PlaceBase (var_id, name) ->
      let name =
        match name with
        | None -> ""
        | Some name -> name
      in
      (* We add the "llbc" suffix to the variable index, because span-places
       * use indices of the variables in the original LLBC program, while
       * regular places use indices for the pure variables: we want to make
       * this explicit, otherwise it is confusing. *)
      name ^ "^" ^ E.VarId.to_string var_id ^ "llbc"
  | PlaceProjection (p, pe) ->
      let inside = mplace_to_string env p in
      mprojection_elem_to_string env inside pe

let adt_variant_to_string ?(span = None) (env : fmt_env) (adt_id : type_id)
    (variant_id : VariantId.id option) : string =
  match adt_id with
  | TTuple -> "Tuple"
  | TAdtId def_id -> (
      (* "Regular" ADT *)
      match variant_id with
      | Some vid -> adt_variant_from_type_decl_id_to_string env def_id vid
      | None -> type_decl_id_to_string env def_id)
  | TBuiltin aty -> (
      (* Builtin type *)
      match aty with
      | TState | TArray | TSlice | TStr | TRawPtr _ ->
          (* Those types are opaque: we can't get there *)
          craise_opt_span __FILE__ __LINE__ span "Unreachable"
      | TResult ->
          let variant_id = Option.get variant_id in
          if variant_id = result_ok_id then "@Result::Return"
          else if variant_id = result_fail_id then "@Result::Fail"
          else
            craise_opt_span __FILE__ __LINE__ span
              "Unreachable: improper variant id for result type"
      | TError ->
          let variant_id = Option.get variant_id in
          if variant_id = error_failure_id then "@Error::Failure"
          else if variant_id = error_out_of_fuel_id then "@Error::OutOfFuel"
          else
            craise_opt_span __FILE__ __LINE__ span
              "Unreachable: improper variant id for error type"
      | TFuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then "@Fuel::Zero"
          else if variant_id = fuel_succ_id then "@Fuel::Succ"
          else
            craise_opt_span __FILE__ __LINE__ span
              "Unreachable: improper variant id for fuel type")

let adt_field_to_string ?(span = None) (env : fmt_env) (adt_id : type_id)
    (field_id : FieldId.id) : string =
  match adt_id with
  | TTuple ->
      craise_opt_span __FILE__ __LINE__ span "Unreachable"
      (* Tuples don't use the opaque field id for the field indices, but [int] *)
  | TAdtId def_id -> (
      (* "Regular" ADT *)
      let fields = adt_field_names env def_id None in
      match fields with
      | None -> FieldId.to_string field_id
      | Some fields -> FieldId.nth fields field_id)
  | TBuiltin aty -> (
      (* Builtin type *)
      match aty with
      | TState | TFuel | TArray | TSlice | TStr ->
          (* Opaque types: we can't get there *)
          craise_opt_span __FILE__ __LINE__ span "Unreachable"
      | TResult | TError | TRawPtr _ ->
          (* Enumerations: we can't get there *)
          craise_opt_span __FILE__ __LINE__ span "Unreachable")

let rec typed_pattern_to_string_aux (span : Meta.span option) (env : fmt_env)
    (v : typed_pattern) : fmt_env * string =
  match v.value with
  | PatConstant cv -> (env, literal_to_string cv)
  | PatVar (v, None) -> (fmt_env_push_var env v, var_to_string env v)
  | PatVar (v, Some mp) ->
      let mp = "[@mplace=" ^ mplace_to_string env mp ^ "]" in
      let env = fmt_env_push_var env v in
      let s =
        "(" ^ var_to_varname v ^ " " ^ mp ^ " : "
        ^ ty_to_string env false v.ty
        ^ ")"
      in
      (env, s)
  | PatDummy -> (env, "_")
  | PatAdt av ->
      adt_pattern_to_string span env av.variant_id av.field_values v.ty

(* TODO: can't make the [span] parameter optional because OCaml infers its type
   to be [span option option]?? *)
and adt_pattern_to_string (span : Meta.span option) (env : fmt_env)
    (variant_id : VariantId.id option) (field_values : typed_pattern list)
    (ty : ty) : fmt_env * string =
  let env, field_values =
    List.fold_left_map (typed_pattern_to_string_aux span) env field_values
  in
  let s =
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
    | TAdt (TBuiltin aty, _) -> (
        (* Builtin type *)
        match aty with
        | TState | TRawPtr _ ->
            (* This type is opaque: we can't get there *)
            craise_opt_span __FILE__ __LINE__ span "Unreachable"
        | TResult ->
            let variant_id = Option.get variant_id in
            if variant_id = result_ok_id then
              match field_values with
              | [ v ] -> "@Result::Return " ^ v
              | _ ->
                  craise_opt_span __FILE__ __LINE__ span
                    "Result::Return takes exactly one value"
            else if variant_id = result_fail_id then
              match field_values with
              | [ v ] -> "@Result::Fail " ^ v
              | _ ->
                  craise_opt_span __FILE__ __LINE__ span
                    "Result::Fail takes exactly one value"
            else
              craise_opt_span __FILE__ __LINE__ span
                "Unreachable: improper variant id for result type"
        | TError ->
            cassert_opt_span __FILE__ __LINE__ (field_values = []) span
              "Ill-formed error value";
            let variant_id = Option.get variant_id in
            if variant_id = error_failure_id then "@Error::Failure"
            else if variant_id = error_out_of_fuel_id then "@Error::OutOfFuel"
            else
              craise_opt_span __FILE__ __LINE__ span
                "Unreachable: improper variant id for error type"
        | TFuel ->
            let variant_id = Option.get variant_id in
            if variant_id = fuel_zero_id then (
              cassert_opt_span __FILE__ __LINE__ (field_values = []) span
                "Ill-formed full value";
              "@Fuel::Zero")
            else if variant_id = fuel_succ_id then
              match field_values with
              | [ v ] -> "@Fuel::Succ " ^ v
              | _ ->
                  craise_opt_span __FILE__ __LINE__ span
                    "@Fuel::Succ takes exactly one value"
            else
              craise_opt_span __FILE__ __LINE__ span
                "Unreachable: improper variant id for fuel type"
        | TArray | TSlice | TStr ->
            cassert_opt_span __FILE__ __LINE__ (variant_id = None) span
              "Ill-formed value";
            let field_values =
              List.mapi (fun i v -> string_of_int i ^ " -> " ^ v) field_values
            in
            let id = builtin_ty_to_string aty in
            id ^ " [" ^ String.concat "; " field_values ^ "]")
    | _ ->
        craise_opt_span __FILE__ __LINE__ span
          ("Inconsistently typed value: expected ADT type but found:"
         ^ "\n- ty: " ^ ty_to_string env false ty ^ "\n- variant_id: "
          ^ Print.option_to_string VariantId.to_string variant_id)
  in
  (env, s)

let typed_pattern_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (v : typed_pattern) : string =
  snd (typed_pattern_to_string_aux span env v)

let back_sg_info_to_string (env : fmt_env) (info : back_sg_info) : string =
  let { inputs; inputs_no_state; outputs; output_names; effect_info; filter } =
    info
  in
  let input_to_string (n, ty) =
    (match n with
    | None -> ""
    | Some n -> n ^ ":")
    ^ ty_to_string env false ty
  in
  let inputs_to_string inputs =
    "[" ^ String.concat "," (List.map input_to_string inputs) ^ "]"
  in
  "{ inputs = " ^ inputs_to_string inputs ^ "; inputs_no_state = "
  ^ inputs_to_string inputs_no_state
  ^ "; outputs = ["
  ^ String.concat "," (List.map (ty_to_string env false) outputs)
  ^ "; output_names = ["
  ^ String.concat ","
      (List.map
         (function
           | None -> "_"
           | Some n -> n)
         output_names)
  ^ "; effect_info = "
  ^ show_fun_effect_info effect_info
  ^ "; filter = "
  ^ Print.bool_to_string filter
  ^ " }"

let decomposed_fun_type_to_string (env : fmt_env) (sg : decomposed_fun_type) :
    string =
  let { fwd_inputs; fwd_output; back_sg; fwd_info } = sg in
  "{\n  fwd_inputs = "
  ^ String.concat "," (List.map (ty_to_string env false) fwd_inputs)
  ^ ";\n  fwd_output = "
  ^ ty_to_string env false fwd_output
  ^ ";\n  back_sg = "
  ^ RegionGroupId.Map.to_string None (back_sg_info_to_string env) back_sg
  ^ ";\n  fwd_info = " ^ show_fun_sig_info fwd_info ^ "\n}"

let trait_type_constraint_to_string (env : fmt_env) (c : trait_type_constraint)
    : string =
  let { trait_ref; type_name; ty } = c in
  trait_ref_to_string env false trait_ref
  ^ "." ^ type_name ^ " = " ^ ty_to_string env false ty

let predicates_to_string (env : fmt_env) (preds : predicates) : string =
  let { trait_type_constraints } = preds in
  String.concat ","
    (List.map (trait_type_constraint_to_string env) trait_type_constraints)

let decomposed_fun_sig_to_string (env : fmt_env) (sg : decomposed_fun_sig) :
    string =
  let { generics; llbc_generics; preds; fun_ty } = sg in
  let llbc_generics =
    let env : _ Charon.PrintUtils.fmt_env =
      { crate = env.crate; generics = []; locals = [] }
    in
    let l0, l1 = Print.generic_params_to_strings env llbc_generics in
    "[" ^ String.concat "," (l0 @ l1) ^ "]"
  in
  "{\n  generics = ["
  ^ String.concat "," (generic_params_to_strings env generics)
  ^ "];\n  llbc_generics = ..." ^ llbc_generics ^ ";\n  preds = "
  ^ predicates_to_string env preds
  ^ ";\n  fun_ty = "
  ^ decomposed_fun_type_to_string env fun_ty
  ^ "\n}"

let fun_sig_to_string (env : fmt_env) (sg : fun_sig) : string =
  let env = { env with generics = [ sg.generics ] } in
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

let fun_suffix (lp_id : LoopId.id option) : string =
  let lp_suff =
    match lp_id with
    | None -> ""
    | Some lp_id -> "^loop" ^ LoopId.to_string lp_id
  in
  lp_suff

let llbc_builtin_fun_id_to_string (fid : A.builtin_fun_id) : string =
  Charon.PrintExpressions.builtin_fun_id_to_string fid

let llbc_fun_id_to_string (env : fmt_env) (fid : A.fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FBuiltin fid -> llbc_builtin_fun_id_to_string fid

let pure_builtin_fun_id_to_string (fid : pure_builtin_fun_id) : string =
  match fid with
  | Return -> "@return"
  | Fail -> "@fail"
  | Assert -> "@assert"
  | ToResult -> "@toResult"
  | FuelDecrease -> "@fuel_decrease"
  | FuelEqZero -> "@fuel_eq_zero"
  | UpdateAtIndex array_or_slice -> begin
      match array_or_slice with
      | Array -> "@ArrayUpdate"
      | Slice -> "@SliceUpdate"
    end

let regular_fun_id_to_string (env : fmt_env) (fun_id : fun_id) : string =
  match fun_id with
  | FromLlbc (fid, lp_id) ->
      let f =
        match fid with
        | FunId (FRegular fid) -> fun_decl_id_to_string env fid
        | FunId (FBuiltin fid) -> llbc_builtin_fun_id_to_string fid
        | TraitMethod (trait_ref, method_name, _) ->
            trait_ref_to_string env true trait_ref ^ "." ^ method_name
      in
      f ^ fun_suffix lp_id
  | Pure fid -> pure_builtin_fun_id_to_string fid

let unop_to_string (unop : unop) : string =
  match unop with
  | Not _ -> "¬"
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
let rec texpression_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (inside : bool) (indent : string) (indent_incr : string) (e : texpression) :
    string =
  match e.e with
  | Var var_id -> var_id_to_string env var_id
  | CVar cg_id -> const_generic_db_var_to_string env (Free cg_id)
  | Const cv -> literal_to_string cv
  | App _ ->
      (* Recursively destruct the app, to have a pair (app, arguments list) *)
      let app, args = destruct_apps e in
      (* Convert to string *)
      app_to_string ~span env inside indent indent_incr app args
  | Lambda _ ->
      let xl, e = destruct_lambdas e in
      let e = lambda_to_string ~span env indent indent_incr xl e in
      if inside then "(" ^ e ^ ")" else e
  | Qualif _ ->
      (* Qualifier without arguments *)
      app_to_string ~span env inside indent indent_incr e []
  | Let (monadic, lv, re, e) ->
      let e = let_to_string ~span env indent indent_incr monadic lv re e in
      if inside then "(" ^ e ^ ")" else e
  | Switch (scrutinee, body) ->
      let e = switch_to_string ~span env indent indent_incr scrutinee body in
      if inside then "(" ^ e ^ ")" else e
  | Loop loop ->
      let e = loop_to_string ~span env indent indent_incr loop in
      if inside then "(" ^ e ^ ")" else e
  | StructUpdate supd ->
      struct_update_to_string ~span env indent indent_incr supd
  | Meta (span', e) -> (
      let span_s = espan_to_string ~span env span' in
      let e = texpression_to_string ~span env inside indent indent_incr e in
      match span' with
      | Assignment _ | SymbolicAssignments _ | SymbolicPlaces _ | Tag _ ->
          let e = span_s ^ "\n" ^ indent ^ e in
          if inside then "(" ^ e ^ ")" else e
      | MPlace _ -> "(" ^ span_s ^ " " ^ e ^ ")")
  | EError (_, _) -> "@Error"

and app_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (inside : bool) (indent : string) (indent_incr : string) (app : texpression)
    (args : texpression list) : string =
  (* There are two possibilities: either the [app] is an instantiated,
   * top-level qualifier (function, ADT constructore...), or it is a "regular"
   * expression *)
  let app, generics =
    match app.e with
    | Qualif qualif -> (
        (* Qualifier case *)
        match qualif.id with
        | FunOrOp fun_id ->
            let generics = generic_args_to_strings env true qualif.generics in
            let qualif_s = fun_or_op_id_to_string env fun_id in
            (qualif_s, generics)
        | Global global_id ->
            let generics = generic_args_to_strings env true qualif.generics in
            (global_decl_id_to_string env global_id, generics)
        | AdtCons adt_cons_id ->
            let variant_s =
              adt_variant_to_string ~span env adt_cons_id.adt_id
                adt_cons_id.variant_id
            in
            (ConstStrings.constructor_prefix ^ variant_s, [])
        | Proj { adt_id; field_id } ->
            let adt_s = adt_variant_to_string ~span env adt_id None in
            let field_s = adt_field_to_string ~span env adt_id field_id in
            (* Adopting an F*-like syntax *)
            (ConstStrings.constructor_prefix ^ adt_s ^ "?." ^ field_s, [])
        | TraitConst (trait_ref, const_name) ->
            let trait_ref = trait_ref_to_string env true trait_ref in
            let qualif = trait_ref ^ "." ^ const_name in
            (qualif, []))
    | _ ->
        (* "Regular" expression case *)
        let inside = args <> [] || (args = [] && inside) in
        (texpression_to_string ~span env inside indent indent_incr app, [])
  in
  (* Convert the arguments.
   * The arguments are expressions, so indentation might get weird... (though
   * those expressions will in most cases just be values) *)
  let arg_to_string =
    let inside = true in
    let indent1 = indent ^ indent_incr in
    texpression_to_string ~span env inside indent1 indent_incr
  in
  let args = List.map arg_to_string args in
  let all_args = List.append generics args in
  (* Put together *)
  let e =
    if all_args = [] then app else app ^ " " ^ String.concat " " all_args
  in
  (* Add parentheses *)
  if all_args <> [] && inside then "(" ^ e ^ ")" else e

and lambda_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (indent : string) (indent_incr : string) (xl : typed_pattern list)
    (e : texpression) : string =
  let env, xl = List.fold_left_map (typed_pattern_to_string_aux span) env xl in
  let e = texpression_to_string ~span env false indent indent_incr e in
  "λ " ^ String.concat " " xl ^ ". " ^ e

and let_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (indent : string) (indent_incr : string) (monadic : bool)
    (lv : typed_pattern) (re : texpression) (e : texpression) : string =
  let indent1 = indent ^ indent_incr in
  let inside = false in
  let re = texpression_to_string ~span env inside indent1 indent_incr re in
  let env, lv = typed_pattern_to_string_aux span env lv in
  let e = texpression_to_string ~span env inside indent indent_incr e in
  if monadic then lv ^ " <-- " ^ re ^ ";\n" ^ indent ^ e
  else "let " ^ lv ^ " = " ^ re ^ " in\n" ^ indent ^ e

and switch_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (indent : string) (indent_incr : string) (scrutinee : texpression)
    (body : switch_body) : string =
  let indent1 = indent ^ indent_incr in
  (* Printing can mess up on the scrutinee, because it is an expression - but
   * in most situations it will be a value or a function call, so it should be
   * ok*)
  let scrut =
    texpression_to_string ~span env true indent1 indent_incr scrutinee
  in
  let e_to_string env =
    texpression_to_string ~span env false indent1 indent_incr
  in
  match body with
  | If (e_true, e_false) ->
      let e_true = e_to_string env e_true in
      let e_false = e_to_string env e_false in
      "if " ^ scrut ^ "\n" ^ indent ^ "then\n" ^ indent1 ^ e_true ^ "\n"
      ^ indent ^ "else\n" ^ indent1 ^ e_false
  | Match branches ->
      let branch_to_string (b : match_branch) : string =
        let env, pat = typed_pattern_to_string_aux span env b.pat in
        indent ^ "| " ^ pat ^ " ->\n" ^ indent1 ^ e_to_string env b.branch
      in
      let branches = List.map branch_to_string branches in
      "match " ^ scrut ^ " with\n" ^ String.concat "\n" branches

and struct_update_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (indent : string) (indent_incr : string) (supd : struct_update) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let s =
    match supd.init with
    | None -> ""
    | Some init ->
        " "
        ^ texpression_to_string ~span env false indent1 indent_incr init
        ^ " with"
  in
  (* The id should be a custom type decl id or an array *)
  match supd.struct_id with
  | TAdtId aid ->
      let field_names = Option.get (adt_field_names env aid None) in
      let fields =
        List.map
          (fun (fid, fe) ->
            let field = FieldId.nth field_names fid in
            let fe =
              texpression_to_string ~span env false indent2 indent_incr fe
            in
            "\n" ^ indent1 ^ field ^ " := " ^ fe ^ ";")
          supd.updates
      in
      let bl = if fields = [] then "" else "\n" ^ indent in
      "{" ^ s ^ String.concat "" fields ^ bl ^ "}"
  | TBuiltin TArray ->
      let fields =
        List.map
          (fun (_, fe) ->
            texpression_to_string ~span env false indent2 indent_incr fe)
          supd.updates
      in
      "[ " ^ String.concat ", " fields ^ " ]"
  | _ -> craise_opt_span __FILE__ __LINE__ span "Unexpected"

and loop_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (indent : string) (indent_incr : string) (loop : loop) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let loop_inputs =
    "fresh_vars: ["
    ^ String.concat "; " (List.map (var_to_string env) loop.inputs)
    ^ "]"
  in
  let output_ty = "output_ty: " ^ ty_to_string env false loop.output_ty in
  let fun_end =
    texpression_to_string ~span env false indent2 indent_incr loop.fun_end
  in
  let loop_body =
    texpression_to_string ~span env false indent2 indent_incr loop.loop_body
  in
  "loop {\n" ^ indent1 ^ loop_inputs ^ "\n" ^ indent1 ^ output_ty ^ "\n"
  ^ indent1 ^ "fun_end: {\n" ^ indent2 ^ fun_end ^ "\n" ^ indent1 ^ "}\n"
  ^ indent1 ^ "loop_body: {\n" ^ indent2 ^ loop_body ^ "\n" ^ indent1 ^ "}\n"
  ^ indent ^ "}"

and espan_to_string ?(span : Meta.span option = None) (env : fmt_env)
    (espan : espan) : string =
  let espan =
    match espan with
    | Assignment (lp, rv, rp) ->
        let rp =
          match rp with
          | None -> ""
          | Some rp -> " [@src=" ^ mplace_to_string env rp ^ "]"
        in
        "@assign(" ^ mplace_to_string env lp ^ " := "
        ^ texpression_to_string ~span env false "" "" rv
        ^ rp ^ ")"
    | SymbolicAssignments info ->
        let infos =
          List.map
            (fun (var_id, rv) ->
              VarId.to_string var_id ^ " == "
              ^ texpression_to_string ~span env false "" "" rv)
            info
        in
        let infos = String.concat ", " infos in
        "@symb_assign(" ^ infos ^ ")"
    | SymbolicPlaces info ->
        let infos =
          List.map
            (fun (var_id, name) ->
              VarId.to_string var_id ^ " == \"" ^ name ^ "\"")
            info
        in
        let infos = String.concat ", " infos in
        "@symb_places(" ^ infos ^ ")"
    | MPlace mp -> "@mplace=" ^ mplace_to_string env mp
    | Tag msg -> "@tag \"" ^ msg ^ "\""
  in
  "@span[" ^ espan ^ "]"

let fun_decl_to_string (env : fmt_env) (def : fun_decl) : string =
  let env = { env with generics = [ def.signature.generics ] } in
  let name = def.name ^ fun_suffix def.loop_id in
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
      let body =
        texpression_to_string ~span:(Some def.item_meta.span) env inside indent
          indent body.body
      in
      "let " ^ name ^ " :\n  " ^ signature ^ " =\n" ^ inputs ^ body
