(** Functions to load CFIM ASTs from json.

    Initially, we used `ppx_derive_yojson` to automate this.
    However, `ppx_derive_yojson` expects formatting to be slightly
    different from what `serde_rs` generates (because it uses [Yojson.Safe.t]
    and not [Yojson.Basic.t]).

    TODO: we should check that the integer values are in the proper range
 *)

open Yojson.Basic
open Identifiers
open Types

type json = t

let ( let* ) o f = match o with Error e -> Error e | Ok x -> f x

let combine_error_msgs js msg res : ('a, string) result =
  match res with
  | Ok x -> Ok x
  | Error e -> Error (msg ^ " failed on: " ^ show js ^ "\n" ^ e)

let bool_of_json (js : json) : (bool, string) result =
  match js with
  | `Bool b -> Ok b
  | _ -> Error ("bool_of_json: not a bool: " ^ show js)

let int_of_json (js : json) : (int, string) result =
  match js with
  | `Int i -> Ok i
  | _ -> Error ("int_of_json: not an int: " ^ show js)

let char_of_json (_js : json) : (char, string) result =
  (* TODO: implement *)
  Error "char_of_json: unimplemented"

let rec of_json_list (a_of_json : json -> ('a, string) result) (jsl : json list)
    : ('a list, string) result =
  match jsl with
  | [] -> Ok []
  | x :: jsl' ->
      let* x = a_of_json x in
      let* jsl' = of_json_list a_of_json jsl' in
      Ok (x :: jsl')

let pair_of_json (a_of_json : json -> ('a, string) result)
    (b_of_json : json -> ('b, string) result) (js : json) :
    ('a * 'b, string) result =
  match js with
  | `List [ a; b ] ->
      let* a = a_of_json a in
      let* b = b_of_json b in
      Ok (a, b)
  | _ -> Error ("pair_of_json failed on: " ^ show js)

let list_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a list, string) result =
  combine_error_msgs js "list_of_json"
    (match js with
    | `List jsl -> of_json_list a_of_json jsl
    | _ -> Error ("not a list: " ^ show js))

let string_of_json (js : json) : (string, string) result =
  match js with
  | `String str -> Ok str
  | _ -> Error ("string_of_json: not a string: " ^ show js)

let option_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a option, string) result =
  combine_error_msgs js "option_of_json"
    (match js with
    | `Null -> Ok None
    | _ ->
        let* x = a_of_json js in
        Ok (Some x))

let string_option_of_json (js : json) : (string option, string) result =
  combine_error_msgs js "string_option_of_json"
    (option_of_json string_of_json js)

let name_of_json (js : json) : (name, string) result =
  combine_error_msgs js "name_of_json" (list_of_json string_of_json js)

let type_var_of_json (js : json) : (type_var, string) result =
  combine_error_msgs js "type_var_of_json"
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = TypeVarId.id_of_json index in
        let* name = string_of_json name in
        Ok { tv_index = index; tv_name = name }
    | _ -> Error "")

let region_var_of_json (js : json) : (region_var, string) result =
  combine_error_msgs js "region_var_of_json"
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = RegionVarId.id_of_json index in
        let* name = string_option_of_json name in
        Ok { rv_index = index; rv_name = name }
    | _ -> Error "")

let region_of_json (js : json) : (RegionVarId.id region, string) result =
  combine_error_msgs js "region_of_json"
    (match js with
    | `Assoc [ ("Static", `List []) ] -> Ok Static (* TODO *)
    | `Assoc [ ("Var", rid) ] ->
        let* rid = RegionVarId.id_of_json rid in
        Ok (Var rid)
    | _ -> Error "")

let erased_region_of_json (js : json) : (erased_region, string) result =
  combine_error_msgs js "erased_region_of_json"
    (match js with `String "Erased" -> Ok Erased | _ -> Error "")

let integer_type_of_json (js : json) : (integer_type, string) result =
  match js with
  | `String "Isize" -> Ok Isize (* TODO *)
  | `String "I8" -> Ok I8
  | `String "I16" -> Ok I16
  | `String "I32" -> Ok I32
  | `String "I64" -> Ok I64
  | `String "I128" -> Ok I128
  | `String "Usize" -> Ok Usize
  | `String "U8" -> Ok U8
  | `String "U16" -> Ok U16
  | `String "U32" -> Ok U32
  | `String "U64" -> Ok U64
  | `String "U128" -> Ok U128
  | _ -> Error ("integer_type_of_json failed on: " ^ show js)

let ref_kind_of_json (js : json) : (ref_kind, string) result =
  match js with
  | `String "Mut" -> Ok Mut
  | `String "Shared" -> Ok Shared
  | _ -> Error ("ref_kind_of_json failed on: " ^ show js)

let assumed_ty_of_json (js : json) : (assumed_ty, string) result =
  combine_error_msgs js "assumed_ty_of_json"
    (match js with `String "Box" -> Ok Box | _ -> Error "")

let rec ty_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r ty, string) result =
  combine_error_msgs js "ty_of_json"
    (match js with
    | `Assoc [ ("Adt", `List [ id; regions; types ]) ] ->
        let* id = TypeDefId.id_of_json id in
        let* regions = list_of_json r_of_json regions in
        let* types = list_of_json (ty_of_json r_of_json) types in
        Ok (Adt (id, regions, types))
    | `Assoc [ ("TypeVar", `List [ id ]) ] ->
        let* id = TypeVarId.id_of_json id in
        Ok (TypeVar id)
    | `Assoc [ ("Bool", `List []) ] -> Ok Bool (* TODO *)
    | `Assoc [ ("Char", `List []) ] -> Ok Char (* TODO *)
    | `Assoc [ ("`Never", `List []) ] -> Ok Never (* TODO *)
    | `Assoc [ ("Integer", `List [ int_ty ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        Ok (Integer int_ty)
    | `Assoc [ ("Str", `List []) ] -> Ok Str (* TODO *)
    | `Assoc [ ("Array", `List [ ty ]) ] ->
        let* ty = ty_of_json r_of_json ty in
        Ok (Array ty)
    | `Assoc [ ("Slice", `List [ ty ]) ] ->
        let* ty = ty_of_json r_of_json ty in
        Ok (Slice ty)
    | `Assoc [ ("Ref", `List [ region; ty; ref_kind ]) ] ->
        let* region = r_of_json region in
        let* ty = ty_of_json r_of_json ty in
        let* ref_kind = ref_kind_of_json ref_kind in
        Ok (Ref (region, ty, ref_kind))
    | `Assoc [ ("Tuple", `List [ types ]) ] ->
        let* types = list_of_json (ty_of_json r_of_json) types in
        Ok (Tuple types)
    | `Assoc [ ("Assumed", `List [ assumed_ty; regions; types ]) ] ->
        let* assumed_ty = assumed_ty_of_json assumed_ty in
        let* regions = list_of_json r_of_json regions in
        let* types = list_of_json (ty_of_json r_of_json) types in
        Ok (Assumed (assumed_ty, regions, types))
    | _ -> Error "")

let rty_of_json (js : json) : (rty, string) result =
  combine_error_msgs js "rty_of_json" (ty_of_json region_of_json js)

let ety_of_json (js : json) : (ety, string) result =
  combine_error_msgs js "ety_of_json" (ty_of_json erased_region_of_json js)

let field_of_json (js : json) : (field, string) result =
  combine_error_msgs js "field_of_json"
    (match js with
    | `Assoc [ ("name", name); ("ty", ty) ] ->
        let* name = string_of_json name in
        let* ty = rty_of_json ty in
        Ok { field_name = name; field_ty = ty }
    | _ -> Error "")

let variant_of_json (js : json) : (variant, string) result =
  combine_error_msgs js "variant_of_json"
    (match js with
    | `Assoc [ ("name", name); ("fields", fields) ] ->
        let* name = string_of_json name in
        let* fields = FieldId.vector_of_json field_of_json fields in
        Ok { variant_name = name; fields }
    | _ -> Error "")

let type_def_kind_of_json (js : json) : (type_def_kind, string) result =
  combine_error_msgs js "type_def_kind_of_json"
    (match js with
    | `Assoc [ ("Struct", fields) ] ->
        let* fields = FieldId.vector_of_json field_of_json fields in
        Ok (Struct fields)
    | `Assoc [ ("Enum", variants) ] ->
        let* variants = VariantId.vector_of_json variant_of_json variants in
        Ok (Enum variants)
    | _ -> Error "")

let type_def_of_json (js : json) : (type_def, string) result =
  combine_error_msgs js "type_def_of_json"
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("name", name);
          ("region_params", region_params);
          ("type_params", type_params);
          ("kind", kind);
        ] ->
        let* def_id = TypeDefId.id_of_json def_id in
        let* name = name_of_json name in
        let* region_params =
          RegionVarId.vector_of_json region_var_of_json region_params
        in
        let* type_params =
          TypeVarId.vector_of_json type_var_of_json type_params
        in
        let* kind = type_def_kind_of_json kind in
        Ok { def_id; name; region_params; type_params; kind }
    | _ -> Error "")

open Values

let var_of_json (js : json) : (var, string) result =
  combine_error_msgs js "var_of_json"
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = VarId.id_of_json index in
        let* name = string_option_of_json name in
        let* ty = ety_of_json ty in
        Ok { index; name; ty }
    | _ -> Error "")

let big_int_of_json (js : json) : (big_int, string) result =
  combine_error_msgs js "big_int_of_json"
    (match js with
    | `Int i -> Ok (Z.of_int i)
    | `String is -> Ok (Z.of_string is)
    | _ -> Error "")

let scalar_value_of_json (js : json) : (scalar_value, string) result =
  combine_error_msgs js "scalar_value_of_json"
    (match js with
    | `Assoc [ ("Isize", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (Isize bi)
    | `Assoc [ ("I8", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (I8 bi)
    | `Assoc [ ("I16", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (I16 bi)
    | `Assoc [ ("I32", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (I32 bi)
    | `Assoc [ ("I64", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (I64 bi)
    | `Assoc [ ("I128", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (I128 bi)
    | `Assoc [ ("Usize", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (Usize bi)
    | `Assoc [ ("U8", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (U8 bi)
    | `Assoc [ ("U16", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (U16 bi)
    | `Assoc [ ("U32", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (U32 bi)
    | `Assoc [ ("U64", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (U64 bi)
    | `Assoc [ ("U128", bi) ] ->
        let* bi = big_int_of_json bi in
        Ok (U128 bi)
    | _ -> Error "")

let constant_value_of_json (js : json) : (constant_value, string) result =
  combine_error_msgs js "constant_value_of_json"
    (match js with
    | `Assoc [ ("Scalar", scalar_value) ] ->
        let* scalar_value = scalar_value_of_json scalar_value in
        Ok (Scalar scalar_value)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (Bool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (Char v)
    | `Assoc [ ("String", v) ] ->
        let* v = string_of_json v in
        Ok (String v)
    | _ -> Error "")

open Expressions

let field_proj_kind_of_json (js : json) : (field_proj_kind, string) result =
  combine_error_msgs js "field_proj_kind_of_json"
    (match js with
    | `Assoc [ ("ProjAdt", `List [ def_id; opt_variant_id ]) ] ->
        let* def_id = TypeDefId.id_of_json def_id in
        let* opt_variant_id =
          option_of_json VariantId.id_of_json opt_variant_id
        in
        Ok (ProjAdt (def_id, opt_variant_id))
    | `Assoc [ ("ProjTuple", i) ] ->
        let* i = int_of_json i in
        Ok (ProjTuple i)
    | _ -> Error "")

let projection_elem_of_json (js : json) : (projection_elem, string) result =
  combine_error_msgs js "projection_elem_of_json"
    (match js with
    | `String "Deref" -> Ok Deref
    | `String "DerefBox" -> Ok DerefBox
    | `Assoc [ ("Field", `List [ proj_kind; field_id ]) ] ->
        let* proj_kind = field_proj_kind_of_json proj_kind in
        let* field_id = FieldId.id_of_json field_id in
        Ok (Field (proj_kind, field_id))
    | `Assoc [ ("Downcast", variant_id) ] ->
        let* variant_id = VariantId.id_of_json variant_id in
        Ok (Downcast variant_id)
    | _ -> Error ("projection_elem_of_json failed on:" ^ show js))

let projection_of_json (js : json) : (projection, string) result =
  combine_error_msgs js "projection_of_json"
    (list_of_json projection_elem_of_json js)

let place_of_json (js : json) : (place, string) result =
  combine_error_msgs js "place_of_json"
    (match js with
    | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
        let* var_id = VarId.id_of_json var_id in
        let* projection = projection_of_json projection in
        Ok { var_id; projection }
    | _ -> Error "")

let borrow_kind_of_json (js : json) : (borrow_kind, string) result =
  match js with
  | `String "Shared" -> Ok Shared
  | `String "Mut" -> Ok Mut
  | `String "TwoPhaseMut" -> Ok TwoPhaseMut
  | _ -> Error ("borrow_kind_of_json failed on:" ^ show js)

let unop_of_json (js : json) : (unop, string) result =
  match js with
  | `String "Not" -> Ok Not
  | `String "Neg" -> Ok Neg
  | _ -> Error ("unop_of_json failed on:" ^ show js)

let binop_of_json (js : json) : (binop, string) result =
  match js with
  | `String "BitXor" -> Ok BitXor
  | `String "BitAnd" -> Ok BitAnd
  | `String "BitOr" -> Ok BitOr
  | `String "Eq" -> Ok Eq
  | `String "Lt" -> Ok Lt
  | `String "Le" -> Ok Le
  | `String "Ne" -> Ok Ne
  | `String "Ge" -> Ok Ge
  | `String "Gt" -> Ok Gt
  | `String "Div" -> Ok Div
  | `String "Rem" -> Ok Rem
  | `String "Add" -> Ok Add
  | `String "Sub" -> Ok Sub
  | `String "Mul" -> Ok Mul
  | `String "Shl" -> Ok Shl
  | `String "Shr" -> Ok Shr
  | _ -> Error ("binop_of_json failed on:" ^ show js)

let operand_constant_value_of_json (js : json) :
    (operand_constant_value, string) result =
  combine_error_msgs js "operand_constant_value_of_json"
    (match js with
    | `Assoc [ ("ConstantValue", cv) ] ->
        let* cv = constant_value_of_json cv in
        Ok (ConstantValue cv)
    | `Assoc [ ("ConstantAdt", id) ] ->
        let* id = TypeDefId.id_of_json id in
        Ok (ConstantAdt id)
    | `Assoc [ ("Unit", `List []) ] -> Ok Unit
    | _ -> Error "")

let operand_of_json (js : json) : (operand, string) result =
  combine_error_msgs js "operand_of_json"
    (match js with
    | `Assoc [ ("Copy", place) ] ->
        let* place = place_of_json place in
        Ok (Copy place)
    | `Assoc [ ("Move", place) ] ->
        let* place = place_of_json place in
        Ok (Move place)
    | `Assoc [ ("Constant", `List [ ty; cv ]) ] ->
        let* ty = ety_of_json ty in
        let* cv = operand_constant_value_of_json cv in
        Ok (Constant (ty, cv))
    | _ -> Error "")

let aggregate_kind_of_json (js : json) : (aggregate_kind, string) result =
  combine_error_msgs js "operand_kind_of_json"
    (match js with
    | `Assoc [ ("AggregatedTuple", `List []) ] -> Ok AggregatedTuple
    | `Assoc [ ("AggregatedAdt", `List [ id; opt_variant_id ]) ] ->
        let* id = TypeDefId.id_of_json id in
        let* opt_variant_id =
          option_of_json VariantId.id_of_json opt_variant_id
        in
        Ok (AggregatedAdt (id, opt_variant_id))
    | _ -> Error "")

let rvalue_of_json (js : json) : (rvalue, string) result =
  combine_error_msgs js "rvalue_of_json"
    (match js with
    | `Assoc [ ("Use", op) ] ->
        let* op = operand_of_json op in
        Ok (Use op)
    | `Assoc [ ("Ref", `List [ place; borrow_kind ]) ] ->
        let* place = place_of_json place in
        let* borrow_kind = borrow_kind_of_json borrow_kind in
        Ok (Ref (place, borrow_kind))
    | `Assoc [ ("UnaryOp", `List [ unop; op ]) ] ->
        let* unop = unop_of_json unop in
        let* op = operand_of_json op in
        Ok (UnaryOp (unop, op))
    | `Assoc [ ("BinaryOp", `List [ binop; op1; op2 ]) ] ->
        let* binop = binop_of_json binop in
        let* op1 = operand_of_json op1 in
        let* op2 = operand_of_json op2 in
        Ok (BinaryOp (binop, op1, op2))
    | `Assoc [ ("Discriminant", place) ] ->
        let* place = place_of_json place in
        Ok (Discriminant place)
    | `Assoc [ ("Aggregate", `List [ aggregate_kind; ops ]) ] ->
        let* aggregate_kind = aggregate_kind_of_json aggregate_kind in
        let* ops = list_of_json operand_of_json ops in
        Ok (Aggregate (aggregate_kind, ops))
    | _ -> Error "")

open CfimAst

let assumed_fun_id_of_json (js : json) : (assumed_fun_id, string) result =
  match js with
  | `String "BoxNew" -> Ok BoxNew
  | `String "BoxDeref" -> Ok BoxDeref
  | `String "BoxDerefMut" -> Ok BoxDerefMut
  | `String "BoxFree" -> Ok BoxFree
  | _ -> Error ("assumed_fun_id_of_json failed on:" ^ show js)

let fun_id_of_json (js : json) : (fun_id, string) result =
  combine_error_msgs js "fun_id_of_json"
    (match js with
    | `Assoc [ ("Local", id) ] ->
        let* id = FunDefId.id_of_json id in
        Ok (Local id)
    | `Assoc [ ("Assumed", fid) ] ->
        let* fid = assumed_fun_id_of_json fid in
        Ok (Assumed fid)
    | _ -> Error "")

let assertion_of_json (js : json) : (assertion, string) result =
  combine_error_msgs js "assertion_of_json"
    (match js with
    | `Assoc [ ("cond", cond); ("expected", expected) ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        Ok { cond; expected }
    | _ -> Error "")

let fun_sig_of_json (js : json) : (fun_sig, string) result =
  combine_error_msgs js "fun_sig_of_json"
    (match js with
    | `Assoc
        [
          ("region_params", region_params);
          ("num_early_bound_regions", num_early_bound_regions);
          ("type_params", type_params);
          ("inputs", inputs);
          ("output", output);
        ] ->
        let* region_params =
          RegionVarId.vector_of_json region_var_of_json region_params
        in
        let* num_early_bound_regions = int_of_json num_early_bound_regions in
        let* type_params =
          TypeVarId.vector_of_json type_var_of_json type_params
        in
        let* inputs = VarId.vector_of_json rty_of_json inputs in
        let* output = rty_of_json output in
        Ok
          {
            region_params;
            num_early_bound_regions;
            type_params;
            inputs;
            output;
          }
    | _ -> Error "")

let call_of_json (js : json) : (call, string) result =
  combine_error_msgs js "call_of_json"
    (match js with
    | `Assoc
        [
          ("func", func);
          ("region_params", region_params);
          ("type_params", type_params);
          ("args", args);
          ("dest", dest);
        ] ->
        let* func = fun_id_of_json func in
        let* region_params = list_of_json erased_region_of_json region_params in
        let* type_params = list_of_json ety_of_json type_params in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok { func; region_params; type_params; args; dest }
    | _ -> Error "")

let statement_of_json (js : json) : (statement, string) result =
  combine_error_msgs js "statement_of_json"
    (match js with
    | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
        let* place = place_of_json place in
        let* rvalue = rvalue_of_json rvalue in
        Ok (Assign (place, rvalue))
    | `Assoc [ ("FakeRead", place) ] ->
        let* place = place_of_json place in
        Ok (FakeRead place)
    | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
        let* place = place_of_json place in
        let* variant_id = VariantId.id_of_json variant_id in
        Ok (SetDiscriminant (place, variant_id))
    | `Assoc [ ("Drop", place) ] ->
        let* place = place_of_json place in
        Ok (Drop place)
    | `Assoc [ ("Assert", assertion) ] ->
        let* assertion = assertion_of_json assertion in
        Ok (Assert assertion)
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json call in
        Ok (Call call)
    | `String "Panic" -> Ok Panic (* TODO *)
    | `String "Return" -> Ok Return
    | `Assoc [ ("Break", i) ] ->
        let* i = int_of_json i in
        Ok (Break i)
    | `Assoc [ ("Continue", i) ] ->
        let* i = int_of_json i in
        Ok (Continue i)
    | `String "Nop" -> Ok Nop
    | _ -> Error "")

let rec expression_of_json (js : json) : (expression, string) result =
  combine_error_msgs js "expression_of_json"
    (match js with
    | `Assoc [ ("Statement", statement) ] ->
        let* statement = statement_of_json statement in
        Ok (Statement statement)
    | `Assoc [ ("Sequence", `List [ e1; e2 ]) ] ->
        let* e1 = expression_of_json e1 in
        let* e2 = expression_of_json e2 in
        Ok (Sequence (e1, e2))
    | `Assoc [ ("Switch", `List [ op; tgt ]) ] ->
        let* op = operand_of_json op in
        let* tgt = switch_targets_of_json tgt in
        Ok (Switch (op, tgt))
    | `Assoc [ ("Loop", e) ] ->
        let* e = expression_of_json e in
        Ok (Loop e)
    | _ -> Error "")

and switch_targets_of_json (js : json) : (switch_targets, string) result =
  combine_error_msgs js "switch_targets_of_json"
    (match js with
    | `Assoc [ ("If", `List [ e1; e2 ]) ] ->
        let* e1 = expression_of_json e1 in
        let* e2 = expression_of_json e2 in
        Ok (If (e1, e2))
    | `Assoc [ ("SwitchInt", `List [ int_ty; tgts; otherwise ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json scalar_value_of_json expression_of_json)
            tgts
        in
        let* otherwise = expression_of_json otherwise in
        Ok (SwitchInt (int_ty, tgts, otherwise))
    | _ -> Error "")

let fun_def_of_json (js : json) : (fun_def, string) result =
  combine_error_msgs js "fun_def_of_json"
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("name", name);
          ("signature", signature);
          ("divergent", divergent);
          ("arg_count", arg_count);
          ("locals", locals);
          ("body", body);
        ] ->
        let* def_id = FunDefId.id_of_json def_id in
        let* name = name_of_json name in
        let* signature = fun_sig_of_json signature in
        let* divergent = bool_of_json divergent in
        let* arg_count = int_of_json arg_count in
        let* locals = VarId.vector_of_json var_of_json locals in
        let* body = expression_of_json body in
        Ok { def_id; name; signature; divergent; arg_count; locals; body }
    | _ -> Error "")

(** Module declaration *)
type declaration =
  | Type of TypeDefId.id
  | Fun of FunDefId.id
  | RecTypes of TypeDefId.id list
  | RecFuns of FunDefId.id list

type cfim_module = {
  declarations : declaration list;
  types : type_def TypeDefId.vector;
  functions : fun_def FunDefId.vector;
}
(** CFIM module *)

let declaration_of_json (js : json) : (declaration, string) result =
  combine_error_msgs js "declaration_of_json"
    (match js with
    | `Assoc [ ("Type", id) ] ->
        let* id = TypeDefId.id_of_json id in
        Ok (Type id)
    | `Assoc [ ("Fun", id) ] ->
        let* id = FunDefId.id_of_json id in
        Ok (Fun id)
    | `Assoc [ ("RecTypes", ids) ] ->
        let* ids = list_of_json TypeDefId.id_of_json ids in
        Ok (RecTypes ids)
    | `Assoc [ ("RecFuns", ids) ] ->
        let* ids = list_of_json FunDefId.id_of_json ids in
        Ok (RecFuns ids)
    | _ -> Error "")

let cfim_module_of_json (js : json) : (cfim_module, string) result =
  combine_error_msgs js "cfim_module_of_json"
    (match js with
    | `Assoc
        [
          ("declarations", declarations);
          ("types", types);
          ("functions", functions);
        ] ->
        let* declarations = list_of_json declaration_of_json declarations in
        let* types = TypeDefId.vector_of_json type_def_of_json types in
        let* functions = FunDefId.vector_of_json fun_def_of_json functions in
        Ok { declarations; types; functions }
    | _ -> Error "")
