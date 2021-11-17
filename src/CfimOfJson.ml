(** Functions to load CFIM ASTs from json.

    Initially, we used `ppx_derive_yojson` to automate this.
    However, `ppx_derive_yojson` expects formatting to be slightly
    different from what `serde_rs` generates.

    For instance, if you consider the following rust definition:
    ```
    enum t = | V
    ```
    Serializing `t::V` with `serde_rs` will generate: `"V"`.

    However, if you consider the following OCaml definition:
    ```
    type t = V
    ```
    Serializing `V` will generate: `["V"]`.

    As we consider that the `serde_rs` formatting is more logical, we decided
    to implement our own deserializing functions. Moreover, it allows us to
    generate a friendlier debugging output in case the deserialization functions
    fail.

    TODO: we should check that the integer values are in the proper range
 *)

open Yojson.Safe
open Identifiers
open Types

type json = t

let ( let* ) o f = match o with Error e -> Error e | Ok x -> f x

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
  | `Tuple [ a; b ] ->
      let* a = a_of_json a in
      let* b = b_of_json b in
      Ok (a, b)
  | _ -> Error ("pair_of_json failed on: " ^ show js)

let list_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a list, string) result =
  match js with
  | `List jsl -> of_json_list a_of_json jsl
  | _ -> Error ("list_of_json: not a list: " ^ show js)

let string_of_json (js : json) : (string, string) result =
  match js with
  | `String str -> Ok str
  | _ -> Error ("string_of_json: not a string: " ^ show js)

let option_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a option, string) result =
  match js with
  | `Variant ("Some", Some x) ->
      let* x = a_of_json x in
      Ok (Some x)
  | `Variant ("None", None) -> Ok None
  | _ -> Error ("option_of_json failed on: " ^ show js)

let string_option_of_json (js : json) : (string option, string) result =
  option_of_json string_of_json js

let name_of_json (js : json) : (name, string) result =
  list_of_json string_of_json js

let type_var_of_json (js : json) : (type_var, string) result =
  match js with
  | `Assoc [ ("index", index); ("name", name) ] ->
      let* index = TypeVarId.id_of_json index in
      let* name = string_of_json name in
      Ok { tv_index = index; tv_name = name }
  | _ -> Error ("type_var_of_json failed on:" ^ show js)

let region_var_of_json (js : json) : (region_var, string) result =
  match js with
  | `Assoc [ ("index", index); ("name", name) ] ->
      let* index = RegionVarId.id_of_json index in
      let* name = string_option_of_json name in
      Ok { rv_index = index; rv_name = name }
  | _ -> Error ("region_var_of_json failed on:" ^ show js)

let region_of_json (js : json) : (RegionVarId.id region, string) result =
  match js with
  | `Variant ("Static", None) -> Ok Static
  | `Variant ("Var", Some rid) ->
      let* rid = RegionVarId.id_of_json rid in
      Ok (Var rid)
  | _ -> Error ("region_of_json failed on:" ^ show js)

let erased_region_of_json (js : json) : (erased_region, string) result =
  match js with
  | `Variant ("Erased", None) -> Ok Erased
  | _ -> Error ("erased_region_of_json failed on:" ^ show js)

let integer_type_of_json (js : json) : (integer_type, string) result =
  match js with
  | `Variant ("Isize", None) -> Ok Isize
  | `Variant ("I8", None) -> Ok I8
  | `Variant ("I16", None) -> Ok I16
  | `Variant ("I32", None) -> Ok I32
  | `Variant ("I64", None) -> Ok I64
  | `Variant ("I128", None) -> Ok I128
  | `Variant ("Usize", None) -> Ok Usize
  | `Variant ("U8", None) -> Ok U8
  | `Variant ("U16", None) -> Ok U16
  | `Variant ("U32", None) -> Ok U32
  | `Variant ("U64", None) -> Ok U64
  | `Variant ("U128", None) -> Ok U128
  | _ -> Error ("integer_type_of_json failed on:" ^ show js)

let ref_kind_of_json (js : json) : (ref_kind, string) result =
  match js with
  | `Variant ("Mut", None) -> Ok Mut
  | `Variant ("Shared", None) -> Ok Shared
  | _ -> Error ("ref_kind_of_json failed on:" ^ show js)

let assumed_ty_of_json (js : json) : (assumed_ty, string) result =
  match js with
  | `Variant ("Box", None) -> Ok Box
  | _ -> Error ("assumed_ty_of_json failed on:" ^ show js)

let rec ty_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r ty, string) result =
  match js with
  | `Variant ("Adt", Some (`Tuple [ id; regions; types ])) ->
      let* id = TypeDefId.id_of_json id in
      let* regions = list_of_json r_of_json regions in
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Adt (id, regions, types))
  | `Variant ("TypeVar", Some id) ->
      let* id = TypeVarId.id_of_json id in
      Ok (TypeVar id)
  | `Variant ("Bool", None) -> Ok Bool
  | `Variant ("Char", None) -> Ok Char
  | `Variant ("Never", None) -> Ok Never
  | `Variant ("Integer", Some int_ty) ->
      let* int_ty = integer_type_of_json int_ty in
      Ok (Integer int_ty)
  | `Variant ("Str", None) -> Ok Str
  | `Variant ("Array", Some ty) ->
      let* ty = ty_of_json r_of_json ty in
      Ok (Array ty)
  | `Variant ("Slice", Some ty) ->
      let* ty = ty_of_json r_of_json ty in
      Ok (Slice ty)
  | `Variant ("Ref", Some (`Tuple [ region; ty; ref_kind ])) ->
      let* region = r_of_json region in
      let* ty = ty_of_json r_of_json ty in
      let* ref_kind = ref_kind_of_json ref_kind in
      Ok (Ref (region, ty, ref_kind))
  | `Variant ("Tuple", Some types) ->
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Tuple types)
  | `Variant ("Assumed", Some (`Tuple [ assumed_ty; regions; types ])) ->
      let* assumed_ty = assumed_ty_of_json assumed_ty in
      let* regions = list_of_json r_of_json regions in
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Assumed (assumed_ty, regions, types))
  | _ -> Error ("ty_of_json failed on:" ^ show js)

let rty_of_json (js : json) : (rty, string) result =
  ty_of_json region_of_json js

let ety_of_json (js : json) : (ety, string) result =
  ty_of_json erased_region_of_json js

let field_of_json (js : json) : (field, string) result =
  match js with
  | `Assoc [ ("name", name); ("ty", ty) ] ->
      let* name = string_of_json name in
      let* ty = rty_of_json ty in
      Ok { field_name = name; field_ty = ty }
  | _ -> Error ("field_of_json failed on:" ^ show js)

let variant_of_json (js : json) : (variant, string) result =
  match js with
  | `Assoc [ ("name", name); ("fields", fields) ] ->
      let* name = string_of_json name in
      let* fields = FieldId.vector_of_json field_of_json fields in
      Ok { variant_name = name; fields }
  | _ -> Error ("variant_of_json failed on:" ^ show js)

let type_def_kind_of_json (js : json) : (type_def_kind, string) result =
  match js with
  | `Variant ("Struct", Some fields) ->
      let* fields = FieldId.vector_of_json field_of_json fields in
      Ok (Struct fields)
  | `Variant ("Enum", Some variants) ->
      let* variants = VariantId.vector_of_json variant_of_json variants in
      Ok (Enum variants)
  | _ -> Error ("type_def_kind_of_json failed on:" ^ show js)

let type_def_of_json (js : json) : (type_def, string) result =
  match js with
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
  | _ -> Error ("type_def_of_json failed on:" ^ show js)

open Values

let var_of_json (js : json) : (var, string) result =
  match js with
  | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
      let* index = VarId.id_of_json index in
      let* name = string_option_of_json name in
      let* ty = ety_of_json ty in
      Ok { index; name; ty }
  | _ -> Error ("var_of_json failed on:" ^ show js)

let big_int_of_json (js : json) : (big_int, string) result =
  match js with
  | `Int i -> Ok (Z.of_int i)
  | `Intlit is -> Ok (Z.of_string is)
  | _ -> Error ("big_int_of_json failed on: " ^ show js)

let scalar_value_of_json (js : json) : (scalar_value, string) result =
  match js with
  | `Variant ("Isize", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (Isize bi)
  | `Variant ("I8", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (I8 bi)
  | `Variant ("I16", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (I16 bi)
  | `Variant ("I32", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (I32 bi)
  | `Variant ("I64", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (I64 bi)
  | `Variant ("I128", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (I128 bi)
  | `Variant ("Usize", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (Usize bi)
  | `Variant ("U8", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (U8 bi)
  | `Variant ("U16", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (U16 bi)
  | `Variant ("U32", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (U32 bi)
  | `Variant ("U64", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (U64 bi)
  | `Variant ("U128", Some bi) ->
      let* bi = big_int_of_json bi in
      Ok (U128 bi)
  | _ -> Error ("scalar_value_of_json failed on:" ^ show js)

let constant_value_of_json (js : json) : (constant_value, string) result =
  match js with
  | `Variant ("Scalar", Some scalar_value) ->
      let* scalar_value = scalar_value_of_json scalar_value in
      Ok (Scalar scalar_value)
  | `Variant ("Bool", Some v) ->
      let* v = bool_of_json v in
      Ok (Bool v)
  | `Variant ("Char", Some v) ->
      let* v = char_of_json v in
      Ok (Char v)
  | `Variant ("String", Some v) ->
      let* v = string_of_json v in
      Ok (String v)
  | _ -> Error ("constant_value_of_json failed on:" ^ show js)

open Expressions

let field_proj_kind_of_json (js : json) : (field_proj_kind, string) result =
  match js with
  | `Variant ("ProjAdt", Some (`Tuple [ def_id; opt_variant_id ])) ->
      let* def_id = TypeDefId.id_of_json def_id in
      let* opt_variant_id =
        option_of_json VariantId.id_of_json opt_variant_id
      in
      Ok (ProjAdt (def_id, opt_variant_id))
  | `Variant ("ProjTuple", Some i) ->
      let* i = int_of_json i in
      Ok (ProjTuple i)
  | _ -> Error ("field_proj_kind_of_json failed on:" ^ show js)

let projection_elem_of_json (js : json) : (projection_elem, string) result =
  match js with
  | `Variant ("Deref", None) -> Ok Deref
  | `Variant ("DerefBox", None) -> Ok DerefBox
  | `Variant ("Field", Some (`Tuple [ proj_kind; field_id ])) ->
      let* proj_kind = field_proj_kind_of_json proj_kind in
      let* field_id = FieldId.id_of_json field_id in
      Ok (Field (proj_kind, field_id))
  | `Variant ("Downcast", Some variant_id) ->
      let* variant_id = VariantId.id_of_json variant_id in
      Ok (Downcast variant_id)
  | _ -> Error ("projection_elem_of_json failed on:" ^ show js)

let projection_of_json (js : json) : (projection, string) result =
  list_of_json projection_elem_of_json js

let place_of_json (js : json) : (place, string) result =
  match js with
  | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
      let* var_id = VarId.id_of_json var_id in
      let* projection = projection_of_json projection in
      Ok { var_id; projection }
  | _ -> Error ("place_of_json failed on:" ^ show js)

let borrow_kind_of_json (js : json) : (borrow_kind, string) result =
  match js with
  | `Variant ("Shared", None) -> Ok Shared
  | `Variant ("Mut", None) -> Ok Mut
  | `Variant ("TwoPhaseMut", None) -> Ok TwoPhaseMut
  | _ -> Error ("borrow_kind_of_json failed on:" ^ show js)

let unop_of_json (js : json) : (unop, string) result =
  match js with
  | `Variant ("Not", None) -> Ok Not
  | `Variant ("Neg", None) -> Ok Neg
  | _ -> Error ("unop_of_json failed on:" ^ show js)

let binop_of_json (js : json) : (binop, string) result =
  match js with
  | `Variant ("BitXor", None) -> Ok BitXor
  | `Variant ("BitAnd", None) -> Ok BitAnd
  | `Variant ("BitOr", None) -> Ok BitOr
  | `Variant ("Eq", None) -> Ok Eq
  | `Variant ("Lt", None) -> Ok Lt
  | `Variant ("Le", None) -> Ok Le
  | `Variant ("Ne", None) -> Ok Ne
  | `Variant ("Ge", None) -> Ok Ge
  | `Variant ("Gt", None) -> Ok Gt
  | `Variant ("Div", None) -> Ok Div
  | `Variant ("Rem", None) -> Ok Rem
  | `Variant ("Add", None) -> Ok Add
  | `Variant ("Sub", None) -> Ok Sub
  | `Variant ("Mul", None) -> Ok Mul
  | `Variant ("Shl", None) -> Ok Shl
  | `Variant ("Shr", None) -> Ok Shr
  | _ -> Error ("binop_of_json failed on:" ^ show js)

let operand_constant_value_of_json (js : json) :
    (operand_constant_value, string) result =
  match js with
  | `Variant ("ConstantValue", Some cv) ->
      let* cv = constant_value_of_json cv in
      Ok (ConstantValue cv)
  | `Variant ("ConstantAdt", Some id) ->
      let* id = TypeDefId.id_of_json id in
      Ok (ConstantAdt id)
  | `Variant ("Unit", None) -> Ok Unit
  | _ -> Error ("operand_constant_value_of_json failed on:" ^ show js)

let operand_of_json (js : json) : (operand, string) result =
  match js with
  | `Variant ("Copy", Some place) ->
      let* place = place_of_json place in
      Ok (Copy place)
  | `Variant ("Move", Some place) ->
      let* place = place_of_json place in
      Ok (Move place)
  | `Variant ("Constant", Some (`Tuple [ ty; cv ])) ->
      let* ty = ety_of_json ty in
      let* cv = operand_constant_value_of_json cv in
      Ok (Constant (ty, cv))
  | _ -> Error ("operand_of_json failed on:" ^ show js)

let aggregate_kind_of_json (js : json) : (aggregate_kind, string) result =
  match js with
  | `Variant ("AggregatedTuple", None) -> Ok AggregatedTuple
  | `Variant ("AggregatedAdt", Some (`Tuple [ id; opt_variant_id ])) ->
      let* id = TypeDefId.id_of_json id in
      let* opt_variant_id =
        option_of_json VariantId.id_of_json opt_variant_id
      in
      Ok (AggregatedAdt (id, opt_variant_id))
  | _ -> Error ("aggregate_kind_of_json failed on:" ^ show js)

let rvalue_of_json (js : json) : (rvalue, string) result =
  match js with
  | `Variant ("Use", Some op) ->
      let* op = operand_of_json op in
      Ok (Use op)
  | `Variant ("Ref", Some (`Tuple [ place; borrow_kind ])) ->
      let* place = place_of_json place in
      let* borrow_kind = borrow_kind_of_json borrow_kind in
      Ok (Ref (place, borrow_kind))
  | `Variant ("UnaryOp", Some (`Tuple [ unop; op ])) ->
      let* unop = unop_of_json unop in
      let* op = operand_of_json op in
      Ok (UnaryOp (unop, op))
  | `Variant ("BinaryOp", Some (`Tuple [ binop; op1; op2 ])) ->
      let* binop = binop_of_json binop in
      let* op1 = operand_of_json op1 in
      let* op2 = operand_of_json op2 in
      Ok (BinaryOp (binop, op1, op2))
  | `Variant ("Discriminant", Some place) ->
      let* place = place_of_json place in
      Ok (Discriminant place)
  | `Variant ("Aggregate", Some (`Tuple [ aggregate_kind; ops ])) ->
      let* aggregate_kind = aggregate_kind_of_json aggregate_kind in
      let* ops = list_of_json operand_of_json ops in
      Ok (Aggregate (aggregate_kind, ops))
  | _ -> Error ("rvalue_of_json failed on:" ^ show js)

open CfimAst

let assumed_fun_id_of_json (js : json) : (assumed_fun_id, string) result =
  match js with
  | `Variant ("BoxNew", None) -> Ok BoxNew
  | `Variant ("BoxDeref", None) -> Ok BoxDeref
  | `Variant ("BoxDerefMut", None) -> Ok BoxDerefMut
  | `Variant ("BoxFree", None) -> Ok BoxFree
  | _ -> Error ("assumed_fun_id_of_json failed on:" ^ show js)

let fun_id_of_json (js : json) : (fun_id, string) result =
  match js with
  | `Variant ("Local", Some id) ->
      let* id = FunDefId.id_of_json id in
      Ok (Local id)
  | `Variant ("BoxDeref", Some fid) ->
      let* fid = assumed_fun_id_of_json fid in
      Ok (Assumed fid)
  | _ -> Error ("fun_id_of_json failed on:" ^ show js)

let assertion_of_json (js : json) : (assertion, string) result =
  match js with
  | `Assoc [ ("cond", cond); ("expected", expected) ] ->
      let* cond = operand_of_json cond in
      let* expected = bool_of_json expected in
      Ok { cond; expected }
  | _ -> Error ("assertion_of_json failed on:" ^ show js)

let fun_sig_of_json (js : json) : (fun_sig, string) result =
  match js with
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
      Ok { region_params; num_early_bound_regions; type_params; inputs; output }
  | _ -> Error ("fun_sig_of_json failed on:" ^ show js)

let call_of_json (js : json) : (call, string) result =
  match js with
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
  | _ -> Error ("call_of_json failed on:" ^ show js)

let statement_of_json (js : json) : (statement, string) result =
  match js with
  | `Variant ("Assign", Some (`Tuple [ place; rvalue ])) ->
      let* place = place_of_json place in
      let* rvalue = rvalue_of_json rvalue in
      Ok (Assign (place, rvalue))
  | `Variant ("FakeRead", Some place) ->
      let* place = place_of_json place in
      Ok (FakeRead place)
  | `Variant ("SetDiscriminant", Some (`Tuple [ place; variant_id ])) ->
      let* place = place_of_json place in
      let* variant_id = VariantId.id_of_json variant_id in
      Ok (SetDiscriminant (place, variant_id))
  | `Variant ("Drop", Some place) ->
      let* place = place_of_json place in
      Ok (Drop place)
  | `Variant ("Assert", Some assertion) ->
      let* assertion = assertion_of_json assertion in
      Ok (Assert assertion)
  | `Variant ("Call", Some call) ->
      let* call = call_of_json call in
      Ok (Call call)
  | `Variant ("Panic", None) -> Ok Panic
  | `Variant ("Return", None) -> Ok Return
  | `Variant ("Break", Some i) ->
      let* i = int_of_json i in
      Ok (Break i)
  | `Variant ("Continue", Some i) ->
      let* i = int_of_json i in
      Ok (Continue i)
  | `Variant ("Nop", None) -> Ok Nop
  | _ -> Error ("statement_of_json failed on:" ^ show js)

let rec expression_of_json (js : json) : (expression, string) result =
  match js with
  | `Variant ("Statement", Some statement) ->
      let* statement = statement_of_json statement in
      Ok (Statement statement)
  | `Variant ("Sequence", Some (`Tuple [ e1; e2 ])) ->
      let* e1 = expression_of_json e1 in
      let* e2 = expression_of_json e2 in
      Ok (Sequence (e1, e2))
  | `Variant ("Switch", Some (`Tuple [ op; tgt ])) ->
      let* op = operand_of_json op in
      let* tgt = switch_targets_of_json tgt in
      Ok (Switch (op, tgt))
  | `Variant ("Loop", Some e) ->
      let* e = expression_of_json e in
      Ok (Loop e)
  | _ -> Error ("expression_of_json failed on:" ^ show js)

and switch_targets_of_json (js : json) : (switch_targets, string) result =
  match js with
  | `Variant ("If", Some (`Tuple [ e1; e2 ])) ->
      let* e1 = expression_of_json e1 in
      let* e2 = expression_of_json e2 in
      Ok (If (e1, e2))
  | `Variant ("SwitchInt", Some (`Tuple [ int_ty; tgts; otherwise ])) ->
      let* int_ty = integer_type_of_json int_ty in
      let* tgts =
        list_of_json (pair_of_json scalar_value_of_json expression_of_json) tgts
      in
      let* otherwise = expression_of_json otherwise in
      Ok (SwitchInt (int_ty, tgts, otherwise))
  | _ -> Error ("switch_targets_of_json failed on:" ^ show js)
