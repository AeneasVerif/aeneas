(** This module defines printing functions for the types defined in Pure.ml *)

open Pure
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module TypeDefId = T.TypeDefId
module TypeVarId = T.TypeVarId
module RegionId = T.RegionId
module VariantId = T.VariantId
module FieldId = T.FieldId
module SymbolicValueId = V.SymbolicValueId
module FunDefId = A.FunDefId

type type_formatter = {
  type_var_id_to_string : TypeVarId.id -> string;
  type_def_id_to_string : TypeDefId.id -> string;
}

type value_formatter = {
  type_var_id_to_string : TypeVarId.id -> string;
  type_def_id_to_string : TypeDefId.id -> string;
  adt_variant_to_string : TypeDefId.id -> VariantId.id -> string;
  var_id_to_string : VarId.id -> string;
  adt_field_names : TypeDefId.id -> VariantId.id option -> string list option;
}

let value_to_type_formatter (fmt : value_formatter) : type_formatter =
  {
    type_var_id_to_string = fmt.type_var_id_to_string;
    type_def_id_to_string = fmt.type_def_id_to_string;
  }

(* TODO: we need to store which variables we have encountered so far, and
   remove [var_id_to_string].
*)
type ast_formatter = {
  type_var_id_to_string : TypeVarId.id -> string;
  type_def_id_to_string : TypeDefId.id -> string;
  adt_variant_to_string : TypeDefId.id -> VariantId.id -> string;
  var_id_to_string : VarId.id -> string;
  adt_field_to_string :
    TypeDefId.id -> VariantId.id option -> FieldId.id -> string option;
  adt_field_names : TypeDefId.id -> VariantId.id option -> string list option;
  fun_def_id_to_string : A.FunDefId.id -> string;
}

let ast_to_value_formatter (fmt : ast_formatter) : value_formatter =
  {
    type_var_id_to_string = fmt.type_var_id_to_string;
    type_def_id_to_string = fmt.type_def_id_to_string;
    adt_variant_to_string = fmt.adt_variant_to_string;
    var_id_to_string = fmt.var_id_to_string;
    adt_field_names = fmt.adt_field_names;
  }

let ast_to_type_formatter (fmt : ast_formatter) : type_formatter =
  let fmt = ast_to_value_formatter fmt in
  value_to_type_formatter fmt

let name_to_string = Print.name_to_string

let option_to_string = Print.option_to_string

let type_var_to_string = Print.Types.type_var_to_string

let integer_type_to_string = Print.Types.integer_type_to_string

let scalar_value_to_string = Print.Values.scalar_value_to_string

let mk_type_formatter (type_defs : T.type_def TypeDefId.Map.t)
    (type_params : type_var list) : type_formatter =
  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth type_params vid in
    type_var_to_string var
  in
  let type_def_id_to_string def_id =
    let def = T.TypeDefId.Map.find def_id type_defs in
    name_to_string def.name
  in
  { type_var_id_to_string; type_def_id_to_string }

(* TODO: there is a bit of duplication with Print.fun_def_to_ast_formatter.

   TODO: use the pure defs as inputs? Note that it is a bit annoying for the
   functions (there is a difference between the forward/backward functions...)
   while we only need those definitions to lookup proper names for the def ids.
*)
let mk_ast_formatter (type_defs : T.type_def TypeDefId.Map.t)
    (fun_defs : A.fun_def FunDefId.Map.t) (type_params : type_var list) :
    ast_formatter =
  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth type_params vid in
    type_var_to_string var
  in
  let type_def_id_to_string def_id =
    let def = T.TypeDefId.Map.find def_id type_defs in
    name_to_string def.name
  in
  let adt_variant_to_string =
    Print.Contexts.type_ctx_to_adt_variant_to_string_fun type_defs
  in
  let var_id_to_string vid =
    (* TODO: somehow lookup in the context *)
    "^" ^ VarId.to_string vid
  in
  let adt_field_names =
    Print.Contexts.type_ctx_to_adt_field_names_fun type_defs
  in
  let adt_field_to_string =
    Print.CfimAst.type_ctx_to_adt_field_to_string_fun type_defs
  in
  let fun_def_id_to_string def_id =
    let def = A.FunDefId.Map.find def_id fun_defs in
    name_to_string def.name
  in
  {
    type_var_id_to_string;
    type_def_id_to_string;
    adt_variant_to_string;
    var_id_to_string;
    adt_field_names;
    adt_field_to_string;
    fun_def_id_to_string;
  }

let type_id_to_string (fmt : type_formatter) (id : type_id) : string =
  match id with
  | AdtId id -> fmt.type_def_id_to_string id
  | Tuple -> ""
  | Assumed aty -> (
      match aty with Result -> "Result" | Option -> "Option" | Vec -> "Vec")

let rec ty_to_string (fmt : type_formatter) (ty : ty) : string =
  match ty with
  | Adt (id, tys) -> (
      let tys = List.map (ty_to_string fmt) tys in
      match id with
      | Tuple -> "(" ^ String.concat " * " tys ^ ")"
      | AdtId _ | Assumed _ ->
          let tys = if tys = [] then "" else " " ^ String.concat " " tys in
          type_id_to_string fmt id ^ tys)
  | TypeVar tv -> fmt.type_var_id_to_string tv
  | Bool -> "bool"
  | Char -> "char"
  | Integer int_ty -> integer_type_to_string int_ty
  | Str -> "str"
  | Array aty -> "[" ^ ty_to_string fmt aty ^ "; ?]"
  | Slice sty -> "[" ^ ty_to_string fmt sty ^ "]"

let field_to_string fmt (f : field) : string =
  match f.field_name with
  | None -> ty_to_string fmt f.field_ty
  | Some field_name -> field_name ^ " : " ^ ty_to_string fmt f.field_ty

let variant_to_string fmt (v : variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string fmt) v.fields)
  ^ ")"

let type_def_to_string (fmt : type_formatter) (def : type_def) : string =
  let types = def.type_params in
  let name = name_to_string def.name in
  let params =
    if types = [] then ""
    else " " ^ String.concat " " (List.map type_var_to_string types)
  in
  match def.kind with
  | Struct fields ->
      if List.length fields > 0 then
        let fields =
          String.concat ","
            (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
        in
        "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
      else "struct " ^ name ^ params ^ "{}"
  | Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ " =\n" ^ variants

let var_to_string (fmt : type_formatter) (v : var) : string =
  let varname =
    match v.basename with
    | Some name -> name ^ "^" ^ VarId.to_string v.id
    | None -> "^" ^ VarId.to_string v.id
  in
  "(" ^ varname ^ " : " ^ ty_to_string fmt v.ty ^ ")"

let var_or_dummy_to_string (fmt : value_formatter) (v : var_or_dummy) : string =
  match v with
  | Var (v, _) -> var_to_string (value_to_type_formatter fmt) v
  | Dummy -> "_"

let rec projection_to_string (fmt : ast_formatter) (inside : string)
    (p : projection) : string =
  match p with
  | [] -> inside
  | pe :: p' -> (
      let s = projection_to_string fmt inside p' in
      match pe.pkind with
      | E.ProjOption variant_id ->
          assert (variant_id == T.option_some_id);
          assert (pe.field_id == T.FieldId.zero);
          "(" ^ s ^ "as Option::Some)." ^ T.FieldId.to_string pe.field_id
      | E.ProjTuple _ -> "(" ^ s ^ ")." ^ T.FieldId.to_string pe.field_id
      | E.ProjAdt (adt_id, opt_variant_id) -> (
          let field_name =
            match fmt.adt_field_to_string adt_id opt_variant_id pe.field_id with
            | Some field_name -> field_name
            | None -> T.FieldId.to_string pe.field_id
          in
          match opt_variant_id with
          | None -> "(" ^ s ^ ")." ^ field_name
          | Some variant_id ->
              let variant_name = fmt.adt_variant_to_string adt_id variant_id in
              "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name))

let place_to_string (fmt : ast_formatter) (p : place) : string =
  (* TODO: improve that *)
  let var = fmt.var_id_to_string p.var in
  projection_to_string fmt var p.projection

let adt_g_value_to_string (fmt : value_formatter)
    (value_to_string : 'v -> string) (variant_id : VariantId.id option)
    (field_values : 'v list) (ty : ty) : string =
  let field_values = List.map value_to_string field_values in
  match ty with
  | Adt (Tuple, _) ->
      (* Tuple *)
      "(" ^ String.concat ", " field_values ^ ")"
  | Adt (AdtId def_id, _) ->
      (* "Regular" ADT *)
      let adt_ident =
        match variant_id with
        | Some vid -> fmt.adt_variant_to_string def_id vid
        | None -> fmt.type_def_id_to_string def_id
      in
      if field_values <> [] then
        match fmt.adt_field_names def_id variant_id with
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
  | Adt (Assumed aty, _) -> (
      (* Assumed type *)
      match aty with
      | Result ->
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then
            match field_values with
            | [ v ] -> "@Result::Return " ^ v
            | _ -> failwith "Result::Return takes exactly one value"
          else if variant_id = result_fail_id then (
            assert (field_values = []);
            "@Result::Fail")
          else failwith "Unreachable: improper variant id for result type"
      | Option ->
          let variant_id = Option.get variant_id in
          if variant_id = option_some_id then
            match field_values with
            | [ v ] -> "@Option::Some " ^ v
            | _ -> failwith "Option::Some takes exactly one value"
          else if variant_id = option_none_id then (
            assert (field_values = []);
            "@Option::None")
          else failwith "Unreachable: improper variant id for result type"
      | Vec ->
          assert (variant_id = None);
          let field_values =
            List.mapi (fun i v -> string_of_int i ^ " -> " ^ v) field_values
          in
          "Vec [" ^ String.concat "; " field_values ^ "]")
  | _ -> failwith "Inconsistent typed value"

let rec typed_lvalue_to_string (fmt : value_formatter) (v : typed_lvalue) :
    string =
  match v.value with
  | LvConcrete cv -> Print.Values.constant_value_to_string cv
  | LvVar var -> var_or_dummy_to_string fmt var
  | LvAdt av ->
      adt_g_value_to_string fmt
        (typed_lvalue_to_string fmt)
        av.variant_id av.field_values v.ty

let rec typed_rvalue_to_string (fmt : ast_formatter) (v : typed_rvalue) : string
    =
  match v.value with
  | RvConcrete cv -> Print.Values.constant_value_to_string cv
  | RvPlace p -> place_to_string fmt p
  | RvAdt av ->
      adt_g_value_to_string
        (ast_to_value_formatter fmt)
        (typed_rvalue_to_string fmt)
        av.variant_id av.field_values v.ty

let fun_sig_to_string (fmt : ast_formatter) (sg : fun_sig) : string =
  let ty_fmt = ast_to_type_formatter fmt in
  let type_params = List.map type_var_to_string sg.type_params in
  let inputs = List.map (ty_to_string ty_fmt) sg.inputs in
  let outputs = List.map (ty_to_string ty_fmt) sg.outputs in
  let outputs =
    match outputs with
    | [] ->
        (* Can happen with backward functions which don't give back
         * anything (shared borrows only) *)
        "()"
    | [ out ] -> out
    | outputs -> "(" ^ String.concat " * " outputs ^ ")"
  in
  let all_types = List.concat [ type_params; inputs; [ outputs ] ] in
  String.concat " -> " all_types

let inst_fun_sig_to_string (fmt : ast_formatter) (sg : inst_fun_sig) : string =
  let ty_fmt = ast_to_type_formatter fmt in
  let inputs = List.map (ty_to_string ty_fmt) sg.inputs in
  let outputs = List.map (ty_to_string ty_fmt) sg.outputs in
  let outputs =
    match outputs with
    | [] -> "()"
    | [ out ] -> out
    | outputs -> "(" ^ String.concat " * " outputs ^ ")"
  in
  let all_types = List.append inputs [ outputs ] in
  String.concat " -> " all_types

let regular_fun_id_to_string (fmt : ast_formatter) (fun_id : A.fun_id) : string
    =
  match fun_id with
  | A.Local fid -> fmt.fun_def_id_to_string fid
  | A.Assumed fid -> (
      match fid with
      | A.Replace -> "core::mem::replace"
      | A.BoxNew -> "alloc::boxed::Box::new"
      | A.BoxDeref -> "core::ops::deref::Deref::deref"
      | A.BoxDerefMut -> "core::ops::deref::DerefMut::deref_mut"
      | A.BoxFree -> "alloc::alloc::box_free"
      | A.VecNew -> "alloc::vec::Vec::new"
      | A.VecPush -> "alloc::vec::Vec::push"
      | A.VecInsert -> "alloc::vec::Vec::insert"
      | A.VecLen -> "alloc::vec::Vec::len"
      | A.VecIndex -> "core::ops::index::Index<alloc::vec::Vec>::index"
      | A.VecIndexMut ->
          "core::ops::index::IndexMut<alloc::vec::Vec>::index_mut")

let fun_suffix (rg_id : T.RegionGroupId.id option) : string =
  match rg_id with
  | None -> ""
  | Some rg_id -> "@" ^ T.RegionGroupId.to_string rg_id

let unop_to_string (unop : unop) : string =
  match unop with Not -> "¬" | Neg _ -> "-"

let binop_to_string = Print.CfimAst.binop_to_string

let fun_id_to_string (fmt : ast_formatter) (fun_id : fun_id) : string =
  match fun_id with
  | Regular (fun_id, rg_id) ->
      let f = regular_fun_id_to_string fmt fun_id in
      f ^ fun_suffix rg_id
  | Unop unop -> unop_to_string unop
  | Binop (binop, int_ty) ->
      binop_to_string binop ^ "<" ^ integer_type_to_string int_ty ^ ">"

let mplace_to_string (fmt : ast_formatter) (p : mplace) : string =
  let name = match p.name with None -> "_" | Some name -> name in
  projection_to_string fmt name p.projection

let meta_to_string (fmt : ast_formatter) (meta : meta) : string =
  let meta =
    match meta with
    | Assignment (p, rv) ->
        "@assign(" ^ mplace_to_string fmt p ^ " := "
        ^ typed_rvalue_to_string fmt rv
        ^ ")"
  in
  "@meta[" ^ meta ^ "]"

let rec expression_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (e : expression) : string =
  match e with
  | Value (v, _) -> typed_rvalue_to_string fmt v
  | Call call -> call_to_string fmt indent indent_incr call
  | Let (monadic, lv, re, e) ->
      let_to_string fmt indent indent_incr monadic lv re e
  | Switch (scrutinee, body) ->
      switch_to_string fmt indent indent_incr scrutinee body
  | Meta (meta, e) ->
      let meta = meta_to_string fmt meta in
      let e = texpression_to_string fmt indent indent_incr e in
      indent ^ meta ^ "\n" ^ e

and texpression_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (e : texpression) : string =
  expression_to_string fmt indent indent_incr e.e

and call_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (call : call) : string =
  let ty_fmt = ast_to_type_formatter fmt in
  let tys = List.map (ty_to_string ty_fmt) call.type_params in
  (* The arguments are expressions, so indentation might get weird... (though
   * those expressions will in most cases just be values) *)
  let indent1 = indent ^ indent_incr in
  let args =
    List.map (texpression_to_string fmt indent1 indent_incr) call.args
  in
  let all_args = List.append tys args in
  let fun_id = fun_id_to_string fmt call.func in
  if all_args = [] then fun_id else fun_id ^ " " ^ String.concat " " all_args

and let_to_string (fmt : ast_formatter) (indent : string) (indent_incr : string)
    (monadic : bool) (lv : typed_lvalue) (re : texpression) (e : texpression) :
    string =
  let indent1 = indent ^ indent_incr in
  let val_fmt = ast_to_value_formatter fmt in
  let re = texpression_to_string fmt indent1 indent_incr re in
  let e = texpression_to_string fmt indent indent_incr e in
  let lv = typed_lvalue_to_string val_fmt lv in
  if monadic then lv ^ " <-- " ^ re ^ ";\n" ^ indent ^ e
  else "let " ^ lv ^ " = " ^ re ^ " in\n" ^ indent ^ e

and switch_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (scrutinee : texpression) (body : switch_body) :
    string =
  let indent1 = indent ^ indent_incr in
  (* Printing can mess up on the scrutinee, because it is an expression - but
   * in most situations it will be a value or a function call, so it should be
   * ok*)
  let scrut = texpression_to_string fmt indent1 indent_incr scrutinee in
  match body with
  | If (e_true, e_false) ->
      let e_true = texpression_to_string fmt indent1 indent_incr e_true in
      let e_false = texpression_to_string fmt indent1 indent_incr e_false in
      "if " ^ scrut ^ "\n" ^ indent ^ "then\n" ^ indent ^ e_true ^ "\n" ^ indent
      ^ "else\n" ^ indent ^ e_false
  | Match branches ->
      let val_fmt = ast_to_value_formatter fmt in
      let branch_to_string (b : match_branch) : string =
        let pat = typed_lvalue_to_string val_fmt b.pat in
        indent ^ "| " ^ pat ^ " ->\n" ^ indent1
        ^ texpression_to_string fmt indent1 indent_incr b.branch
      in
      let branches = List.map branch_to_string branches in
      "match " ^ scrut ^ " with\n" ^ String.concat "\n" branches

let fun_def_to_string (fmt : ast_formatter) (def : fun_def) : string =
  let type_fmt = ast_to_type_formatter fmt in
  let name = name_to_string def.basename ^ fun_suffix def.back_id in
  let signature = fun_sig_to_string fmt def.signature in
  let inputs = List.map (var_to_string type_fmt) def.inputs in
  let inputs =
    if inputs = [] then "" else "  fun " ^ String.concat " " inputs ^ " ->\n"
  in
  let body = texpression_to_string fmt "  " "  " def.body in
  "let " ^ name ^ " :\n  " ^ signature ^ " =\n" ^ inputs ^ "  " ^ body
