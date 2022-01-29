(** Extract to F* *)

open Errors
open Pure
open TranslateCore
open PureToExtract
open StringUtils
module F = Format

(*let mk_name_formatter =
    let int_name (int_ty : integer_type)  =
      match int_ty with
      | Isize -> "isize"
      | I8 -> "i8"
      | I16 -> "i16"
      | I32 -> "i32"
      | I64 -> "i64"
      | I128 -> "i128"
      | Usize -> "usize"
      | U8 -> "u8"
      | U16 -> "u16"
      | U32 -> "u32"
      | U64 -> "u64"
      | U128 -> "u128"
    in
    (* For now, we treat only the case where the type name is:
     * `Module::Type`
     * *)
    let type_name name =
      let name = Collections.List.pop_last name in
      to_snake_case name
    in
    let field_name (def_name : name) (field_id : FieldId.id) (field_name : string option) : string =
      let def_name = type_name def_name in
      match field_name with
      | Some field_name -> def_name ^ "_" ^ field_name
      | None -> def_name ^ "_f" ^ FieldId.to_string field_id
    in
    let variant_name (def_name :name) (variant : string) : string =
      type_name def_name ^ to_camel_case variant
    in
    {
      bool_name : "bool";
      char_name : "char";
      int_name;
      str_name : "string";
      field_name;
      variant_name;
      type_name;
      fun_name : A.fun_id -> name -> int -> region_group_info option -> string;
      var_basename : StringSet.t -> ty -> string;
      type_var_basename : StringSet.t -> string;
      append_index : string -> int -> string;
  }*)

(** [inside] constrols whether we should add parentheses or not around type
    application (if `true` we add parentheses).
 *)
let rec extract_ty (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (ty : ty) : unit =
  match ty with
  | Adt (type_id, tys) -> (
      match type_id with
      | Tuple ->
          F.pp_print_string fmt "(";
          Collections.List.iter_link (F.pp_print_space fmt)
            (extract_ty ctx fmt true) tys;
          F.pp_print_string fmt ")"
      | AdtId _ | Assumed _ ->
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt (ctx_get_type type_id ctx);
          if tys <> [] then F.pp_print_space fmt ();
          Collections.List.iter_link (F.pp_print_space fmt)
            (extract_ty ctx fmt true) tys;
          if inside then F.pp_print_string fmt ")")
  | TypeVar vid -> F.pp_print_string fmt (ctx_get_type_var vid ctx)
  | Bool -> F.pp_print_string fmt ctx.fmt.bool_name
  | Char -> F.pp_print_string fmt ctx.fmt.char_name
  | Integer int_ty -> F.pp_print_string fmt (ctx.fmt.int_name int_ty)
  | Str -> F.pp_print_string fmt ctx.fmt.str_name
  | Array _ | Slice _ -> raise Unimplemented

let extract_type_def_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) (fields : field list) : unit =
  (* We want to generate a definition which looks like this:
   * ```
   * type t = { x : int; y : bool; }
   * ```
   *
   * Or if there isn't enough space on one line:
   * ```
   * type t = {
   *   x : int;
   *   y : bool;
   * }
   * ```
   * Note that we already printed: `type t =`
   *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "{";
  (* The body itself *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;
  F.pp_print_space fmt ();
  (* Print the fields *)
  let print_field (field_id : FieldId.id) (f : field) : unit =
    let field_name = ctx_get_field def.def_id field_id ctx in
    F.pp_open_box fmt ctx.indent_incr;
    F.pp_print_string fmt field_name;
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    extract_ty ctx fmt false f.field_ty;
    F.pp_close_box fmt ()
  in
  let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
  List.iter (fun (fid, f) -> print_field fid f) fields;
  (* Close *)
  F.pp_close_box fmt ();
  F.pp_print_string fmt "}";
  F.pp_close_box fmt ()

let extract_type_def_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) (def_name : string) (type_params : string list)
    (variants : variant list) : unit =
  (* We want to generate a definition which looks like this:
   * ```
   * type list a = | Cons : a -> list a -> list a | Nil : list a
   * ```
   *
   * If there isn't enough space on one line:
   * ```
   * type s =
   * | Cons : a -> list a -> list a
   * | Nil : list a
   * ```
   *
   * And if we need to write the type of a variant on several lines:
   * ```
   * type s =
   * | Cons :
   *   a ->
   *   list a ->
   *   list a
   * | Nil : list a
   * ```
   *
   * Finally, it is possible to give names to the variant fields in Rust.
   * In this situation, we generate a definition like this:
   * ```
   * type s =
   * | Cons : hd:a -> tl:list a -> list a
   * | Nil : list a
   * ```
   *
   * Note that we already printed: `type s =`
   *)
  (* Open the body box *)
  F.pp_open_hvbox fmt 0;
  (* Print the variants *)
  let print_variant (variant_id : VariantId.id) (variant : variant) : unit =
    let variant_name = ctx_get_variant def.def_id variant_id ctx in
    F.pp_print_space fmt ();
    F.pp_open_hvbox fmt ctx.indent_incr;
    (* variant box *)
    (* `| Cons :`
     * Note that we really don't want any break above so we print everything
     * at once. *)
    F.pp_print_string fmt ("| " ^ variant_name ^ " :");
    F.pp_print_space fmt ();
    let print_field (fid : FieldId.id) (f : field) (ctx : extraction_ctx) :
        extraction_ctx =
      (* Open the field box *)
      F.pp_open_box fmt ctx.indent_incr;
      (* Print the field names
       * `  x :`
       * Note that when printing fields, we register the field names as
       * *variables*: they don't need to be unique at the top level. *)
      let ctx =
        match f.field_name with
        | None -> ctx
        | Some field_name ->
            let var_id = VarId.of_int (FieldId.to_int fid) in
            let ctx, field_name = ctx_add_var field_name var_id ctx in
            F.pp_print_string fmt (field_name ^ " :");
            F.pp_print_space fmt ();
            ctx
      in
      (* Print the field type *)
      extract_ty ctx fmt false f.field_ty;
      (* Print the arrow `->`*)
      F.pp_print_space fmt ();
      F.pp_print_string fmt "->";
      (* Close the field box *)
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* Return *)
      ctx
    in
    (* Print the fields *)
    let fields = FieldId.mapi (fun fid f -> (fid, f)) variant.fields in
    let ctx =
      List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
    in
    (* Print the final type *)
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt def_name;
    List.iter
      (fun type_param ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt type_param)
      type_params;
    F.pp_close_box fmt ();
    (* Close the variant box *)
    F.pp_close_box fmt ()
  in
  (* Print the variants *)
  let variants = VariantId.mapi (fun vid v -> (vid, v)) variants in
  List.iter (fun (vid, v) -> print_variant vid v) variants;
  (* Close the body box *)
  F.pp_close_box fmt ()

let rec extract_type_def (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) : extraction_ctx =
  (* Compute and register the type def name *)
  let ctx, def_name = ctx_add_type_def def ctx in
  (* Compute and register:
   * - the variant names, if this is an enumeration
   * - the field names, if this is a structure
   * We do this because in F*, they have to be unique at the top-level.
   *)
  let ctx =
    match def.kind with
    | Struct fields ->
        fst (ctx_add_fields def (FieldId.mapi (fun id f -> (id, f)) fields) ctx)
    | Enum variants ->
        fst
          (ctx_add_variants def
             (VariantId.mapi (fun id v -> (id, v)) variants)
             ctx)
  in
  (* Add the type params - note that we remember those bindings only for the
   * body translation: the updated ctx we return at the end of the function
   * only contains the registered type def and variant names *)
  let ctx_body, type_params = ctx_add_type_params def.type_params ctx in
  (* > "type TYPE_NAME =" *)
  F.pp_print_string fmt "type";
  F.pp_print_space fmt ();
  F.pp_print_string fmt def_name;
  (match def.kind with
  | Struct fields -> extract_type_def_struct_body ctx_body fmt def fields
  | Enum variants ->
      extract_type_def_enum_body ctx_body fmt def def_name type_params variants);
  ctx
