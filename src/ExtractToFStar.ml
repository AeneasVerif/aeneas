(** Extract to F* *)

open Errors
open Pure
open TranslateCore
open PureToExtract
module F = Format

(** Iter "between".

    Iterate over a list, but call a function between every two elements
    (but not before the first element, and not after the last).
 *)
let list_iterb (between : unit -> unit) (f : 'a -> unit) (ls : 'a list) : unit =
  let rec iter ls =
    match ls with
    | [] -> ()
    | [ x ] -> f x
    | x :: y :: ls ->
        f x;
        between ();
        iter (y :: ls)
  in
  iter ls

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
          list_iterb (F.pp_print_space fmt) (extract_ty ctx fmt true) tys;
          F.pp_print_string fmt ")"
      | AdtId _ | Assumed _ ->
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt (ctx_get_type type_id ctx);
          if tys <> [] then F.pp_print_space fmt ();
          list_iterb (F.pp_print_space fmt) (extract_ty ctx fmt true) tys;
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
    (def : type_def) (type_name : string) (type_params : string list)
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
            F.pp_space fmt ();
            ctx
      in
      (* Print the field type *)
      extract_ty ctx fmt false f.field_ty;
      (* Print the arrow `->`*)
      F.pp_space fmt ();
      F.pp_print_string "->";
      (* Close the field box *)
      F.pp_close_box fmt ();
      F.pp_space fmt ();
      (* Return *)
      ctx
    in
    (* Print the fields *)
    let fields = FieldId.mapi (fun fid f -> (fid, f)) variant.fields in
    let ctx =
      List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
    in
    (* Print the final type *)
    F.pp_open_hovbox fmt ();
    F.pp_string fmt def_name;
    List.iter
      (fun type_param ->
        F.pp_space fmt ();
        F.pp_string fmt type_param)
      type_params;
    F.pp_close_hovbox fmt ();
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
  | Struct fields -> extract_type_def_struct_body ctx_body fmt fields
  | Enum variants ->
      extract_type_def_enum_body ctx_body fmt def def_name type_params variants);
  ctx
