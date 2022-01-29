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
          F.pp_print_string fmt (ctx_find_type type_id ctx);
          if tys <> [] then F.pp_print_space fmt ();
          list_iterb (F.pp_print_space fmt) (extract_ty ctx fmt true) tys;
          if inside then F.pp_print_string fmt ")")
  | TypeVar vid -> F.pp_print_string fmt (ctx_find_type_var vid ctx)
  | Bool -> F.pp_print_string fmt ctx.fmt.bool_name
  | Char -> F.pp_print_string fmt ctx.fmt.char_name
  | Integer int_ty -> F.pp_print_string fmt (ctx.fmt.int_name int_ty)
  | Str -> F.pp_print_string fmt ctx.fmt.str_name
  | Array _ | Slice _ -> raise Unimplemented

let extract_type_def_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_name : string) (type_params : string list) (fields : field list) :
    unit =
  (* We want to generate a definition which looks like this:
   * ```
   * type s = { x : int; y : bool; }
   * ```
   *
   * Or if there isn't enough space on one line:
   * ```
   * type s = {
   *   x : int;
   *   y : bool;
   * }
   * ```
   * Note that we already printed: `type s =`
   *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "{";
  (* The body itself *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;
  F.pp_print_space fmt ();
  (* Print the fields *)
  let print_field (f : field) : unit =
    let field_name = ctx.fmt.field_name type_name f.field_name in
    F.pp_open_box fmt ctx.indent_incr;
    F.pp_print_string fmt field_name;
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    extract_ty ctx fmt false f.field_ty;
    F.pp_close_box fmt ()
  in
  List.iter print_field fields;
  (* Close *)
  F.pp_close_box fmt ();
  F.pp_print_string fmt "}";
  F.pp_close_box fmt ()

let extract_type_def_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_name : string) (type_params : string list) (variants : variant list) :
    unit =
  raise Unimplemented

let rec extract_type_def (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) : unit =
  let name = ctx_find_local_type def.def_id ctx in
  let ctx, type_params = ctx_add_type_params def.type_params ctx in
  (* > "type TYPE_NAME =" *)
  F.pp_print_string fmt "type";
  F.pp_print_space fmt ();
  F.pp_print_string fmt name;
  match def.kind with
  | Struct fields ->
      extract_type_def_struct_body ctx fmt name type_params fields
  | Enum variants ->
      extract_type_def_enum_body ctx fmt name type_params variants

(*let rec extract_field (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (ty : ty) : unit =*)
