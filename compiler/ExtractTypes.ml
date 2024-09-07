(** The generic extraction *)

open Pure
open PureUtils
open TranslateCore
open Config
open Errors
include ExtractBase
module T = Types

(** Format a constant value.

    Inputs:
    - formatter
    - [is_pattern]: if [true], it means we are generating a (match) pattern
    - [inside]: if [true], the value should be wrapped in parentheses
      if it is made of an application (ex.: [U32 3])
    - the constant value
 *)
let extract_literal (span : Meta.span) (fmt : F.formatter) (is_pattern : bool)
    (inside : bool) (cv : literal) : unit =
  match cv with
  | VScalar sv -> (
      match backend () with
      | FStar -> F.pp_print_string fmt (Z.to_string sv.value)
      | Coq | HOL4 | Lean ->
          let print_brackets = inside && backend () = HOL4 in
          if print_brackets then F.pp_print_string fmt "(";
          (match backend () with
          | Coq | Lean -> ()
          | HOL4 ->
              F.pp_print_string fmt ("int_to_" ^ int_name sv.int_ty);
              F.pp_print_space fmt ()
          | _ -> craise __FILE__ __LINE__ span "Unreachable");
          (* We need to add parentheses if the value is negative *)
          if sv.value >= Z.of_int 0 then
            F.pp_print_string fmt (Z.to_string sv.value)
          else F.pp_print_string fmt ("(" ^ Z.to_string sv.value ^ ")");
          (match backend () with
          | Coq ->
              let iname = int_name sv.int_ty in
              F.pp_print_string fmt ("%" ^ iname)
          | Lean ->
              (* We don't use the same notation for patterns and regular literals *)
              if is_pattern then F.pp_print_string fmt "#scalar"
              else
                let iname = String.lowercase_ascii (int_name sv.int_ty) in
                F.pp_print_string fmt ("#" ^ iname)
          | HOL4 -> ()
          | _ -> craise __FILE__ __LINE__ span "Unreachable");
          if print_brackets then F.pp_print_string fmt ")")
  | VBool b ->
      let b =
        match backend () with
        | HOL4 -> if b then "T" else "F"
        | Coq | FStar | Lean -> if b then "true" else "false"
      in
      F.pp_print_string fmt b
  | VChar c -> (
      match backend () with
      | HOL4 ->
          (* [#"a"] is a notation for [CHR 97] (97 is the ASCII code for 'a') *)
          F.pp_print_string fmt ("#\"" ^ String.make 1 c ^ "\"")
      | FStar | Lean -> F.pp_print_string fmt ("'" ^ String.make 1 c ^ "'")
      | Coq ->
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt "char_of_byte";
          F.pp_print_space fmt ();
          (* Convert the the char to ascii *)
          let c =
            let i = Char.code c in
            let x0 = i / 16 in
            let x1 = i mod 16 in
            "Coq.Init.Byte.x" ^ string_of_int x0 ^ string_of_int x1
          in
          F.pp_print_string fmt c;
          if inside then F.pp_print_string fmt ")")
  | VStr _ | VByteStr _ ->
      craise __FILE__ __LINE__ span
        "String and byte string literals are unsupported"

(** Format a unary operation

    Inputs:
    - a formatter for expressions (called on the argument of the unop)
    - extraction context (see below)
    - formatter
    - expression formatter
    - [inside]
    - unop
    - argument
 *)
let extract_unop (span : Meta.span) (extract_expr : bool -> texpression -> unit)
    (fmt : F.formatter) (inside : bool) (unop : unop) (arg : texpression) : unit
    =
  match unop with
  | Not _ | Neg _ ->
      let unop = unop_name unop in
      if inside then F.pp_print_string fmt "(";
      F.pp_print_string fmt unop;
      F.pp_print_space fmt ();
      extract_expr true arg;
      if inside then F.pp_print_string fmt ")"
  | Cast (src, tgt) -> (
      (* HOL4 has a special treatment: because it doesn't support dependent
         types, we don't have a specific operator for the cast *)
      match backend () with
      | HOL4 ->
          (* Casting, say, an u32 to an i32 would be done as follows:
             {[
               mk_i32 (u32_to_int x)
             ]}
          *)
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt ("mk_" ^ scalar_name tgt);
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          F.pp_print_string fmt (scalar_name src ^ "_to_int");
          F.pp_print_space fmt ();
          extract_expr true arg;
          F.pp_print_string fmt ")";
          if inside then F.pp_print_string fmt ")"
      | FStar | Coq | Lean ->
          if inside then F.pp_print_string fmt "(";
          (* Rem.: the source type is an implicit parameter *)
          (* Different cases depending on the conversion *)
          (let cast_str, src, tgt =
             let integer_type_to_string (ty : integer_type) : string =
               if backend () = Lean then "." ^ int_name ty
               else
                 StringUtils.capitalize_first_letter
                   (PrintPure.integer_type_to_string ty)
             in
             match (src, tgt) with
             | TInteger src, TInteger tgt ->
                 let cast_str =
                   match backend () with
                   | Coq | FStar -> "scalar_cast"
                   | Lean -> "Scalar.cast"
                   | HOL4 -> craise __FILE__ __LINE__ span "Unreachable"
                 in
                 let src =
                   if backend () <> Lean then Some (integer_type_to_string src)
                   else None
                 in
                 let tgt = integer_type_to_string tgt in
                 (cast_str, src, Some tgt)
             | TBool, TInteger tgt ->
                 let cast_str =
                   match backend () with
                   | Coq | FStar -> "scalar_cast_bool"
                   | Lean -> "Scalar.cast_bool"
                   | HOL4 -> craise __FILE__ __LINE__ span "Unreachable"
                 in
                 let tgt = integer_type_to_string tgt in
                 (cast_str, None, Some tgt)
             | TInteger _, TBool ->
                 (* This is not allowed by rustc: the way of doing it in Rust is: [x != 0] *)
                 craise __FILE__ __LINE__ span
                   "Unexpected cast: integer to bool"
             | TBool, TBool ->
                 (* There shouldn't be any cast here. Note that if
                    one writes [b as bool] in Rust (where [b] is a
                    boolean), it gets compiled to [b] (i.e., no cast
                    is introduced). *)
                 craise __FILE__ __LINE__ span "Unexpected cast: bool to bool"
             | _ -> craise __FILE__ __LINE__ span "Unreachable"
           in
           (* Print the name of the function *)
           F.pp_print_string fmt cast_str;
           (* Print the src type argument *)
           (match src with
           | None -> ()
           | Some src ->
               F.pp_print_space fmt ();
               F.pp_print_string fmt src);
           (* Print the tgt type argument *)
           match tgt with
           | None -> ()
           | Some tgt ->
               F.pp_print_space fmt ();
               F.pp_print_string fmt tgt);
          (* Extract the argument *)
          F.pp_print_space fmt ();
          extract_expr true arg;
          if inside then F.pp_print_string fmt ")")

(** Format a binary operation

    Inputs:
    - a formatter for expressions (called on the arguments of the binop)
    - extraction context (see below)
    - formatter
    - expression formatter
    - [inside]
    - binop
    - argument 0
    - argument 1
 *)
let extract_binop (span : Meta.span)
    (extract_expr : bool -> texpression -> unit) (fmt : F.formatter)
    (inside : bool) (binop : E.binop) (int_ty : integer_type)
    (arg0 : texpression) (arg1 : texpression) : unit =
  if inside then F.pp_print_string fmt "(";
  (* Some binary operations have a special notation depending on the backend *)
  (match (backend (), binop) with
  | HOL4, (Eq | Ne)
  | (FStar | Coq | Lean), (Eq | Lt | Le | Ne | Ge | Gt)
  | Lean, (Div | Rem | Add | Sub | Mul | Shl | Shr | BitXor | BitOr | BitAnd) ->
      let binop =
        match binop with
        | Eq -> "="
        | Lt -> "<"
        | Le -> "<="
        | Ne -> if backend () = Lean then "!=" else "<>"
        | Ge -> ">="
        | Gt -> ">"
        | Div -> "/"
        | Rem -> "%"
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | CheckedAdd | CheckedSub | CheckedMul ->
            craise __FILE__ __LINE__ span
              "Checked operations are not implemented"
        | Shl -> "<<<"
        | Shr -> ">>>"
        | BitXor -> "^^^"
        | BitOr -> "|||"
        | BitAnd -> "&&&"
      in
      let binop =
        match backend () with
        | FStar | Lean | HOL4 -> binop
        | Coq -> "s" ^ binop
      in
      extract_expr false arg0;
      F.pp_print_space fmt ();
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | _ ->
      let binop_is_shift =
        match binop with
        | Shl | Shr -> true
        | _ -> false
      in
      let binop = named_binop_name binop int_ty in
      F.pp_print_string fmt binop;
      (* In the case of F*, for shift operations, because machine integers
         are simply integers with a refinement, if the second argument is a
         constant we need to provide the second implicit type argument *)
      if binop_is_shift && backend () = FStar && is_const arg1 then (
        F.pp_print_space fmt ();
        let ty = ty_as_integer span arg1.ty in
        F.pp_print_string fmt
          ("#" ^ StringUtils.capitalize_first_letter (int_name ty)));
      F.pp_print_space fmt ();
      extract_expr true arg0;
      F.pp_print_space fmt ();
      extract_expr true arg1);
  if inside then F.pp_print_string fmt ")"

let is_single_opaque_fun_decl_group (dg : Pure.fun_decl list) : bool =
  match dg with
  | [ d ] -> d.body = None
  | _ -> false

let is_single_opaque_type_decl_group (dg : Pure.type_decl list) : bool =
  match dg with
  | [ d ] -> d.kind = Opaque
  | _ -> false

let is_empty_record_type_decl (d : Pure.type_decl) : bool = d.kind = Struct []

let is_empty_record_type_decl_group (dg : Pure.type_decl list) : bool =
  match dg with
  | [ d ] -> is_empty_record_type_decl d
  | _ -> false

(** In some provers, groups of definitions must be delimited.

    - in Coq, *every* group (including singletons) must end with "."
    - in Lean, groups of mutually recursive definitions must end with "end"
    - in HOL4 (in most situations) the whole group must be within a `Define` command

    Calls to {!Extract.extract_fun_decl} should be inserted between calls to
    {!start_fun_decl_group} and {!end_fun_decl_group}.

    TODO: maybe those [{start/end}_decl_group] functions are not that much a good
    idea and we should merge them with the corresponding [extract_decl] functions.
 *)
let start_fun_decl_group (ctx : extraction_ctx) (fmt : F.formatter)
    (is_rec : bool) (dg : Pure.fun_decl list) =
  match backend () with
  | FStar | Coq | Lean -> ()
  | HOL4 ->
      (* In HOL4, opaque functions have a special treatment *)
      if is_single_opaque_fun_decl_group dg then ()
      else
        let compute_fun_def_name (def : Pure.fun_decl) : string =
          ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
          ^ "_def"
        in
        let names = List.map compute_fun_def_name dg in
        (* Add a break before *)
        F.pp_print_break fmt 0 0;
        (* Open the box for the delimiters *)
        F.pp_open_vbox fmt 0;
        (* Open the box for the definitions themselves *)
        F.pp_open_vbox fmt ctx.indent_incr;
        (* Print the delimiters *)
        if is_rec then
          F.pp_print_string fmt
            ("val [" ^ String.concat ", " names ^ "] = DefineDiv ‘")
        else (
          sanity_check_opt_span __FILE__ __LINE__ (List.length names = 1) None;
          let name = List.hd names in
          F.pp_print_string fmt ("val " ^ name ^ " = Define ‘"));
        F.pp_print_cut fmt ()

(** See {!start_fun_decl_group}. *)
let end_fun_decl_group (fmt : F.formatter) (is_rec : bool)
    (dg : Pure.fun_decl list) =
  match backend () with
  | FStar -> ()
  | Coq ->
      (* For aesthetic reasons, we print the Coq end group delimiter directly
         in {!extract_fun_decl}. *)
      ()
  | Lean ->
      (* We must add the "end" keyword to groups of mutually recursive functions *)
      if is_rec && List.length dg > 1 then (
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "end";
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)
      else ()
  | HOL4 ->
      (* In HOL4, opaque functions have a special treatment *)
      if is_single_opaque_fun_decl_group dg then ()
      else (
        (* Close the box for the definitions *)
        F.pp_close_box fmt ();
        (* Print the end delimiter *)
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "’";
        (* Close the box for the delimiters *)
        F.pp_close_box fmt ();
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)

(** See {!start_fun_decl_group}: similar usage, but for the type declarations. *)
let start_type_decl_group (ctx : extraction_ctx) (fmt : F.formatter)
    (is_rec : bool) (dg : Pure.type_decl list) =
  match backend () with
  | FStar | Coq -> ()
  | Lean ->
      if is_rec && List.length dg > 1 then (
        F.pp_print_space fmt ();
        F.pp_print_string fmt "mutual";
        F.pp_print_space fmt ())
  | HOL4 ->
      (* In HOL4, opaque types and empty records have a special treatment *)
      if
        is_single_opaque_type_decl_group dg
        || is_empty_record_type_decl_group dg
      then ()
      else (
        (* Add a break before *)
        F.pp_print_break fmt 0 0;
        (* Open the box for the delimiters *)
        F.pp_open_vbox fmt 0;
        (* Open the box for the definitions themselves *)
        F.pp_open_vbox fmt ctx.indent_incr;
        (* Print the delimiters *)
        F.pp_print_string fmt "Datatype:";
        F.pp_print_cut fmt ())

(** See {!start_fun_decl_group}. *)
let end_type_decl_group (fmt : F.formatter) (is_rec : bool)
    (dg : Pure.type_decl list) =
  match backend () with
  | FStar -> ()
  | Coq ->
      (* For aesthetic reasons, we print the Coq end group delimiter directly
         in {!extract_fun_decl}. *)
      ()
  | Lean ->
      (* We must add the "end" keyword to groups of mutually recursive functions *)
      if is_rec && List.length dg > 1 then (
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "end";
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)
      else ()
  | HOL4 ->
      (* In HOL4, opaque types and empty records have a special treatment *)
      if
        is_single_opaque_type_decl_group dg
        || is_empty_record_type_decl_group dg
      then ()
      else (
        (* Close the box for the definitions *)
        F.pp_close_box fmt ();
        (* Print the end delimiter *)
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "End";
        (* Close the box for the delimiters *)
        F.pp_close_box fmt ();
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)

let unit_name () =
  match backend () with
  | Lean -> "Unit"
  | Coq | FStar | HOL4 -> "unit"

(** Small helper *)
let extract_arrow (fmt : F.formatter) () : unit =
  if Config.backend () = Lean then F.pp_print_string fmt "→"
  else F.pp_print_string fmt "->"

let extract_const_generic (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (inside : bool) (cg : const_generic) : unit =
  match cg with
  | CgGlobal id ->
      let s = ctx_get_global span id ctx in
      F.pp_print_string fmt s
  | CgValue v -> extract_literal span fmt false inside v
  | CgVar id ->
      let s = ctx_get_const_generic_var span id ctx in
      F.pp_print_string fmt s

let extract_literal_type (_ctx : extraction_ctx) (fmt : F.formatter)
    (ty : literal_type) : unit =
  match ty with
  | TBool -> F.pp_print_string fmt (bool_name ())
  | TChar -> F.pp_print_string fmt (char_name ())
  | TInteger int_ty -> F.pp_print_string fmt (int_name int_ty)
  | TFloat float_ty -> F.pp_print_string fmt (float_name float_ty)

(** [inside] constrols whether we should add parentheses or not around type
    applications (if [true] we add parentheses).

    [no_params_tys]: for all the types inside this set, do not print the type parameters.
    This is used for HOL4. As polymorphism is uniform in HOL4, printing the
    type parameters in the recursive definitions is useless (and actually
    forbidden).

    For instance, where in F* we would write:
    {[
      type list a = | Nil : list a | Cons : a -> list a -> list a
    ]}

    In HOL4 we would simply write:
    {[
      Datatype:
        list = Nil 'a | Cons 'a list
      End
    ]}
 *)

let extract_ty_errors (fmt : F.formatter) : unit =
  match Config.backend () with
  | FStar | Coq -> F.pp_print_string fmt "admit"
  | Lean -> F.pp_print_string fmt "sorry"
  | HOL4 -> F.pp_print_string fmt "(* ERROR: could not generate the code *)"

let rec extract_ty (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (inside : bool) (ty : ty) : unit =
  let extract_rec = extract_ty span ctx fmt no_params_tys in
  match ty with
  | TAdt (type_id, generics) -> (
      let has_params = generics <> empty_generic_args in
      match type_id with
      | TTuple ->
          (* This is a bit annoying, but in F*/Coq/HOL4 [()] is not the unit type:
           * we have to write [unit]... *)
          if generics.types = [] then F.pp_print_string fmt (unit_name ())
          else (
            F.pp_print_string fmt "(";
            Collections.List.iter_link
              (fun () ->
                F.pp_print_space fmt ();
                let product =
                  match backend () with
                  | FStar -> "&"
                  | Coq -> "*"
                  | Lean -> "×"
                  | HOL4 -> "#"
                in
                F.pp_print_string fmt product;
                F.pp_print_space fmt ())
              (extract_rec true) generics.types;
            F.pp_print_string fmt ")")
      | TAdtId _ | TAssumed _ -> (
          (* HOL4 behaves differently. Where in Coq/FStar/Lean we would write:
             `tree a b`

             In HOL4 we would write:
             `('a, 'b) tree`
          *)
          match backend () with
          | FStar | Coq | Lean ->
              let print_paren = inside && has_params in
              if print_paren then F.pp_print_string fmt "(";
              (* TODO: for now, only the opaque *functions* are extracted in the
                 opaque module. The opaque *types* are assumed. *)
              F.pp_print_string fmt (ctx_get_type (Some span) type_id ctx);
              (* We might need to filter the type arguments, if the type
                 is builtin (for instance, we filter the global allocator type
                 argument for `Vec`). *)
              let generics =
                match type_id with
                | TAdtId id -> (
                    match
                      TypeDeclId.Map.find_opt id ctx.types_filter_type_args_map
                    with
                    | None -> generics
                    | Some filter ->
                        let types = List.combine filter generics.types in
                        let types =
                          List.filter_map
                            (fun (b, ty) -> if b then Some ty else None)
                            types
                        in
                        { generics with types })
                | _ -> generics
              in
              extract_generic_args span ctx fmt no_params_tys generics;
              if print_paren then F.pp_print_string fmt ")"
          | HOL4 ->
              let { types; const_generics; trait_refs } = generics in
              (* Const generics are not supported in HOL4 *)
              cassert __FILE__ __LINE__ (const_generics = []) span
                "Constant generics are not supported yet when generating code \
                 for HOL4";
              let print_tys =
                match type_id with
                | TAdtId id -> not (TypeDeclId.Set.mem id no_params_tys)
                | TAssumed _ -> true
                | _ -> craise __FILE__ __LINE__ span "Unreachable"
              in
              if types <> [] && print_tys then (
                let print_paren = List.length types > 1 in
                if print_paren then F.pp_print_string fmt "(";
                Collections.List.iter_link
                  (fun () ->
                    F.pp_print_string fmt ",";
                    F.pp_print_space fmt ())
                  (extract_rec true) types;
                if print_paren then F.pp_print_string fmt ")";
                F.pp_print_space fmt ());
              F.pp_print_string fmt (ctx_get_type (Some span) type_id ctx);
              if trait_refs <> [] then (
                F.pp_print_space fmt ();
                Collections.List.iter_link (F.pp_print_space fmt)
                  (extract_trait_ref span ctx fmt no_params_tys true)
                  trait_refs)))
  | TVar vid -> F.pp_print_string fmt (ctx_get_type_var span vid ctx)
  | TLiteral lty -> extract_literal_type ctx fmt lty
  | TArrow (arg_ty, ret_ty) ->
      if inside then F.pp_print_string fmt "(";
      extract_rec false arg_ty;
      F.pp_print_space fmt ();
      extract_arrow fmt ();
      F.pp_print_space fmt ();
      extract_rec false ret_ty;
      if inside then F.pp_print_string fmt ")"
  | TTraitType (trait_ref, type_name) -> (
      if !parameterize_trait_types then
        craise __FILE__ __LINE__ span "Unimplemented"
      else
        let type_name =
          ctx_get_trait_type span trait_ref.trait_decl_ref.trait_decl_id
            type_name ctx
        in
        let add_brackets (s : string) =
          if backend () = Coq then "(" ^ s ^ ")" else s
        in
        (* There may be a special treatment depending on the instance id.
           See the comments for {!extract_trait_instance_id_with_dot}.
           TODO: there should be a cleaner way to do. The annoying thing
           here is that if we project directly over the self clause, then
           we have to be careful (we may not have to print the "Self.").
           Otherwise, we can directly call {!extract_trait_ref}.
        *)
        match trait_ref.trait_id with
        | Self ->
            extract_trait_instance_id_with_dot span ctx fmt no_params_tys false
              trait_ref.trait_id;
            F.pp_print_string fmt type_name
        | _ ->
            (* HOL4 doesn't have 1st class types *)
            cassert __FILE__ __LINE__
              (backend () <> HOL4)
              span
              "Trait types are not supported yet when generating code for HOL4";
            extract_trait_ref span ctx fmt no_params_tys false trait_ref;
            F.pp_print_string fmt ("." ^ add_brackets type_name))
  | Error -> extract_ty_errors fmt

and extract_trait_ref (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t) (inside : bool)
    (tr : trait_ref) : unit =
  extract_trait_instance_id span ctx fmt no_params_tys inside tr.trait_id

and extract_trait_decl_ref (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t) (inside : bool)
    (tr : trait_decl_ref) : unit =
  let use_brackets = tr.decl_generics <> empty_generic_args && inside in
  let name = ctx_get_trait_decl span tr.trait_decl_id ctx in
  if use_brackets then F.pp_print_string fmt "(";
  F.pp_print_string fmt name;
  (* There is something subtle here: the trait obligations for the implemented
     trait are put inside the parent clauses, so we must ignore them here *)
  let generics = { tr.decl_generics with trait_refs = [] } in
  extract_generic_args span ctx fmt no_params_tys generics;
  if use_brackets then F.pp_print_string fmt ")"

and extract_generic_args (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t)
    ?(explicit : explicit_info option = None) (generics : generic_args) : unit =
  let { types; const_generics; trait_refs } = generics in
  if backend () <> HOL4 then (
    (* Filter the input parameters if some of them are implicit *)
    let types, const_generics =
      match explicit with
      | None -> (types, const_generics)
      | Some explicit ->
          let filter (x, e) = if e = Explicit then Some x else None in
          let filter xl explicit =
            List.filter_map filter (List.combine xl explicit)
          in
          ( filter types explicit.explicit_types,
            filter const_generics explicit.explicit_const_generics )
    in
    if types <> [] then (
      F.pp_print_space fmt ();
      Collections.List.iter_link (F.pp_print_space fmt)
        (extract_ty span ctx fmt no_params_tys true)
        types);
    if const_generics <> [] then (
      cassert __FILE__ __LINE__
        (backend () <> HOL4)
        span
        "Constant generics are not supported yet when generating code for HOL4";
      F.pp_print_space fmt ();
      Collections.List.iter_link (F.pp_print_space fmt)
        (extract_const_generic span ctx fmt true)
        const_generics));
  if trait_refs <> [] then (
    F.pp_print_space fmt ();
    Collections.List.iter_link (F.pp_print_space fmt)
      (extract_trait_ref span ctx fmt no_params_tys true)
      trait_refs)

(** We sometimes need to ignore references to `Self` when generating the
    code, espcially when we project associated items. For this reason we
    have a special function for the cases where we project from an instance
    id (e.g., `<Self as Foo>::foo` - note that in the extracted code, the
    projections are often written with a dot '.').
 *)
and extract_trait_instance_id_with_dot (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t) (inside : bool)
    (id : trait_instance_id) : unit =
  match id with
  | Self ->
      (* There are two situations:
         - we are extracting a declared item and need to refer to another
           item (for instance, we are extracting a method signature and
           need to refer to an associated type).
           We directly refer to the other item (we extract trait declarations
           as structures, so we can refer to their fields)
         - we are extracting a provided method for a trait declaration. We
           refer to the item in the self trait clause (see {!SelfTraitClauseId}).

         Remark: we can't get there for trait *implementations* because then the
         types should have been normalized.
      *)
      if ctx.is_provided_method then
        (* Provided method: use the trait self clause *)
        let self_clause = ctx_get_trait_self_clause span ctx in
        F.pp_print_string fmt (self_clause ^ ".")
      else
        (* Declaration: nothing to print, we will directly refer to
           the item. *)
        ()
  | _ ->
      (* Other cases *)
      extract_trait_instance_id span ctx fmt no_params_tys inside id;
      F.pp_print_string fmt "."

and extract_trait_instance_id (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t) (inside : bool)
    (id : trait_instance_id) : unit =
  let add_brackets (s : string) =
    if backend () = Coq then "(" ^ s ^ ")" else s
  in
  match id with
  | Self ->
      (* This has a specific treatment depending on the item we're extracting
         (associated type, etc.). We should have caught this elsewhere. *)
      save_error __FILE__ __LINE__ (Some span) "Unexpected occurrence of `Self`";
      F.pp_print_string fmt "ERROR(\"Unexpected Self\")"
  | TraitImpl (id, generics) ->
      (* We may need to filter the parameters if the trait is builtin *)
      let generics =
        match
          TraitImplId.Map.find_opt id ctx.trait_impls_filter_type_args_map
        with
        | None -> generics
        | Some filter ->
            let types =
              List.filter_map
                (fun (b, x) -> if b then Some x else None)
                (List.combine filter generics.types)
            in
            { generics with types }
      in
      let name = ctx_get_trait_impl span id ctx in
      let use_brackets = generics <> empty_generic_args && inside in
      if use_brackets then F.pp_print_string fmt "(";
      F.pp_print_string fmt name;
      extract_generic_args span ctx fmt no_params_tys generics;
      if use_brackets then F.pp_print_string fmt ")"
  | Clause id ->
      let name = ctx_get_local_trait_clause span id ctx in
      F.pp_print_string fmt name
  | ParentClause (inst_id, decl_id, clause_id) ->
      (* Use the trait decl id to lookup the name *)
      let name = ctx_get_trait_parent_clause span decl_id clause_id ctx in
      extract_trait_instance_id_with_dot span ctx fmt no_params_tys true inst_id;
      F.pp_print_string fmt (add_brackets name)
  | UnknownTrait _ ->
      (* This is an error case *)
      craise __FILE__ __LINE__ span "Unexpected"

(** Compute the names for all the top-level identifiers used in a type
    definition (type name, variant names, field names, etc. but not type
    parameters).

    We need to do this preemptively, beforce extracting any definition,
    because of recursive definitions.
 *)
let extract_type_decl_register_names (ctx : extraction_ctx) (def : type_decl) :
    extraction_ctx =
  (* Lookup the builtin information, if there is *)
  let open ExtractBuiltin in
  let info =
    match_name_find_opt ctx.trans_ctx def.item_meta.name (builtin_types_map ())
  in
  (* Register the filtering information, if there is *)
  let ctx =
    match info with
    | Some { keep_params = Some keep; _ } ->
        {
          ctx with
          types_filter_type_args_map =
            TypeDeclId.Map.add def.def_id keep ctx.types_filter_type_args_map;
        }
    | _ -> ctx
  in
  (* Compute and register the type decl name *)
  let def_name =
    match info with
    | None -> ctx_compute_type_decl_name ctx def
    | Some info -> info.extract_name
  in
  let ctx =
    ctx_add def.item_meta.span (TypeId (TAdtId def.def_id)) def_name ctx
  in
  (* Compute and register:
   * - the variant names, if this is an enumeration
   * - the field names, if this is a structure
   *)
  let ctx =
    (* Ignore this if the type is to be extracted as a tuple *)
    if
      TypesUtils.type_decl_from_decl_id_is_tuple_struct
        ctx.trans_ctx.type_ctx.type_infos def.def_id
    then ctx
    else
      match def.kind with
      | Struct fields ->
          (* Compute the names *)
          let field_names, cons_name =
            match info with
            | None | Some { body_info = None; _ } ->
                let field_names =
                  FieldId.mapi
                    (fun fid (field : field) ->
                      ( fid,
                        ctx_compute_field_name def field.attr_info ctx
                          def.item_meta.name fid field.field_name ))
                    fields
                in
                let cons_name =
                  ctx_compute_struct_constructor def ctx def.item_meta.name
                in
                (field_names, cons_name)
            | Some { body_info = Some (Struct (cons_name, field_names)); _ } ->
                let field_names =
                  FieldId.mapi
                    (fun fid (field : field) ->
                      let rust_name = Option.get field.field_name in
                      let name =
                        snd
                          (List.find (fun (n, _) -> n = rust_name) field_names)
                      in
                      (fid, name))
                    fields
                in
                (field_names, cons_name)
            | Some info ->
                craise __FILE__ __LINE__ def.item_meta.span
                  ("Invalid builtin information: " ^ show_builtin_type_info info)
          in
          (* Add the fields *)
          let ctx =
            List.fold_left
              (fun ctx (fid, name) ->
                ctx_add def.item_meta.span
                  (FieldId (TAdtId def.def_id, fid))
                  name ctx)
              ctx field_names
          in
          (* Add the constructor name *)
          ctx_add def.item_meta.span (StructId (TAdtId def.def_id)) cons_name
            ctx
      | Enum variants ->
          let variant_names =
            match info with
            | None ->
                VariantId.mapi
                  (fun variant_id (variant : variant) ->
                    let name = ctx_compute_variant_name ctx def variant in
                    (* Add the type name prefix for Lean *)
                    let name =
                      if Config.backend () = Lean then
                        let type_name = ctx_compute_type_decl_name ctx def in
                        type_name ^ "." ^ name
                      else name
                    in
                    (variant_id, name))
                  variants
            | Some { body_info = Some (Enum variant_infos); _ } ->
                (* We need to compute the map from variant to variant *)
                let variant_map =
                  StringMap.of_list
                    (List.map
                       (fun (info : builtin_enum_variant_info) ->
                         (info.rust_variant_name, info.extract_variant_name))
                       variant_infos)
                in
                VariantId.mapi
                  (fun variant_id (variant : variant) ->
                    (variant_id, StringMap.find variant.variant_name variant_map))
                  variants
            | _ ->
                craise __FILE__ __LINE__ def.item_meta.span
                  "Invalid builtin information"
          in
          List.fold_left
            (fun ctx (vid, vname) ->
              ctx_add def.item_meta.span
                (VariantId (TAdtId def.def_id, vid))
                vname ctx)
            ctx variant_names
      | Opaque ->
          (* Nothing to do *)
          ctx
  in
  (* Return *)
  ctx

(** Print the variants *)
let extract_type_decl_variant (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (type_decl_group : TypeDeclId.Set.t)
    (type_name : string) (type_params : string list) (cg_params : string list)
    (cons_name : string) (fields : field list) : unit =
  F.pp_print_space fmt ();
  (* variant box *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [| Cons :]
   * Note that we really don't want any break above so we print everything
   * at once. *)
  let opt_colon = if backend () <> HOL4 then " :" else "" in
  F.pp_print_string fmt ("| " ^ cons_name ^ opt_colon);
  let print_field (fid : FieldId.id) (f : field) (ctx : extraction_ctx) :
      extraction_ctx =
    F.pp_print_space fmt ();
    (* Open the field box *)
    F.pp_open_box fmt ctx.indent_incr;
    (* Print the field names, if the backend accepts it.
     * [  x :]
     * Note that when printing fields, we register the field names as
     * *variables*: they don't need to be unique at the top level. *)
    let ctx =
      match backend () with
      | FStar -> (
          match f.field_name with
          | None -> ctx
          | Some field_name ->
              let var_id = VarId.of_int (FieldId.to_int fid) in
              let field_name =
                ctx_compute_var_basename span ctx (Some field_name) f.field_ty
              in
              let ctx, field_name = ctx_add_var span field_name var_id ctx in
              F.pp_print_string fmt (field_name ^ " :");
              F.pp_print_space fmt ();
              ctx)
      | Coq | Lean | HOL4 -> ctx
    in
    (* Print the field type *)
    let inside = backend () = HOL4 in
    extract_ty span ctx fmt type_decl_group inside f.field_ty;
    (* Print the arrow [->] *)
    if backend () <> HOL4 then (
      F.pp_print_space fmt ();
      extract_arrow fmt ());
    (* Close the field box *)
    F.pp_close_box fmt ();
    (* Return *)
    ctx
  in
  (* Print the fields *)
  let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
  let _ =
    List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
  in
  (* Sanity check: HOL4 doesn't support const generics *)
  sanity_check __FILE__ __LINE__ (cg_params = [] || backend () <> HOL4) span;
  (* Print the final type *)
  if backend () <> HOL4 then (
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt type_name;
    List.iter
      (fun p ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt p)
      (List.append type_params cg_params);
    F.pp_close_box fmt ());
  (* Close the variant box *)
  F.pp_close_box fmt ()

(* TODO: we don' need the [def_name] paramter: it can be retrieved from the context *)
let extract_type_decl_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (def : type_decl) (def_name : string)
    (type_params : string list) (cg_params : string list)
    (variants : variant list) : unit =
  (* We want to generate a definition which looks like this (taking F* as example):
     {[
       type list a = | Cons : a -> list a -> list a | Nil : list a
     ]}

     If there isn't enough space on one line:
     {[
       type s =
       | Cons : a -> list a -> list a
       | Nil : list a
     ]}

     And if we need to write the type of a variant on several lines:
     {[
       type s =
       | Cons :
         a ->
         list a ->
         list a
       | Nil : list a
     ]}

     Finally, it is possible to give names to the variant fields in Rust.
     In this situation, we generate a definition like this:
     {[
       type s =
       | Cons : hd:a -> tl:list a -> list a
       | Nil : list a
     ]}

     Note that we already printed: [type s =]
  *)
  let print_variant _variant_id (v : variant) =
    (* We don't lookup the name, because it may have a prefix for the type
       id (in the case of Lean) *)
    let cons_name = ctx_compute_variant_name ctx def v in
    let fields = v.fields in
    extract_type_decl_variant def.item_meta.span ctx fmt type_decl_group
      def_name type_params cg_params cons_name fields
  in
  (* Print the variants *)
  let variants = VariantId.mapi (fun vid v -> (vid, v)) variants in
  List.iter (fun (vid, v) -> print_variant vid v) variants

(** Extract a struct as a tuple *)
let extract_type_decl_tuple_struct_body (span : Meta.span)
    (ctx : extraction_ctx) (fmt : F.formatter) (fields : field list) : unit =
  (* If the type is empty, we need to have a special treatment *)
  if fields = [] then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt (unit_name ()))
  else
    let sep =
      match backend () with
      | Coq | FStar | HOL4 -> "*"
      | Lean -> "×"
    in
    Collections.List.iter_link
      (fun () ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt sep)
      (fun (f : field) ->
        F.pp_print_space fmt ();
        extract_ty span ctx fmt TypeDeclId.Set.empty true f.field_ty)
      fields

let extract_type_decl_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl)
    (type_params : string list) (cg_params : string list) (fields : field list)
    : unit =
  (* We want to generate a definition which looks like this (taking F* as example):
     {[
       type t = { x : int; y : bool; }
     ]}

     If there isn't enough space on one line:
     {[
       type t =
       {
         x : int; y : bool;
       }
     ]}

     And if there is even less space:
     {[
       type t =
       {
         x : int;
         y : bool;
       }
     ]}

     Also, in case there are no fields, we need to define the type as [unit]
     ([type t = {}] doesn't work in F* ).

     Coq:
     ====
     We need to define the constructor name upon defining the struct (record, in Coq).
     The syntex is:
     {[
       Record Foo = mkFoo { x : int; y : bool; }.
     }]

     Also, Coq doesn't support groups of mutually recursive inductives and records.
     This is fine, because we can then define records as inductives, and leverage
     the fact that when record fields are accessed, the records are symbolically
     expanded which introduces let bindings of the form: [let RecordCons ... = x in ...].
     As a consequence, we never use the record projectors (unless we reconstruct
     them in the micro passes of course).

     HOL4:
     =====
     Type definitions are written as follows:
     {[
       Datatype:
         tree =
           TLeaf 'a
         | TNode node ;

         node =
           Node (tree list)
       End
     ]}
  *)
  (* Note that we already printed: [type t =] *)
  let is_rec = decl_is_from_rec_group kind in
  let _ =
    if backend () = FStar && fields = [] then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt (unit_name ()))
    else if backend () = Lean && fields = [] then ()
      (* If the definition is recursive, we may need to extract it as an inductive
         (instead of a record). We start with the "normal" case: we extract it
         as a record. *)
    else if (not is_rec) || (backend () <> Coq && backend () <> Lean) then (
      if backend () <> Lean then F.pp_print_space fmt ();
      (* If Coq: print the constructor name *)
      (* TODO: remove superfluous test not is_rec below *)
      if backend () = Coq && not is_rec then (
        F.pp_print_string fmt
          (ctx_get_struct def.item_meta.span (TAdtId def.def_id) ctx);
        F.pp_print_string fmt " ");
      (match backend () with
      | Lean -> ()
      | FStar | Coq -> F.pp_print_string fmt "{"
      | HOL4 -> F.pp_print_string fmt "<|");
      F.pp_print_break fmt 1 ctx.indent_incr;
      (* The body itself *)
      (* Open a box for the body *)
      (match backend () with
      | Coq | FStar | HOL4 -> F.pp_open_hvbox fmt 0
      | Lean -> F.pp_open_vbox fmt 0);
      (* Print the fields *)
      let print_field (field_id : FieldId.id) (f : field) : unit =
        let field_name =
          ctx_get_field def.item_meta.span (TAdtId def.def_id) field_id ctx
        in
        (* Open a box for the field *)
        F.pp_open_box fmt ctx.indent_incr;
        F.pp_print_string fmt field_name;
        F.pp_print_space fmt ();
        F.pp_print_string fmt ":";
        F.pp_print_space fmt ();
        extract_ty def.item_meta.span ctx fmt type_decl_group false f.field_ty;
        if backend () <> Lean then F.pp_print_string fmt ";";
        (* Close the box for the field *)
        F.pp_close_box fmt ()
      in
      let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
      Collections.List.iter_link (F.pp_print_space fmt)
        (fun (fid, f) -> print_field fid f)
        fields;
      (* Close the box for the body *)
      F.pp_close_box fmt ();
      match backend () with
      | Lean -> ()
      | FStar | Coq ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "}"
      | HOL4 ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "|>")
    else (
      (* We extract for Coq or Lean, and we have a recursive record, or a record in
         a group of mutually recursive types: we extract it as an inductive type *)
      cassert __FILE__ __LINE__
        (is_rec && (backend () = Coq || backend () = Lean))
        def.item_meta.span
        "Constant generics are not supported yet when generating code for HOL4";
      (* Small trick: in Lean we use namespaces, meaning we don't need to prefix
         the constructor name with the name of the type at definition site,
         i.e., instead of generating `inductive Foo := | MkFoo ...` like in Coq
         we generate `inductive Foo := | mk ... *)
      let cons_name =
        if backend () = Lean then "mk"
        else ctx_get_struct def.item_meta.span (TAdtId def.def_id) ctx
      in
      let def_name = ctx_get_local_type def.item_meta.span def.def_id ctx in
      extract_type_decl_variant def.item_meta.span ctx fmt type_decl_group
        def_name type_params cg_params cons_name fields)
  in
  ()

(** Extract a nestable, muti-line comment *)
let extract_comment (fmt : F.formatter) (sl : string list) : unit =
  (* Delimiters, space after we break a line *)
  let ld, space, rd =
    match backend () with
    | Coq | FStar | HOL4 -> ("(** ", 4, " *)")
    | Lean -> ("/- ", 3, " -/")
  in
  F.pp_open_vbox fmt space;
  F.pp_print_string fmt ld;
  (match sl with
  | [] -> ()
  | s :: sl ->
      F.pp_print_string fmt s;
      List.iter
        (fun s ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt s)
        sl);
  F.pp_print_string fmt rd;
  F.pp_close_box fmt ()

let extract_comment_with_raw_span (ctx : extraction_ctx) (fmt : F.formatter)
    (sl : string list) (name : Types.name option)
    ?(generics : (Types.generic_params * Types.generic_args) option = None)
    (raw_span : Meta.raw_span) : unit =
  let raw_span = raw_span_to_string raw_span in
  let name =
    match (name, generics) with
    | None, _ -> []
    | Some name, None ->
        [ "Name pattern: " ^ name_to_pattern_string ctx.trans_ctx name ]
    | Some name, Some (params, args) ->
        [
          "Name pattern: "
          ^ name_with_generics_to_pattern_string ctx.trans_ctx name params args;
        ]
  in
  extract_comment fmt (sl @ [ raw_span ] @ name)

let extract_trait_clause_type (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t)
    (clause : trait_clause) : unit =
  let trait_name = ctx_get_trait_decl span clause.trait_id ctx in
  F.pp_print_string fmt trait_name;
  (* let span = (TraitDeclId.Map.find clause.trait_id ctx.trans_trait_decls).span in
   *)
  extract_generic_args span ctx fmt no_params_tys clause.generics

(** Insert a space, if necessary *)
let insert_req_space (fmt : F.formatter) (space : bool ref) : unit =
  if !space then space := false else F.pp_print_space fmt ()

(** Extract the trait self clause.

    We add the trait self clause for provided methods (see {!TraitSelfClauseId}).
 *)
let extract_trait_self_clause (insert_req_space : unit -> unit)
    (ctx : extraction_ctx) (fmt : F.formatter) (trait_decl : trait_decl)
    (params : string list) : unit =
  insert_req_space ();
  F.pp_print_string fmt "(";
  let self_clause = ctx_get_trait_self_clause trait_decl.item_meta.span ctx in
  F.pp_print_string fmt self_clause;
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();
  let trait_id =
    ctx_get_trait_decl trait_decl.item_meta.span trait_decl.def_id ctx
  in
  F.pp_print_string fmt trait_id;
  List.iter
    (fun p ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt p)
    params;
  F.pp_print_string fmt ")"

(**
 - [trait_decl]: if [Some], it means we are extracting the generics for a provided
   method and need to insert a trait self clause (see {!TraitSelfClauseId}).
 *)
let extract_generic_params (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (no_params_tys : TypeDeclId.Set.t) ?(use_forall = false)
    ?(use_forall_use_sep = true) ?(use_arrows = false)
    ?(as_implicits : bool = false) ?(space : bool ref option = None)
    ?(trait_decl : trait_decl option = None) (generics : generic_params)
    (type_params : string list) (cg_params : string list)
    (trait_clauses : string list) : unit =
  let all_params = List.concat [ type_params; cg_params; trait_clauses ] in
  (* HOL4 doesn't support const generics *)
  cassert __FILE__ __LINE__
    (cg_params = [] || backend () <> HOL4)
    span "Constant generics are not supported yet when generating code for HOL4";
  let left_bracket (implicit : bool) =
    if implicit && backend () <> FStar then F.pp_print_string fmt "{"
    else F.pp_print_string fmt "("
  in
  let right_bracket (implicit : bool) =
    if implicit && backend () <> FStar then F.pp_print_string fmt "}"
    else F.pp_print_string fmt ")"
  in
  let print_implicit_symbol (implicit : bool) =
    if implicit && backend () = FStar then F.pp_print_string fmt "#" else ()
  in
  let insert_req_space () =
    match space with
    | None -> F.pp_print_space fmt ()
    | Some space -> insert_req_space fmt space
  in
  (* Print the type/const generic parameters *)
  if all_params <> [] then (
    if use_forall then (
      if use_forall_use_sep then (
        insert_req_space ();
        F.pp_print_string fmt ":");
      insert_req_space ();
      F.pp_print_string fmt "forall");
    (* Small helper - we may need to split the parameters *)
    let print_generics (as_implicits : bool) (type_params : string list)
        (const_generics : const_generic_var list)
        (trait_clauses : trait_clause list) : unit =
      (* Note that in HOL4 we don't print the type parameters. *)
      if backend () <> HOL4 then (
        (* Print the type parameters *)
        if type_params <> [] then (
          insert_req_space ();
          (* ( *)
          left_bracket as_implicits;
          List.iter
            (fun s ->
              print_implicit_symbol as_implicits;
              F.pp_print_string fmt s;
              F.pp_print_space fmt ())
            type_params;
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt (type_keyword span);
          (* ) *)
          right_bracket as_implicits;
          if use_arrows then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "->"));
        (* Print the const generic parameters *)
        List.iter
          (fun (var : const_generic_var) ->
            insert_req_space ();
            (* ( *)
            left_bracket as_implicits;
            let n = ctx_get_const_generic_var span var.index ctx in
            print_implicit_symbol as_implicits;
            F.pp_print_string fmt n;
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_literal_type ctx fmt var.ty;
            (* ) *)
            right_bracket as_implicits;
            if use_arrows then (
              F.pp_print_space fmt ();
              F.pp_print_string fmt "->"))
          const_generics);
      (* Print the trait clauses *)
      List.iter
        (fun (clause : trait_clause) ->
          insert_req_space ();
          (* ( *)
          left_bracket as_implicits;
          let n = ctx_get_local_trait_clause span clause.clause_id ctx in
          print_implicit_symbol as_implicits;
          F.pp_print_string fmt n;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          extract_trait_clause_type span ctx fmt no_params_tys clause;
          (* ) *)
          right_bracket as_implicits;
          if use_arrows then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "->"))
        trait_clauses
    in
    (* If we extract the generics for a provided method for a trait declaration
       (indicated by the trait decl given as input), we need to split the generics:
       - we print the generics for the trait decl
       - we print the trait self clause
       - we print the generics for the trait method
    *)
    match trait_decl with
    | None ->
        print_generics as_implicits type_params generics.const_generics
          generics.trait_clauses
    | Some trait_decl ->
        (* Split the generics between the generics specific to the trait decl
           and those specific to the trait method *)
        let open Collections.List in
        let dtype_params, mtype_params =
          split_at type_params (length trait_decl.generics.types)
        in
        let dcgs, mcgs =
          split_at generics.const_generics
            (length trait_decl.generics.const_generics)
        in
        let dtrait_clauses, mtrait_clauses =
          split_at generics.trait_clauses
            (length trait_decl.generics.trait_clauses)
        in
        (* Extract the trait decl generics - note that we can always deduce
           those parameters from the trait self clause: for this reason
           they are always implicit *)
        print_generics true dtype_params dcgs dtrait_clauses;
        (* Extract the trait self clause *)
        let params =
          concat
            [
              dtype_params;
              map
                (fun (cg : const_generic_var) ->
                  ctx_get_const_generic_var trait_decl.item_meta.span cg.index
                    ctx)
                dcgs;
              map
                (fun c ->
                  ctx_get_local_trait_clause trait_decl.item_meta.span
                    c.clause_id ctx)
                dtrait_clauses;
            ]
        in
        extract_trait_self_clause insert_req_space ctx fmt trait_decl params;
        (* Extract the method generics *)
        print_generics as_implicits mtype_params mcgs mtrait_clauses)

(** Extract a type declaration.

    This function is for all type declarations and all backends **at the exception**
    of opaque (assumed/declared) types format4 HOL4.

    See {!extract_type_decl}.
 *)
let extract_type_decl_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl)
    (extract_body : bool) : unit =
  (* Sanity check *)
  sanity_check __FILE__ __LINE__
    (extract_body || backend () <> HOL4)
    def.item_meta.span;
  let is_tuple_struct =
    TypesUtils.type_decl_from_decl_id_is_tuple_struct
      ctx.trans_ctx.type_ctx.type_infos def.def_id
  in
  let is_tuple_struct_one_or_zero_field =
    is_tuple_struct
    &&
    match def.kind with
    | Struct [] | Struct [ _ ] -> true
    | _ -> false
  in
  let type_kind =
    if extract_body then
      if is_tuple_struct then Some Tuple
      else
        match def.kind with
        | Struct _ -> Some Struct
        | Enum _ -> Some Enum
        | Opaque -> None
    else None
  in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type) (N0 : ...) ... (Nn : ...), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque = type_kind = None in
  let is_opaque_coq = backend () = Coq && is_opaque in
  let use_forall = is_opaque_coq && def.generics <> empty_generic_params in
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.item_meta.span def.def_id ctx in
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx_body, type_params, cg_params, trait_clauses =
    ctx_add_generic_params def.item_meta.span def.item_meta.name
      def.llbc_generics def.generics ctx
  in
  (* Add a break before *)
  if backend () <> HOL4 || not (decl_is_first_from_group kind) then
    F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  (let name =
     if !Config.extract_external_name_patterns && not def.item_meta.is_local
     then Some def.item_meta.name
     else None
   in
   extract_comment_with_raw_span ctx fmt
     [ "[" ^ name_to_string ctx def.item_meta.name ^ "]" ]
     name def.item_meta.span.span);
  F.pp_print_break fmt 0 0;
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line. Note however that in the case of Lean line breaks are important
   * for parsing: we thus use a hovbox. *)
  (match backend () with
  | Coq | FStar | HOL4 -> F.pp_open_hvbox fmt 0
  | Lean ->
      if is_tuple_struct then F.pp_open_hvbox fmt 0 else F.pp_open_vbox fmt 0);
  (* Open a box for "type TYPE_NAME (TYPE_PARAMS CONST_GEN_PARAMS) =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "@[reducible]"
     We need this annotation, otherwise Lean sometimes doesn't manage to typecheck
     the expressions when it needs to coerce the type.
  *)
  if is_tuple_struct_one_or_zero_field && backend () = Lean then (
    F.pp_print_string fmt "@[reducible]";
    F.pp_print_space fmt ())
  else ();
  (* > "type TYPE_NAME" *)
  let qualif = type_decl_kind_to_qualif def.item_meta.span kind type_kind in
  (match qualif with
  | Some qualif -> F.pp_print_string fmt (qualif ^ " " ^ def_name)
  | None -> F.pp_print_string fmt def_name);
  (* HOL4 doesn't support const generics, and type definitions in HOL4 don't
     support trait clauses *)
  cassert __FILE__ __LINE__
    ((cg_params = [] && trait_clauses = []) || backend () <> HOL4)
    def.item_meta.span
    "Constant generics and type definitions with trait clauses are not \
     supported yet when generating code for HOL4";
  (* Print the generic parameters *)
  extract_generic_params def.item_meta.span ctx_body fmt type_decl_group
    ~use_forall def.generics type_params cg_params trait_clauses;
  (* Print the "=" if we extract the body*)
  if extract_body then (
    F.pp_print_space fmt ();
    let eq =
      match backend () with
      | FStar -> "="
      | Coq ->
          (* For Coq, the `*` is overloaded. If we want to extract a product
             type (and not a product between, say, integers) we need to help Coq
             a bit *)
          if is_tuple_struct then ": Type :=" else ":="
      | Lean ->
          if type_kind = Some Struct && kind = SingleNonRec then "where"
          else ":="
      | HOL4 -> "="
    in
    F.pp_print_string fmt eq)
  else (
    (* Otherwise print ": Type", unless it is the HOL4 backend (in
       which case we declare the type with `new_type`) *)
    if use_forall then F.pp_print_string fmt ","
    else (
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":");
    F.pp_print_space fmt ();
    F.pp_print_string fmt (type_keyword def.item_meta.span));
  (* Close the box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_close_box fmt ();
  (if extract_body then
     match def.kind with
     | Struct fields ->
         if is_tuple_struct then
           extract_type_decl_tuple_struct_body def.item_meta.span ctx_body fmt
             fields
         else
           extract_type_decl_struct_body ctx_body fmt type_decl_group kind def
             type_params cg_params fields
     | Enum variants ->
         extract_type_decl_enum_body ctx_body fmt type_decl_group def def_name
           type_params cg_params variants
     | Opaque -> craise __FILE__ __LINE__ def.item_meta.span "Unreachable");
  (* Add the definition end delimiter *)
  if backend () = HOL4 && decl_is_not_last_from_group kind then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt ";")
  else if backend () = Coq && decl_is_last_from_group kind then (
    (* This is actually an end of group delimiter. For aesthetic reasons
       we print it here instead of in {!end_type_decl_group}. *)
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  if backend () <> HOL4 || decl_is_not_last_from_group kind then
    F.pp_print_break fmt 0 0

(** Extract an opaque type declaration to HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_type_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) : unit =
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.item_meta.span def.def_id ctx in
  (* Generic parameters are unsupported *)
  cassert __FILE__ __LINE__
    (def.generics.const_generics = [])
    def.item_meta.span
    "Constant generics are not supported yet when generating code for HOL4";
  (* Trait clauses on type definitions are unsupported *)
  cassert __FILE__ __LINE__
    (def.generics.trait_clauses = [])
    def.item_meta.span
    "Types with trait clauses are not supported yet when generating code for \
     HOL4";
  (* Types  *)
  (* Count the number of parameters *)
  let num_params = List.length def.generics.types in
  (* Generate the declaration *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt
    ("val _ = new_type (\"" ^ def_name ^ "\", " ^ string_of_int num_params ^ ")");
  F.pp_print_space fmt ()

(** Extract an empty record type declaration to HOL4.

    Empty records are not supported in HOL4, so we extract them as type
    abbreviations to the unit type.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_type_decl_hol4_empty_record (ctx : extraction_ctx)
    (fmt : F.formatter) (def : type_decl) : unit =
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.item_meta.span def.def_id ctx in
  (* Sanity check *)
  sanity_check __FILE__ __LINE__
    (def.generics = empty_generic_params)
    def.item_meta.span;
  (* Generate the declaration *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ("Type " ^ def_name ^ " = “: unit”");
  F.pp_print_space fmt ()

(** Extract a type declaration.

    Note that all the names used for extraction should already have been
    registered.

    This function should be inserted between calls to {!start_type_decl_group}
    and {!end_type_decl_group}.
 *)
let extract_type_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl) :
    unit =
  let extract_body =
    match kind with
    | SingleNonRec | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> true
    | Assumed | Declared -> false
  in
  if extract_body then
    if backend () = HOL4 && is_empty_record_type_decl def then
      extract_type_decl_hol4_empty_record ctx fmt def
    else extract_type_decl_gen ctx fmt type_decl_group kind def extract_body
  else
    match backend () with
    | FStar | Coq | Lean ->
        extract_type_decl_gen ctx fmt type_decl_group kind def extract_body
    | HOL4 -> extract_type_decl_hol4_opaque ctx fmt def

(** Generate a [Argument] instruction in Coq to allow omitting implicit
    arguments for variants, fields, etc..

    For instance, provided we have this definition:
    {[
      Inductive result A :=
      | Return : A -> result A
      | Fail_ : error -> result A.
    ]}

    We may want to generate those instructions:
    {[
      Arguments Return {_} a.
      Arguments Fail_ {_}.
    ]}
 *)
let extract_coq_arguments_instruction (ctx : extraction_ctx) (fmt : F.formatter)
    (cons_name : string) (num_implicit_params : int) : unit =
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Open a box *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_break fmt 0 0;
  F.pp_print_string fmt "Arguments";
  F.pp_print_space fmt ();
  F.pp_print_string fmt cons_name;
  (* Print the type/const params and the trait clauses (`{T}`) *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "{";
  Collections.List.iter_times num_implicit_params (fun () ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt "_");
  F.pp_print_space fmt ();
  F.pp_print_string fmt "}.";

  (* Close the box *)
  F.pp_close_box fmt ()

(** Auxiliary function.

    Generate [Arguments] instructions in Coq for type definitions.
 *)
let extract_type_decl_coq_arguments (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (decl : type_decl) : unit =
  sanity_check __FILE__ __LINE__ (backend () = Coq) decl.item_meta.span;
  (* Generating the [Arguments] instructions is useful only if there are parameters *)
  let num_params =
    List.length decl.generics.types
    + List.length decl.generics.const_generics
    + List.length decl.generics.trait_clauses
  in
  if num_params = 0 then ()
  else
    (* Generate the [Arguments] instruction *)
    match decl.kind with
    | Opaque -> ()
    | Struct fields ->
        let adt_id = TAdtId decl.def_id in
        (* Generate the instruction for the record constructor *)
        let cons_name = ctx_get_struct decl.item_meta.span adt_id ctx in
        extract_coq_arguments_instruction ctx fmt cons_name num_params;
        (* Generate the instruction for the record projectors, if there are *)
        let is_rec = decl_is_from_rec_group kind in
        if not is_rec then
          FieldId.iteri
            (fun fid _ ->
              let cons_name =
                ctx_get_field decl.item_meta.span adt_id fid ctx
              in
              extract_coq_arguments_instruction ctx fmt cons_name num_params)
            fields;
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0
    | Enum variants ->
        (* Generate the instructions *)
        VariantId.iteri
          (fun vid (_ : variant) ->
            let cons_name =
              ctx_get_variant decl.item_meta.span (TAdtId decl.def_id) vid ctx
            in
            extract_coq_arguments_instruction ctx fmt cons_name num_params)
          variants;
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0

(** Auxiliary function.

    Generate field projectors for Lean and Coq.

    Recursive structs are defined as inductives in Lean and Coq.
    Field projectors allow to retrieve the facilities provided by
    Lean structures.
 *)
let extract_type_decl_record_field_projectors (ctx : extraction_ctx)
    (fmt : F.formatter) (kind : decl_kind) (decl : type_decl) : unit =
  sanity_check __FILE__ __LINE__
    (backend () = Coq || backend () = Lean)
    decl.item_meta.span;
  match decl.kind with
  | Opaque | Enum _ -> ()
  | Struct fields ->
      (* Records are extracted as inductives only if they are recursive *)
      let is_rec = decl_is_from_rec_group kind in
      if is_rec then
        (* Add the type params *)
        let ctx, type_params, cg_params, trait_clauses =
          ctx_add_generic_params decl.item_meta.span decl.item_meta.name
            decl.llbc_generics decl.generics ctx
        in
        (* Record_var will be the ADT argument to the projector *)
        let ctx, record_var =
          ctx_add_var decl.item_meta.span "x" (VarId.of_int 0) ctx
        in
        (* Field_var will be the variable in the constructor that is returned by the projector *)
        let ctx, field_var =
          ctx_add_var decl.item_meta.span "x" (VarId.of_int 1) ctx
        in
        (* Name of the ADT *)
        let def_name = ctx_get_local_type decl.item_meta.span decl.def_id ctx in
        (* Name of the ADT constructor. As we are in the struct case, we only have
           one constructor *)
        let cons_name =
          ctx_get_struct decl.item_meta.span (TAdtId decl.def_id) ctx
        in

        let extract_field_proj (field_id : FieldId.id) (_ : field) : unit =
          F.pp_print_space fmt ();
          (* Outer box for the projector definition *)
          F.pp_open_hvbox fmt 0;
          (* Inner box for the projector definition *)
          F.pp_open_hvbox fmt ctx.indent_incr;

          (* For Lean: add some attributes *)
          if backend () = Lean then (
            (* Box for the attributes *)
            F.pp_open_vbox fmt 0;
            (* Annotate the projectors with both simp and reducible.
               The first one allows to automatically unfold when calling simp in proofs.
               The second ensures that projectors will interact well with the unifier *)
            F.pp_print_string fmt "@[reducible]";
            F.pp_print_break fmt 0 0;
            (* Close box for the attributes *)
            F.pp_close_box fmt ());

          (* Box for the [def ADT.proj ... :=] *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          (match backend () with
          | Lean -> F.pp_print_string fmt "def"
          | Coq -> F.pp_print_string fmt "Definition"
          | _ -> internal_error __FILE__ __LINE__ decl.item_meta.span);
          F.pp_print_space fmt ();

          (* Print the function name. In Lean, the syntax ADT.proj will
             allow us to call x.proj for any x of type ADT. In Coq,
             we will have to introduce a notation for the projector. *)
          let field_name =
            ctx_get_field decl.item_meta.span (TAdtId decl.def_id) field_id ctx
          in
          if backend () = Lean then (
            F.pp_print_string fmt def_name;
            F.pp_print_string fmt ".");
          F.pp_print_string fmt field_name;

          (* Print the generics *)
          let as_implicits = true in
          extract_generic_params decl.item_meta.span ctx fmt
            TypeDeclId.Set.empty ~as_implicits decl.generics type_params
            cg_params trait_clauses;

          (* Print the record parameter as "(x : ADT)" *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          F.pp_print_string fmt record_var;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt def_name;
          List.iter
            (fun p ->
              F.pp_print_space fmt ();
              F.pp_print_string fmt p)
            type_params;
          F.pp_print_string fmt ")";

          F.pp_print_space fmt ();
          F.pp_print_string fmt ":=";

          (* Close the box for the [def ADT.proj ... :=] *)
          F.pp_close_box fmt ();
          F.pp_print_space fmt ();

          (* Open a box for the whole match *)
          F.pp_open_hvbox fmt 0;

          (* Open a box for the [match ... with] *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "match";
          F.pp_print_space fmt ();
          F.pp_print_string fmt record_var;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "with";
          (* Close the box for the [match ... with] *)
          F.pp_close_box fmt ();

          (* Open a box for the branch *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          (* Print the match branch *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt "|";
          F.pp_print_space fmt ();
          F.pp_print_string fmt cons_name;
          FieldId.iteri
            (fun id _ ->
              F.pp_print_space fmt ();
              if field_id = id then F.pp_print_string fmt field_var
              else F.pp_print_string fmt "_")
            fields;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "=>";
          F.pp_print_space fmt ();
          F.pp_print_string fmt field_var;
          (* Close the box for the branch *)
          F.pp_close_box fmt ();

          (* Print the [end] *)
          if backend () = Coq then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "end");

          (* Close the box for the whole match *)
          F.pp_close_box fmt ();
          (* Close the inner box projector *)
          F.pp_close_box fmt ();
          (* If Coq: end the definition with a "." *)
          if backend () = Coq then (
            F.pp_print_cut fmt ();
            F.pp_print_string fmt ".");
          (* Close the outer box for projector definition *)
          F.pp_close_box fmt ();
          (* Add breaks to insert new lines between definitions *)
          F.pp_print_break fmt 0 0
        in

        (* Only for Coq: we need to define a notation for the projector *)
        let extract_proj_notation (field_id : FieldId.id) (_ : field) : unit =
          F.pp_print_space fmt ();
          (* Outer box for the projector definition *)
          F.pp_open_hvbox fmt 0;
          (* Inner box for the projector definition *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          let ctx, record_var =
            ctx_add_var decl.item_meta.span "x" (VarId.of_int 0) ctx
          in
          F.pp_print_string fmt "Notation";
          F.pp_print_space fmt ();
          let field_name =
            ctx_get_field decl.item_meta.span (TAdtId decl.def_id) field_id ctx
          in
          F.pp_print_string fmt ("\"" ^ record_var ^ " .(" ^ field_name ^ ")\"");
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":=";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          F.pp_print_string fmt field_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt record_var;
          F.pp_print_string fmt ")";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(at level 9)";
          (* Close the inner box projector *)
          F.pp_close_box fmt ();
          (* If Coq: end the definition with a "." *)
          if backend () = Coq then (
            F.pp_print_cut fmt ();
            F.pp_print_string fmt ".");
          (* Close the outer box projector  *)
          F.pp_close_box fmt ();
          (* Add breaks to insert new lines between definitions *)
          F.pp_print_break fmt 0 0
        in

        let extract_field_proj_and_notation (field_id : FieldId.id)
            (field : field) : unit =
          extract_field_proj field_id field;
          if backend () = Coq then extract_proj_notation field_id field
        in

        FieldId.iteri extract_field_proj_and_notation fields

(** Auxiliary function.

    Generate field projectors simp lemmas for Lean.

    See {!extract_type_decl_record_field_projectors}.
 *)
let extract_type_decl_record_field_projectors_simp_lemmas (ctx : extraction_ctx)
    (fmt : F.formatter) (kind : decl_kind) (decl : type_decl) : unit =
  let span = decl.item_meta.span in
  sanity_check __FILE__ __LINE__ (backend () = Coq || backend () = Lean) span;
  match decl.kind with
  | Opaque | Enum _ -> ()
  | Struct fields ->
      (* Records are extracted as inductives only if they are recursive *)
      let is_rec = decl_is_from_rec_group kind in
      if is_rec then
        (* Add the type params *)
        let ctx, type_params, cg_params, trait_clauses =
          ctx_add_generic_params span decl.item_meta.name decl.llbc_generics
            decl.generics ctx
        in
        (* Name of the ADT *)
        let def_name = ctx_get_local_type span decl.def_id ctx in
        (* Name of the ADT constructor. As we are in the struct case, we only have
           one constructor *)
        let cons_name = ctx_get_struct span (TAdtId decl.def_id) ctx in

        let extract_field_proj_simp_lemma (field_id : FieldId.id) (_ : field) :
            unit =
          F.pp_print_space fmt ();
          (* Outer box for the projector definition *)
          F.pp_open_hvbox fmt 0;
          (* Inner box for the projector definition *)
          F.pp_open_hvbox fmt ctx.indent_incr;

          (* For Lean: add some attributes *)
          if backend () = Lean then (
            (* Box for the attributes *)
            F.pp_open_vbox fmt 0;
            (* Annotate the projectors with both simp and reducible.
               The first one allows to automatically unfold when calling simp in proofs.
               The second ensures that projectors will interact well with the unifier *)
            F.pp_print_string fmt "@[simp]";
            F.pp_print_break fmt 0 0;
            (* Close box for the attributes *)
            F.pp_close_box fmt ());

          (* Box for the [theorem ... : ... = ... :=] *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          (match backend () with
          | Lean -> F.pp_print_string fmt "theorem"
          | _ -> internal_error __FILE__ __LINE__ span);
          F.pp_print_space fmt ();

          (* Print the theorem name. *)
          let field_name =
            ctx_get_field span (TAdtId decl.def_id) field_id ctx
          in
          (* TODO: check for name collisions *)
          F.pp_print_string fmt (def_name ^ "." ^ field_name ^ "._simpLemma_");

          (* Print the generics *)
          let as_implicits = true in
          extract_generic_params span ctx fmt TypeDeclId.Set.empty ~as_implicits
            decl.generics type_params cg_params trait_clauses;

          (* Print the input parameters (the fields) *)
          let print_field (ctx : extraction_ctx) (field_id : FieldId.id)
              (f : field) : extraction_ctx * string =
            let id = VarId.of_int (FieldId.to_int field_id) in
            let field_name =
              ctx_get_field span (TAdtId decl.def_id) field_id ctx
            in
            let ctx, vname = ctx_add_var span field_name id ctx in
            F.pp_print_space fmt ();
            F.pp_print_string fmt "(";
            F.pp_print_string fmt vname;
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_ty span ctx fmt TypeDeclId.Set.empty false f.field_ty;
            F.pp_print_string fmt ")";
            (ctx, field_name)
          in
          let _, field_names =
            List.fold_left_map
              (fun ctx (id, f) -> print_field ctx id f)
              ctx
              (FieldId.mapi (fun i f -> (i, f)) fields)
          in

          (* The theorem content *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          (* (mk ... x ...).f = x *)
          (* Open a box for the theorem content *)
          F.pp_open_hvbox fmt ctx.indent_incr;
          F.pp_print_string fmt "(";
          F.pp_print_string fmt cons_name;
          List.iter
            (fun f ->
              F.pp_print_space fmt ();
              F.pp_print_string fmt f)
            field_names;
          F.pp_print_string fmt (")." ^ field_name);
          F.pp_print_space fmt ();
          F.pp_print_string fmt "=";
          F.pp_print_space fmt ();
          F.pp_print_string fmt (FieldId.nth field_names field_id);
          (* Close the box for the theorem content *)
          F.pp_close_box fmt ();

          (* The proof *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":=";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "by rfl";

          (* Close the box for the [theorem ... :=] *)
          F.pp_close_box fmt ();

          (* Close the inner box projector *)
          F.pp_close_box fmt ();
          (* If Coq: end the definition with a "." *)
          if backend () = Coq then (
            F.pp_print_cut fmt ();
            F.pp_print_string fmt ".");
          (* Close the outer box for projector definition *)
          F.pp_close_box fmt ();
          (* Add breaks to insert new lines between definitions *)
          F.pp_print_break fmt 0 0
        in

        FieldId.iteri extract_field_proj_simp_lemma fields

(** Extract extra information for a type (e.g., [Arguments] instructions in Coq).

    Note that all the names used for extraction should already have been
    registered.
 *)
let extract_type_decl_extra_info (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (decl : type_decl) : unit =
  match backend () with
  | FStar | HOL4 -> ()
  | Lean | Coq ->
      if
        not
          (TypesUtils.type_decl_from_decl_id_is_tuple_struct
             ctx.trans_ctx.type_ctx.type_infos decl.def_id)
      then (
        if backend () = Coq then
          extract_type_decl_coq_arguments ctx fmt kind decl;
        extract_type_decl_record_field_projectors ctx fmt kind decl;
        if backend () = Lean then
          extract_type_decl_record_field_projectors_simp_lemmas ctx fmt kind
            decl)

(** Extract the state type declaration. *)
let extract_state_type (fmt : F.formatter) (ctx : extraction_ctx)
    (kind : decl_kind) : unit =
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment  *)
  extract_comment fmt [ "The state type used in the state-error monad" ];
  F.pp_print_break fmt 0 0;
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Retrieve the name *)
  let state_name = ctx_get_assumed_type None TState ctx in
  (* The syntax for Lean and Coq is almost identical. *)
  let print_axiom () =
    let axiom =
      match backend () with
      | Coq -> "Axiom"
      | Lean -> "axiom"
      | FStar | HOL4 -> raise (Failure "Unexpected")
    in
    F.pp_print_string fmt axiom;
    F.pp_print_space fmt ();
    F.pp_print_string fmt state_name;
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type";
    if backend () = Coq then F.pp_print_string fmt "."
  in
  (* The kind should be [Assumed] or [Declared] *)
  (match kind with
  | SingleNonRec | SingleRec | MutRecFirst | MutRecInner | MutRecLast ->
      raise (Failure "Unexpected")
  | Assumed -> (
      match backend () with
      | FStar ->
          F.pp_print_string fmt "assume";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "type";
          F.pp_print_space fmt ();
          F.pp_print_string fmt state_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "Type0"
      | HOL4 ->
          F.pp_print_string fmt ("val _ = new_type (\"" ^ state_name ^ "\", 0)")
      | Coq | Lean -> print_axiom ())
  | Declared -> (
      match backend () with
      | FStar ->
          F.pp_print_string fmt "val";
          F.pp_print_space fmt ();
          F.pp_print_string fmt state_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "Type0"
      | HOL4 ->
          F.pp_print_string fmt ("val _ = new_type (\"" ^ state_name ^ "\", 0)")
      | Coq | Lean -> print_axiom ()));
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0
