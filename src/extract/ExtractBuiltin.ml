(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends.

    TODO: there misses trait **implementations**
 *)

open Config
open Charon.NameMatcher (* TODO: include? *)
include ExtractName (* TODO: only open? *)

let log = Logging.builtin_log

(** Small utility to memoize some computations *)
let mk_memoized (f : unit -> 'a) : unit -> 'a =
  let r = ref None in
  let g () =
    match !r with
    | Some x -> x
    | None ->
        let x = f () in
        r := Some x;
        x
  in
  g

let split_on_separator (s : string) : string list =
  Str.split (Str.regexp "\\(::\\|\\.\\)") s

let flatten_name (name : string list) : string =
  match backend () with
  | FStar | Coq | HOL4 -> String.concat "_" name
  | Lean -> String.concat "." name

(** Utility for Lean-only definitions **)
let mk_lean_only (funs : 'a list) : 'a list =
  match backend () with
  | Lean -> funs
  | _ -> []

let () =
  assert (split_on_separator "x::y::z" = [ "x"; "y"; "z" ]);
  assert (split_on_separator "x.y.z" = [ "x"; "y"; "z" ])

(** Switch between two values depending on the target backend.

    We often compute the same value (typically: a name) if the target
    is F*, Coq or HOL4, and a different value if the target is Lean.
 *)
let backend_choice (fstar_coq_hol4 : 'a) (lean : 'a) : 'a =
  match backend () with
  | Coq | FStar | HOL4 -> fstar_coq_hol4
  | Lean -> lean

let builtin_globals : (string * string) list =
  [
    (* Min *)
    ("core::num::{usize}::MIN", "core_usize_min");
    ("core::num::{u8}::MIN", "core_u8_min");
    ("core::num::{u16}::MIN", "core_u16_min");
    ("core::num::{u32}::MIN", "core_u32_min");
    ("core::num::{u64}::MIN", "core_u64_min");
    ("core::num::{u128}::MIN", "core_u128_min");
    ("core::num::{isize}::MIN", "core_isize_min");
    ("core::num::{i8}::MIN", "core_i8_min");
    ("core::num::{i16}::MIN", "core_i16_min");
    ("core::num::{i32}::MIN", "core_i32_min");
    ("core::num::{i64}::MIN", "core_i64_min");
    ("core::num::{i128}::MIN", "core_i128_min");
    (* Max *)
    ("core::num::{usize}::MAX", "core_usize_max");
    ("core::num::{u8}::MAX", "core_u8_max");
    ("core::num::{u16}::MAX", "core_u16_max");
    ("core::num::{u32}::MAX", "core_u32_max");
    ("core::num::{u64}::MAX", "core_u64_max");
    ("core::num::{u128}::MAX", "core_u128_max");
    ("core::num::{isize}::MAX", "core_isize_max");
    ("core::num::{i8}::MAX", "core_i8_max");
    ("core::num::{i16}::MAX", "core_i16_max");
    ("core::num::{i32}::MAX", "core_i32_max");
    ("core::num::{i64}::MAX", "core_i64_max");
    ("core::num::{i128}::MAX", "core_i128_max");
  ]

let builtin_globals_map : string NameMatcherMap.t =
  NameMatcherMap.of_list
    (List.map (fun (x, y) -> (parse_pattern x, y)) builtin_globals)

type builtin_variant_info = { fields : (string * string) list }
[@@deriving show]

type builtin_enum_variant_info = {
  rust_variant_name : string;
  extract_variant_name : string;
  fields : string list option;
}
[@@deriving show]

type builtin_type_body_info =
  | Struct of string * (string * string) list
    (* The constructor name and the map for the field names *)
  | Enum of builtin_enum_variant_info list
(* For every variant, a map for the field names *)
[@@deriving show]

type builtin_type_info = {
  rust_name : pattern;
  extract_name : string;
  keep_params : bool list option;
      (** We might want to filter some of the type parameters.

          For instance, `Vec` type takes a type parameter for the allocator,
          which we want to ignore.
       *)
  body_info : builtin_type_body_info option;
}
[@@deriving show]

type type_variant_kind =
  | KOpaque
  | KStruct of (string * string option) list
      (** Contains the list of (field rust name, field extracted name) *)
  | KEnum of string list

let mk_struct_constructor (type_name : string) : string =
  let prefix =
    match backend () with
    | FStar -> "Mk"
    | Coq | HOL4 -> "mk"
    | Lean -> ""
  in
  let suffix =
    match backend () with
    | FStar | Coq | HOL4 -> ""
    | Lean -> ".mk"
  in
  prefix ^ type_name ^ suffix

(** The assumed types.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is
    a type parameter for the allocator to use, which we want to filter.
 *)
let builtin_types () : builtin_type_info list =
  let mk_type (rust_name : string) ?(custom_name : string option = None)
      ?(keep_params : bool list option = None)
      ?(kind : type_variant_kind = KOpaque) () : builtin_type_info =
    let rust_name = parse_pattern rust_name in
    let extract_name =
      match custom_name with
      | None -> flatten_name (pattern_to_type_extract_name rust_name)
      | Some name -> flatten_name (split_on_separator name)
    in
    let body_info : builtin_type_body_info option =
      match kind with
      | KOpaque -> None
      | KStruct fields ->
          let fields =
            List.map
              (fun (rname, name) ->
                ( rname,
                  let name =
                    match name with
                    | None -> rname
                    | Some name -> name
                  in
                  match backend () with
                  | FStar | Lean -> name
                  | Coq | HOL4 -> extract_name ^ "_" ^ name ))
              fields
          in
          let constructor = mk_struct_constructor extract_name in
          Some (Struct (constructor, fields))
      | KEnum variants ->
          let variants =
            List.map
              (fun variant ->
                let extract_variant_name =
                  match backend () with
                  | FStar | Coq -> extract_name ^ "_" ^ variant
                  | Lean -> extract_name ^ "." ^ variant
                  | HOL4 -> extract_name ^ variant
                in
                {
                  rust_variant_name = variant;
                  extract_variant_name;
                  fields = None;
                })
              variants
          in
          Some (Enum variants)
    in
    { rust_name; extract_name; keep_params; body_info }
  in

  [
    (* Alloc *)
    mk_type "alloc::alloc::Global" ();
    (* String *)
    mk_type "alloc::string::String"
      ~custom_name:(Some (backend_choice "string" "String"))
      ();
    (* Vec *)
    mk_type "alloc::vec::Vec" ~keep_params:(Some [ true; false ]) ();
    (* Range *)
    mk_type "core::ops::range::Range"
      ~kind:(KStruct [ ("start", None); ("end", Some "end_") ])
      ();
    (* Option

       This one is more custom because we use the standard "option" type from
       the target backend.
    *)
    {
      rust_name = parse_pattern "core::option::Option";
      extract_name =
        (match backend () with
        | Lean -> "Option"
        | Coq | FStar | HOL4 -> "option");
      keep_params = None;
      body_info =
        Some
          (Enum
             [
               {
                 rust_variant_name = "None";
                 extract_variant_name =
                   (match backend () with
                   | FStar | Coq -> "None"
                   | Lean -> "none"
                   | HOL4 -> "NONE");
                 fields = None;
               };
               {
                 rust_variant_name = "Some";
                 extract_variant_name =
                   (match backend () with
                   | FStar | Coq -> "Some"
                   | Lean -> "some"
                   | HOL4 -> "SOME");
                 fields = None;
               };
             ]);
    };
  ]
  @ mk_lean_only
      [
        mk_type "core::fmt::Formatter" ();
        mk_type "core::result::Result" ~kind:(KEnum [ "Ok"; "Err" ]) ();
        mk_type "core::fmt::Error" ();
        mk_type "core::array::TryFromSliceError" ();
        mk_type "core::ops::range::RangeFrom"
          ~kind:(KStruct [ ("start", None) ])
          ();
      ]

let mk_builtin_types_map () =
  NameMatcherMap.of_list
    (List.map (fun info -> (info.rust_name, info)) (builtin_types ()))

let builtin_types_map = mk_memoized mk_builtin_types_map

type builtin_fun_info = {
  extract_name : string;
  can_fail : bool;
  stateful : bool;
}
[@@deriving show]

let int_and_smaller_list : (string * string) list =
  let uint_names = List.rev [ "u8"; "u16"; "u32"; "u64"; "u128" ] in
  let int_names = List.rev [ "i8"; "i16"; "i32"; "i64"; "i128" ] in
  let rec compute_pairs l =
    match l with
    | [] -> []
    | x :: l -> List.map (fun y -> (x, y)) (x :: l) @ compute_pairs l
  in
  [
    (* Usize *)
    ("usize", "u8");
    ("usize", "u16");
    ("usize", "u32");
    ("usize", "usize");
    (* Isize *)
    ("isize", "i8");
    ("isize", "i16");
    ("isize", "i32");
    ("isize", "isize");
  ]
  @ compute_pairs uint_names @ compute_pairs int_names

(** The builtin functions.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is
    a type parameter for the allocator to use, which we want to filter.
 *)
let mk_builtin_funs () : (pattern * bool list option * builtin_fun_info) list =
  (* Small utility *)
  let mk_fun (rust_name : string) ?(filter : bool list option = None)
      ?(can_fail = true) ?(stateful = false)
      ?(extract_name : string option = None) () :
      pattern * bool list option * builtin_fun_info =
    let rust_name =
      try parse_pattern rust_name
      with Failure _ ->
        raise (Failure ("Could not parse pattern: " ^ rust_name))
    in
    let extract_name =
      match extract_name with
      | None -> pattern_to_fun_extract_name rust_name
      | Some name -> split_on_separator name
    in
    let basename = flatten_name extract_name in
    let f = { extract_name = basename; can_fail; stateful } in
    (rust_name, filter, f)
  in
  let mk_scalar_fun (rust_name : string -> string)
      (extract_name : string -> string) ?(can_fail = true) () :
      (pattern * bool list option * builtin_fun_info) list =
    List.map
      (fun ty ->
        mk_fun (rust_name ty)
          ~extract_name:(Some (extract_name ty))
          ~can_fail ())
      all_int_names
  in
  [
    mk_fun "core::mem::replace" ~can_fail:false ();
    mk_fun "core::mem::take" ~can_fail:false ();
    mk_fun "core::slice::{[@T]}::len"
      ~extract_name:(Some (backend_choice "slice::len" "Slice::len"))
      ~can_fail:false ();
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::new"
      ~extract_name:(Some "alloc::vec::Vec::new") ~can_fail:false ();
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::push"
      ~filter:(Some [ true; false ])
      ();
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::insert"
      ~filter:(Some [ true; false ])
      ();
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::len"
      ~filter:(Some [ true; false ])
      ~can_fail:false ();
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T, @A>, \
       @I>}::index"
      ~extract_name:(Some "alloc.vec.Vec.index")
      ~filter:(Some [ true; true; false ])
      ();
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T, @A>, \
       @I>}::index_mut"
      ~extract_name:(Some "alloc.vec.Vec.index_mut")
      ~filter:(Some [ true; true; false ])
      ();
    mk_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>>}::deref"
      ~extract_name:(Some "alloc.boxed.Box.deref")
      ~filter:(Some [ true; false ])
      ();
    mk_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>>}::deref_mut"
      ~extract_name:(Some "alloc.boxed.Box.deref_mut")
      ~filter:(Some [ true; false ])
      ();
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I>}::index"
      ~extract_name:(Some "core.slice.index.Slice.index") ();
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I>}::index_mut"
      ~extract_name:(Some "core.slice.index.Slice.index_mut") ();
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I>}::index"
      ~extract_name:(Some "core.array.Array.index") ();
    mk_fun "core::array::{core::ops::index::IndexMut<[@T; @N], @I>}::index_mut"
      ~extract_name:(Some "core.array.Array.index_mut") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get"
      ~extract_name:(Some "core::slice::index::RangeUsize::get") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_mut"
      ~extract_name:(Some "core::slice::index::RangeUsize::get_mut") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::index"
      ~extract_name:(Some "core::slice::index::RangeUsize::index") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::index_mut"
      ~extract_name:(Some "core::slice::index::RangeUsize::index_mut") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_unchecked"
      ~extract_name:(Some "core::slice::index::RangeUsize::get_unchecked") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_unchecked_mut"
      ~extract_name:(Some "core::slice::index::RangeUsize::get_unchecked_mut")
      ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T]>}::get"
      ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_mut"
      ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_unchecked"
      ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_unchecked_mut"
      ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T]>}::index"
      ~extract_name:(Some "core_slice_index_Slice_index") ();
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::index_mut"
      ~extract_name:(Some "core_slice_index_Slice_index_mut") ();
    mk_fun "alloc::slice::{[@T]}::to_vec"
      ~extract_name:(Some "alloc.slice.Slice.to_vec") ();
    mk_fun
      "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::with_capacity"
      ~extract_name:(Some "alloc.vec.Vec.with_capacity") ~can_fail:false ();
    mk_fun "core::slice::{[@T]}::reverse"
      ~extract_name:(Some "core.slice.Slice.reverse") ~can_fail:false ();
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T, @A>>}::deref"
      ~extract_name:(Some "alloc.vec.DerefVec.deref")
      ~filter:(Some [ true; false ])
      ~can_fail:false ();
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T, \
       @A>>}::deref_mut"
      ~extract_name:(Some "alloc.vec.DerefMutVec.deref_mut")
      ~filter:(Some [ true; false ])
      ();
    mk_fun "core::option::{core::option::Option<@T>}::unwrap"
      ~extract_name:(Some "core.option.Option.unwrap") ();
  ]
  @ List.flatten
      (List.map
         (fun op ->
           mk_scalar_fun
             (fun ty -> "core::num::{" ^ ty ^ "}::checked_" ^ op)
             (fun ty ->
               StringUtils.capitalize_first_letter ty ^ ".checked_" ^ op)
             ~can_fail:false ())
         [ "add"; "sub"; "mul"; "div"; "rem" ])
  (* From<INT, bool> *)
  @ mk_scalar_fun
      (fun ty ->
        "core::convert::num::{core::convert::From<" ^ ty ^ ", bool>}::from")
      (fun ty ->
        "core.convert.num.From"
        ^ StringUtils.capitalize_first_letter ty
        ^ "Bool.from")
      ~can_fail:false ()
  (* From<INT, INT> *)
  @ List.map
      (fun (big, small) ->
        mk_fun
          ("core::convert::num::{core::convert::From<" ^ big ^ ", " ^ small
         ^ ">}::from")
          ~extract_name:
            (Some
               ("core.convert.num.From"
               ^ StringUtils.capitalize_first_letter big
               ^ StringUtils.capitalize_first_letter small
               ^ ".from"))
          ~can_fail:false ())
      int_and_smaller_list
  (* Leading zeros *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::leading_zeros")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".leading_zeros")
      ~can_fail:false ()
  (* to_le_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::to_le_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".to_le_bytes")
      ~can_fail:false ()
  (* to_be_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::to_be_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".to_be_bytes")
      ~can_fail:false ()
  (* from_le_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::from_le_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".from_le_bytes")
      ~can_fail:false ()
  (* from_be_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::from_be_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".from_be_bytes")
      ~can_fail:false ()
  (* Clone<bool> *)
  @ [
      mk_fun "core::clone::impls::{core::clone::Clone<bool>}::clone"
        ~extract_name:(Some "core.clone.impls.CloneBool.clone") ~can_fail:false
        ();
    ]
  (* Clone<INT> *)
  @ mk_scalar_fun
      (fun ty -> "core::clone::impls::{core::clone::Clone<" ^ ty ^ ">}::clone")
      (fun ty ->
        "core.clone.impls.Clone"
        ^ StringUtils.capitalize_first_letter ty
        ^ ".clone")
      ~can_fail:false ()
  (* Lean-only definitions *)
  @ mk_lean_only
      ([
         mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::resize"
           ~filter:(Some [ true; false ])
           ();
         mk_fun "core::mem::swap" ~can_fail:false ();
         mk_fun "core::option::{core::option::Option<@T>}::take"
           ~extract_name:
             (backend_choice None (Some "core::option::Option::take"))
           ~can_fail:false ();
         mk_fun "core::option::{core::option::Option<@T>}::is_none"
           ~extract_name:
             (backend_choice None (Some "core::option::Option::is_none"))
           ~can_fail:false ();
         mk_fun "core::clone::Clone::clone_from" ();
         (* Into<T, U: From<T>> *)
         mk_fun "core::convert::{core::convert::Into<@T, @U>}::into"
           ~extract_name:(Some "core.convert.IntoFrom.into") ();
         (* From<T, T> *)
         mk_fun "core::convert::{core::convert::From<@T, @T>}::from"
           ~can_fail:false ~extract_name:(Some "core.convert.FromSame.from_") ();
         (* [core::slice::{@Slice<T>}::copy_from_slice] *)
         mk_fun "core::slice::{[@T]}::copy_from_slice" ();
         mk_fun "core::result::{core::result::Result<@T, @E>}::unwrap" ();
         (* Vec *)
         mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::extend_from_slice"
           ~filter:(Some [ true; false ])
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::get"
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::get_mut"
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::get_unchecked"
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::get_unchecked_mut"
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::index"
           ();
         mk_fun
           "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
            [@T]>}::index_mut"
           ();
       ]
      @ List.flatten
          (List.map
             (fun int_name ->
               List.map
                 (fun (can_fail, op) ->
                   mk_fun
                     ("core::num::" ^ "{" ^ int_name ^ "}::" ^ op)
                     ~extract_name:
                       (Some
                          ("core.num."
                          ^ StringUtils.capitalize_first_letter int_name
                          ^ "." ^ op))
                     ~can_fail ())
                 [
                   (false, "saturating_add");
                   (false, "saturating_sub");
                   (false, "wrapping_add");
                   (false, "wrapping_sub");
                   (false, "overflowing_add");
                   (false, "rotate_left");
                   (false, "rotate_right");
                 ])
             all_int_names))

let builtin_funs : unit -> (pattern * bool list option * builtin_fun_info) list
    =
  mk_memoized mk_builtin_funs

let mk_builtin_funs_map () =
  let m =
    NameMatcherMap.of_list
      (List.map
         (fun (name, filter, info) -> (name, (filter, info)))
         (builtin_funs ()))
  in
  log#ltrace
    (lazy ("builtin_funs_map:\n" ^ NameMatcherMap.to_string (fun _ -> "...") m));
  m

let builtin_funs_map = mk_memoized mk_builtin_funs_map

type effect_info = { can_fail : bool; stateful : bool }

let mk_builtin_fun_effects () : (pattern * effect_info) list =
  let builtin_funs : (pattern * bool list option * builtin_fun_info) list =
    builtin_funs ()
  in
  List.map
    (fun ((pattern, _, info) : _ * _ * builtin_fun_info) ->
      let info = { can_fail = info.can_fail; stateful = info.stateful } in
      (pattern, info))
    builtin_funs

let mk_builtin_fun_effects_map () =
  NameMatcherMap.of_list (if_backend mk_builtin_fun_effects [])

let builtin_fun_effects_map = mk_memoized mk_builtin_fun_effects_map

type builtin_trait_decl_info = {
  rust_name : pattern;
  extract_name : string;
  constructor : string;
  parent_clauses : string list;
  consts : (string * string) list;
  types : (string * string) list;
      (** Every type has:
          - a Rust name
          - an extraction name *)
  methods : (string * builtin_fun_info) list;
}
[@@deriving show]

let builtin_trait_decls_info () =
  let mk_trait (rust_name : string) ?(extract_name : string option = None)
      ?(parent_clauses : string list = []) ?(types : string list = [])
      ?(methods : string list = [])
      ?(methods_with_extract : (string * string) list option = None) () :
      builtin_trait_decl_info =
    let rust_name = parse_pattern rust_name in
    let extract_name =
      match extract_name with
      | Some n -> n
      | None ->
          let rust_name = pattern_to_fun_extract_name rust_name in
          flatten_name rust_name
    in
    let constructor = mk_struct_constructor extract_name in
    let consts = [] in
    let types =
      let mk_type item_name =
        let type_name =
          if !record_fields_short_names then item_name
          else extract_name ^ "_" ^ item_name
        in
        let type_name =
          match backend () with
          | FStar | Coq | HOL4 -> StringUtils.lowercase_first_letter type_name
          | Lean -> type_name
        in
        (item_name, type_name)
      in
      List.map mk_type types
    in
    let methods =
      match methods_with_extract with
      | None ->
          let mk_method item_name =
            (* TODO: factor out with builtin_funs_info *)
            let basename =
              if !record_fields_short_names then item_name
              else extract_name ^ "_" ^ item_name
            in
            let fwd =
              { extract_name = basename; can_fail = true; stateful = false }
            in
            (item_name, fwd)
          in
          List.map mk_method methods
      | Some methods ->
          List.map
            (fun (item_name, extract_name) ->
              (item_name, { extract_name; can_fail = true; stateful = false }))
            methods
    in
    {
      rust_name;
      extract_name;
      constructor;
      parent_clauses;
      consts;
      types;
      methods;
    }
  in
  [
    (* Deref *)
    mk_trait "core::ops::deref::Deref" ~types:[ "Target" ] ~methods:[ "deref" ]
      ();
    (* DerefMut *)
    mk_trait "core::ops::deref::DerefMut" ~parent_clauses:[ "derefInst" ]
      ~methods:[ "deref_mut" ] ();
    (* Index *)
    mk_trait "core::ops::index::Index" ~types:[ "Output" ] ~methods:[ "index" ]
      ();
    (* IndexMut *)
    mk_trait "core::ops::index::IndexMut" ~parent_clauses:[ "indexInst" ]
      ~methods:[ "index_mut" ] ();
    (* Sealed *)
    mk_trait "core::slice::index::private_slice_index::Sealed" ();
    (* SliceIndex *)
    mk_trait "core::slice::index::SliceIndex" ~parent_clauses:[ "sealedInst" ]
      ~types:[ "Output" ]
      ~methods:
        [
          "get";
          "get_mut";
          "get_unchecked";
          "get_unchecked_mut";
          "index";
          "index_mut";
        ]
      ();
    (* From *)
    mk_trait "core::convert::From"
      ~methods_with_extract:(Some [ ("from", "from_") ])
      ();
    (* Clone *)
    mk_trait "core::clone::Clone" ~methods:[ "clone" ] ();
    (* Copy *)
    mk_trait "core::marker::Copy" ~parent_clauses:[ "cloneInst" ] ();
  ]
  @ mk_lean_only
      [
        (* Into *)
        mk_trait "core::convert::Into" ~types:[ "T"; "U" ] ~methods:[ "into" ]
          ();
        (* Debug *)
        mk_trait "core::fmt::Debug" ~types:[ "T" ] ~methods:[ "fmt" ] ();
        mk_trait "core::convert::TryFrom" ~methods:[ "try_from" ] ();
        mk_trait "core::convert::TryInto" ~methods:[ "try_into" ] ();
      ]

let mk_builtin_trait_decls_map () =
  NameMatcherMap.of_list
    (List.map
       (fun info -> (info.rust_name, info))
       (builtin_trait_decls_info ()))

let builtin_trait_decls_map = mk_memoized mk_builtin_trait_decls_map

let builtin_trait_impls_info () : (pattern * (bool list option * string)) list =
  let fmt (rust_name : string) ?(extract_name : string option = None)
      ?(filter : bool list option = None) () :
      pattern * (bool list option * string) =
    let rust_name = parse_pattern rust_name in
    let name =
      let name =
        match extract_name with
        | None -> pattern_to_trait_impl_extract_name rust_name
        | Some name -> split_on_separator name
      in
      flatten_name name
    in
    (rust_name, (filter, name))
  in
  [
    (* core::ops::Deref<alloc::boxed::Box<T>> *)
    fmt "core::ops::deref::Deref<Box<@T>>"
      ~extract_name:(Some "alloc::boxed::Box::coreopsDerefInst") ();
    (* core::ops::DerefMut<alloc::boxed::Box<T>> *)
    fmt "core::ops::deref::DerefMut<Box<@T>>"
      ~extract_name:(Some "alloc::boxed::Box::coreopsDerefMutInst") ();
    (* core::ops::index::Index<[T], I> *)
    fmt "core::ops::index::Index<[@T], @I>"
      ~extract_name:(Some "core::ops::index::IndexSliceTIInst") ();
    (* core::ops::index::IndexMut<[T], I> *)
    fmt "core::ops::index::IndexMut<[@T], @I>"
      ~extract_name:(Some "core::ops::index::IndexMutSliceTIInst") ();
    (* core::slice::index::private_slice_index::Sealed<Range<usize>> *)
    fmt
      "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
      ~extract_name:
        (Some "core.slice.index.private_slice_index.SealedRangeUsizeInst") ();
    (* core::slice::index::SliceIndex<Range<usize>, [T]> *)
    fmt "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T]>"
      ~extract_name:(Some "core::slice::index::SliceIndexRangeUsizeSliceTInst")
      ();
    (* core::ops::index::Index<[T; N], I> *)
    fmt "core::ops::index::Index<[@T; @N], @I>"
      ~extract_name:(Some "core::ops::index::IndexArrayInst") ();
    (* core::ops::index::IndexMut<[T; N], I> *)
    fmt "core::ops::index::IndexMut<[@T; @N], @I>"
      ~extract_name:(Some "core::ops::index::IndexMutArrayIInst") ();
    (* core::slice::index::private_slice_index::Sealed<usize> *)
    fmt "core::slice::index::private_slice_index::Sealed<usize>"
      ~extract_name:
        (Some "core::slice::index::private_slice_index::SealedUsizeInst") ();
    (* core::slice::index::SliceIndex<usize, [T]> *)
    fmt "core::slice::index::SliceIndex<usize, [@T]>"
      ~extract_name:(Some "core::slice::index::SliceIndexUsizeSliceTInst") ();
    (* core::ops::index::Index<alloc::vec::Vec<T>, T> *)
    fmt "core::ops::index::Index<alloc::vec::Vec<@T, @A>, @T>"
      ~extract_name:(Some "alloc::vec::Vec::coreopsindexIndexInst")
      ~filter:(Some [ true; true; false ])
      ();
    (* core::ops::index::IndexMut<alloc::vec::Vec<T>, T> *)
    fmt "core::ops::index::IndexMut<alloc::vec::Vec<@T, @A>, @T>"
      ~extract_name:(Some "alloc::vec::Vec::coreopsindexIndexMutInst")
      ~filter:(Some [ true; true; false ])
      ();
    (* core::clone::impls::{core::clone::Clone for bool} *)
    fmt "core::clone::Clone<bool>" ~extract_name:(Some "core::clone::CloneBool")
      ();
    fmt "core::ops::deref::Deref<alloc::vec::Vec<@Self, @>>"
      ~extract_name:(Some "alloc.vec.DerefVec")
      ~filter:(Some [ true; false ])
      ();
    fmt "core::ops::deref::DerefMut<alloc::vec::Vec<@Self, @>>"
      ~extract_name:(Some "alloc.vec.DerefMutVec")
      ~filter:(Some [ true; false ])
      ();
  ]
  @ mk_lean_only
      [
        (* Into<T, U: From<T>> *)
        fmt "core::convert::Into<@Self, @T>"
          ~extract_name:(Some "core::convert::IntoFrom") ();
        (* From<T, T> *)
        fmt "core::convert::From<@Self, @Self>"
          ~extract_name:(Some "core::convert::FromSame") ();
        (* TryInto<T, U : TryFrom<T>> *)
        fmt "core::convert::{core::convert::TryInto<@T, @U>}"
          ~extract_name:(Some "core::convert::TryIntoFrom") ();
        fmt
          "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"
          ();
        fmt
          "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, \
           [@Self]>"
          ();
      ]
  (* From<INT, bool> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::convert::From<" ^ ty ^ ", bool>")
          ~extract_name:
            (Some
               ("core.convert.From"
               ^ StringUtils.capitalize_first_letter ty
               ^ "Bool"))
          ())
      all_int_names
  (* From<INT, INT> *)
  @ List.map
      (fun (big, small) ->
        fmt
          ("core::convert::From<" ^ big ^ ", " ^ small ^ ">")
          ~extract_name:
            (Some
               ("core.convert.From"
               ^ StringUtils.capitalize_first_letter big
               ^ StringUtils.capitalize_first_letter small))
          ())
      int_and_smaller_list
  (* Clone<INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::clone::Clone<" ^ ty ^ ">")
          ~extract_name:
            (Some ("core.clone.Clone" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names
  (* Copy<INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::marker::Copy<" ^ ty ^ ">")
          ~extract_name:
            (Some ("core.marker.Copy" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names

let mk_builtin_trait_impls_map () =
  let m = NameMatcherMap.of_list (builtin_trait_impls_info ()) in
  log#ltrace
    (lazy
      ("builtin_trait_impls_map:\n"
      ^ NameMatcherMap.to_string (fun _ -> "...") m));
  m

let builtin_trait_impls_map = mk_memoized mk_builtin_trait_impls_map
