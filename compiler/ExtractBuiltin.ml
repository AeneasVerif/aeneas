(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends.

    TODO: there misses trait **implementations**
 *)

open Config
open Charon.NameMatcher (* TODO: include? *)
include ExtractName (* TODO: only open? *)

let log = Logging.builtin_log

let all_int_names =
  [
    "usize";
    "u8";
    "u16";
    "u32";
    "u64";
    "u128";
    "isize";
    "i8";
    "i16";
    "i32";
    "i64";
    "i128";
  ]

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
  match !backend with
  | FStar | Coq | HOL4 -> String.concat "_" name
  | Lean -> String.concat "." name

let () =
  assert (split_on_separator "x::y::z" = [ "x"; "y"; "z" ]);
  assert (split_on_separator "x.y.z" = [ "x"; "y"; "z" ])

(** Switch between two values depending on the target backend.

    We often compute the same value (typically: a name) if the target
    is F*, Coq or HOL4, and a different value if the target is Lean.
 *)
let backend_choice (fstar_coq_hol4 : 'a) (lean : 'a) : 'a =
  match !backend with Coq | FStar | HOL4 -> fstar_coq_hol4 | Lean -> lean

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
  | KStruct of (string * string) list
  (* TODO: handle the tuple case *)
  | KEnum (* TODO *)

let mk_struct_constructor (type_name : string) : string =
  let prefix =
    match !backend with FStar -> "Mk" | Coq | HOL4 -> "mk" | Lean -> ""
  in
  let suffix = match !backend with FStar | Coq | HOL4 -> "" | Lean -> ".mk" in
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
                  match !backend with
                  | FStar | Lean -> name
                  | Coq | HOL4 -> extract_name ^ "_" ^ name ))
              fields
          in
          let constructor = mk_struct_constructor extract_name in
          Some (Struct (constructor, fields))
      | KEnum -> raise (Failure "TODO")
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
      ~kind:(KStruct [ ("start", "start"); ("end", "end_") ])
      ();
    (* Option

       This one is more custom because we use the standard "option" type from
       the target backend.
    *)
    {
      rust_name = parse_pattern "core::option::Option";
      extract_name =
        (match !backend with
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
                   (match !backend with
                   | FStar | Coq -> "None"
                   | Lean -> "none"
                   | HOL4 -> "NONE");
                 fields = None;
               };
               {
                 rust_variant_name = "Some";
                 extract_variant_name =
                   (match !backend with
                   | FStar | Coq -> "Some"
                   | Lean -> "some"
                   | HOL4 -> "SOME");
                 fields = None;
               };
             ]);
    };
  ]

let mk_builtin_types_map () =
  NameMatcherMap.of_list
    (List.map (fun info -> (info.rust_name, info)) (builtin_types ()))

let builtin_types_map = mk_memoized mk_builtin_types_map

type builtin_fun_info = { extract_name : string } [@@deriving show]

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

(** The assumed functions.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is
    a type parameter for the allocator to use, which we want to filter.
 *)
let builtin_funs () : (pattern * bool list option * builtin_fun_info) list =
  (* Small utility *)
  let mk_fun (rust_name : string) (extract_name : string option)
      (filter : bool list option) :
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
    let f = { extract_name = basename } in
    (rust_name, filter, f)
  in
  let mk_scalar_fun (rust_name : string -> string)
      (extract_name : string -> string) :
      (pattern * bool list option * builtin_fun_info) list =
    List.map
      (fun ty -> mk_fun (rust_name ty) (Some (extract_name ty)) None)
      all_int_names
  in
  [
    mk_fun "core::mem::replace" None None;
    mk_fun "core::mem::swap" None None;
    mk_fun "core::slice::{[@T]}::len"
      (Some (backend_choice "slice::len" "Slice::len"))
      None;
    mk_fun "core::option::{core::option::Option<@T>}::take"
      (Some (backend_choice "option::take" "Option::take"))
      None;
    mk_fun "core::option::{core::option::Option<@T>}::is_none"
      (Some (backend_choice "option::is_none" "Option::isNone"))
      (Some [ false ]);
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::new"
      (Some "alloc::vec::Vec::new") None;
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::push" None
      (Some [ true; false ]);
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::insert" None
      (Some [ true; false ]);
    mk_fun "alloc::vec::{alloc::vec::Vec<@T, @A>}::len" None
      (Some [ true; false ]);
    mk_fun
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T, @A>, \
       @I>}::index"
      (Some "alloc.vec.Vec.index")
      (Some [ true; true; false ]);
    mk_fun
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T, @A>, \
       @I>}::index_mut"
      (Some "alloc.vec.Vec.index_mut")
      (Some [ true; true; false ]);
    mk_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>>}::deref"
      (Some "alloc.boxed.Box.deref")
      (Some [ true; false ]);
    mk_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>>}::deref_mut"
      (Some "alloc.boxed.Box.deref_mut")
      (Some [ true; false ]);
    mk_fun "core::slice::index::{core::ops::index::Index<[@T], @I>}::index"
      (Some "core.slice.index.Slice.index") None;
    mk_fun
      "core::slice::index::{core::ops::index::IndexMut<[@T], @I>}::index_mut"
      (Some "core.slice.index.Slice.index_mut") None;
    mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I>}::index"
      (Some "core.array.Array.index") None;
    mk_fun "core::array::{core::ops::index::IndexMut<[@T; @N], @I>}::index_mut"
      (Some "core.array.Array.index_mut") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get"
      (Some "core::slice::index::RangeUsize::get") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_mut"
      (Some "core::slice::index::RangeUsize::get_mut") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::index"
      (Some "core::slice::index::RangeUsize::index") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::index_mut"
      (Some "core::slice::index::RangeUsize::index_mut") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_unchecked"
      (Some "core::slice::index::RangeUsize::get_unchecked") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
       [@T]>}::get_unchecked_mut"
      (Some "core::slice::index::RangeUsize::get_unchecked_mut") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T]>}::get"
      None None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_mut"
      None None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_unchecked"
      None None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::get_unchecked_mut"
      None None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, [@T]>}::index"
      (Some "core_slice_index_Slice_index") None;
    mk_fun
      "core::slice::index::{core::slice::index::SliceIndex<usize, \
       [@T]>}::index_mut"
      (Some "core_slice_index_Slice_index_mut") None;
    mk_fun "alloc::slice::{[@T]}::to_vec" (Some "alloc.slice.Slice.to_vec") None;
    mk_fun
      "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::with_capacity"
      (Some "alloc.vec.Vec.with_capacity") None;
    mk_fun "core::slice::{[@T]}::reverse" (Some "core.slice.Slice.reverse") None;
    mk_fun
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T, @A>>}::deref"
      (Some "alloc.vec.DerefVec.deref")
      (Some [ true; false ]);
    mk_fun
      "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T, \
       @A>>}::deref_mut"
      (Some "alloc.vec.DerefMutVec.deref_mut")
      (Some [ true; false ]);
  ]
  @ List.flatten
      (List.map
         (fun op ->
           mk_scalar_fun
             (fun ty -> "core::num::{" ^ ty ^ "}::checked_" ^ op)
             (fun ty ->
               StringUtils.capitalize_first_letter ty ^ ".checked_" ^ op))
         [ "add"; "sub"; "mul"; "div"; "rem" ])
  (* From<INT, bool> *)
  @ mk_scalar_fun
      (fun ty ->
        "core::convert::num::{core::convert::From<" ^ ty ^ ", bool>}::from")
      (fun ty ->
        "core.convert.num.From"
        ^ StringUtils.capitalize_first_letter ty
        ^ "Bool.from")
  (* From<INT, INT> *)
  @ List.map
      (fun (big, small) ->
        mk_fun
          ("core::convert::num::{core::convert::From<" ^ big ^ ", " ^ small
         ^ ">}::from")
          (Some
             ("core.convert.num.From"
             ^ StringUtils.capitalize_first_letter big
             ^ StringUtils.capitalize_first_letter small
             ^ ".from"))
          None)
      int_and_smaller_list
  (* Leading zeros *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::leading_zeros")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".leading_zeros")
  (* to_le_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::to_le_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".to_le_bytes")
  (* to_be_bytes *)
  @ mk_scalar_fun
      (fun ty -> "core::num::{" ^ ty ^ "}::to_be_bytes")
      (fun ty ->
        "core.num." ^ StringUtils.capitalize_first_letter ty ^ ".to_be_bytes")
  (* Clone<bool> *)
  @ [
      mk_fun "core::clone::impls::{core::clone::Clone<bool>}::clone"
        (Some "core.clone.CloneBool.clone") None;
    ]
  (* Clone<INT> *)
  @ mk_scalar_fun
      (fun ty -> "core::clone::impls::{core::clone::Clone<" ^ ty ^ ">}::clone")
      (fun ty ->
        "core.clone.Clone" ^ StringUtils.capitalize_first_letter ty ^ ".clone")

let mk_builtin_funs_map () =
  let m =
    NameMatcherMap.of_list
      (List.map
         (fun (name, filter, info) -> (name, (filter, info)))
         (builtin_funs ()))
  in
  log#ldebug
    (lazy ("builtin_funs_map:\n" ^ NameMatcherMap.to_string (fun _ -> "...") m));
  m

let builtin_funs_map = mk_memoized mk_builtin_funs_map

type effect_info = { can_fail : bool; stateful : bool }

let builtin_fun_effects =
  let int_ops =
    [ "wrapping_add"; "wrapping_sub"; "rotate_left"; "rotate_right" ]
  in
  let int_funs =
    List.map
      (fun int_name ->
        List.map (fun op -> "core::num::" ^ "{" ^ int_name ^ "}::" ^ op) int_ops)
      all_int_names
    @ List.map
        (fun op ->
          List.map
            (fun ty -> "core::num::{" ^ ty ^ "}::checked_" ^ op)
            all_int_names)
        [ "add"; "sub"; "mul"; "div"; "rem" ]
    (* From<INT, bool> *)
    @ [
        List.map
          (fun int_name ->
            "core::convert::num::{core::convert::From<" ^ int_name
            ^ ", bool>}::from")
          all_int_names;
      ]
    (* From<INT, INT> *)
    @ [
        List.map
          (fun (big, small) ->
            "core::convert::num::{core::convert::From<" ^ big ^ ", " ^ small
            ^ ">}::from")
          int_and_smaller_list;
      ]
    (* Leading zeros *)
    @ [
        List.map
          (fun ty -> "core::num::{" ^ ty ^ "}::leading_zeros")
          all_int_names;
      ]
    (* to_{le,be}_bytes *)
    @ List.map
        (fun ty ->
          let pre = "core::num::{" ^ ty ^ "}::" in
          [ pre ^ "to_le_bytes"; pre ^ "to_be_bytes" ])
        all_int_names
    (* clone *)
    @ [
        List.map
          (fun ty ->
            "core::clone::impls::{core::clone::Clone<" ^ ty ^ ">}::clone")
          all_int_names;
      ]
  in

  let int_funs = List.concat int_funs in
  let no_fail_no_state_funs =
    [
      (* TODO: redundancy with the funs information above *)
      "core::slice::{[@T]}::len";
      "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::new";
      "alloc::vec::{alloc::vec::Vec<@T, @A>}::len";
      "core::mem::replace";
      "core::mem::swap";
      "core::mem::take";
      "core::option::{core::option::Option<@T>}::take";
      "core::option::{core::option::Option<@T>}::is_none";
      "core::clone::impls::{core::clone::Clone<bool>}::clone";
      "alloc::vec::{alloc::vec::Vec<@T, alloc::alloc::Global>}::with_capacity";
      "core::slice::{[@T]}::reverse";
      "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T, @A>>}::deref";
    ]
    @ int_funs
  in
  let no_fail_no_state_funs =
    List.map
      (fun n -> (n, { can_fail = false; stateful = false }))
      no_fail_no_state_funs
  in
  let no_state_funs =
    [
      (* TODO: redundancy with the funs information above *)
      "alloc::vec::{alloc::vec::Vec<@T, @A>}::push";
      "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T, @A>, \
       @I>}::index";
      "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T, @A>, \
       @I>}::index_mut";
    ]
  in
  let no_state_funs =
    List.map (fun n -> (n, { can_fail = true; stateful = false })) no_state_funs
  in
  no_fail_no_state_funs @ no_state_funs

let builtin_fun_effects_map =
  NameMatcherMap.of_list
    (List.map (fun (n, x) -> (parse_pattern n, x)) builtin_fun_effects)

type builtin_trait_decl_info = {
  rust_name : pattern;
  extract_name : string;
  constructor : string;
  parent_clauses : string list;
  consts : (string * string) list;
  types : (string * (string * string list)) list;
      (** Every type has:
          - a Rust name
          - an extraction name
          - a list of clauses *)
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
          match !backend with
          | FStar | Coq | HOL4 -> StringUtils.lowercase_first_letter type_name
          | Lean -> type_name
        in
        let clauses = [] in
        (item_name, (type_name, clauses))
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
            let fwd = { extract_name = basename } in
            (item_name, fwd)
          in
          List.map mk_method methods
      | Some methods ->
          List.map
            (fun (item_name, extract_name) -> (item_name, { extract_name }))
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

let mk_builtin_trait_impls_map () =
  let m = NameMatcherMap.of_list (builtin_trait_impls_info ()) in
  log#ldebug
    (lazy
      ("builtin_trait_impls_map:\n"
      ^ NameMatcherMap.to_string (fun _ -> "...") m));
  m

let builtin_trait_impls_map = mk_memoized mk_builtin_trait_impls_map
