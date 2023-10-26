(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends.

    TODO: there misses trait **implementations**
 *)

open Names
open Config

type simple_name = string list [@@deriving show, ord]

let name_to_simple_name (s : name) : simple_name =
  (* We simply ignore the disambiguators *)
  List.filter_map (function Ident id -> Some id | Disambiguator _ -> None) s

(** Small helper which cuts a string at the occurrences of "::" *)
let string_to_simple_name (s : string) : simple_name =
  (* No function to split by using string separator?? *)
  let name = String.split_on_char ':' s in
  List.filter (fun s -> s <> "") name

module SimpleNameOrd = struct
  type t = simple_name

  let compare = compare_simple_name
  let to_string = show_simple_name
  let pp_t = pp_simple_name
  let show_t = show_simple_name
end

module SimpleNameMap = Collections.MakeMap (SimpleNameOrd)
module SimpleNameSet = Collections.MakeSet (SimpleNameOrd)

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

(** Switch between two values depending on the target backend.

    We often compute the same value (typically: a name) if the target
    is F*, Coq or HOL4, and a different value if the target is Lean.
 *)
let backend_choice (fstar_coq_hol4 : 'a) (lean : 'a) : 'a =
  match !backend with Coq | FStar | HOL4 -> fstar_coq_hol4 | Lean -> lean

let builtin_globals : (string * string) list =
  [
    (* Min *)
    ("core::num::usize::MIN", "core_usize_min");
    ("core::num::u8::MIN", "core_u8_min");
    ("core::num::u16::MIN", "core_u16_min");
    ("core::num::u32::MIN", "core_u32_min");
    ("core::num::u64::MIN", "core_u64_min");
    ("core::num::u128::MIN", "core_u128_min");
    ("core::num::isize::MIN", "core_isize_min");
    ("core::num::i8::MIN", "core_i8_min");
    ("core::num::i16::MIN", "core_i16_min");
    ("core::num::i32::MIN", "core_i32_min");
    ("core::num::i64::MIN", "core_i64_min");
    ("core::num::i128::MIN", "core_i128_min");
    (* Max *)
    ("core::num::usize::MAX", "core_usize_max");
    ("core::num::u8::MAX", "core_u8_max");
    ("core::num::u16::MAX", "core_u16_max");
    ("core::num::u32::MAX", "core_u32_max");
    ("core::num::u64::MAX", "core_u64_max");
    ("core::num::u128::MAX", "core_u128_max");
    ("core::num::isize::MAX", "core_isize_max");
    ("core::num::i8::MAX", "core_i8_max");
    ("core::num::i16::MAX", "core_i16_max");
    ("core::num::i32::MAX", "core_i32_max");
    ("core::num::i64::MAX", "core_i64_max");
    ("core::num::i128::MAX", "core_i128_max");
  ]

let builtin_globals_map : string SimpleNameMap.t =
  SimpleNameMap.of_list
    (List.map (fun (x, y) -> (string_to_simple_name x, y)) builtin_globals)

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
  rust_name : string list;
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
  let mk_type (rust_name : string list) ?(keep_params : bool list option = None)
      ?(kind : type_variant_kind = KOpaque) () : builtin_type_info =
    let extract_name =
      let sep = backend_choice "_" "." in
      String.concat sep rust_name
    in
    let body_info : builtin_type_body_info option =
      match kind with
      | KOpaque -> None
      | KStruct fields ->
          let fields =
            List.map
              (fun (rname, name) ->
                (rname, backend_choice (extract_name ^ name) name))
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
    mk_type [ "alloc"; "alloc"; "Global" ] ();
    (* Vec *)
    mk_type [ "alloc"; "vec"; "Vec" ] ~keep_params:(Some [ true; false ]) ();
    (* Range *)
    mk_type
      [ "core"; "ops"; "range"; "Range" ]
      ~kind:(KStruct [ ("start", "start"); ("end", "end_") ])
      ();
    (* Option

       This one is more custom because we use the standard "option" type from
       the target backend.
    *)
    {
      rust_name = [ "core"; "option"; "Option" ];
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
  SimpleNameMap.of_list
    (List.map (fun info -> (info.rust_name, info)) (builtin_types ()))

let builtin_types_map = mk_memoized mk_builtin_types_map

type builtin_fun_info = {
  rg : Types.RegionGroupId.id option;
  extract_name : string;
}
[@@deriving show]

(** The assumed functions.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is
    a type parameter for the allocator to use, which we want to filter.
 *)
let builtin_funs () :
    (string list * bool list option * builtin_fun_info list) list =
  let rg0 = Some Types.RegionGroupId.zero in
  (* Small utility *)
  let mk_fun (name : string list) (extract_name : string list option)
      (filter : bool list option) (with_back : bool) (back_no_suffix : bool) :
      string list * bool list option * builtin_fun_info list =
    let extract_name =
      match extract_name with None -> name | Some name -> name
    in
    let basename =
      match !backend with
      | FStar | Coq | HOL4 -> String.concat "_" extract_name
      | Lean -> String.concat "." extract_name
    in
    let fwd_suffix = if with_back && back_no_suffix then "_fwd" else "" in
    let fwd = [ { rg = None; extract_name = basename ^ fwd_suffix } ] in
    let back_suffix = if with_back && back_no_suffix then "" else "_back" in
    let back =
      if with_back then [ { rg = rg0; extract_name = basename ^ back_suffix } ]
      else []
    in
    (name, filter, fwd @ back)
  in
  [
    mk_fun [ "core"; "mem"; "replace" ] None None true false;
    mk_fun [ "alloc"; "vec"; "Vec"; "new" ] None None false false;
    mk_fun
      [ "alloc"; "vec"; "Vec"; "push" ]
      None
      (Some [ true; false ])
      true true;
    mk_fun
      [ "alloc"; "vec"; "Vec"; "insert" ]
      None
      (Some [ true; false ])
      true true;
    mk_fun
      [ "alloc"; "vec"; "Vec"; "len" ]
      None
      (Some [ true; false ])
      true false;
    mk_fun
      [ "alloc"; "vec"; "Vec"; "index" ]
      None
      (Some [ true; true; false ])
      true false;
    mk_fun
      [ "alloc"; "vec"; "Vec"; "index_mut" ]
      None
      (Some [ true; true; false ])
      true false;
    mk_fun
      [ "alloc"; "boxed"; "Box"; "deref" ]
      None
      (Some [ true; false ])
      true false;
    mk_fun
      [ "alloc"; "boxed"; "Box"; "deref_mut" ]
      None
      (Some [ true; false ])
      true false;
    (* TODO: fix the same like "[T]" below *)
    mk_fun
      [ "core"; "slice"; "index"; "[T]"; "index" ]
      (Some [ "core"; "slice"; "index"; "Slice"; "index" ])
      None true false;
    mk_fun
      [ "core"; "slice"; "index"; "[T]"; "index_mut" ]
      (Some [ "core"; "slice"; "index"; "Slice"; "index_mut" ])
      None true false;
    mk_fun
      [ "core"; "array"; "[T; N]"; "index" ]
      (Some [ "core"; "array"; "Array"; "index" ])
      None true false;
    mk_fun
      [ "core"; "array"; "[T; N]"; "index_mut" ]
      (Some [ "core"; "array"; "Array"; "index_mut" ])
      None true false;
    mk_fun [ "core"; "slice"; "index"; "Range"; "get" ] None None true false;
    mk_fun [ "core"; "slice"; "index"; "Range"; "get_mut" ] None None true false;
    mk_fun [ "core"; "slice"; "index"; "Range"; "index" ] None None true false;
    mk_fun
      [ "core"; "slice"; "index"; "Range"; "index_mut" ]
      None None true false;
    mk_fun
      [ "core"; "slice"; "index"; "Range"; "get_unchecked" ]
      None None false false;
    mk_fun
      [ "core"; "slice"; "index"; "Range"; "get_unchecked_mut" ]
      None None false false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "get" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "get" ])
      None true false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "get_mut" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "get_mut" ])
      None true false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "get_unchecked" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "get_unchecked" ])
      None false false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "get_unchecked_mut" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "get_unchecked_mut" ])
      None false false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "index" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "index" ])
      None true false;
    mk_fun
      [ "core"; "slice"; "index"; "usize"; "index_mut" ]
      (Some [ "core"; "slice"; "index"; "Usize"; "index_mut" ])
      None true false;
  ]

let mk_builtin_funs_map () =
  SimpleNameMap.of_list
    (List.map
       (fun (name, filter, info) -> (name, (filter, info)))
       (builtin_funs ()))

let builtin_funs_map = mk_memoized mk_builtin_funs_map

let builtin_non_fallible_funs =
  let int_names =
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
  in
  let int_ops =
    [ "wrapping_add"; "wrapping_sub"; "rotate_left"; "rotate_right" ]
  in
  let int_funs =
    List.map
      (fun int_name ->
        List.map (fun op -> "core::num::" ^ int_name ^ "::" ^ op) int_ops)
      int_names
  in
  let int_funs = List.concat int_funs in
  [
    "alloc::vec::Vec::new";
    "alloc::vec::Vec::len";
    "alloc::boxed::Box::deref";
    "alloc::boxed::Box::deref_mut";
    "core::mem::replace";
    "core::mem::take";
  ]
  @ int_funs

let builtin_non_fallible_funs_set =
  SimpleNameSet.of_list
    (List.map string_to_simple_name builtin_non_fallible_funs)

type builtin_trait_decl_info = {
  rust_name : string;
  extract_name : string;
  parent_clauses : string list;
  consts : (string * string) list;
  types : (string * (string * string list)) list;
      (** Every type has:
          - a Rust name
          - an extraction name
          - a list of clauses *)
  methods : (string * builtin_fun_info list) list;
}
[@@deriving show]

let builtin_trait_decls_info () =
  let rg0 = Some Types.RegionGroupId.zero in
  let mk_trait (rust_name : string list) ?(extract_name : string option = None)
      ?(parent_clauses : string list = []) ?(types : string list = [])
      ?(methods : (string * bool) list = []) () : builtin_trait_decl_info =
    let extract_name =
      match extract_name with
      | Some n -> n
      | None -> (
          match !backend with
          | Coq | FStar | HOL4 -> String.concat "_" rust_name
          | Lean -> String.concat "." rust_name)
    in
    let consts = [] in
    let types =
      let mk_type item_name =
        let type_name =
          match !backend with
          | Coq | FStar | HOL4 -> extract_name ^ "_" ^ item_name
          | Lean -> item_name
        in
        let clauses = [] in
        (item_name, (type_name, clauses))
      in
      List.map mk_type types
    in
    let methods =
      let mk_method (item_name, with_back) =
        (* TODO: factor out with builtin_funs_info *)
        let basename =
          match !backend with
          | Coq | FStar | HOL4 -> extract_name ^ "_" ^ item_name
          | Lean -> item_name
        in
        let back_no_suffix = false in
        let fwd_suffix = if with_back && back_no_suffix then "_fwd" else "" in
        let fwd = [ { rg = None; extract_name = basename ^ fwd_suffix } ] in
        let back_suffix = if with_back && back_no_suffix then "" else "_back" in
        let back =
          if with_back then
            [ { rg = rg0; extract_name = basename ^ back_suffix } ]
          else []
        in
        (item_name, fwd @ back)
      in
      List.map mk_method methods
    in
    let rust_name = String.concat "::" rust_name in
    { rust_name; extract_name; parent_clauses; consts; types; methods }
  in
  [
    (* Deref *)
    mk_trait
      [ "core"; "ops"; "deref"; "Deref" ]
      ~types:[ "Target" ]
      ~methods:[ ("deref", true) ]
      ();
    (* DerefMut *)
    mk_trait
      [ "core"; "ops"; "deref"; "DerefMut" ]
      ~parent_clauses:[ backend_choice "deref_inst" "derefInst" ]
      ~methods:[ ("deref_mut", true) ]
      ();
    (* Index *)
    mk_trait
      [ "core"; "ops"; "index"; "Index" ]
      ~types:[ "Output" ]
      ~methods:[ ("index", true) ]
      ();
    (* IndexMut *)
    mk_trait
      [ "core"; "ops"; "index"; "IndexMut" ]
      ~parent_clauses:[ backend_choice "index_inst" "indexInst" ]
      ~methods:[ ("index_mut", true) ]
      ();
    (* Sealed *)
    mk_trait [ "core"; "slice"; "index"; "private_slice_index"; "Sealed" ] ();
    (* SliceIndex *)
    mk_trait
      [ "core"; "slice"; "index"; "SliceIndex" ]
      ~parent_clauses:[ backend_choice "sealed_inst" "sealedInst" ]
      ~types:[ "Output" ]
      ~methods:
        [
          ("get", true);
          ("get_mut", true);
          ("get_unchecked", false);
          ("get_unchecked_mut", false);
          ("index", true);
          ("index_mut", true);
        ]
      ();
  ]

let mk_builtin_trait_decls_map () =
  SimpleNameMap.of_list
    (List.map
       (fun info -> (string_to_simple_name info.rust_name, info))
       (builtin_trait_decls_info ()))

let builtin_trait_decls_map = mk_memoized mk_builtin_trait_decls_map

(* TODO: generalize this.

   For now, the key is:
   - name of the impl (ex.: "alloc.boxed.Boxed")
   - name of the implemented trait (ex.: "core.ops.deref.Deref"
*)
type simple_name_pair = simple_name * simple_name [@@deriving show, ord]

module SimpleNamePairOrd = struct
  type t = simple_name_pair

  let compare = compare_simple_name_pair
  let to_string = show_simple_name_pair
  let pp_t = pp_simple_name_pair
  let show_t = show_simple_name_pair
end

module SimpleNamePairMap = Collections.MakeMap (SimpleNamePairOrd)

let builtin_trait_impls_info () :
    ((string list * string list) * (bool list option * string)) list =
  let fmt (type_name : string list)
      ?(extract_type_name : string list option = None)
      (trait_name : string list) ?(filter : bool list option = None) () :
      (string list * string list) * (bool list option * string) =
    let name =
      let trait_name = String.concat "" trait_name ^ "Inst" in
      let sep = backend_choice "_" "." in
      let type_name =
        match extract_type_name with
        | Some type_name -> type_name
        | None -> type_name
      in
      String.concat sep type_name ^ sep ^ trait_name
    in
    ((type_name, trait_name), (filter, name))
  in
  (* TODO: fix the names like "[T]" below *)
  [
    (* core::ops::Deref<alloc::boxed::Box<T>> *)
    fmt [ "alloc"; "boxed"; "Box" ] [ "core"; "ops"; "deref"; "Deref" ] ();
    (* core::ops::DerefMut<alloc::boxed::Box<T>> *)
    fmt [ "alloc"; "boxed"; "Box" ] [ "core"; "ops"; "deref"; "DerefMut" ] ();
    (* core::ops::index::Index<[T], I> *)
    fmt
      [ "core"; "slice"; "index"; "[T]" ]
      ~extract_type_name:(Some [ "core"; "slice"; "index"; "Slice" ])
      [ "core"; "ops"; "index"; "Index" ]
      ();
    (* core::ops::index::IndexMut<[T], I> *)
    fmt
      [ "core"; "slice"; "index"; "[T]" ]
      ~extract_type_name:(Some [ "core"; "slice"; "index"; "Slice" ])
      [ "core"; "ops"; "index"; "IndexMut" ]
      ();
    (* core::slice::index::private_slice_index::Sealed<Range<usize>> *)
    fmt
      [ "core"; "slice"; "index"; "private_slice_index"; "Range" ]
      [ "core"; "slice"; "index"; "private_slice_index"; "Sealed" ]
      ();
    (* core::slice::index::SliceIndex<Range<usize>, [T]> *)
    fmt
      [ "core"; "slice"; "index"; "Range" ]
      [ "core"; "slice"; "index"; "SliceIndex" ]
      ();
    (* core::ops::index::Index<[T; N], I> *)
    fmt
      [ "core"; "array"; "[T; N]" ]
      ~extract_type_name:(Some [ "core"; "array"; "Array" ])
      [ "core"; "ops"; "index"; "Index" ]
      ();
    (* core::ops::index::IndexMut<[T; N], I> *)
    fmt
      [ "core"; "array"; "[T; N]" ]
      ~extract_type_name:(Some [ "core"; "array"; "Array" ])
      [ "core"; "ops"; "index"; "IndexMut" ]
      ();
    (* core::slice::index::private_slice_index::Sealed<usize> *)
    fmt
      [ "core"; "slice"; "index"; "private_slice_index"; "usize" ]
      [ "core"; "slice"; "index"; "private_slice_index"; "Sealed" ]
      ();
    (* core::slice::index::SliceIndex<usize, [T]> *)
    fmt
      [ "core"; "slice"; "index"; "usize" ]
      [ "core"; "slice"; "index"; "SliceIndex" ]
      ();
    (* core::ops::index::Index<Vec<T>, T> *)
    fmt [ "alloc"; "vec"; "Vec" ]
      [ "core"; "ops"; "index"; "Index" ]
      ~filter:(Some [ true; true; false ])
      ();
    (* core::ops::index::IndexMut<Vec<T>, T> *)
    fmt [ "alloc"; "vec"; "Vec" ]
      [ "core"; "ops"; "index"; "IndexMut" ]
      ~filter:(Some [ true; true; false ])
      ();
  ]

let mk_builtin_trait_impls_map () =
  SimpleNamePairMap.of_list (builtin_trait_impls_info ())

let builtin_trait_impls_map = mk_memoized mk_builtin_trait_impls_map
