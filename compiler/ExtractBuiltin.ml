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
  | Struct of string * string list
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

(** The assumed types.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is
    a type parameter for the allocator to use, which we want to filter.
 *)
let builtin_types () : builtin_type_info list =
  [
    (* Alloc *)
    {
      rust_name = [ "alloc"; "alloc"; "Global" ];
      extract_name =
        (match !backend with
        | Lean -> "alloc.alloc.Global"
        | Coq | FStar | HOL4 -> "alloc_global");
      keep_params = None;
      body_info = None;
    };
    (* Vec *)
    {
      rust_name = [ "alloc"; "vec"; "Vec" ];
      extract_name =
        (match !backend with Lean -> "Vec" | Coq | FStar | HOL4 -> "vec");
      keep_params = Some [ true; false ];
      body_info = None;
    };
    (* Option *)
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
    (* Range *)
    {
      rust_name = [ "core"; "ops"; "range"; "Range" ];
      extract_name =
        (match !backend with Lean -> "Range" | Coq | FStar | HOL4 -> "range");
      keep_params = None;
      body_info =
        Some
          (Struct
             ( (match !backend with
               | Lean -> "Range.mk"
               | Coq | HOL4 -> "mk_range"
               | FStar -> "Mkrange"),
               [ "start"; "end_" ] ));
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
  [
    ( [ "core"; "mem"; "replace" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_mem_replace_fwd"
            | Lean -> "core.mem.replace");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_mem_replace_back"
            | Lean -> "core.mem.replace_back");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "new" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_new"
            | Lean -> "Vec.new");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_new_back"
            | Lean -> "Vec.new_back");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "push" ],
      Some [ true; false ],
      [
        (* The forward function shouldn't be used *)
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_push_fwd"
            | Lean -> "Vec.push_fwd");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_push_back"
            | Lean -> "Vec.push");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "insert" ],
      Some [ true; false ],
      [
        (* The forward function shouldn't be used *)
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_insert_fwd"
            | Lean -> "Vec.insert_fwd");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_insert_back"
            | Lean -> "Vec.insert");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "len" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_len"
            | Lean -> "Vec.len");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "index" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_index_fwd"
            | Lean -> "Vec.index_shared");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_index_back"
            | Lean -> "Vec.index_shared_back");
        };
      ] );
    ( [ "alloc"; "vec"; "Vec"; "index_mut" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_index_mut_fwd"
            | Lean -> "Vec.index_mut");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "vec_index_mut_back"
            | Lean -> "Vec.index_mut_back");
        };
      ] );
    ( [ "alloc"; "boxed"; "Box"; "deref" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "alloc_boxed_Box_deref"
            | Lean -> "alloc.boxed.Box.deref");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "alloc_boxed_Box_deref_back"
            | Lean -> "alloc.boxed.Box.deref_back");
        };
      ] );
    ( [ "alloc"; "boxed"; "Box"; "deref_mut" ],
      Some [ true; false ],
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "alloc_boxed_Box_deref_mut"
            | Lean -> "alloc.boxed.Box.deref_mut");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "alloc_boxed_box_deref_mut_back"
            | Lean -> "alloc.boxed.Box.deref_mut_back");
        };
      ] );
    (* TODO: fix the same like "[T]" below *)
    ( [ "core"; "slice"; "index"; "[T]"; "index" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Slice_index"
            | Lean -> "core.slice.index.Slice.index");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Slice_index_back"
            | Lean -> "core.slice.index.Slice.index_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "[T]"; "index_mut" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Slice_index_mut"
            | Lean -> "core.slice.index.Slice.index_mut");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Slice_index_mut_back"
            | Lean -> "core.slice.index.Slice.index_mut_back");
        };
      ] );
    ( [ "core"; "array"; "[T; N]"; "index" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_array_Array_index"
            | Lean -> "core.array.Array.index");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_array_Array_index_back"
            | Lean -> "core.array.Array.index_back");
        };
      ] );
    ( [ "core"; "array"; "[T; N]"; "index_mut" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_array_Array_index_mut"
            | Lean -> "core.array.Array.index_mut");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_array_Array_index_mut_back"
            | Lean -> "core.array.Array.index_mut_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "get" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get"
            | Lean -> "core.slice.index.Range.get");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get_back"
            | Lean -> "core.slice.index.Range.get_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "get_mut" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get_mut"
            | Lean -> "core.slice.index.Range.get_mut");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get_mut_back"
            | Lean -> "core.slice.index.Range.get_mut_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "index" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_index"
            | Lean -> "core.slice.index.Range.index");
        };
        (* The backward function shouldn't be used *)
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_index_back"
            | Lean -> "core.slice.index.Range.index_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "index_mut" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_index_mut"
            | Lean -> "core.slice.index.Range.index_mut");
        };
        {
          rg = rg0;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_index_mut_back"
            | Lean -> "core.slice.index.Range.index_mut_back");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "get_unchecked" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get_unchecked"
            | Lean -> "core.slice.index.Range.get_unchecked");
        };
      ] );
    ( [ "core"; "slice"; "index"; "Range"; "get_unchecked_mut" ],
      None,
      [
        {
          rg = None;
          extract_name =
            (match !backend with
            | FStar | Coq | HOL4 -> "core_slice_index_Range_get_unchecked_mut"
            | Lean -> "core.slice.index.Range.get_unchecked_mut");
        };
      ] );
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
  funs : (string * (Types.RegionGroupId.id option * string) list) list;
}
[@@deriving show]

let builtin_trait_decls_info () =
  let rg0 = Some Types.RegionGroupId.zero in
  [
    {
      (* Deref *)
      rust_name = "core::ops::deref::Deref";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_ops_deref_Deref"
        | Lean -> "core.ops.deref.Deref");
      parent_clauses = [];
      consts = [];
      types =
        [
          ( "Target",
            ( (match !backend with
              | Coq | FStar | HOL4 -> "core_ops_deref_Deref_Target"
              | Lean -> "Target"),
              [] ) );
        ];
      funs =
        [
          ( "deref",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_deref_Deref_deref"
                | Lean -> "deref" );
            ] );
        ];
    };
    {
      (* DerefMut *)
      rust_name = "core::ops::deref::DerefMut";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_ops_deref_DerefMut"
        | Lean -> "core.ops.deref.DerefMut");
      parent_clauses =
        [
          (match !backend with
          | Coq | FStar | HOL4 -> "deref_inst"
          | Lean -> "derefInst");
        ];
      consts = [];
      types = [];
      funs =
        [
          ( "deref_mut",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_deref_DerefMut_deref_mut"
                | Lean -> "deref_mut" );
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_deref_DerefMut_deref_mut_back"
                | Lean -> "deref_mut_back" );
            ] );
        ];
    };
    {
      (* Index *)
      rust_name = "core::ops::index::Index";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_ops_index_Index"
        | Lean -> "core.ops.index.Index");
      parent_clauses = [];
      consts = [];
      types =
        [
          ( "Output",
            ( (match !backend with
              | Coq | FStar | HOL4 -> "core_ops_index_Index_Output"
              | Lean -> "Output"),
              [] ) );
        ];
      funs =
        [
          ( "index",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_index_Index_index"
                | Lean -> "index" );
            ] );
        ];
    };
    {
      (* IndexMut *)
      rust_name = "core::ops::index::IndexMut";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_ops_index_IndexMut"
        | Lean -> "core.ops.index.IndexMut");
      parent_clauses =
        [
          (match !backend with
          | Coq | FStar | HOL4 -> "index_inst"
          | Lean -> "indexInst");
        ];
      consts = [];
      types = [];
      funs =
        [
          ( "index_mut",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_index_IndexMut_mut"
                | Lean -> "index_mut" );
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_ops_index_IndexMut_mut_back"
                | Lean -> "index_mut_back" );
            ] );
        ];
    };
    {
      (* Sealed *)
      rust_name = "core::slice::index::private_slice_index::Sealed";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_slice_index_sealed"
        | Lean -> "core.slice.index.private_slice_index.Sealed");
      parent_clauses = [];
      consts = [];
      types = [];
      funs = [];
    };
    {
      (* SliceIndex *)
      rust_name = "core::slice::index::SliceIndex";
      extract_name =
        (match !backend with
        | Coq | FStar | HOL4 -> "core_SliceIndex"
        | Lean -> "core.slice.index.SliceIndex");
      parent_clauses =
        [
          (match !backend with
          | Coq | FStar | HOL4 -> "sealed_inst"
          | Lean -> "sealedInst");
        ];
      consts = [];
      types =
        [
          ( "Output",
            ( (match !backend with
              | Coq | FStar | HOL4 -> "core_SliceIndex_Output"
              | Lean -> "Output"),
              [] ) );
        ];
      funs =
        [
          ( "get",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get"
                | Lean -> "get" );
              (* The backward function shouldn't be used *)
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get_back"
                | Lean -> "get_back" );
            ] );
          ( "get_mut",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get_mut"
                | Lean -> "get_mut" );
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get_mut_back"
                | Lean -> "get_mut_back" );
            ] );
          ( "get_unchecked",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get_unchecked"
                | Lean -> "get_unchecked" );
            ] );
          ( "get_unchecked_mut",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_get_unchecked_mut"
                | Lean -> "get_unchecked_mut" );
            ] );
          ( "index",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_index"
                | Lean -> "index" );
              (* The backward function shouldn't be used *)
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_index_back"
                | Lean -> "index_back" );
            ] );
          ( "index_mut",
            [
              ( None,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_index_mut"
                | Lean -> "index_mut" );
              ( rg0,
                match !backend with
                | Coq | FStar | HOL4 -> "core_SliceIndex_index_mut_back"
                | Lean -> "index_mut_back" );
            ] );
        ];
    };
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

let builtin_trait_impls_info () : ((string list * string list) * string) list =
  (* TODO: fix the names like "[T]" below *)
  [
    (* core::ops::Deref<alloc::boxed::Box<T>> *)
    ( ([ "alloc"; "boxed"; "Box" ], [ "core"; "ops"; "deref"; "Deref" ]),
      "alloc.boxed.Box.coreOpsDerefInst" );
    (* core::ops::DerefMut<alloc::boxed::Box<T>> *)
    ( ([ "alloc"; "boxed"; "Box" ], [ "core"; "ops"; "deref"; "DerefMut" ]),
      "alloc.boxed.Box.coreOpsDerefMutInst" );
    (* core::ops::index::Index<[T], I> *)
    ( ([ "core"; "slice"; "index"; "[T]" ], [ "core"; "ops"; "index"; "Index" ]),
      "core.slice.index.Slice.coreopsindexIndexInst" );
    (* core::slice::index::private_slice_index::Sealed<Range<usize>> *)
    ( ( [ "core"; "slice"; "index"; "private_slice_index"; "Range" ],
        [ "core"; "slice"; "index"; "private_slice_index"; "Sealed" ] ),
      "core.slice.index.private_slice_index.Range.coresliceindexprivate_slice_indexSealedInst"
    );
    (* core::slice::index::SliceIndex<Range<usize>, [T]> *)
    ( ( [ "core"; "slice"; "index"; "Range" ],
        [ "core"; "slice"; "index"; "SliceIndex" ] ),
      "core.slice.index.Range.coresliceindexSliceIndexInst" );
    (* core::ops::index::IndexMut<[T], I> *)
    ( ( [ "core"; "slice"; "index"; "[T]" ],
        [ "core"; "ops"; "index"; "IndexMut" ] ),
      "core.slice.index.Slice.coreopsindexIndexMutInst" );
    (* core::ops::index::Index<[T; N], I> *)
    ( ([ "core"; "array"; "[T; N]" ], [ "core"; "ops"; "index"; "Index" ]),
      "core.array.Array.coreopsindexIndexInst" );
    (* core::ops::index::IndexMut<[T; N], I> *)
    ( ([ "core"; "array"; "[T; N]" ], [ "core"; "ops"; "index"; "IndexMut" ]),
      "core.array.Array.coreopsindexIndexMutInst" );
  ]

let mk_builtin_trait_impls_map () =
  SimpleNamePairMap.of_list (builtin_trait_impls_info ())

let builtin_trait_impls_map = mk_memoized mk_builtin_trait_impls_map
