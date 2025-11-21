(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends.

    TODO: there misses trait **implementations** *)

open Config
include ExtractBuiltinCore
include ExtractBuiltinLean
open NameMatcher (* TODO: include? *)
include ExtractName (* TODO: only open? *)

let log = Logging.builtin_log

let builtin_globals () : (string * string) list =
  let mk_int_global (ty : string) (name : string) : string * string =
    ( "core::num::{" ^ ty ^ "}::" ^ name,
      let sep = if backend () = Lean then "." else "_" in
      "core" ^ sep ^ "num" ^ sep
      ^ StringUtils.capitalize_first_letter ty
      ^ sep ^ name )
  in
  let mk_ints_globals name =
    List.map (fun ty -> mk_int_global ty name) all_int_names
  in
  List.concat
    ([
       mk_ints_globals "MIN";
       mk_ints_globals "MAX";
       [
         (* UNIT_METADATA should be eliminated through a micro-pass and should
           never appear in the code.. *)
         ("UNIT_METADATA", "UNIT_METADATA");
       ];
     ]
    @ mk_lean_only lean_builtin_consts)

let mk_builtin_globals_map () : Pure.builtin_global_info NameMatcherMap.t =
  NameMatcherMap.of_list
    (List.map
       (fun (x, y) -> (parse_pattern x, { Pure.global_name = y }))
       (builtin_globals ()))

let builtin_globals_map = mk_memoized mk_builtin_globals_map

(** The assumed types.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is a
    type parameter for the allocator to use, which we want to filter. *)
let builtin_types () : Pure.builtin_type_info list =
  (let mk_type (rust_name : string) ?(custom_name : string option = None)
       ?(keep_params : bool list option = None)
       ?(kind : type_variant_kind = KOpaque) () : Pure.builtin_type_info =
     let rust_name = parse_pattern rust_name in
     let extract_name =
       match custom_name with
       | None -> flatten_name (pattern_to_type_extract_name rust_name)
       | Some name -> flatten_name (split_on_separator name)
     in
     let body_info : Pure.builtin_type_body_info option =
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
               (fun (variant, evariant) ->
                 let evariant =
                   match evariant with
                   | Some variant -> variant
                   | None -> variant
                 in
                 let extract_variant_name =
                   match backend () with
                   | FStar | Coq -> extract_name ^ "_" ^ evariant
                   | Lean -> extract_name ^ "." ^ evariant
                   | HOL4 -> extract_name ^ evariant
                 in
                 ({
                    rust_variant_name = variant;
                    extract_variant_name;
                    fields = None;
                  }
                   : Pure.builtin_enum_variant_info))
               variants
           in
           Some (Enum variants)
     in
     { rust_name; extract_name; keep_params; body_info }
   in
   []
   @ mk_not_lean
       [
         (* Alloc *)
         mk_type "alloc::alloc::Global" ();
         (* String *)
         mk_type "alloc::string::String" ~custom_name:(Some "string") ();
         (* Vec *)
         mk_type "alloc::vec::Vec" ();
         (* Range *)
         mk_type "core::ops::range::Range"
           ~kind:(KStruct [ ("start", None); ("end", Some "end_") ])
           ();
         (* RangeTo *)
         mk_type "core::ops::range::RangeTo"
           ~kind:(KStruct [ ("end", Some "end_") ])
           ();
         (* Option

            This one is more custom because we use the standard "option" type
            from the target backend. *)
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
       ])
  @ mk_lean_only lean_builtin_types

let mk_builtin_types_map () =
  NameMatcherMap.of_list
    (List.map
       (fun (info : Pure.builtin_type_info) -> (info.rust_name, info))
       (builtin_types ()))

let builtin_types_map = mk_memoized mk_builtin_types_map

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

let builtin_trait_decls_info () =
  let mk_trait (rust_name : string) ?(extract_name : string option = None)
      ?(parent_clauses : string list = []) ?(types : string list = [])
      ?(methods : string list = []) ?(default_methods : string list = [])
      ?(methods_with_extract : (string * string) list option = None) () :
      Pure.builtin_trait_decl_info =
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
      List.map (fun x -> (false, x)) methods
      @ List.map (fun x -> (true, x)) default_methods
    in
    let methods =
      match methods_with_extract with
      | None ->
          let mk_method (has_default, item_name) =
            (* TODO: factor out with builtin_funs_info *)
            let basename =
              if !record_fields_short_names then item_name
              else extract_name ^ "_" ^ item_name
            in
            let fwd : Pure.builtin_fun_info =
              {
                filter_params = None;
                extract_name = basename;
                can_fail = true;
                stateful = false;
                lift = true;
                has_default;
              }
            in

            (item_name, fwd)
          in
          List.map mk_method methods
      | Some methods ->
          List.map
            (fun (item_name, extract_name) ->
              ( item_name,
                ({
                   filter_params = None;
                   extract_name;
                   can_fail = true;
                   stateful = false;
                   lift = true;
                   has_default = false;
                 }
                  : Pure.builtin_fun_info) ))
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
  mk_not_lean
    [
      (* Deref *)
      mk_trait "core::ops::deref::Deref" ~types:[] ~methods:[ "deref" ] ();
      (* DerefMut *)
      mk_trait "core::ops::deref::DerefMut" ~parent_clauses:[ "derefInst" ]
        ~methods:[ "deref_mut" ] ();
      (* Index *)
      mk_trait "core::ops::index::Index" ~types:[] ~methods:[ "index" ] ();
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
      mk_trait "core::clone::Clone" ~methods:[ "clone" ]
        ~default_methods:[ "clone_from" ] ();
      (* Copy *)
      mk_trait "core::marker::Copy" ~parent_clauses:[ "cloneInst" ] ();
    ]
  @ mk_lean_only lean_builtin_trait_decls

let mk_builtin_trait_decls_map () =
  NameMatcherMap.of_list
    (List.map
       (fun (info : Pure.builtin_trait_decl_info) -> (info.rust_name, info))
       (builtin_trait_decls_info ()))

let builtin_trait_decls_map = mk_memoized mk_builtin_trait_decls_map

let builtin_trait_impls_info () : (pattern * Pure.builtin_trait_impl_info) list
    =
  let fmt (rust_name : string) ?(extract_name : string option = None)
      ?(filter : bool list option = None) () :
      pattern * Pure.builtin_trait_impl_info =
    let rust_name = parse_pattern rust_name in
    let name =
      let name =
        match extract_name with
        | None -> pattern_to_trait_impl_extract_name rust_name
        | Some name -> split_on_separator name
      in
      flatten_name name
    in
    (rust_name, { filter_params = filter; extract_name = name })
  in
  mk_not_lean
    [
      (* core::ops::Deref<alloc::boxed::Box<T>> *)
      fmt "core::ops::deref::Deref<Box<@T>, @T>"
        ~extract_name:(Some "core::ops::deref::DerefBoxInst") ();
      (* Core::ops::DerefMut<alloc::boxed::Box<T>> *)
      fmt "core::ops::deref::DerefMut<Box<@T>, @T>"
        ~extract_name:(Some "core::ops::deref::DerefBoxMutInst") ();
      (* core::ops::Deref<alloc::vec::Vec<T>> *)
      fmt "core::ops::deref::Deref<alloc::vec::Vec<@T>, [@T]>"
        ~extract_name:(Some "core::ops::deref::DerefVecInst")
        ~filter:(Some [ true; false ])
        ();
      (* core::ops::DerefMut<alloc::vec::Vec<T>> *)
      fmt "core::ops::deref::DerefMut<alloc::vec::Vec<@T>, [@T]>"
        ~extract_name:(Some "core::ops::deref::DerefMutVecInst")
        ~filter:(Some [ true; false ])
        ();
      (* core::ops::index::Index<[T], I> *)
      fmt "core::ops::index::Index<[@T], @I, @O>"
        ~extract_name:(Some "core::ops::index::IndexSliceInst") ();
      (* core::ops::index::IndexMut<[T], I> *)
      fmt "core::ops::index::IndexMut<[@T], @I, @O>"
        ~extract_name:(Some "core::ops::index::IndexMutSliceInst") ();
      (* core::slice::index::private_slice_index::Sealed<Range<usize>> *)
      fmt
        "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"
        ~extract_name:
          (Some "core.slice.index.private_slice_index.SealedRangeUsizeInst") ();
      (* core::slice::index::SliceIndex<Range<usize>, [T]> *)
      fmt
        "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], \
         [@T]>"
        ~extract_name:(Some "core::slice::index::SliceIndexRangeUsizeSliceInst")
        ();
      (* core::ops::index::Index<[T; N], I> *)
      fmt "core::ops::index::Index<[@T; @N], @I, @O>"
        ~extract_name:(Some "core::ops::index::IndexArrayInst") ();
      (* core::ops::index::IndexMut<[T; N], I> *)
      fmt "core::ops::index::IndexMut<[@T; @N], @I, @O>"
        ~extract_name:(Some "core::ops::index::IndexMutArrayInst") ();
      (* core::slice::index::private_slice_index::Sealed<usize> *)
      fmt "core::slice::index::private_slice_index::Sealed<usize>"
        ~extract_name:
          (Some "core::slice::index::private_slice_index::SealedUsizeInst") ();
      (* core::slice::index::SliceIndex<usize, [T]> *)
      fmt "core::slice::index::SliceIndex<usize, [@T], @T>"
        ~extract_name:(Some "core::slice::index::SliceIndexUsizeSliceInst") ();
      (* core::ops::index::Index<alloc::vec::Vec<T>, T> *)
      fmt "core::ops::index::Index<alloc::vec::Vec<@T>, @T, @O>"
        ~extract_name:(Some "alloc::vec::Vec::IndexInst")
        ~filter:(Some [ true; true; false; true ])
        ();
      (* core::ops::index::IndexMut<alloc::vec::Vec<T>, T> *)
      fmt "core::ops::index::IndexMut<alloc::vec::Vec<@T>, @T, @O>"
        ~extract_name:(Some "alloc::vec::Vec::IndexMutInst")
        ~filter:(Some [ true; true; false; true ])
        ();
      fmt "core::ops::deref::Deref<alloc::vec::Vec<@Self>>"
        ~extract_name:(Some "alloc.vec.DerefVec")
        ~filter:(Some [ true; false ])
        ();
      fmt "core::ops::deref::DerefMut<alloc::vec::Vec<@Self>>"
        ~extract_name:(Some "alloc.vec.DerefMutVec")
        ~filter:(Some [ true; false ])
        ();
      (* core::clone::impls::{core::clone::Clone for bool} *)
      fmt "core::clone::Clone<bool>"
        ~extract_name:(Some "core::clone::CloneBool") ();
    ]
  @ mk_lean_only lean_builtin_trait_impls
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
  (* PartialEq<INT, INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::cmp::PartialEq<" ^ ty ^ "," ^ ty ^ ">")
          ~extract_name:
            (Some ("core.cmp.PartialEq" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names
  (* Eq<INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::cmp::Eq<" ^ ty ^ ">")
          ~extract_name:
            (Some ("core.cmp.Eq" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names
  (* PartialOrd<INT, INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::cmp::PartialOrd<" ^ ty ^ "," ^ ty ^ ">")
          ~extract_name:
            (Some
               ("core.cmp.PartialOrd" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names
  (* Ord<INT> *)
  @ List.map
      (fun ty ->
        fmt
          ("core::cmp::Ord<" ^ ty ^ ">")
          ~extract_name:
            (Some ("core.cmp.Ord" ^ StringUtils.capitalize_first_letter ty))
          ())
      all_int_names
  (* Default<INT> *)
  @ List.map
      (fun ty -> fmt ("core::default::Default<" ^ ty ^ ">") ())
      all_int_names

let mk_builtin_trait_impls_map () =
  let m = NameMatcherMap.of_list (builtin_trait_impls_info ()) in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let builtin_trait_impls_map = mk_memoized mk_builtin_trait_impls_map

(** The builtin functions.

    The optional list of booleans is filtering information for the type
    parameters. For instance, in the case of the `Vec` functions, there is a
    type parameter for the allocator to use, which we want to filter. *)
let mk_builtin_funs () : (pattern * Pure.builtin_fun_info) list =
  (* Small utility. *)
  let mk_fun (rust_name : string) ?(filter : bool list option = None)
      ?(can_fail = true) ?(stateful = false) ?(lift = true)
      ?(extract_name : string option = None) () :
      pattern * Pure.builtin_fun_info =
    let rust_name =
      [%ldebug "About to parse pattern: " ^ rust_name];
      try
        let pat = parse_pattern rust_name in
        [%ldebug "Successfully parsed the pattern"];
        pat
      with Failure _ ->
        raise (Failure ("Could not parse pattern: " ^ rust_name))
    in
    let extract_name =
      match extract_name with
      | None -> pattern_to_fun_extract_name rust_name
      | Some name -> split_on_separator name
    in
    let basename = flatten_name extract_name in
    let f : Pure.builtin_fun_info =
      {
        filter_params = filter;
        extract_name = basename;
        can_fail;
        stateful;
        lift;
        has_default = false;
      }
    in
    (rust_name, f)
  in
  let mk_funs (rust_name : string -> string) (extract_name : string -> string)
      (funs : (bool * string) list) : (pattern * Pure.builtin_fun_info) list =
    List.map
      (fun (can_fail, name) ->
        let extract_name = Some (extract_name name) in
        mk_fun (rust_name name) ~can_fail ~extract_name ())
      funs
  in
  let mk_scalar_fun (rust_name : string -> string)
      (extract_name : string -> string) ?(can_fail = true) () :
      (pattern * Pure.builtin_fun_info) list =
    List.map
      (fun ty ->
        mk_fun (rust_name ty)
          ~extract_name:(Some (extract_name ty))
          ~can_fail ())
      all_int_names
  in
  let mk_scalar_funs (rust_name : string -> string -> string)
      (extract_name : string -> string -> string) (funs : (bool * string) list)
      : (pattern * Pure.builtin_fun_info) list =
    List.flatten
      (List.map
         (fun ty ->
           List.map
             (fun (can_fail, fun_name) ->
               mk_fun (rust_name ty fun_name)
                 ~extract_name:(Some (extract_name ty fun_name))
                 ~can_fail ())
             funs)
         all_int_names)
  in
  List.flatten
    (List.map
       (fun op ->
         mk_scalar_fun
           (fun ty -> "core::num::{" ^ ty ^ "}::checked_" ^ op)
           (fun ty -> StringUtils.capitalize_first_letter ty ^ ".checked_" ^ op)
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
  @ mk_funs
      (fun fn -> "core::clone::impls::{core::clone::Clone<bool>}::" ^ fn)
      (fun fn -> "core.clone.impls.CloneBool." ^ fn)
      [ (false, "clone"); (false, "clone_from") ]
  (* Clone<INT> *)
  @ mk_scalar_funs
      (fun ty fn ->
        "core::clone::impls::{core::clone::Clone<" ^ ty ^ ">}::" ^ fn)
      (fun ty fn ->
        "core.clone.impls.Clone"
        ^ StringUtils.capitalize_first_letter ty
        ^ "." ^ fn)
      [ (false, "clone"); (false, "clone_from") ]
  (* Definitions not for Lean *)
  @ mk_not_lean
      [
        mk_fun "core::mem::replace" ~can_fail:false ~lift:false ();
        mk_fun "core::mem::take" ~can_fail:false ~lift:false ();
        mk_fun "core::option::{core::option::Option<@T>}::unwrap"
          ~extract_name:(Some "core.option.Option.unwrap") ();
        mk_fun
          "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"
          ~extract_name:(Some "core.slice.index.Slice.index") ();
        mk_fun
          "core::slice::index::{core::ops::index::IndexMut<[@T], @I, \
           @O>}::index_mut"
          ~extract_name:(Some "core.slice.index.Slice.index_mut") ();
        mk_fun "core::slice::{[@T]}::get"
          ~extract_name:(Some "core.slice.Slice.get") ();
        mk_fun "core::slice::{[@T]}::get_mut"
          ~extract_name:(Some "core.slice.Slice.get_mut") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::get"
          ~extract_name:
            (Some "core::slice::index::SliceIndexRangeUsizeSlice::get") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::get_mut"
          ~extract_name:
            (Some "core::slice::index::SliceIndexRangeUsizeSlice::get_mut") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::index"
          ~extract_name:
            (Some "core::slice::index::SliceIndexRangeUsizeSlice::index") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::index_mut"
          ~extract_name:
            (Some "core::slice::index::SliceIndexRangeUsizeSlice::index_mut") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::get_unchecked"
          ~extract_name:
            (Some "core::slice::index::SliceIndexRangeUsizeSlice::get_unchecked")
          ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, \
           [@T], [@T]>}::get_unchecked_mut"
          ~extract_name:
            (Some
               "core::slice::index::SliceIndexRangeUsizeSlice::get_unchecked_mut")
          ();
        mk_fun
          "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, \
           @O>}::index"
          ~extract_name:(Some "alloc.vec.Vec.index")
          ~filter:(Some [ true; true; false; true ])
          ();
        mk_fun
          "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
           @O>}::index_mut"
          ~extract_name:(Some "alloc.vec.Vec.index_mut")
          ~filter:(Some [ true; true; false; true ])
          ();
        mk_fun "core::slice::{[@T]}::len" ~extract_name:(Some "slice::len")
          ~can_fail:false ~lift:false ();
        mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::new"
          ~extract_name:(Some "alloc::vec::Vec::new") ~can_fail:false
          ~lift:false ();
        mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::push"
          ~filter:(Some [ true; false ])
          ();
        mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::insert"
          ~filter:(Some [ true; false ])
          ();
        mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::len"
          ~filter:(Some [ true; false ])
          ~can_fail:false ~lift:false ();
        mk_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref"
          ~can_fail:false ~extract_name:(Some "alloc.boxed.Box.deref")
          ~filter:(Some [ true; false ])
          ();
        mk_fun
          "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut"
          ~can_fail:false ~extract_name:(Some "alloc.boxed.Box.deref_mut")
          ~filter:(Some [ true; false ])
          ();
        mk_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"
          ~extract_name:(Some "core.array.Array.index") ();
        mk_fun
          "core::array::{core::ops::index::IndexMut<[@T; @N], @I, \
           @O>}::index_mut"
          ~extract_name:(Some "core.array.Array.index_mut") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::get"
          ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::get_mut"
          ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::get_unchecked"
          ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::get_unchecked_mut"
          ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::index"
          ~extract_name:(Some "core_slice_index_Slice_index") ();
        mk_fun
          "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], \
           @T>}::index_mut"
          ~extract_name:(Some "core_slice_index_Slice_index_mut") ();
        mk_fun "alloc::slice::{[@T]}::to_vec"
          ~extract_name:(Some "alloc.slice.Slice.to_vec") ();
        mk_fun "alloc::vec::{alloc::vec::Vec<@T>}::with_capacity"
          ~extract_name:(Some "alloc.vec.Vec.with_capacity") ~can_fail:false
          ~lift:false ();
        mk_fun "core::slice::{[@T]}::reverse"
          ~extract_name:(Some "core.slice.Slice.reverse") ~can_fail:false ();
        mk_fun
          "alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T>, \
           [@T]>}::deref"
          ~extract_name:(Some "alloc::vec::Vec::deref")
          ~filter:(Some [ true; false ])
          ~can_fail:false ~lift:false ();
        mk_fun
          "alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T>, \
           [@T]>}::deref_mut"
          ~extract_name:(Some "alloc::vec::Vec::deref_mut") ~can_fail:false
          ~filter:(Some [ true; false ])
          ();
      ]
  (* Lean-only definitions *)
  @ mk_lean_only
      ((* PartialEq, Eq, PartialOrd, Ord *)
       mk_scalar_funs
         (fun ty fun_name ->
           "core::cmp::impls::{core::cmp::PartialEq<" ^ ty ^ "," ^ ty ^ ">}::"
           ^ fun_name)
         (fun ty fun_name ->
           "core.cmp.impls.PartialEq"
           ^ StringUtils.capitalize_first_letter ty
           ^ "." ^ fun_name)
         [ (false, "eq"); (false, "ne") ]
      (* Eq: no methods *)
      (* PartialOrd *)
      @ mk_scalar_funs
          (fun ty fun_name ->
            "core::cmp::impls::{core::cmp::PartialOrd<" ^ ty ^ "," ^ ty ^ ">}::"
            ^ fun_name)
          (fun ty fun_name ->
            "core.cmp.impls.PartialCmp"
            ^ StringUtils.capitalize_first_letter ty
            ^ "." ^ fun_name)
          [
            (false, "partial_cmp");
            (false, "lt");
            (false, "le");
            (false, "gt");
            (false, "ge");
          ]
      (* Ord *)
      @ mk_scalar_fun
          (fun ty ->
            "core::default::{core::default::Default<" ^ ty ^ ">}::default")
          (fun ty ->
            "core.default.Default"
            ^ StringUtils.capitalize_first_letter ty
            ^ ".default")
          ~can_fail:false ()
      (* Default::default *)
      @ mk_scalar_funs
          (fun ty fun_name ->
            "core::cmp::impls::{core::cmp::Ord<" ^ ty ^ ">}::" ^ fun_name)
          (fun ty fun_name ->
            "core.cmp.impls.Ord"
            ^ StringUtils.capitalize_first_letter ty
            ^ "." ^ fun_name)
          [ (false, "cmp"); (false, "max"); (false, "min"); (true, "clamp") ]
      (* Binops *)
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
                   (false, "wrapping_mul");
                   (false, "overflowing_add");
                   (false, "rotate_left");
                   (false, "rotate_right");
                 ])
             all_int_names)
      @ lean_builtin_funs)

let builtin_funs : unit -> (pattern * Pure.builtin_fun_info) list =
  (* We need to take into account the default trait methods *)
  let mk () =
    let funs = mk_builtin_funs () in
    let trait_decls = builtin_trait_decls_info () in
    let default_methods =
      List.map
        (fun (d : Pure.builtin_trait_decl_info) ->
          List.filter_map
            (fun ((fpat, f) : string * Pure.builtin_fun_info) ->
              if f.has_default then
                let sep =
                  match backend () with
                  | Lean -> "."
                  | _ -> "_"
                in
                let pattern = d.rust_name @ [ PIdent (fpat, 0, []) ] in
                let info =
                  {
                    f with
                    extract_name =
                      d.extract_name ^ sep ^ f.extract_name ^ sep ^ "default";
                  }
                in
                Some (pattern, info)
              else None)
            d.methods)
        trait_decls
    in
    funs @ List.concat default_methods
  in
  mk_memoized mk

let name_matcher_map_of_list (ls : (pattern * 'a) list) : 'a NameMatcherMap.t =
  let config : print_config = { tgt = TkPattern } in
  List.fold_left
    (fun m (pat, info) ->
      [%ldebug "About to add pattern: " ^ pattern_to_string config pat];
      (* [replace] inserts and checks whether we replaced a pattern *)
      let m, old = NameMatcherMap.replace pat info m in
      [%cassert_opt_span] None (old = None)
        ("Pattern registered twice for a builtin definition: "
        ^ pattern_to_string config pat);
      m)
    NameMatcherMap.empty ls

let mk_builtin_funs_map () =
  [%ldebug "Builting the builtin funs map"];
  let m =
    name_matcher_map_of_list
      (List.map (fun (name, info) -> (name, info)) (builtin_funs ()))
  in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let builtin_funs_map = mk_memoized mk_builtin_funs_map

type effect_info = { can_fail : bool }

let mk_builtin_fun_effects () : (pattern * effect_info) list =
  let builtin_funs : (pattern * Pure.builtin_fun_info) list = builtin_funs () in
  List.map
    (fun ((pattern, info) : _ * Pure.builtin_fun_info) ->
      let info = { can_fail = info.can_fail } in
      (pattern, info))
    builtin_funs

let mk_builtin_fun_effects_map () =
  [%ldebug "Builting the builtin funs effects map"];
  name_matcher_map_of_list (if_backend mk_builtin_fun_effects [])

let builtin_fun_effects_map = mk_memoized mk_builtin_fun_effects_map
