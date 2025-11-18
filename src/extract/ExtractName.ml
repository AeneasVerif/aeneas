(** Utilities for extracting names *)

open Charon.NameMatcher

let log = Logging.extract_log
let match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs

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

let literal_type_names = "bool" :: "str" :: all_int_names
let literal_type_nameset = Collections.StringSet.of_list literal_type_names

module NameMatcherMap = struct
  module NMM = NameMatcherMap

  type 'a t = 'a NMM.t

  let config = { map_vars_to_vars = true; match_with_trait_decl_refs }
  let empty = NMM.empty

  let find_opt (ctx : 'stt ctx) (name : Types.name) (m : 'a t) : 'a option =
    NMM.find_opt ctx config name m

  let find_with_generics_opt (ctx : 'stt ctx) (name : Types.name)
      (g : Types.generic_args) (m : 'a t) : 'a option =
    NMM.find_with_generics_opt ctx config name g m

  let mem (ctx : 'stt ctx) (name : Types.name) (m : 'a t) : bool =
    NMM.mem ctx config name m

  let of_list (ls : (pattern * 'a) list) : 'a t = NMM.of_list ls
  let add = NMM.add
  let replace = NMM.replace
  let to_string = NMM.to_string
end

(** Helper to convert name patterns to names for extraction.

    For impl blocks, we simply use the name of the type (without its arguments)
    if all the arguments are variables. *)
let pattern_to_extract_name (_span : Meta.span option) (name : pattern) :
    string list =
  let c = { tgt = TkName } in
  let all_vars =
    let check (g : generic_arg) : bool =
      match g with
      | GExpr (EVar _) | GRegion (RVar _) -> true
      | _ -> false
    in
    List.for_all check
  in

  (* This is a bit of a hack: we want to simplify some names.
     We explore the pattern and replace such occurrences with a specific name.
  *)
  let simplify_name (id : pattern) =
    match id with
    | [
     PIdent ("core", _, []); PIdent ("option", _, []); PIdent ("Option", _, g);
    ] ->
        (* Option *)
        [ PIdent ("Option", 0, g) ]
    | [ PIdent (id, _, []) ]
      when Collections.StringSet.mem id literal_type_nameset ->
        (* Literals: we want to capitalize the first letter *)
        [ PIdent (StringUtils.capitalize_first_letter id, 0, []) ]
    | _ -> id
  in
  let visitor =
    object
      inherit [_] map_pattern as super

      method! visit_PIdent _ s d g =
        if all_vars g then super#visit_PIdent () s d []
        else super#visit_PIdent () s d g

      method! visit_EComp _ id =
        (* Simplify if this is [Option] *)
        super#visit_EComp () (simplify_name id)

      method! visit_PImpl _ ty =
        match ty with
        | EComp id ->
            (* Only keep the last ident *)
            let id = Collections.List.last id in
            super#visit_PImpl () (EComp [ id ])
        | _ -> super#visit_PImpl () ty

      method! visit_EPrimAdt _ adt g =
        if all_vars g then
          match adt with
          | TTuple ->
              let l = List.length g in
              if l = 2 then EComp [ PIdent ("Pair", 0, []) ]
              else super#visit_EPrimAdt () adt g
          | TArray -> EComp [ PIdent ("Array", 0, []) ]
          | TSlice -> EComp [ PIdent ("Slice", 0, []) ]
        else if adt = TTuple && List.length g = 2 then
          super#visit_EComp () [ PIdent ("Pair", 0, g) ]
        else super#visit_EPrimAdt () adt g
    end
  in
  let name = visitor#visit_pattern () name in
  List.map (pattern_elem_to_string c) name

let pattern_to_type_extract_name = pattern_to_extract_name None
let pattern_to_fun_extract_name = pattern_to_extract_name None
let pattern_to_trait_impl_extract_name = pattern_to_extract_name None

(* TODO: this is provisional. We just want to make sure that the extraction
   names we derive from the patterns (for the builtin definitions) are
   consistent with the extraction names we derive from the Rust names *)
let name_to_simple_name (ctx : 'stt ctx) (n : Types.name) : string list =
  let c : to_pat_config =
    { tgt = TkName; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  pattern_to_extract_name None (name_to_pattern ctx c n)

(** If the [prefix] is Some, we attempt to remove the common prefix between
    [prefix] and [name] from [name] *)
let name_with_generics_to_simple_name (ctx : 'stt ctx)
    ?(prefix : Types.name option = None) (name : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let c : to_pat_config =
    { tgt = TkName; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  let name = name_with_generics_to_pattern ctx c p name g in
  let name =
    match prefix with
    | None -> name
    | Some prefix ->
        let prefix =
          name_with_generics_to_pattern ctx c TypesUtils.empty_generic_params
            prefix TypesUtils.empty_generic_args
        in
        let _, _, name = pattern_common_prefix { equiv = true } prefix name in
        name
  in
  pattern_to_extract_name None name
