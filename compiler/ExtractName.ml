(** Utilities for extracting names *)

open Charon.NameMatcher

let log = Logging.extract_log
let match_with_trait_decl_refs = true

module NameMatcherMap = struct
  module NMM = NameMatcherMap

  type 'a t = 'a NMM.t

  let config = { map_vars_to_vars = true; match_with_trait_decl_refs }

  let find_opt (ctx : ctx) (name : Types.name) (m : 'a t) : 'a option =
    NMM.find_opt ctx config name m

  let find_with_generics_opt (ctx : ctx) (name : Types.name)
      (g : Types.generic_args) (m : 'a t) : 'a option =
    NMM.find_with_generics_opt ctx config name g m

  let mem (ctx : ctx) (name : Types.name) (m : 'a t) : bool =
    NMM.mem ctx config name m

  let of_list (ls : (pattern * 'a) list) : 'a t = NMM.of_list ls
  let to_string = NMM.to_string
end

(** Helper to convert name patterns to names for extraction.

    For impl blocks, we simply use the name of the type (without its arguments)
    if all the arguments are variables.
 *)
let pattern_to_extract_name (name : pattern) : string list =
  let c = { tgt = TkName } in
  let is_var (g : generic_arg) : bool =
    match g with
    | GExpr (EVar _) -> true
    | GRegion (RVar _) -> true
    | _ -> false
  in
  let all_distinct_vars = List.for_all is_var in

  (* This is a bit of a hack: we want to simplify the occurrences of
     tuples of two variables, arrays with only variables, slices with
     only variables, etc.
     We explore the pattern and replace such occurrences with a specific name.
  *)
  let visitor =
    object
      inherit [_] map_pattern as super

      method! visit_PImpl _ ty =
        (* TODO: Option *)
        match ty with
        | EComp id -> (
            (* Retrieve the last ident *)
            let id = Collections.List.last id in
            match id with
            | PIdent (s, g) as id ->
                if all_distinct_vars g then PImpl (EComp [ PIdent (s, []) ])
                else super#visit_PImpl () (EComp [ id ])
            | PImpl _ -> raise (Failure "Unreachable"))
        | _ -> super#visit_PImpl () ty

      method! visit_EPrimAdt _ adt g =
        if all_distinct_vars g then
          match adt with
          | TTuple ->
              let l = List.length g in
              if l = 2 then EComp [ PIdent ("Pair", []) ]
              else super#visit_EPrimAdt () adt g
          | TArray -> EComp [ PIdent ("Array", []) ]
          | TSlice -> EComp [ PIdent ("Slice", []) ]
          (*else if adt = TTuple && List.length g = 2 then
            super#visit_EComp () [ PIdent ("Pair", g) ]*)
        else super#visit_EPrimAdt () adt g
    end
  in
  let name = visitor#visit_pattern () name in
  List.map (pattern_elem_to_string c) name

let pattern_to_type_extract_name = pattern_to_extract_name
let pattern_to_fun_extract_name = pattern_to_extract_name
let pattern_to_trait_impl_extract_name = pattern_to_extract_name

(* TODO: this is provisional. We just want to make sure that the extraction
   names we derive from the patterns (for the builtin definitions) are
   consistent with the extraction names we derive from the Rust names *)
let name_to_simple_name (ctx : ctx) (n : Types.name) : string list =
  let c : to_pat_config =
    { tgt = TkName; use_trait_decl_refs = match_with_trait_decl_refs }
  in
  pattern_to_extract_name (name_to_pattern ctx c n)

(** If the [prefix] is Some, we attempt to remove the common prefix
    between [prefix] and [name] from [name] *)
let name_with_generics_to_simple_name (ctx : ctx)
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
  pattern_to_extract_name name
