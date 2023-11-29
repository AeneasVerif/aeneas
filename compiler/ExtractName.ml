(** Utilities for extracting names *)

open Charon.NameMatcher

let log = Logging.extract_log

module NameMatcherMap = struct
  module NMM = NameMatcherMap

  type 'a t = 'a NMM.t

  let config = { map_vars_to_vars = true }

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
let pattern_to_extract_name (is_trait_impl : bool) (name : pattern) :
    string list =
  let c = { tgt = TkName } in
  let is_var (g : generic_arg) : bool =
    match g with
    | GExpr (EVar _) -> true
    | GRegion (RVar _) -> true
    | _ -> false
  in
  let all_vars = List.for_all is_var in
  let elem_to_string (e : pattern_elem) : string =
    match e with
    | PIdent _ -> pattern_elem_to_string c e
    | PImpl ty -> (
        match ty with
        | EComp id -> (
            (* Retrieve the last ident *)
            let id = Collections.List.last id in
            match id with
            | PIdent (s, g) ->
                if all_vars g then s else pattern_elem_to_string c id
            | PImpl _ -> raise (Failure "Unreachable"))
        | EPrimAdt (adt, g) ->
            if all_vars g then
              match adt with
              | TTuple ->
                  let l = List.length g in
                  if l = 2 then "Pair" else expr_to_string c ty
              | TArray -> "Array"
              | TSlice -> "Slice"
            else expr_to_string c ty
        | ERef _ | EVar _ ->
            (* We simply convert the pattern to a string. This is not very
               satisfying but we should rarely get there. *)
            expr_to_string c ty)
  in
  let rec pattern_to_string (n : pattern) : string list =
    match n with
    | [] -> raise (Failure "Unreachable")
    | [ e ] ->
        let e = elem_to_string e in
        if is_trait_impl then [ e ^ "Inst" ] else [ e ]
    | e :: n -> elem_to_string e :: pattern_to_string n
  in
  pattern_to_string name

let pattern_to_type_extract_name = pattern_to_extract_name false
let pattern_to_fun_extract_name = pattern_to_extract_name false
let pattern_to_trait_impl_extract_name = pattern_to_extract_name true

(* TODO: this is provisional. We just want to make sure that the extraction
   names we derive from the patterns (for the builtin definitions) are
   consistent with the extraction names we derive from the Rust names *)
let name_to_simple_name (ctx : ctx) (is_trait_impl : bool) (n : Types.name) :
    string list =
  let c : to_pat_config = { tgt = TkName } in
  pattern_to_extract_name is_trait_impl (name_to_pattern ctx c n)

(** If the [prefix] is Some, we attempt to remove the common prefix
    between [prefix] and [name] from [name] *)
let name_with_generics_to_simple_name (ctx : ctx) (is_trait_impl : bool)
    ?(prefix : Types.name option = None) (name : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  let c : to_pat_config = { tgt = TkName } in
  let name = name_with_generics_to_pattern ctx c name p g in
  let name =
    match prefix with
    | None -> name
    | Some prefix ->
        let prefix =
          name_with_generics_to_pattern ctx c prefix
            TypesUtils.empty_generic_params TypesUtils.empty_generic_args
        in
        let _, _, name = pattern_common_prefix prefix name in
        name
  in
  pattern_to_extract_name is_trait_impl name
