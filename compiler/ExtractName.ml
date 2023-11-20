(** Utilities for extracting names *)

open Charon.NameMatcher

module NameMatcherMap = struct
  type 'a t = (pattern * 'a) list

  let config = { map_vars_to_vars = true }

  let find_opt (ctx : ctx) (name : Types.name) (m : 'a t) : 'a option =
    match List.find_opt (fun (pat, _) -> match_name ctx config pat name) m with
    | None -> None
    | Some (_, v) -> Some v

  let find_with_generics_opt (ctx : ctx) (name : Types.name)
      (g : Types.generic_args) (m : 'a t) : 'a option =
    match
      List.find_opt
        (fun (pat, _) -> match_name_with_generics ctx config pat name g)
        m
    with
    | None -> None
    | Some (_, v) -> Some v

  let mem (ctx : ctx) (name : Types.name) (m : 'a t) : bool =
    find_opt ctx name m <> None

  let of_list (ls : (pattern * 'a) list) : 'a t = ls
end

(** Helper to convert name patterns to names for extraction.

    For impl blocks, we simply use the name of the type (without its arguments)
    if all the arguments are variables.
 *)
let pattern_to_extract_name (is_trait_impl : bool) (name : pattern) :
    string list =
  let c = { tgt_kind = TkName } in
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
        | ERef _ | EVar _ -> raise (Failure ""))
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

let pattern_to_fun_extract_name = pattern_to_extract_name false
let pattern_to_trait_impl_extract_name = pattern_to_extract_name true

(* TODO: this is provisional. We just want to make sure that the extraction
   names we derive from the patterns (for the builtin definitions) are
   consistent with the extraction names we derive from the Rust names *)
let name_to_simple_name (ctx : ctx) (n : Types.name) : string list =
  pattern_to_extract_name false (name_to_pattern ctx n)

let name_with_generics_to_simple_name (ctx : ctx) (n : Types.name)
    (p : Types.generic_params) (g : Types.generic_args) : string list =
  pattern_to_extract_name true (name_with_generics_to_pattern ctx n p g)

(*
  (* Prepare a name.
     The first id elem is always the crate: if it is the local crate,
     we remove it. We ignore disambiguators (there may be collisions, but we
     check if there are).
  *)
  let rec name_to_simple_name (name : llbc_name) : string list =
    (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
    match name with
    | (PeIdent (crate, _) as id) :: name ->
        let name = if crate = crate_name then name else id :: name in
        let open Types in
        let name =
          List.map
            (function
              | PeIdent (s, _) -> s
              | PeImpl impl -> impl_elem_to_simple_name impl)
            name
        in
        name
    | _ ->
        raise
          (Failure
             ("Unexpected name shape: " ^ TranslateCore.name_to_string ctx name))
  and impl_elem_to_simple_name (impl : Types.impl_elem) : string =
    (* We do something simple for now.
       TODO: we might want to do something different for impl elements which are
       actually trait implementations, in order to prevent name collisions (it
       is possible to define several times the same trait for the same type,
       but with different instantiations of the type, or different trait
       requirements *)
    ty_to_simple_name impl.generics impl.ty
  and ty_to_simple_name (generics : Types.generic_params) (ty : Types.ty) :
      string =
    (* We do something simple for now.
       TODO: find a more principled way of converting types to names.
       In particular, we might want to do something different for impl elements which are
       actually trait implementations, in order to prevent name collisions (it
       is possible to define several times the same trait for the same type,
       but with different instantiations of the type, or different trait
       requirements *)
    match ty with
    | TAdt (id, args) -> (
        match id with
        | TAdtId id ->
            let def = TypeDeclId.Map.find id ctx.type_ctx.type_decls in
            name_last_elem_as_ident def.name
        | TTuple ->
            (* TODO *)
            "Tuple"
            ^ String.concat ""
                (List.map (ty_to_simple_name generics) args.types)
        | TAssumed id -> (
            match id with
            | Types.TBox -> "Box"
            | Types.TArray -> "Array"
            | Types.TSlice -> "Slice"
            | Types.TStr -> "Str"))
    | TVar vid ->
        (* Use the variable name *)
        (List.find (fun (v : type_var) -> v.index = vid) generics.types).name
    | TLiteral lty ->
        StringUtils.capitalize_first_letter
          (Print.Types.literal_type_to_string lty)
    | TNever -> raise (Failure "Unreachable")
    | TRef (_, rty, rk) -> (
        let rty = ty_to_simple_name generics rty in
        match rk with
        | RMut -> "MutBorrow" ^ rty
        | RShared -> "SharedBorrow" ^ rty)
    | TRawPtr (rty, rk) -> (
        let rty = ty_to_simple_name generics rty in
        match rk with RMut -> "MutPtr" ^ rty | RShared -> "ConstPtr" ^ rty)
    | TTraitType (tr, _, name) ->
        (* TODO: this is way too simple *)
        let trait_decl =
          TraitDeclId.Map.find tr.trait_decl_ref.trait_decl_id
            ctx.trait_decls_ctx.trait_decls
        in
        name_last_elem_as_ident trait_decl.name ^ name
    | TArrow (inputs, output) ->
        "Arrow"
        ^ String.concat ""
            (List.map (ty_to_simple_name generics) (inputs @ [ output ]))
  in
*)
