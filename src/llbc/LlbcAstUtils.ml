open Types
open LlbcAst
include Charon.LlbcAstUtils

let body_as_body = Charon.LlbcAstUtils.body_as_structured

let body_as_body_exn file line f =
  match body_as_body f with
  | Some body -> body
  | None -> Errors.craise_opt_span file line None "Not a LLBC body"

let body_is_known (b : body) : bool = Option.is_some (body_as_body b)

let body_as_target_dispatch (b : body) :
    (string * Types.fun_decl_ref) list option =
  match b with
  | TargetDispatchBody targets -> Some targets
  | _ -> None

let body_is_target_dispatch (b : body) : bool =
  Option.is_some (body_as_target_dispatch b)

(** A function body is translatable if it is either a structured body (normal
    case) or a target dispatch body (multi-target). *)
let body_is_translatable (b : body) : bool =
  body_is_known b || body_is_target_dispatch b

let fun_decl_global_initializer (f : fun_decl) : global_decl_ref option =
  match f.src with
  | GlobalInitializerFun global -> Some global
  | _ -> None

let fun_decl_is_global_initializer (f : fun_decl) : bool =
  Option.is_some (fun_decl_global_initializer f)

(** Is a global an anonymous constant (i.e., a promoted constant)? *)
let global_decl_is_anon_const (g : global_decl) : bool =
  match g.global_kind with
  | AnonConst -> true
  | _ -> false

(** Is a function the initializer of an anonymous constant (i.e., a promoted
    constant)? *)
let fun_decl_is_anon_const_initializer
    (global_decls : global_decl GlobalDeclId.Map.t) (f : fun_decl) : bool =
  match f.src with
  | GlobalInitializerFun gref -> (
      match GlobalDeclId.Map.find_opt gref.id global_decls with
      | Some g -> global_decl_is_anon_const g
      | None -> false)
  | _ -> false

(** Return the opaque declarations found in the crate, which are also *not
    builtin*.

    [filter_builtin]: if [true], do not consider as opaque the external
    definitions that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global
    bodies. *)
let crate_get_opaque_non_builtin_decls (k : crate) (filter_builtin : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  let is_opaque_fun (d : fun_decl) : bool =
    (not (body_is_known d.body))
    && ((not filter_builtin)
       || (not
             (NameMatcherMap.mem ctx d.item_meta.name (builtin_globals_map ())))
          && not (NameMatcherMap.mem ctx d.item_meta.name (builtin_funs_map ()))
       )
  in
  let is_opaque_type (d : type_decl) : bool =
    d.kind = Opaque
    && ((not filter_builtin)
       || not (NameMatcherMap.mem ctx d.item_meta.name (builtin_types_map ())))
  in
  (* Note that by checking the function bodies we also the globals *)
  ( List.filter is_opaque_type (TypeDeclId.Map.values type_decls),
    List.filter is_opaque_fun (FunDeclId.Map.values fun_decls) )

(** Return true if the crate contains opaque declarations, ignoring the builtin
    definitions. *)
let crate_has_opaque_non_builtin_decls (k : crate) (filter_builtin : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : bool =
  crate_get_opaque_non_builtin_decls k filter_builtin type_decls fun_decls
  <> ([], [])

(** Decides whether an item is a builtin, i.e. one that Aeneas has a model for,
    so that we don't extract it.

    This is figured out by looking in the [ExtractBuiltin] map for its kind. We
    do not use {!crate_get_opaque_non_builtin_decls} because it only looks at
    types and functions (missing globals, trait decls, and trait impls).

    The type declarations Charon introduces for the builtin types (tuples,
    [Box], [str]) are builtin too: like {!Interp.compute_contexts}, we recognize
    them by their [BuiltinType] source. *)
let item_is_builtin (k : crate) : item_id -> bool =
  let open ExtractBuiltin in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  fun (id : item_id) : bool ->
    (* Whether the item's name is in the given builtin map. *)
    let name_in map =
      match crate_get_item_meta k id with
      | None -> false
      | Some meta -> NameMatcherMap.mem ctx meta.name (map ())
    in
    match id with
    | IdType tid -> (
        match TypeDeclId.Map.find_opt tid k.type_decls with
        | Some { src = BuiltinType _; _ } -> true
        | _ -> name_in builtin_types_map)
    | IdFun _ ->
        (* A global's initializer function has the same name as the global, so
           the initializer of a builtin global is builtin too. *)
        name_in builtin_funs_map || name_in builtin_globals_map
    | IdGlobal _ -> name_in builtin_globals_map
    | IdTraitDecl _ -> name_in builtin_trait_decls_map
    | IdTraitImpl iid -> (
        match TraitImplId.Map.find_opt iid k.trait_impls with
        | None -> false
        | Some d -> (
            match TraitDeclId.Map.find_opt d.impl_trait.id k.trait_decls with
            | None -> false
            | Some trait_decl ->
                Option.is_some
                  (NameMatcherMap.find_with_generics_opt ctx
                     trait_decl.item_meta.name d.impl_trait.generics
                     (builtin_trait_impls_map ()))))

(** Whether an item is opaque, i.e. extracted as an axiom. An item whose
    declaration can't be found is not opaque.

    We look at the declaration itself rather than at [item_meta.opacity]: all
    the ways of making an item opaque ([extern] blocks, [--opaque] patterns,
    foreign items) end up as a missing body or field list, and that is also what
    the emitter looks at when it decides to emit an axiom. *)
let item_is_opaque (k : crate) (id : item_id) : bool =
  (* A function is opaque if its body can't be translated. A multi-target
     dispatch body counts as translatable, as in the translation itself (see
     {!body_is_translatable}). *)
  let fun_is_opaque (fid : FunDeclId.id) : bool =
    match FunDeclId.Map.find_opt fid k.fun_decls with
    | None -> false
    | Some d -> not (body_is_translatable d.body)
  in
  match id with
  | IdType tid -> (
      (* A type is opaque if its fields or variants were not translated. *)
      match TypeDeclId.Map.find_opt tid k.type_decls with
      | None -> false
      | Some d -> TypesUtils.type_decl_is_opaque d)
  | IdFun fid -> fun_is_opaque fid
  | IdGlobal gid -> (
      (* A global's value is computed by its initializer function, so the global
         is opaque if that function is. *)
      match GlobalDeclId.Map.find_opt gid k.global_decls with
      | None -> false
      | Some d -> (
          match init_fun_id_of_global d with
          | None -> false
          | Some fid -> fun_is_opaque fid))
  | IdTraitDecl _ | IdTraitImpl _ ->
      (* Charon ignores opacity annotations on trait declarations and
         implementations, so they are never opaque. *)
      false

(** Strip trailing [PeTarget] elements from a name.

    Multi-target extraction appends [PeTarget] to per-target function names.
    This element doesn't participate in pattern matching (the pattern generator
    skips it), so we strip it before calling [name_to_pattern] to avoid
    triggering its roundtrip assertion. *)
let strip_target_suffix (n : name) : name =
  match List.rev n with
  | Types.PeTarget _ :: rest -> List.rev rest
  | _ -> n

let strip_target_or_instantiated_suffix (n : name) : name =
  let rec strip_all (n : name) : name =
    match n with
    | (PeTarget _ | PeInstantiated _) :: rest -> strip_all rest
    | _ -> List.rev n
  in
  strip_all (List.rev n)

(** Extract and strip any trailing [PeTarget] element from a name, returning the
    cleaned name and an optional target suffix string (with [-] replaced by
    [_]). *)
let extract_target_suffix (name : name) : name * string option =
  match Collections.List.last name with
  | PeTarget target ->
      let target = String.concat "_" (String.split_on_char '-' target) in
      (Collections.List.prefix (List.length name - 1) name, Some target)
  | _ -> (name, None)

let add_target_suffix (name : name) (target_suffix : string option) : name =
  match target_suffix with
  | None -> name
  | Some target -> name @ [ PeTarget target ]

let name_to_pattern (span : Meta.span option) (ctx : Charon.NameMatcher.ctx)
    (c : Charon.NameMatcher.to_pat_config) (n : name) =
  let n = strip_target_suffix n in
  if !Config.fail_hard then Charon.NameMatcher.name_to_pattern ctx c n
  else
    try Charon.NameMatcher.name_to_pattern ctx c n
    with Not_found | Assert_failure _ ->
      [%craise_opt_span] span "Could not convert the name to a pattern"

let name_with_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (n : Types.name) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    {
      tgt = TkPattern;
      use_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  let pat = name_to_pattern span mctx c n in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let name_with_generics_to_pattern (span : Meta.span option)
    (ctx : Charon.NameMatcher.ctx) (c : Charon.NameMatcher.to_pat_config)
    (params : generic_params) (n : Charon.Types.name) (args : generic_args) =
  if !Config.fail_hard then
    Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
  else
    try Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
    with Not_found | Assert_failure _ ->
      [%craise_opt_span] span "Could not convert the name to a pattern"

let name_with_generics_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (n : Types.name) (params : Types.generic_params)
    (args : Types.generic_args) : string =
  let mctx = Charon.NameMatcher.ctx_from_crate crate in
  let c : Charon.NameMatcher.to_pat_config =
    {
      tgt = TkPattern;
      use_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  let pat = name_with_generics_to_pattern span mctx c params n args in
  Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat

let trait_impl_with_crate_to_pattern_string (span : Meta.span option)
    (crate : LlbcAst.crate) (trait_decl : LlbcAst.trait_decl)
    (trait_impl : LlbcAst.trait_impl) : string =
  name_with_generics_crate_to_pattern_string span crate
    trait_decl.item_meta.name trait_decl.generics trait_impl.impl_trait.generics

(** Return true if the statement contains an instruction which breaks the
    control flow, at the exception of panics (that is: a break, a continue or a
    return) *)
let statement_has_break_continue_return (st : statement) : bool =
  let visitor =
    object
      inherit [_] iter_statement
      method! visit_Break _ _ = raise Utils.Found
      method! visit_Continue _ _ = raise Utils.Found
      method! visit_Return _ = raise Utils.Found
    end
  in
  try
    visitor#visit_statement () st;
    false
  with Utils.Found -> true

(** Return true if the block contains a statement which breaks the control flow,
    at the exception of panics (that is: a break, a continue or a return) *)
let block_has_break_continue_return (st : block) : bool =
  let visitor =
    object
      inherit [_] iter_statement
      method! visit_Break _ _ = raise Utils.Found
      method! visit_Continue _ _ = raise Utils.Found
      method! visit_Return _ = raise Utils.Found
    end
  in
  try
    visitor#visit_block () st;
    false
  with Utils.Found -> true

(** Compute the size of a function body - we count the number of statements and
    blocks *)
let compute_body_size (b : body) : int =
  let size = ref 0 in
  let incr () = size := !size + 1 in
  let visitor =
    object
      inherit [_] iter_statement as super

      method! visit_statement env st =
        incr ();
        super#visit_statement env st

      method! visit_block env st =
        incr ();
        super#visit_block env st
    end
  in
  let () =
    match b with
    | StructuredBody body -> visitor#visit_block () body.body
    | _ -> ()
  in
  !size

(** Compute the size of a function - we count the number of statements and
    blocks *)
let compute_fun_decl_size (f : fun_decl) : int = compute_body_size f.body
