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
    external*.

    [filter_external]: if [true], do not consider as opaque the external
    definitions, which we map to models (shipped, or from [-external-names]).

    Remark: the list of functions also contains the list of opaque global
    bodies. *)
let crate_get_opaque_non_external_decls (k : crate) (filter_external : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : type_decl list * fun_decl list =
  let open ExtractName in
  let open ExternalNames in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  let is_opaque_fun (d : fun_decl) : bool =
    (not (body_is_known d.body))
    && ((not filter_external)
       || (not
             (NameMatcherMap.mem ctx d.item_meta.name (external_globals_map ())))
          && not
               (NameMatcherMap.mem ctx d.item_meta.name (external_funs_map ()))
       )
  in
  let is_opaque_type (d : type_decl) : bool =
    d.kind = Opaque
    && ((not filter_external)
       || not (NameMatcherMap.mem ctx d.item_meta.name (external_types_map ()))
       )
  in
  (* Note that by checking the function bodies we also the globals *)
  ( List.filter is_opaque_type (TypeDeclId.Map.values type_decls),
    List.filter is_opaque_fun (FunDeclId.Map.values fun_decls) )

(** Return true if the crate contains opaque declarations, ignoring the external
    definitions. *)
let crate_has_opaque_non_external_decls (k : crate) (filter_external : bool)
    (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : bool =
  crate_get_opaque_non_external_decls k filter_external type_decls fun_decls
  <> ([], [])

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

(** The error for a definition which is mapped to an external name
    ([extract_name], the model it is mapped to), if it should not be: a model
    may only replace a missing body.

    [opaque] is [Some b] for the definitions which have a body or not
    (functions, globals, types: [b] is [true] if there is none), and [None] for
    the ones which do not (traits and trait impls). [foreign_too] also refuses
    the definitions of other crates which have a body: Charon translates the
    body of a function or a global of another crate only when asked to (e.g.
    with [--include]), but the definition of a public type of another crate by
    default, which the models describe. *)
let external_mapping_error (k : crate) (kind : string) ~(opaque : bool option)
    ~(foreign_too : bool) (item_meta : item_meta) (extract_name : string option)
    : string option =
  let refused =
    match opaque with
    | Some true -> false
    | Some false -> item_meta.is_local || foreign_too
    | None -> item_meta.is_local
  in
  if not refused then None
  else
    Option.map
      (fun model ->
        let fix =
          match opaque with
          | None -> " Remove that entry."
          | Some _ ->
              let pattern =
                name_with_crate_to_pattern_string (Some item_meta.span) k
                  item_meta.name
              in
              " Remove that entry, or make the definition opaque for Charon"
              ^ " (--opaque '" ^ pattern ^ "')."
        in
        let what =
          if item_meta.is_local then " is defined in this crate"
          else " has a body"
        in
        kind ^ what
        ^ ", but an external name (user-provided or built-in) maps it to the \
           model '" ^ model ^ "', which would silently replace it." ^ fix)
      extract_name

(** Saves the error of {!external_mapping_error}, if any. *)
let check_not_external (k : crate) (kind : string) ~(opaque : bool option)
    ~(foreign_too : bool) (item_meta : item_meta) (extract_name : string option)
    : unit =
  Option.iter
    (fun msg -> [%save_error] item_meta.span msg)
    (external_mapping_error k kind ~opaque ~foreign_too item_meta extract_name)

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
