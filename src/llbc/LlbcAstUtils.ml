open Types
open LlbcAst
include Charon.LlbcAstUtils
open Collections

module FunIdOrderedType : OrderedType with type t = fun_id = struct
  type t = fun_id

  let compare = compare_fun_id
  let to_string = show_fun_id
  let pp_t = pp_fun_id
  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    fun_sig =
  match fun_id with
  | FRegular id -> (FunDeclId.Map.find id fun_decls).signature
  | FBuiltin aid -> Builtin.get_builtin_fun_sig aid

(** Return the opaque declarations found in the crate, which are also *not
    builtin*.

    [filter_builtin]: if [true], do not consider as opaque the external
    definitions that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global
    bodies. *)
let crate_get_opaque_non_builtin_decls (k : crate) (filter_builtin : bool) :
    type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  let is_opaque_fun (d : fun_decl) : bool =
    d.body = None
    (* Something to pay attention to: we must ignore trait method *declarations*
       (which don't have a body but must not be considered as opaque) *)
    && (match d.src with
       | TraitDeclItem (_, _, false) -> false
       | _ -> true)
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
  ( List.filter is_opaque_type (TypeDeclId.Map.values k.type_decls),
    List.filter is_opaque_fun (FunDeclId.Map.values k.fun_decls) )

(** Return true if the crate contains opaque declarations, ignoring the builtin
    definitions. *)
let crate_has_opaque_non_builtin_decls (k : crate) (filter_builtin : bool) :
    bool =
  crate_get_opaque_non_builtin_decls k filter_builtin <> ([], [])

let name_to_pattern (span : Meta.span option) (ctx : 'a Charon.NameMatcher.ctx)
    (c : Charon.NameMatcher.to_pat_config) (n : name) =
  if !Config.fail_hard then Charon.NameMatcher.name_to_pattern ctx c n
  else
    try Charon.NameMatcher.name_to_pattern ctx c n
    with Not_found ->
      [%craise_opt_span] span
        "Could not convert the name to a pattern because of missing \
         definition(s)"

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
    (ctx : 'a Charon.NameMatcher.ctx) (c : Charon.NameMatcher.to_pat_config)
    (params : generic_params) (n : Charon.Types.name) (args : generic_args) =
  if !Config.fail_hard then
    Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
  else
    try Charon.NameMatcher.name_with_generics_to_pattern ctx c params n args
    with Not_found ->
      [%craise_opt_span] span
        "Could not convert the name to a pattern because of missing \
         definition(s)"

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
