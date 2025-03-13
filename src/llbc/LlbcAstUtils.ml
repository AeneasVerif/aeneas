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

(** Return the opaque declarations found in the crate, which are also *not builtin*.

    [filter_builtin]: if [true], do not consider as opaque the external definitions
    that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global bodies.
 *)
let crate_get_opaque_non_builtin_decls (k : crate) (filter_builtin : bool) :
    type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let ctx = Charon.NameMatcher.ctx_from_crate k in
  let is_opaque_fun (d : fun_decl) : bool =
    d.body = None
    (* Something to pay attention to: we must ignore trait method *declarations*
       (which don't have a body but must not be considered as opaque) *)
    && (match d.kind with
       | TraitDeclItem (_, _, false) -> false
       | _ -> true)
    && ((not filter_builtin)
       || (not (NameMatcherMap.mem ctx d.item_meta.name builtin_globals_map))
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
