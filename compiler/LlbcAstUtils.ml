open LlbcAst
include Charon.LlbcAstUtils

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    fun_sig =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).signature
  | Assumed aid -> Assumed.get_assumed_fun_sig aid

let lookup_fun_name (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    Names.fun_name =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).name
  | Assumed aid -> Assumed.get_assumed_fun_name aid

(** Return the opaque declarations found in the crate.

    [filter_assumed]: if [true], do not consider as opaque the external definitions
    that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global bodies.
 *)
let crate_get_opaque_decls (k : crate) (filter_assumed : bool) :
    T.type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let is_opaque_fun (d : fun_decl) : bool =
    let sname = name_to_simple_name d.name in
    d.body = None
    (* Something to pay attention to: we must ignore trait method *declarations*
       (which don't have a body but must not be considered as opaque) *)
    && (match d.kind with TraitMethodDecl _ -> false | _ -> true)
    && ((not filter_assumed)
       || not (SimpleNameMap.mem sname builtin_globals_map))
  in
  let is_opaque_type (d : T.type_decl) : bool = d.kind = T.Opaque in
  (* Note that by checking the function bodies we also the globals *)
  ( List.filter is_opaque_type (T.TypeDeclId.Map.values k.types),
    List.filter is_opaque_fun (FunDeclId.Map.values k.functions) )

(** Return true if the crate contains opaque declarations, ignoring the assumed
    definitions. *)
let crate_has_opaque_decls (k : crate) (filter_assumed : bool) : bool =
  crate_get_opaque_decls k filter_assumed <> ([], [])
