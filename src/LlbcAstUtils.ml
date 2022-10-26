open LlbcAst
open Utils
module T = Types

(** Check if a {!type:LlbcAst.statement} contains loops *)
let statement_has_loops (st : statement) : bool =
  let obj =
    object
      inherit [_] iter_statement
      method! visit_Loop _ _ = raise Found
    end
  in
  try
    obj#visit_statement () st;
    false
  with Found -> true

(** Check if a {!type:LlbcAst.fun_decl} contains loops *)
let fun_decl_has_loops (fd : fun_decl) : bool =
  match fd.body with
  | Some body -> statement_has_loops body.body
  | None -> false

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    fun_sig =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).signature
  | Assumed aid -> Assumed.get_assumed_sig aid

let lookup_fun_name (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    Names.fun_name =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).name
  | Assumed aid -> Assumed.get_assumed_name aid

(** Small utility: list the transitive parents of a region var group.
    We don't do that in an efficient manner, but it doesn't matter.
    
    TODO: rename to "list_ancestors_..."

    This list *doesn't* include the current region.
 *)
let rec list_parent_region_groups (sg : fun_sig) (gid : T.RegionGroupId.id) :
    T.RegionGroupId.Set.t =
  let rg = T.RegionGroupId.nth sg.regions_hierarchy gid in
  let parents =
    List.fold_left
      (fun s gid ->
        (* Compute the parents *)
        let parents = list_parent_region_groups sg gid in
        (* Parents U current region *)
        let parents = T.RegionGroupId.Set.add gid parents in
        (* Make the union with the accumulator *)
        T.RegionGroupId.Set.union s parents)
      T.RegionGroupId.Set.empty rg.parents
  in
  parents

(** Small utility: same as {!list_parent_region_groups}, but returns an ordered list.  *)
let list_ordered_parent_region_groups (sg : fun_sig) (gid : T.RegionGroupId.id)
    : T.RegionGroupId.id list =
  let pset = list_parent_region_groups sg gid in
  let parents =
    List.filter
      (fun (rg : T.region_var_group) -> T.RegionGroupId.Set.mem rg.id pset)
      sg.regions_hierarchy
  in
  let parents = List.map (fun (rg : T.region_var_group) -> rg.id) parents in
  parents

let fun_body_get_input_vars (fbody : fun_body) : var list =
  let locals = List.tl fbody.locals in
  Collections.List.prefix fbody.arg_count locals
