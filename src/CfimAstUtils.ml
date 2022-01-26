open CfimAst
open Utils
module T = Types

(** Check if a [statement] contains loops *)
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

(** Check if a [fun_def] contains loops *)
let fun_def_has_loops (fd : fun_def) : bool = statement_has_loops fd.body

(** Small utility: list the transitive parents of a region var group.
    We don't do that in an efficient manner, but it doesn't matter.
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

(** Small utility: same as [list_parent_region_groups], but returns an ordered list.  *)
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
