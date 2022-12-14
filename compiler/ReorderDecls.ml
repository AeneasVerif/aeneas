open Graph
open Collections
open SCC
open Pure

type fun_id = { def_id : FunDeclId.id; rg_id : T.RegionGroupId.id option }
[@@deriving show, ord]

module FunIdOrderedType : OrderedType with type t = fun_id = struct
  type t = fun_id

  let compare = compare_fun_id
  let to_string = show_fun_id
  let pp_t = pp_fun_id
  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

(** Compute the dependencies of a function body, taking only into account
    the *custom* (i.e., not assumed) functions ids (ignoring operations, types,
    globals, etc.).
 *)
let compute_body_fun_deps (e : texpression) : FunIdSet.t =
  let ids = ref FunIdSet.empty in

  let visitor =
    object
      inherit [_] iter_expression

      method! visit_qualif _ id =
        match id.id with
        | FunOrOp (Unop _ | Binop _) | Global _ | AdtCons _ | Proj _ -> ()
        | FunOrOp (Fun fid) -> (
            match fid with
            | Pure _ -> ()
            | FromLlbc (fid, rg_id) -> (
                match fid with
                | Assumed _ -> ()
                | Regular fid ->
                    let id = { def_id = fid; rg_id } in
                    ids := FunIdSet.add id !ids))
    end
  in

  visitor#visit_texpression () e;
  !ids

type function_group = {
  is_rec : bool;
      (** [true] if (mutually) recursive. Useful only if there is exactly one
       declaration in the group.
    *)
  decls : fun_decl list;
}

(** Group mutually recursive functions together and reorder the groups so that
    if a group B depends on a group A then A comes before B, while trying to
    respect the original order as much as possible.
 *)
let group_reorder_fun_decls (decls : fun_decl list) :
    (bool * fun_decl list) list =
  let module IntMap = MakeMap (OrderedInt) in
  let get_fun_id (decl : fun_decl) : fun_id =
    { def_id = decl.def_id; rg_id = decl.back_id }
  in
  (* Compute the list/set of identifiers *)
  let idl = List.map get_fun_id decls in
  let ids = FunIdSet.of_list idl in

  (* Explore the bodies to compute the dependencies - we ignore the ids
     which refer to declarations not in the group we want to reorder *)
  let deps : (fun_id * FunIdSet.t) list =
    List.map
      (fun decl ->
        let id = get_fun_id decl in
        match decl.body with
        | None -> (id, FunIdSet.empty)
        | Some body ->
            let deps = compute_body_fun_deps body.body in
            (id, FunIdSet.inter deps ids))
      decls
  in

  (*
   * Create the dependency graph
   *)
  (* Convert the ids to vertices (i.e., injectively map ids to integers) *)
  let id_to_vertex : int FunIdMap.t =
    let cnt = ref 0 in
    FunIdMap.of_list
      (List.map
         (fun id ->
           let v = !cnt in
           cnt := !cnt + 1;
           (id, v))
         idl)
  in
  let vertex_to_id : fun_id IntMap.t =
    IntMap.of_list
      (List.map (fun (fid, vid) -> (vid, fid)) (FunIdMap.bindings id_to_vertex))
  in
  let to_v id = Pack.Graph.V.create (FunIdMap.find id id_to_vertex) in
  let to_id v = IntMap.find (Pack.Graph.V.label v) vertex_to_id in

  let g = Pack.Graph.create () in
  (* First add the vertices *)
  List.iter (fun id -> Pack.Graph.add_vertex g (to_v id)) idl;

  (* Then add the edges *)
  List.iter
    (fun (fun_id, deps) ->
      FunIdSet.iter
        (fun dep_id -> Pack.Graph.add_edge g (to_v fun_id) (to_v dep_id))
        deps)
    deps;

  (* Compute the SCCs *)
  let module Comp = Components.Make (Pack.Graph) in
  let sccs = Comp.scc_list g in

  (* Convert the vertices to ids *)
  let sccs = List.map (List.map to_id) sccs in

  (* Reorder *)
  let module Reorder = SCC.Make (FunIdOrderedType) in
  let id_deps =
    FunIdMap.of_list
      (List.map (fun (fid, deps) -> (fid, FunIdSet.elements deps)) deps)
  in
  let sccs = Reorder.reorder_sccs id_deps idl sccs in

  (* Group the declarations *)
  let deps = FunIdMap.of_list deps in
  let decls = FunIdMap.of_list (List.map (fun d -> (get_fun_id d, d)) decls) in
  List.map
    (fun (_, ids) ->
      (* is_rec is useful only if there is exactly one declaration *)
      let is_rec =
        match ids with
        | [] -> raise (Failure "Unreachable")
        | [ id ] ->
            let dep_ids = FunIdMap.find id deps in
            FunIdSet.mem id dep_ids
        | _ -> true
      in
      let decls = List.map (fun id -> FunIdMap.find id decls) ids in
      (is_rec, decls))
    (SccId.Map.bindings sccs.sccs)
