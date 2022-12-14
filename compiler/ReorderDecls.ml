open Graph
open Collections
open SCC
open Pure

(** The local logger *)
let log = Logging.reorder_decls_log

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

  log#ldebug
    (lazy
      ("group_reorder_fun_decls: ids:\n"
      ^ (Print.list_to_string FunIdOrderedType.show_t) idl));

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
            (* Restrict the set dependencies *)
            let deps = FunIdSet.inter deps ids in
            (id, deps))
      decls
  in

  (*
   * Create the dependency graph
   *)
  (* Convert the ids to vertices (i.e., injectively map ids to integers, and create
     vertices labeled with those integers).

     Rem.: [Graph.create] is *imperative*: it generates a new vertex every time
     it is called (!!).
  *)
  let module Graph = Pack.Digraph in
  let id_to_vertex : Graph.V.t FunIdMap.t =
    let cnt = ref 0 in
    FunIdMap.of_list
      (List.map
         (fun id ->
           let lbl = !cnt in
           cnt := !cnt + 1;
           (* We create a vertex *)
           let v = Graph.V.create lbl in
           (id, v))
         idl)
  in
  let vertex_to_id : fun_id IntMap.t =
    IntMap.of_list
      (List.map
         (fun (fid, v) -> (Graph.V.label v, fid))
         (FunIdMap.bindings id_to_vertex))
  in

  let to_v id = FunIdMap.find id id_to_vertex in
  let to_id v = IntMap.find (Graph.V.label v) vertex_to_id in

  let g = Graph.create () in

  (* Add the edges, first from the vertices to themselves, then between vertices *)
  List.iter
    (fun (fun_id, deps) ->
      let v = to_v fun_id in
      Graph.add_edge g v v;
      FunIdSet.iter (fun dep_id -> Graph.add_edge g v (to_v dep_id)) deps)
    deps;

  (* Compute the SCCs *)
  let module Comp = Components.Make (Graph) in
  let sccs = Comp.scc_list g in

  (* Convert the vertices to ids *)
  let sccs = List.map (List.map to_id) sccs in

  log#ldebug
    (lazy
      ("group_reorder_fun_decls: SCCs:\n"
      ^ Print.list_to_string (Print.list_to_string FunIdOrderedType.show_t) sccs
      ));

  (* Sanity check *)
  let _ =
    (* Check that the SCCs are pairwise disjoint *)
    assert (FunIdSet.pairwise_disjoint (List.map FunIdSet.of_list sccs));
    (* Check that all the ids are in the sccs *)
    let scc_ids = FunIdSet.of_list (List.concat sccs) in

    log#ldebug
      (lazy
        ("group_reorder_fun_decls: sanity check:" ^ "\n- ids    : "
       ^ FunIdSet.show ids ^ "\n- scc_ids: " ^ FunIdSet.show scc_ids));

    assert (FunIdSet.equal scc_ids ids)
  in

  log#ldebug
    (lazy
      ("group_reorder_fun_decls: reordered SCCs:\n"
      ^ Print.list_to_string (Print.list_to_string FunIdOrderedType.show_t) sccs
      ));

  (* Reorder *)
  let module Reorder = SCC.Make (FunIdOrderedType) in
  let id_deps =
    FunIdMap.of_list
      (List.map (fun (fid, deps) -> (fid, FunIdSet.elements deps)) deps)
  in
  let sccs = Reorder.reorder_sccs id_deps idl sccs in

  (* Sanity check *)
  let _ =
    (* Check that the SCCs are pairwise disjoint *)
    let sccs = List.map snd (SccId.Map.bindings sccs.sccs) in
    assert (FunIdSet.pairwise_disjoint (List.map FunIdSet.of_list sccs));
    (* Check that all the ids are in the sccs *)
    let scc_ids = FunIdSet.of_list (List.concat sccs) in
    assert (scc_ids = ids)
  in

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
