(** Utilities for strongly connected components - this is similar to the
    [graphs.rs] file in Charon *)

open Collections
module SccId = Identifiers.IdGen ()

(** The local logger *)
let log = Logging.scc_log

(** A structure containing information about SCCs (strongly connected
    components) *)
type 'id sccs = {
  sccs : 'id list SccId.Map.t;
  scc_deps : SccId.Set.t SccId.Map.t;  (** The dependencies between sccs *)
}
[@@deriving show]

(** A functor which provides functions to work on strongly connected components
*)
module MakeReorder (Id : OrderedType) = struct
  module IdMap = MakeMap (Id)
  module IdSet = MakeSet (Id)

  type id = Id.t

  let pp_id = Id.pp_t

  (** The order in which Tarjan's algorithm generates the SCCs is arbitrary,
      while we want to keep as much as possible the original order (the order in
      which the user generated the ids). For this, we iterate through the
      ordered ids and try to add the SCC containing the id to a new list of SCCs
      Of course, this SCC might have dependencies, so we need to add the
      dependencies first (in which case we have reordering to do). This is what
      this function does: we add an SCC and its dependencies to the list of
      reordered SCCs by doing a depth-first search. We also compute the SCC
      dependencies while performing this exploration.

      Rem.: we push SCCs to the *front* of [reordered_sccs] (which should then
      be reversed before being used).

      Rem.: [scc_deps]: we use the fact that the elements inside [SccId.Set.t]
      are ordered.

      TODO: change the type of [reordered_sccs] (not efficient...) *)
  let rec insert_scc_with_deps (id_deps : Id.t list IdMap.t)
      (reordered_sccs : SccId.id list ref)
      (scc_deps : SccId.Set.t SccId.Map.t ref) (sccs : Id.t list SccId.Map.t)
      (id_to_scc : SccId.id IdMap.t) (scc_id : SccId.id) : unit =
    (* Check if the SCC id has already been added *)
    if List.mem scc_id !reordered_sccs then ()
    else
      (* Add the dependencies.
         For every id in the dependencies, get the SCC containing this id.
         If this is the current SCC: continue. If it is a different one, it is
         a dependency: add it to the list of reordered SCCs. *)
      let scc = SccId.Map.find scc_id sccs in
      List.iter
        (fun id ->
          let ids = IdMap.find id id_deps in
          List.iter
            (fun dep_id ->
              let dep_scc_id = IdMap.find dep_id id_to_scc in
              if dep_scc_id = scc_id then ()
              else
                (* Insert the dependency *)
                let scc_deps_set = SccId.Map.find scc_id !scc_deps in
                let scc_deps_set = SccId.Set.add dep_scc_id scc_deps_set in
                scc_deps := SccId.Map.add scc_id scc_deps_set !scc_deps;

                (* Explore the parent SCC *)
                insert_scc_with_deps id_deps reordered_sccs scc_deps sccs
                  id_to_scc dep_scc_id)
            ids)
        scc;
      (* Add the current SCC *)
      reordered_sccs := scc_id :: !reordered_sccs

  (** Provided we computed the SCCs (Strongly Connected Components) of a set of
      identifier, and those identifiers are ordered, compute the set of SCCs
      where the order of the SCCs and the order of the identifiers inside the
      SCCs attempt to respect as much as possible the original order between the
      identifiers. The [ids] vector gives the ordered set of identifiers.

      This is used to generate the translated definitions in a consistent and
      stable manner. For instance, if some Rust functions are mutually
      recursive, it is possible that we can extract the forward functions in one
      group, and extract the backward functions in one group (after filtering
      the useless calls in {!module:PureMicroPasses}), but is is also possible
      that all the functions (forward and backward) are mutually recursive). For
      this reason, we compute the dependency graph and the strongly connected
      components of that graph. Similar problems when functions contain loops
      (especially mutually recursive functions which contain loops (!)).

      Also see the comments for the equivalent function in [graph.rs] in the
      Charon project. *)
  let reorder_sccs (id_deps : Id.t list IdMap.t) (ids : Id.t list)
      (sccs : Id.t list list) : id sccs =
    (* Map the identifiers to the SCC indices *)
    let id_to_scc =
      IdMap.of_list
        (List.concat
           (SccId.mapi
              (fun scc_id scc -> List.map (fun id -> (id, scc_id)) scc)
              sccs))
    in

    (* Reorder the identifiers inside the SCCs.
       We iterate over the identifiers (in the order in which we register them) and add
       them in their corresponding SCCs.
       TODO: we append to the end of lists, this is not very efficient...
    *)
    let reordered_sccs : Id.t list SccId.Map.t ref =
      ref (SccId.Map.of_list (SccId.mapi (fun scc_id _ -> (scc_id, [])) sccs))
    in
    List.iter
      (fun id ->
        let scc_id = IdMap.find id id_to_scc in
        let scc_ids = SccId.Map.find scc_id !reordered_sccs in
        (* TODO: this is not efficient *)
        let scc_ids = List.append scc_ids [ id ] in
        reordered_sccs := SccId.Map.add scc_id scc_ids !reordered_sccs)
      ids;

    (* Reorder the SCCs themselves - just do a depth first search. Iterate over
       the def ids, and add the corresponding SCCs (with their dependencies) *)
    let reordered_sccs_ids = ref [] in
    let scc_deps =
      ref (SccId.Map.map (fun _ -> SccId.Set.empty) !reordered_sccs)
    in
    List.iter
      (fun id ->
        let scc_id = IdMap.find id id_to_scc in
        insert_scc_with_deps id_deps reordered_sccs_ids scc_deps !reordered_sccs
          id_to_scc scc_id)
      ids;
    let reordered_sccs_ids = List.rev !reordered_sccs_ids in

    (* Compute the map from the original SCC ids to the new SCC ids (after reordering) *)
    let old_to_new_id =
      SccId.Map.of_list
        (SccId.mapi (fun new_id old_id -> (old_id, new_id)) reordered_sccs_ids)
    in

    (* Generate the reordered SCCs *)
    let tgt_sccs =
      SccId.Map.of_list
        (SccId.mapi
           (fun new_id scc_id ->
             (new_id, SccId.Map.find scc_id !reordered_sccs))
           reordered_sccs_ids)
    in

    (* Compute the dependencies with the new indices *)
    let tgt_deps =
      SccId.Map.of_list
        (List.map
           (fun (old_id, deps_ids) ->
             let new_id = SccId.Map.find old_id old_to_new_id in
             let new_deps_ids =
               SccId.Set.map
                 (fun id -> SccId.Map.find id old_to_new_id)
                 deps_ids
             in
             (new_id, new_deps_ids))
           (SccId.Map.bindings !scc_deps))
    in

    (* Return *)
    { sccs = tgt_sccs; scc_deps = tgt_deps }
end

module Make (Id : OrderedType) = struct
  module M = MakeMap (Id)
  module S = MakeSet (Id)

  (** Compute the ordered SCC components for a graph, which is a map from
      identifier to set of identifiers (which represent the set of edges
      starting from an identifier). *)
  let compute (m : (Id.t * S.t) list) : Id.t sccs =
    (*
     * Create the dependency graph
     *)
    (* Compute the list/set of identifiers *)
    let idl = List.map fst m in
    let ids = S.of_list idl in

    (* Convert the ids to vertices (i.e., injectively map ids to integers,
       and create vertices labeled with those integers).

       Rem.: [Graph.create] is *imperative*: it generates a new vertex every
       time it is called (!!). For this reason, we first add all the vertices
       we need, then add the edges.
    *)
    let open Graph in
    let module IntMap = MakeMap (OrderedInt) in
    let module Graph = Pack.Digraph in
    let id_to_vertex : Graph.V.t M.t =
      let cnt = ref 0 in
      M.of_list
        (List.map
           (fun id ->
             let lbl = !cnt in
             cnt := !cnt + 1;
             (* We create a vertex *)
             let v = Graph.V.create lbl in
             (id, v))
           idl)
    in
    let vertex_to_id : Id.t IntMap.t =
      IntMap.of_list
        (List.map
           (fun (fid, v) -> (Graph.V.label v, fid))
           (M.bindings id_to_vertex))
    in

    let to_v id = M.find id id_to_vertex in
    let to_id v = IntMap.find (Graph.V.label v) vertex_to_id in

    let g = Graph.create () in

    (* Add the edges, first from the vertices to themselves, then between
       vertices. *)
    List.iter
      (fun (id, deps) ->
        let v = to_v id in
        Graph.add_edge g v v;
        S.iter (fun dep_id -> Graph.add_edge g v (to_v dep_id)) deps)
      m;

    (* Compute the SCCs *)
    let module Comp = Components.Make (Graph) in
    let sccs = Comp.scc_list g in

    (* Convert the vertices to ids *)
    let sccs = List.map (List.map to_id) sccs in

    (* Sanity check *)
    let _ =
      (* Check that the SCCs are pairwise disjoint *)
      assert (S.pairwise_disjoint (List.map S.of_list sccs));
      (* Check that all the ids are in the sccs *)
      let scc_ids = S.of_list (List.concat sccs) in

      [%ldebug
        "sanity check:" ^ "\n- ids    : " ^ S.show ids ^ "\n- scc_ids: "
        ^ S.show scc_ids];

      assert (S.equal scc_ids ids)
    in

    (* Reorder *)
    let module Reorder = MakeReorder (Id) in
    let id_deps =
      M.of_list (List.map (fun (fid, deps) -> (fid, S.elements deps)) m)
    in
    let sccs = Reorder.reorder_sccs id_deps idl sccs in

    (* Sanity check *)
    let _ =
      (* Check that the SCCs are pairwise disjoint *)
      let sccs = List.map snd (SccId.Map.bindings sccs.sccs) in
      assert (S.pairwise_disjoint (List.map S.of_list sccs));
      (* Check that all the ids are in the sccs *)
      let scc_ids = S.of_list (List.concat sccs) in
      assert (S.equal scc_ids ids)
    in

    sccs
end

(** Test - TODO: make "real" unit tests *)
let _ =
  (* Check that some SCCs are correctly reordered *)
  let check_sccs (id_deps : (int * int list) list) (ids : int list)
      (sccs : int list list) (tgt_sccs : int list list) : unit =
    let module Ord = OrderedInt in
    let module Reorder = MakeReorder (Ord) in
    let module Map = MakeMap (Ord) in
    let id_deps = Map.of_list id_deps in

    let reordered = Reorder.reorder_sccs id_deps ids sccs in
    let tgt_sccs =
      SccId.Map.of_list (SccId.mapi (fun scc_id ids -> (scc_id, ids)) tgt_sccs)
    in
    assert (reordered.sccs = tgt_sccs)
  in

  (* Shouldn't reorder *)
  let _ =
    let id_deps =
      [ (0, []); (1, [ 2; 3 ]); (2, [ 1 ]); (3, [ 1 ]); (4, [ 2 ]) ]
    in
    let ids = [ 0; 1; 2; 3; 4 ] in
    let sccs = [ [ 0 ]; [ 1; 2; 3 ]; [ 4 ] ] in
    let tgt_sccs = sccs in
    check_sccs id_deps ids sccs tgt_sccs
  in

  (* Small reorder *)
  let _ =
    let id_deps =
      [ (0, []); (1, [ 2; 3 ]); (2, [ 1 ]); (3, [ 1 ]); (4, [ 2 ]) ]
    in
    let ids = [ 0; 1; 3; 2; 4 ] in
    let sccs = [ [ 0 ]; [ 1; 2; 3 ]; [ 4 ] ] in
    let tgt_sccs = [ [ 0 ]; [ 1; 3; 2 ]; [ 4 ] ] in
    check_sccs id_deps ids sccs tgt_sccs
  in

  let _ =
    let id_deps = [ (0, [ 1 ]); (1, [ 0 ]); (2, [ 3 ]); (3, [ 2 ]) ] in
    let ids = [ 3; 2; 0; 1 ] in
    let sccs = [ [ 0; 1 ]; [ 2; 3 ] ] in
    let tgt_sccs = [ [ 3; 2 ]; [ 0; 1 ] ] in
    check_sccs id_deps ids sccs tgt_sccs
  in

  ()
