(** Given a translated LLBC crate, this module groups the declarations into
    source-file buckets, builds the dependency graph between the buckets, and
    computes its strongly-connected components. *)

open LlbcAst
open LlbcAstUtils
open Types
open Meta

(** Where a declaration/reference lands in the projected file graph.

    If the external item is a builtin already modeled by Aeneas then it will not
    get written to a separate external Lean file, so even if the external
    buckets are non-empty, it may be that no external file is actually
    generated. *)
type bucket =
  | BFile of string
      (** A local source file, keyed on its path below the crate's source root
          (e.g. ["foo.rs"], ["geometry/mod.rs"]). A file outside the source root
          keeps the path charon reports. *)
  | BExternalTypes  (** Referenced external type declarations. *)
  | BExternalFuns  (** Referenced external functions/globals/traits. *)
[@@deriving show, ord]

module BucketOrd : Collections.OrderedType with type t = bucket = struct
  type t = bucket

  let compare = compare_bucket
  let to_string = show_bucket
  let pp_t = pp_bucket
  let show_t = show_bucket
end

module BucketSet = Collections.MakeSet (BucketOrd)
module BucketMap = Collections.MakeMap (BucketOrd)

(** The bucket an item belongs to, or [None] if we can't find its metadata.

    A local item goes into the [BFile] with its path relative to [root]. An
    external item goes into [BExternalTypes] or [BExternalFuns] depending on its
    kind. *)
let bucket_of_item (crate : crate) ~(root : string list) (id : item_id) :
    bucket option =
  match crate_get_item_meta crate id with
  | None -> None
  | Some meta ->
      if not meta.is_local then
        Some
          (match id with
          | IdType _ -> BExternalTypes
          | _ -> BExternalFuns)
      else
        let file = meta.span.data.file in
        let path = Meta.path_of_file_name file.name in
        (* the key is the file's path relative to the source root (for example
           [foo.rs] for [crates/crate1/src/foo.rs]). A file outside the root keeps
           the path charon reported (for example for macro invocations, and
           [include!]). *)
        let key =
          match FileMapping.relative_source_path ~root path with
          | Some key -> key
          | None -> String.concat "/" (FileMapping.path_components path)
        in
        Some (BFile key)

(** The path of the Rust module that contains a local item, computed from the
    item's name. For example, [crate::a::b::f] and [crate::a::b::{impl ..}::f]
    are both in module [a::b], so the result is [["a"; "b"]]. The name of a
    local item always starts with the crate's own name, which is not part of the
    result. *)
let module_path_of_name (name : Types.name) : string list =
  (* In multi-target mode the name ends with [PeTarget]: remove it, or [f] in
     [crate::a::f::<target>] would be taken for a module. *)
  let name =
    match strip_target_suffix name with
    | _crate :: rest -> rest
    | [] -> []
  in
  let rec idents (n : Types.path_elem list) : string list =
    match n with
    | PeIdent (s, _) :: rest -> s :: idents rest
    | _ -> []
  in
  let prefix = idents name in
  (* If the name is only identifiers, the last one is the item itself. *)
  if List.length prefix = List.length name then
    match List.rev prefix with
    | _item :: rev_mods -> List.rev rev_mods
    | [] -> []
  else prefix

(** The file graph of a crate (see {!compute}). *)
type t = {
  crate_name : string;
  item_bucket : bucket AnyDeclIdMap.t;
      (** The bucket of each declaration in [crate.declarations]. A declaration
          whose metadata can't be found has no bucket: {!compute} warns, and it
          is not extracted. *)
  root : string list;
      (** The crate's source root (e.g. [["crates"; "mycrate"; "src"]]): the key
          of a file bucket is the file's path relative to it. *)
  members : item_id list BucketMap.t;  (** The declarations in each bucket. *)
  edges : BucketSet.t BucketMap.t;
      (** [edges] maps a bucket to the buckets it uses. Self-edges are omitted.
      *)
  sccs : bucket SCC.sccs;
      (** The strongly connected components of the bucket graph, dependencies
          first. Each component becomes one Lean module, so buckets in the same
          component end up in the same module. *)
}

(** Compute the file graph of a crate: put each declaration in a bucket, add an
    edge from a bucket to every bucket whose declarations it uses, and compute
    the strongly connected components of that graph. *)
let compute (crate : crate) : t =
  let items =
    List.concat_map declaration_group_to_list (Option.get crate.declarations)
  in
  (* The crate's source root, inferred from the local items whose file belongs
     to this crate. *)
  let root =
    let module_and_path (id : item_id) : (string list * string) option =
      match crate_get_item_meta crate id with
      | Some meta
        when meta.is_local && meta.span.data.file.crate_name = crate.name ->
          Some
            ( module_path_of_name meta.name,
              Meta.path_of_file_name meta.span.data.file.name )
      | _ -> None
    in
    match
      FileMapping.infer_source_root (List.filter_map module_and_path items)
    with
    | Some root -> root
    | None ->
        [%warn_opt_span] None
          "Multi-file extraction: could not infer the crate's source \
           directory; module names will follow the paths relative to the \
           directory cargo ran in";
        []
  in
  let item_bucket : bucket AnyDeclIdMap.t =
    List.fold_left
      (fun acc id ->
        match bucket_of_item crate ~root id with
        | None ->
            (* The id is in [crate.declarations] but the crate has no
               data on it. This shouldn't happen. [FilePlan.place_by_file] also
               warns if this leaves a whole declaration group without a
               bucket. *)
            [%warn_opt_span] None
              ("Multi-file extraction: no metadata found for " ^ show_item_id id
             ^ "; it will not appear in the output");
            acc
        | Some b -> AnyDeclIdMap.add id b acc)
      AnyDeclIdMap.empty items
  in
  let bucket_of (id : item_id) : bucket option =
    AnyDeclIdMap.find_opt id item_bucket
  in

  (* Map each bucket to the items it contains. *)
  let members : item_id list BucketMap.t ref = ref BucketMap.empty in
  List.iter
    (fun id ->
      match bucket_of id with
      | None -> ()
      | Some b ->
          members :=
            BucketMap.update b
              (function
                | None -> Some [ id ]
                | Some l -> Some (id :: l))
              !members)
    items;

  (* Build the bucket dependency graph from the item-level dependency graph.
     [graph_of_uses] maps each used item to the set of items that use it, so
     for every (used, user) pair we add an edge user_bucket -> used_bucket. *)
  let uses = Deps.compute_graph_of_uses crate in
  let edges : BucketSet.t BucketMap.t ref = ref BucketMap.empty in
  let add_edge (src : bucket) (dst : bucket) : unit =
    if BucketOrd.compare src dst <> 0 then
      edges :=
        BucketMap.update src
          (fun s ->
            Some (BucketSet.add dst (Option.value s ~default:BucketSet.empty)))
          !edges
  in
  AnyDeclIdMap.iter
    (fun used users ->
      match bucket_of used with
      | None -> ()
      | Some ub ->
          Deps.ItemInfoSet.iter
            (fun (user : Deps.item_info) ->
              match bucket_of user.id with
              | None -> ()
              | Some usb -> add_edge usb ub)
            users)
    uses.graph;

  (* The SCCs of the bucket graph, dependencies first (see {!t.sccs}). *)
  let module Scc = SCC.Make (BucketOrd) in
  let graph_list : (bucket * BucketSet.t) list =
    List.map
      (fun (b, _) ->
        (b, Option.value (BucketMap.find_opt b !edges) ~default:BucketSet.empty))
      (BucketMap.bindings !members)
  in
  let sccs = Scc.compute graph_list in

  {
    crate_name = crate.name;
    item_bucket;
    root;
    members = !members;
    edges = !edges;
    sccs;
  }

(** How to name a bucket to the user: a file bucket's actual path on disk or a
    placeholder for the external buckets. *)
let bucket_to_string (b : bucket) : string =
  match b with
  | BFile p -> p
  | BExternalTypes -> "<external types>"
  | BExternalFuns -> "<external funs>"

(** The report printed by [-dump-file-graph]: the buckets with their
    declarations, the edges between buckets, and the strongly connected
    components. [get_name] gives the Rust name of an item, for display. *)
let graph_to_string (graph : t) ~(get_name : item_id -> string) : string =
  let buf = Buffer.create 1024 in
  let line fmt =
    Printf.ksprintf (fun s -> Buffer.add_string buf (s ^ "\n")) fmt
  in

  let bucket_list = List.map fst (BucketMap.bindings graph.members) in
  let merges =
    List.filter
      (fun (_, bs) -> List.length bs > 1)
      (SCC.SccId.Map.bindings graph.sccs.sccs)
  in

  line "================ FILE GRAPH ================";
  line "Crate: %s" graph.crate_name;
  line "Source root: %s"
    (match graph.root with
    | [] -> "<directory cargo ran in>"
    | root -> String.concat "/" root);
  line "Buckets: %d   Forced merges (cyclic SCCs): %d" (List.length bucket_list)
    (List.length merges);
  line "";

  line "---- Buckets and their declarations ----";
  List.iter
    (fun b ->
      let ids = Option.value (BucketMap.find_opt b graph.members) ~default:[] in
      line "%s  (%d declarations)" (bucket_to_string b) (List.length ids);
      List.iter
        (fun id ->
          line "    [%-11s] %s" (item_id_to_kind_name id) (get_name id))
        (List.rev ids))
    bucket_list;
  line "";

  line "---- Bucket dependency edges (importer -> imported) ----";
  List.iter
    (fun b ->
      let deps =
        Option.value (BucketMap.find_opt b graph.edges) ~default:BucketSet.empty
      in
      if not (BucketSet.is_empty deps) then
        line "    %s  ->  %s" (bucket_to_string b)
          (String.concat ", "
             (List.map bucket_to_string (BucketSet.elements deps))))
    bucket_list;
  line "";

  line "---- Strongly-connected components ----";
  line "Each SCC becomes one Lean module; an SCC with >1 bucket is a forced";
  line "merge (those source files must share a single Lean module).";
  List.iter
    (fun (scc_id, bs) ->
      let dep_ids =
        Option.value
          (SCC.SccId.Map.find_opt scc_id graph.sccs.scc_deps)
          ~default:SCC.SccId.Set.empty
      in
      let deps_str =
        if SCC.SccId.Set.is_empty dep_ids then ""
        else
          "   (depends on SCC "
          ^ String.concat ", "
              (List.map SCC.SccId.to_string (SCC.SccId.Set.elements dep_ids))
          ^ ")"
      in
      let tag = if List.length bs > 1 then "  <== MERGED (cyclic)" else "" in
      line "  SCC %s: %s%s%s"
        (SCC.SccId.to_string scc_id)
        (String.concat " + " (List.map bucket_to_string bs))
        deps_str tag)
    (SCC.SccId.Map.bindings graph.sccs.sccs);
  line "=======================================================================";

  Buffer.contents buf
