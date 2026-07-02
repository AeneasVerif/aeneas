(** Given a translated LLBC crate, this module groups the declarations into
    source-file buckets, builds the dependency graph between the buckets, and
    computes its strongly-connected components. *)

open LlbcAst
open LlbcAstUtils
open Types
open Meta

(** Where a declaration/reference lands in the projected file graph.

    The external buckets are diagnostic buckets for non-local referenced
    declarations. They do not imply that the current extraction backend will
    emit a corresponding external template file. *)
type bucket =
  | BFile of string  (** A local source file, e.g. ["src/foo.rs"]. *)
  | BExternalTypes  (** Referenced external type declarations. *)
  | BExternalFuns  (** Referenced external functions/globals/traits. *)
[@@deriving show, ord]

module BucketOrd : Collections.OrderedType with type t = bucket = struct
  type t = bucket

  let compare = compare_bucket
  let to_string = show_bucket
  let pp_t fmt x = Format.pp_print_string fmt (show_bucket x)
  let show_t = show_bucket
end

module BucketSet = Collections.MakeSet (BucketOrd)
module BucketMap = Collections.MakeMap (BucketOrd)

(** The bucket an item belongs to, or [None] if we can't find its metadata.

    Bucketing is gated on [is_local]: a local item goes to a [BFile] keyed on
    its source path, a non-local item to an external bucket by kind. *)
let bucket_of_item (crate : crate) (id : item_id) : bucket option =
  match crate_get_item_meta crate id with
  | None -> None
  | Some meta ->
      if meta.is_local then
        Some (BFile (Meta.path_of_file_name meta.span.data.file.name))
      else
        Some
          (match id with
          | IdType _ -> BExternalTypes
          | _ -> BExternalFuns)

let display_bucket (b : bucket) : string =
  match b with
  | BFile p -> p
  | BExternalTypes -> "<external types>"
  | BExternalFuns -> "<external funs>"

type t = {
  crate_name : string;
  item_bucket : bucket AnyDeclIdMap.t;
      (** Every declaration's bucket, computed once. Items whose metadata can't
          be found (e.g. ids a prepass removed from the maps but not from
          [crate.declarations]) are absent. *)
  members : item_id list BucketMap.t;
  edges : BucketSet.t BucketMap.t;
  sccs : bucket SCC.sccs;
}

let compute (crate : crate) : t =
  (* Enumerate the declarations through [crate.declarations] — the same source
     of truth the emitter partitions — and map each item to its bucket once. *)
  (* [declaration_group_to_list] comes from charon's [GAstUtils] via
     [LlbcAstUtils]. *)
  let items = List.concat_map declaration_group_to_list crate.declarations in
  let item_bucket : bucket AnyDeclIdMap.t =
    List.fold_left
      (fun acc id ->
        match bucket_of_item crate id with
        | None -> acc
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

  (* Build the bucket dependency graph from the item-level use graph.
     [graph_of_uses] maps each *used* item to the set of items that use it, so
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

  (* Compute the SCCs of the bucket graph: every node is a bucket, and the
     reordering keeps the topological (dependency-first) order. *)
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
    members = !members;
    edges = !edges;
    sccs;
  }

(** Render the report.

    [get_name] turns an item id into a human-readable Rust name. *)
let render (graph : t) ~(get_name : item_id -> string) : string =
  (* Render the report. *)
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
  line "Buckets: %d   Forced merges (cyclic SCCs): %d" (List.length bucket_list)
    (List.length merges);
  line "";

  line "---- Buckets and their declarations ----";
  List.iter
    (fun b ->
      let ids = Option.value (BucketMap.find_opt b graph.members) ~default:[] in
      line "%s  (%d declarations)" (display_bucket b) (List.length ids);
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
        line "    %s  ->  %s" (display_bucket b)
          (String.concat ", "
             (List.map display_bucket (BucketSet.elements deps))))
    bucket_list;
  line "";

  line "---- Strongly-connected components ----";
  line "Each SCC becomes exactly one Lean file; an SCC with >1 bucket is a";
  line "forced merge (those source files must share a single Lean module).";
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
        (String.concat " + " (List.map display_bucket bs))
        deps_str tag)
    (SCC.SccId.Map.bindings graph.sccs.sccs);
  line "=======================================================================";

  Buffer.contents buf
