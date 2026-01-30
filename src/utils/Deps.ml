open LlbcAst
open LlbcAstUtils
open Types
open Meta

(** The local logger *)
let log = Logging.deps_log

type item_info = { id : item_id; span : span; is_local : bool }
[@@deriving show, ord]

module OrderedItemInfo : Collections.OrderedType with type t = item_info =
struct
  type t = item_info

  let compare = compare_item_info
  let to_string = show_item_info
  let pp_t fmt x = Format.pp_print_string fmt (show_item_info x)
  let show_t = show_item_info
end

module ItemInfoSet = Collections.MakeSet (OrderedItemInfo)

(** The graph from definition id to set of (ids, optional spans) which use this
    definition. This is essentially a reverse dependency graph.

    We use this information to display informative error messages to the user
    whenever an error occurs when processing an external definition: it is
    useful to explain why we need this external definition by pinpointing the
    spans in the local crate which (transitively) use it. *)
type graph_of_uses = {
  graph : ItemInfoSet.t AnyDeclIdMap.t;
  locals : AnyDeclIdSet.t;
}
[@@deriving show]

let compute_graph_of_uses (m : crate) : graph_of_uses =
  let is_local id =
    match crate_get_item_meta m id with
    | None ->
        (* This should never happen, but by default we treat the item as external *)
        false
    | Some meta -> meta.is_local
  in
  let graph = ref AnyDeclIdMap.empty in
  let locals = ref AnyDeclIdSet.empty in
  (* Check if an id is local and add it to the set of local identifiers if that is the case *)
  let add_opt_local id =
    if is_local id then locals := AnyDeclIdSet.add id !locals
  in
  (* Add an edge in the graph, registering the local ids at the same time *)
  let add_edge src info =
    add_opt_local src;
    match info with
    | None -> ()
    | Some (tgt, span) ->
        add_opt_local tgt;
        let is_local = is_local tgt in
        let info = { id = tgt; span; is_local } in
        graph :=
          AnyDeclIdMap.update src
            (fun s ->
              match s with
              | None -> Some (ItemInfoSet.singleton info)
              | Some s -> Some (ItemInfoSet.add info s))
            !graph
  in
  (* Visit the crate *)
  let visitor =
    object
      inherit [_] iter_crate_with_span
      method! visit_type_decl_id info id = add_edge (IdType id) info
      method! visit_fun_decl_id info id = add_edge (IdFun id) info
      method! visit_global_decl_id info id = add_edge (IdGlobal id) info
      method! visit_trait_decl_id info id = add_edge (IdTraitDecl id) info
      method! visit_trait_impl_id info id = add_edge (IdTraitImpl id) info
    end
  in
  visitor#visit_crate None m;

  (* *)
  { graph = !graph; locals = !locals }

(** Given a set of ids, filter to only keep the external ids and compute the set
    of local spans which (transitively) use these ids. *)
let compute_local_uses (graph : graph_of_uses) (ids : item_id list) :
    ItemInfoSet.t =
  let ids =
    List.filter (fun id -> not (AnyDeclIdSet.mem id graph.locals)) ids
  in
  let stack = ref ids in
  let uses = ref ItemInfoSet.empty in
  let explored = ref AnyDeclIdSet.empty in
  while !stack <> [] do
    let id = List.hd !stack in
    stack := List.tl !stack;
    if not (AnyDeclIdSet.mem id !explored) then (
      explored := AnyDeclIdSet.add id !explored;
      Option.iter
        (ItemInfoSet.iter (fun (user : item_info) ->
             if user.is_local then
               (* The user is local: save that use and stop exploring *)
               uses := ItemInfoSet.add user !uses
             else
               (* The user is not local: push it to the stack *)
               stack := user.id :: !stack))
        (AnyDeclIdMap.find_opt id graph.graph))
  done;
  (* *)
  !uses
