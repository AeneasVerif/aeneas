(** The placement plan for [-split-files]: which Lean files we write for each
    strongly connected component of the file graph ({!FileGraph}). Used by the
    emitter ({!Translate.extract_by_file}) and by [-dump-file-graph]. *)

open FileGraph

(** One Lean file of a {!component}. Most components have a single layer. A
    component whose opaque and transparent declarations depend on each other in
    alternation needs several. *)
type component_layer = {
  is_opaque_layer : bool;
      (** An [OpaquesK_Template] file, which the user copies to [OpaquesK] and
          fills in. *)
  import_name : string;
      (** The dotted Lean name of the file. For a template, the name of the
          filled copy. *)
  filename : string;  (** The path we write ([_Template] included). *)
  groups : LlbcAst.declaration_group list;
      (** Its declaration groups, in [crate.declarations] order. *)
}

(** One strongly connected component of the file graph: source files that use
    each other (usually a single file), or an external bucket. It is extracted
    under a single Lean name, in one or more {!component_layer}s. *)
type component = {
  scc_id : SCC.SccId.id;
  buckets : bucket list;  (** Its buckets in the file graph. *)
  source_files : string list;
      (** Its source files, relative to the crate's source root. Empty for an
          external component. *)
  import_name : string;
      (** The Lean name other files import, e.g. [Crate.Foo]. *)
  aggregator : string option;
      (** [Some filename] if there are several layers: an imports-only file at
          [import_name] that imports them all. *)
  layers : component_layer list;
      (** In import order. With a single layer, its file is at [import_name]. *)
}

(** The directory the Lean files go in: [D/Crate/], next to the [D/Crate.lean]
    entry point, or the [-subdir] directory itself. *)
let module_root_dir ~(subdir : string option) ~(full_dest_dir : string)
    ~(crate_name : string) : string =
  match subdir with
  | Some _ -> full_dest_dir
  | None -> Filename.concat full_dest_dir crate_name

(** Whether a declaration group is extracted as a file with generated Lean defs
    ([GroupTransparent]), as a file the user fills in ([GroupOpaque]), or not at
    all ([BuiltinOnly]). A group mixing opaque and transparent members cannot be
    split, so it counts as transparent (with a warning). *)
type group_opacity = BuiltinOnly | GroupOpaque | GroupTransparent

(** The opacity of a declaration group, determined from its non-builtin members.
*)
let group_opacity ~(crate : LlbcAst.crate) ~(is_builtin : Types.item_id -> bool)
    ~(is_opaque : Types.item_id -> bool) (g : LlbcAst.declaration_group) :
    group_opacity =
  let members =
    List.filter
      (fun id -> not (is_builtin id))
      (LlbcAstUtils.declaration_group_to_list g)
  in
  if members = [] then BuiltinOnly
  else
    let opaque, transparent = List.partition is_opaque members in
    if transparent = [] then GroupOpaque
    else (
      (match opaque with
      | [] -> ()
      | first :: _ ->
          let span =
            Option.map
              (fun (m : Types.item_meta) -> m.span)
              (LlbcAstUtils.crate_get_item_meta crate first)
          in
          [%warn_opt_span] span
            ("Mutually-recursive declaration group mixes opaque and \
              transparent members: the opaque members are emitted as inline \
              axioms in the extracted file instead of a file the user fills \
              in. Opaque members: "
            ^ String.concat ", " (List.map Types.show_item_id opaque)));
      GroupTransparent)

(** Split the declaration groups of a module into layers. Returns
    [(is_opaque_layer, groups)] for each layer, in order.

    The layers alternate between regular and opaque, and each decl group goes in
    the lowest layer that comes after the layers it depends on ([deps]), or the
    same layer if they have the same opacity.

    For example, let [b] be an opaque group and [a, c] transparent groups, where
    [b] depends on [a]. If [c] depends on [b], we get three layers: [[a]],
    [[b]], [[c]]. If [c] only depends on [a], we get two: [[a; c]], [[b]]. *)
let cut_layers ~(opacity : 'a -> group_opacity) ~(deps : 'a -> 'a list)
    (groups : 'a list) : (bool * 'a list) list =
  let groups = Array.of_list groups in
  let index = Hashtbl.create 16 in
  Array.iteri (fun i g -> Hashtbl.replace index g i) groups;
  (* The dependencies of group [i], as indices; this drops the ones that are not
     in [groups]. *)
  let deps i =
    List.filter_map (Hashtbl.find_opt index) (deps groups.(i))
    |> List.filter (fun j -> j <> i)
  in
  (* Memoization array for the layer information of each group. *)
  let memo = Array.make (Array.length groups) None in
  (* Used to get the max of the highest transparent and opaque layers a group
     depends on. *)
  let max2 (a, b) (c, d) = (max a c, max b d) in
  (* Get the layer of group i, and the highest transparent and opaque layers [(t, o)] it
     depends on ([-1] if none). Builtin-only groups are skipped over. *)
  let rec info i : int * (int * int) =
    match memo.(i) with
    | Some r -> r
    | None ->
        (* Declaration groups are acyclic; this only guards against looping. *)
        memo.(i) <- Some (0, (-1, -1));
        (* The highest layers among the dependencies. A builtin-only
           dependency contributes the layers it itself depends on. *)
        let below =
          List.fold_left
            (fun acc j -> max2 acc (snd (info j)))
            (-1, -1) (deps i)
        in
        let t, o = below in
        let r =
          match opacity groups.(i) with
          | BuiltinOnly ->
              (* Emits nothing, so it has no parity constraint. It sits as low
                 as its dependencies allow. *)
              (max 0 (max t o), below)
          | GroupTransparent ->
              (* An even layer: at least [t] (same opacity), and after [o]. *)
              let l = max 0 (max t (o + 1)) in
              (l, (l, -1))
          | GroupOpaque ->
              (* An odd layer: at least [o], and after [t]. *)
              let l = max 1 (max (t + 1) o) in
              (l, (-1, l))
        in
        memo.(i) <- Some r;
        r
  in
  let layer_of = Array.init (Array.length groups) (fun i -> fst (info i)) in
  (* The ordered list of layers holding at least one thing that gets emmitted. *)
  let used =
    List.sort_uniq compare
      (List.filter_map
         (fun i ->
           if opacity groups.(i) = BuiltinOnly then None else Some layer_of.(i))
         (List.init (Array.length groups) Fun.id))
  in
  match used with
  | [] ->
      (* Nothing is emitted: a single transparent layer with everything. *)
      if groups = [||] then [] else [ (false, Array.to_list groups) ]
  | first :: _ ->
      (* The layer where group [i] ends up. *)
      let placed i =
        if opacity groups.(i) <> BuiltinOnly then layer_of.(i)
        else
          (* A builtin-only group goes in the layer of its latest dependency,
             or the next layer that is used if that one is skipped. *)
          Option.value ~default:first
            (List.find_opt (fun l -> l >= layer_of.(i)) used)
      in
      (* Odd layers are opaque. *)
      List.map
        (fun l ->
          ( l mod 2 = 1,
            List.filteri (fun i _ -> placed i = l) (Array.to_list groups) ))
        used

(** The path of the file for the module [components]. An opaque layer is written
    as a [_Template] file. *)
let file_of_components ~(module_root_dir : string) ~(is_opaque_layer : bool)
    (components : string list) : string =
  module_root_dir ^ "/"
  ^ String.concat "/" components
  ^ (if is_opaque_layer then "_Template" else "")
  ^ ".lean"

(** The files of the module [base], given its layers (see {!cut_layers}).
    Returns the path of the aggregator, if there is one, and the layers.

    A module with a single layer is a single file at [base]. A module with
    multiple layers has one file per layer ([base.Part1], [base.Opaques2], ...),
    and an aggregator at [base] that imports them all. *)
let module_files ~(import_prefix : string) ~(module_root_dir : string)
    (base : string list) (layers : (bool * LlbcAst.declaration_group list) list)
    : string option * component_layer list =
  (* The layer for the module [components], holding [groups]. *)
  let layer ~(is_opaque_layer : bool) (components : string list)
      (groups : LlbcAst.declaration_group list) : component_layer =
    {
      is_opaque_layer;
      import_name = import_prefix ^ FileMapping.dotted_module_name components;
      filename = file_of_components ~module_root_dir ~is_opaque_layer components;
      groups;
    }
  in
  match layers with
  | [] ->
      (* Nothing to write, so no file. *)
      (None, [])
  | [ (is_opaque_layer, groups) ] ->
      (None, [ layer ~is_opaque_layer base groups ])
  | layers ->
      let layers =
        List.mapi
          (fun i (is_opaque_layer, groups) ->
            let components =
              FileMapping.layer_module_components base
                ~is_opaque:is_opaque_layer ~index:(i + 1)
            in
            layer ~is_opaque_layer components groups)
          layers
      in
      ( Some (file_of_components ~module_root_dir ~is_opaque_layer:false base),
        layers )

(** The Lean files to write for each component of the file graph, dependencies
    first.

    A component is named after its source file, or after all of them in the SCC
    If its declarations need several layers ({!cut_layers}), each layer is its
    own file and the component's name is an aggregator that imports them all.
    Declarations without metadata are left out ({!FileGraph.compute} warns about
    them). *)
let place_by_file (fg : FileGraph.t) ~(crate : LlbcAst.crate)
    ~(import_prefix : string) ~(module_root_dir : string) : component list =
  let scc_list = SCC.SccId.Map.bindings fg.sccs.sccs in
  let is_builtin = LlbcAstUtils.item_is_builtin crate in
  let is_opaque = LlbcAstUtils.item_is_opaque crate in
  let opacity = group_opacity ~crate ~is_builtin ~is_opaque in

  (* The SCC each bucket is in. *)
  let bucket_to_scc =
    SCC.SccId.Map.fold
      (fun scc_id buckets acc ->
        List.fold_left (fun acc b -> BucketMap.add b scc_id acc) acc buckets)
      fg.sccs.sccs BucketMap.empty
  in
  (* The SCC a declaration group is in. All the members of a group are in the
     same SCC, so we use the first one that has a bucket. *)
  let group_scc (g : LlbcAst.declaration_group) : SCC.SccId.id option =
    List.find_map
      (fun id ->
        Option.bind (LlbcAstUtils.AnyDeclIdMap.find_opt id fg.item_bucket)
          (fun b -> BucketMap.find_opt b bucket_to_scc))
      (LlbcAstUtils.declaration_group_to_list g)
  in
  (* The declaration groups of each SCC, in [crate.declarations] order (so
     declarations come before their uses). *)
  let groups_by_scc : LlbcAst.declaration_group list SCC.SccId.Map.t =
    SCC.SccId.Map.map List.rev
      (List.fold_left
         (fun acc g ->
           match group_scc g with
           | None ->
               (* No member has a bucket: [FileGraph.compute] already warned
                  about each of them. *)
               acc
           | Some scc_id ->
               SCC.SccId.Map.update scc_id
                 (function
                   | None -> Some [ g ]
                   | Some gs -> Some (g :: gs))
                 acc)
         SCC.SccId.Map.empty
         (Option.get crate.declarations))
  in

  (* The declaration group of each item. *)
  let group_of_item =
    List.fold_left
      (fun acc g ->
        List.fold_left
          (fun acc id -> LlbcAstUtils.AnyDeclIdMap.add id g acc)
          acc
          (LlbcAstUtils.declaration_group_to_list g))
      LlbcAstUtils.AnyDeclIdMap.empty
      (Option.get crate.declarations)
  in
  (* The groups a group uses. [cut_layers] ignores the ones outside the
     module being cut. *)
  let group_deps (g : LlbcAst.declaration_group) :
      LlbcAst.declaration_group list =
    List.concat_map
      (fun id ->
        List.filter_map
          (fun used -> LlbcAstUtils.AnyDeclIdMap.find_opt used group_of_item)
          (Option.value
             (LlbcAstUtils.AnyDeclIdMap.find_opt id fg.item_uses)
             ~default:[]))
      (LlbcAstUtils.declaration_group_to_list g)
  in

  List.map
    (fun (scc_id, buckets) ->
      let source_files =
        List.filter_map
          (function
            | BFile p -> Some p
            | BExternalTypes | BExternalFuns -> None)
          buckets
      in
      let base =
        match source_files with
        | [ p ] -> FileMapping.module_components_of_file p
        | paths -> FileMapping.merged_module_components paths
      in
      let groups =
        Option.value (SCC.SccId.Map.find_opt scc_id groups_by_scc) ~default:[]
      in
      let aggregator, layers =
        module_files ~import_prefix ~module_root_dir base
          (cut_layers ~opacity ~deps:group_deps groups)
      in
      {
        scc_id;
        buckets;
        source_files;
        import_name = import_prefix ^ FileMapping.dotted_module_name base;
        aggregator;
        layers;
      })
    scc_list
