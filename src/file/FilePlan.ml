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
