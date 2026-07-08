(** Placement plan for [-split-files]: which Lean modules/files each SCC of the
    file-dependency graph becomes, including the per-module opacity layering .
    Used by the emitter ({!Translate.extract_by_file}) and the
    [-dump-file-graph] flag. *)

open FileGraph

(** One emitted declaration file of a placed module: a regenerated [PartK] file,
    or a user-fillable [AxiomsK_Template] file holding an opaque layer. *)
type placed_layer = {
  is_template : bool;
  import_name : string;
      (** The dotted Lean name the file is imported as. For a template this is
          the *filled* name (without [_Template]) *)
  filename : string;
      (** On-disk path the emitter writes ([_Template] included). *)
  groups : LlbcAst.declaration_group list;
      (** The layer's declaration groups, in charon order. *)
}

(** One generated Lean module in [-split-files] mode: a source file, a merged
    SCC, or an external bucket. A module whose declarations are uniform in
    opacity is a single file at its plain name; a module whose declarations
    alternate splits into a chain of layers plus an imports-only aggregator at
    the plain name. *)
type placed_module = {
  scc_id : SCC.SccId.id;
  buckets : bucket list;  (** The source-file/external buckets in this SCC. *)
  is_external : bool;
      (** [true] for the external modules ([TypesExternal] / [FunsExternal]). *)
  is_dropped : bool;
      (** [true] for external modules whose referenced declarations are all
          builtins: we neither emit them nor import them from local modules.
          Implies [is_external]. *)
  import_name : string;
      (** The module's plain dotted name, e.g. [Crate.Foo] — what dependent
          modules and the entry point import, whether or not the module is split
          into layers. *)
  aggregator : string option;
      (** [Some filename] iff the module has >= 2 layers: a generated
          imports-only file at the plain name, pulling in every layer. *)
  layers : placed_layer list;  (** Empty iff [is_dropped]. *)
}

(** The on-disk root the generated modules live under. With [-subdir] that
    directory is already [full_dest_dir]; otherwise we nest under [crate_name]
    so that [-dest D] yields a self-contained [D/Crate/...] tree plus a
    [D/Crate.lean] entry point. *)
let module_root_dir ~(subdir : string option) ~(full_dest_dir : string)
    ~(crate_name : string) : string =
  match subdir with
  | Some _ -> full_dest_dir
  | None -> Filename.concat full_dest_dir crate_name

(** The opacity "color" of a declaration group.

    All-builtin groups are colorless: they emit nothing, so they attach to
    whichever layer is current instead of cutting one. A group mixing opaque and
    transparent members must stay whole, so it degrades to a transparent
    (regenerated) layer — its opaque members are emitted as inline axioms — with
    a warning. *)
type group_color = Colorless | ColorOpaque | ColorTransparent

let group_color ~(crate : LlbcAst.crate) ~(is_builtin : Types.item_id -> bool)
    ~(is_opaque : Types.item_id -> bool) (g : LlbcAst.declaration_group) :
    group_color =
  let members =
    List.filter
      (fun id -> not (is_builtin id))
      (LlbcAstUtils.declaration_group_to_list g)
  in
  if members = [] then Colorless
  else
    let opaque, transparent = List.partition is_opaque members in
    if transparent = [] then ColorOpaque
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
              axioms in a regenerated file instead of a user-fillable \
              template. Opaque members: "
            ^ String.concat ", " (List.map Types.show_item_id opaque)));
      ColorTransparent)

(** Cut a module's (charon-ordered) declaration groups into maximal same-color
    runs: the module's opacity layers. Returns [(is_template, groups)] runs in
    order. Colorless groups attach to the current run; a colorless prefix
    attaches to the first colored run (or forms a single regenerated layer if no
    colored group exists at all). *)
let cut_layers (color : 'a -> group_color) (groups : 'a list) :
    (bool * 'a list) list =
  (* [runs_rev] accumulates finished+current runs, groups reversed within each
     run; [pending_rev] holds a colorless prefix seen before any colored
     group. *)
  let runs_rev, pending_rev =
    List.fold_left
      (fun (runs_rev, pending_rev) g ->
        match (color g, runs_rev) with
        | Colorless, (t, gs) :: rest -> ((t, g :: gs) :: rest, pending_rev)
        | Colorless, [] -> (runs_rev, g :: pending_rev)
        | c, _ -> (
            let t = c = ColorOpaque in
            match runs_rev with
            | (t', gs) :: rest when t' = t -> ((t, g :: gs) :: rest, pending_rev)
            | _ -> ((t, g :: pending_rev) :: runs_rev, [])))
      ([], []) groups
  in
  match (runs_rev, pending_rev) with
  | [], [] -> []
  | [], pending_rev -> [ (false, List.rev pending_rev) ]
  | runs_rev, _ ->
      List.rev_map (fun (t, gs_rev) -> (t, List.rev gs_rev)) runs_rev

(** Resolve every SCC of the file graph to its Lean module identity — plain
    name, opacity layers, optional aggregator — in topological
    (dependency-first) order. Merge indices are allocated to multi-bucket local
    SCCs in that order. *)
let place_by_file (fg : FileGraph.t) ~(crate : LlbcAst.crate)
    ~(import_prefix : string) ~(module_root_dir : string) ~(ext : string) :
    placed_module list =
  let scc_list = SCC.SccId.Map.bindings fg.sccs.sccs in
  let is_builtin = LlbcAstUtils.item_is_builtin crate in
  let is_opaque = LlbcAstUtils.item_is_opaque crate in
  let color = group_color ~crate ~is_builtin ~is_opaque in

  (* Partition the crate's declaration groups by SCC in a single pass, keeping
     charon's topological order within each SCC. All the members of a group
     share a source file / SCC, so any member is a valid representative; a
     group whose representative has no bucket (no metadata) maps to no SCC and
     is dropped, with a warning. *)
  let bucket_to_scc =
    SCC.SccId.Map.fold
      (fun scc_id buckets acc ->
        List.fold_left (fun acc b -> BucketMap.add b scc_id acc) acc buckets)
      fg.sccs.sccs BucketMap.empty
  in
  let group_scc (g : LlbcAst.declaration_group) : SCC.SccId.id option =
    match LlbcAstUtils.declaration_group_to_list g with
    | [] -> None
    | repr :: _ ->
        Option.bind (LlbcAstUtils.AnyDeclIdMap.find_opt repr fg.item_bucket)
          (fun b -> BucketMap.find_opt b bucket_to_scc)
  in
  let groups_by_scc : LlbcAst.declaration_group list SCC.SccId.Map.t =
    SCC.SccId.Map.map List.rev
      (List.fold_left
         (fun acc g ->
           match group_scc g with
           | None ->
               (* The group-level counterpart of the missing-metadata warning
                  in [FileGraph.compute]. *)
               let repr =
                 match LlbcAstUtils.declaration_group_to_list g with
                 | [] -> "<empty declaration group>"
                 | repr :: _ -> Types.show_item_id repr
               in
               [%warn_opt_span] None
                 ("Multi-file extraction: dropping a declaration group whose \
                   representative has no source-file bucket (representative: "
                ^ repr ^ ")");
               acc
           | Some scc_id ->
               SCC.SccId.Map.update scc_id
                 (function
                   | None -> Some [ g ]
                   | Some gs -> Some (g :: gs))
                 acc)
         SCC.SccId.Map.empty crate.declarations)
  in

  let file_of_components ~(is_template : bool) (components : string list) :
      string =
    module_root_dir ^ "/"
    ^ String.concat "/" components
    ^ (if is_template then "_Template" else "")
    ^ ext
  in
  let merge_counter = ref 0 in
  let placed =
    List.map
      (fun (scc_id, buckets) ->
        (* Only the external buckets can be dropped or hold external decls. *)
        let is_external =
          List.exists
            (function
              | BExternalTypes | BExternalFuns -> true
              | BFile _ -> false)
            buckets
        in
        (* An external SCC has nothing to emit iff all its declarations are
           builtins (resolved via [import Aeneas]): dropping it avoids an
           empty file and a dangling import. Decide from the actual members,
           not the crate-global opacity flags, which over- and
           under-approximate in both directions. *)
        let is_dropped =
          is_external
          && List.for_all
               (fun b ->
                 (* Every SCC bucket has members by construction
                    ({!FileGraph.compute} builds the SCCs from the member
                    map's keys), so a missing entry is a broken invariant. *)
                 List.for_all is_builtin
                   ([%silent_unwrap_opt_span] None
                      (BucketMap.find_opt b fg.members)))
               buckets
        in
        let base_components =
          if is_external then
            let suffix =
              if
                List.exists
                  (function
                    | BExternalFuns -> true
                    | _ -> false)
                  buckets
              then "FunsExternal"
              else "TypesExternal"
            in
            [ suffix ]
          else
            match buckets with
            | [ BFile p ] -> FileMapping.module_components_of_file p
            | _ ->
                let idx = !merge_counter in
                incr merge_counter;
                FileMapping.merged_module_components idx
        in
        let import_name =
          import_prefix ^ FileMapping.dotted_module_name base_components
        in
        let groups =
          Option.value (SCC.SccId.Map.find_opt scc_id groups_by_scc) ~default:[]
        in
        let runs = if is_dropped then [] else cut_layers color groups in
        let aggregator, layers =
          match runs with
          | [] -> (None, [])
          | [ (is_template, groups) ] ->
              (* Uniform opacity: a single file at the plain name (a
                 [_Template] one if the whole module is opaque — the
                 [FunsExternal] convention). *)
              ( None,
                [
                  {
                    is_template;
                    import_name;
                    filename = file_of_components ~is_template base_components;
                    groups;
                  };
                ] )
          | runs ->
              let layers =
                List.mapi
                  (fun i (is_template, groups) ->
                    let components =
                      FileMapping.layer_module_components base_components
                        ~is_template ~index:(i + 1)
                    in
                    {
                      is_template;
                      import_name =
                        import_prefix
                        ^ FileMapping.dotted_module_name components;
                      filename = file_of_components ~is_template components;
                      groups;
                    })
                  runs
              in
              ( Some (file_of_components ~is_template:false base_components),
                layers )
        in
        {
          scc_id;
          buckets;
          is_external;
          is_dropped;
          import_name;
          aggregator;
          layers;
        })
      scc_list
  in
  (* Guard against module-name collisions, over every emitted file: plain
     module names (aggregators/single files), synthesized layer names, and
     filled-template names. [StringUtils.to_camel_case] strips underscores (so
     [src/foo_bar.rs] and a [#[path]]-mapped [src/fooBar.rs] both become
     [FooBar]), and synthesized names ([MergeN], [PartK], [AxiomsK]) can also
     be produced by real source files. Two files sharing an import name would
     have the emitter's second [open_out] silently truncate the first, so fail
     loudly instead. Dropped modules emit nothing and are skipped. *)
  let describe (m : placed_module) : string =
    String.concat " + " (List.map display_bucket m.buckets)
  in
  let (_ : (placed_module * string) Collections.StringMap.t) =
    List.fold_left
      (fun seen (m : placed_module) ->
        let entries =
          (match m.aggregator with
          | Some filename -> [ (m.import_name, filename) ]
          | None -> [])
          @ List.map
              (fun (l : placed_layer) -> (l.import_name, l.filename))
              m.layers
        in
        List.fold_left
          (fun seen (import_name, filename) ->
            match Collections.StringMap.find_opt import_name seen with
            | Some ((prev : placed_module), _) ->
                [%craise_opt_span] None
                  (Printf.sprintf
                     "Module-name collision in -split-files: %s and %s both \
                      map to the Lean module [%s] (file %s). Rename one of the \
                      Rust sources so their camel-cased module names differ."
                     (describe prev) (describe m) import_name filename)
            | None -> Collections.StringMap.add import_name (m, filename) seen)
          seen entries)
      Collections.StringMap.empty placed
  in
  placed

(** Render the generated-files section of the [-dump-file-graph] report: exactly
    the files the [-split-files] emitter will write (dropped builtin-only
    external modules excluded), with the opacity layering. *)
let render_placement (placed : placed_module list) : string =
  let buf = Buffer.create 256 in
  let line fmt =
    Printf.ksprintf (fun s -> Buffer.add_string buf (s ^ "\n")) fmt
  in
  let modules =
    List.filter (fun (m : placed_module) -> not m.is_dropped) placed
  in
  let file_count =
    List.fold_left
      (fun n (m : placed_module) ->
        n + List.length m.layers + if m.aggregator = None then 0 else 1)
      0 modules
  in
  line "================ GENERATED FILES (-split-files) ================";
  line "The %d file(s) the emitter will write:" file_count;
  line "";
  List.iter
    (fun (m : placed_module) ->
      let role =
        if m.is_external then "external declarations"
        else
          let src = String.concat " + " (List.map display_bucket m.buckets) in
          if List.length m.buckets > 1 then "merged: " ^ src else src
      in
      line "  %s" m.import_name;
      line "      %s" role;
      (match m.aggregator with
      | Some filename -> line "      file: %s (aggregator)" filename
      | None -> ());
      List.iter
        (fun (l : placed_layer) ->
          line "      file: %s%s" l.filename
            (if l.is_template then "  (template)" else ""))
        m.layers)
    modules;
  line "=======================================================================";
  Buffer.contents buf

(** Unit tests for {!cut_layers}: ['t']/['o']/['c'] mark
    transparent/opaque/colorless test groups. *)
let () =
  let color (c : char) : group_color =
    match c with
    | 'o' -> ColorOpaque
    | 'c' -> Colorless
    | _ -> ColorTransparent
  in
  let cut (s : string) =
    cut_layers color (List.init (String.length s) (String.get s))
  in
  assert (cut "" = []);
  assert (cut "tt" = [ (false, [ 't'; 't' ]) ]);
  assert (cut "o" = [ (true, [ 'o' ]) ]);
  assert (cut "tot" = [ (false, [ 't' ]); (true, [ 'o' ]); (false, [ 't' ]) ]);
  assert (cut "ttoo" = [ (false, [ 't'; 't' ]); (true, [ 'o'; 'o' ]) ]);
  (* Colorless groups attach to the current run without cutting one. *)
  assert (cut "tco" = [ (false, [ 't'; 'c' ]); (true, [ 'o' ]) ]);
  (* A colorless prefix attaches to the first colored run, whatever its
     color. *)
  assert (cut "cto" = [ (false, [ 'c'; 't' ]); (true, [ 'o' ]) ]);
  assert (cut "co" = [ (true, [ 'c'; 'o' ]) ]);
  (* No colored group at all: a single regenerated layer. *)
  assert (cut "cc" = [ (false, [ 'c'; 'c' ]) ])
