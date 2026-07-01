(** Placement plan for [-split-files]: which Lean module/file each SCC of the
    file-dependency graph becomes. Used by the the emitter
    ({!Translate.extract_by_file}) and the [-dump-file-graph] diagnostic. *)

open FileGraph

(** One generated Lean module in [-split-files] mode. *)
type placed_module = {
  scc_id : SCC.SccId.id;
  buckets : bucket list;  (** The source-file/external buckets in this SCC. *)
  is_external : bool;
      (** [true] for the external template modules ([TypesExternal] /
          [FunsExternal]). *)
  is_dropped : bool;
      (** [true] for external modules whose referenced declarations are all
          builtins: we neither emit a (empty) template file for them nor import
          them from local modules. *)
  import_name : string;  (** Dotted Lean module name, e.g. [Crate.Foo]. *)
  filename : string;  (** On-disk path the emitter writes. *)
}

(** The on-disk root the generated modules live under. With [-subdir] that
    directory is already [full_dest_dir]; otherwise we nest under [crate_name]
    so that [-dest D] yields a self-contained [D/Crate/...] tree plus a
    [D/Crate.lean] entry point. *)
let module_root_dir ~(full_dest_dir : string) ~(crate_name : string) : string =
  match !Config.subdir with
  | Some _ -> full_dest_dir
  | None -> Filename.concat full_dest_dir crate_name

(** Resolve every SCC of the file graph to its Lean module identity, in
    topological (dependency-first) order. Merge indices are allocated to
    multi-bucket local SCCs in that order. *)
let place_by_file (fg : FileGraph.t) ~(crate : LlbcAst.crate)
    ~(import_prefix : string) ~(module_root_dir : string) ~(ext : string) :
    placed_module list =
  let scc_list = SCC.SccId.Map.bindings fg.sccs.sccs in
  let is_builtin = LlbcAstUtils.item_is_builtin crate in
  let merge_counter = ref 0 in
  List.map
    (fun (scc_id, buckets) ->
      (* Only the external buckets are emitted as interface/template files. *)
      let is_external =
        List.exists
          (function
            | BExternalTypes | BExternalFuns -> true
            | BFile _ -> false)
          buckets
      in
      (* An external SCC has nothing to emit iff all its declarations are
         builtins (resolved via [import Aeneas]): dropping it avoids an empty
         template file and a dangling import. Decide from the actual members,
         not the crate-global opacity flags, which over- and under-approximate
         in both directions. *)
      let is_dropped =
        is_external
        && List.for_all
             (fun b ->
               List.for_all is_builtin
                 (Option.value (BucketMap.find_opt b fg.members) ~default:[]))
             buckets
      in
      let import_name, filename =
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
          ( import_prefix ^ suffix,
            module_root_dir ^ "/" ^ suffix ^ "_Template" ^ ext )
        else
          let components =
            match buckets with
            | [ BFile p ] -> FileMapping.module_components_of_file p
            | _ ->
                let idx = !merge_counter in
                incr merge_counter;
                FileMapping.merged_module_components idx
          in
          ( import_prefix ^ FileMapping.dotted_module_name components,
            module_root_dir ^ "/" ^ FileMapping.lean_file_subpath components )
      in
      { scc_id; buckets; is_external; is_dropped; import_name; filename })
    scc_list

(** Render the generated-files section of the [-dump-file-graph] report: exactly
    the files the [-split-files] emitter will write (dropped builtin-only
    external modules excluded). *)
let render_placement (placed : placed_module list) : string =
  let buf = Buffer.create 256 in
  let line fmt =
    Printf.ksprintf (fun s -> Buffer.add_string buf (s ^ "\n")) fmt
  in
  let files =
    List.filter (fun (m : placed_module) -> not m.is_dropped) placed
  in
  line "================ GENERATED FILES (-split-files) ================";
  line "The %d file(s) the emitter will write:" (List.length files);
  line "";
  List.iter
    (fun (m : placed_module) ->
      let role =
        if m.is_external then "external declarations (template)"
        else
          let src = String.concat " + " (List.map display_bucket m.buckets) in
          if List.length m.buckets > 1 then "merged: " ^ src else src
      in
      line "  %s" m.import_name;
      line "      file: %s" m.filename;
      line "      %s" role)
    files;
  line "=======================================================================";
  Buffer.contents buf
