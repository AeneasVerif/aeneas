(** The placement plan for [-split-files]: which Lean files we write for each
    strongly connected component of the file graph ({!FileGraph}). Used by the
    emitter ({!Translate.extract_by_file}) and by [-dump-file-graph]. *)

open FileGraph

(** One Lean file of a {!component}. Most components have a single layer. A
    component whose opaque and transparent declarations depend on each other in
    alternation needs several. *)
type component_layer = {
  is_template : bool;
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
