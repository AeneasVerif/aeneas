(** The interface between the extraction driver ({!Translate}) and the file
    layouts.

    A {e layout} decides which files the extraction writes and what goes into
    each of them. It does not write anything: it is given an {!env} describing
    the translated crate, and returns a {!plan}, the list of the files to write.
    The driver then writes the plan ({!Translate.write_plan}), without knowing
    which layout produced it.

    The layouts are the modules implementing {!S}:
    - {!FileLayoutSingle}: everything in a single file (the default)
    - {!FileLayoutByKind}: the legacy split ([Types], [Funs], [TypesExternal],
      [FunsExternal], ...), for [-split-files-legacy]
    - {!FileLayoutByModule}: one Lean module per Rust module, for [-split-files]

    {!FileLayoutRegistry.of_config} picks one from the CLI options.

    {b Adding a layout}: write a module implementing {!S} and add it to
    {!FileLayoutRegistry}. Nothing else has to change.

    {b Adding data to extract}: the layouts get the translated crate as a record
    ({!env.translated}) and describe the contents of a file with records and a
    variant ({!decl_filter}, {!definitions}, {!contents}), which they build from
    {!no_decls} and {!all_decls}. If the translation produces a new kind of
    data:
    - if it goes into the files that hold the definitions, add a flag to
      {!decl_filter} (and to {!no_decls} and {!all_decls}): the layouts which
      extract everything pick it up, the others opt in;
    - if it needs files of its own, add a constructor to {!contents}, and handle
      it in {!Translate.write_plan}. *)

open TranslateCore

(** The local logger *)
let log = Logging.translate_log

(** {1 The input of a layout} *)

(** What a layout knows about the crate to extract.

    The layouts read the CLI options which only concern them directly from
    {!Config}; this record holds what the driver computed. *)
type env = {
  crate : LlbcAst.crate;
  trans_ctx : trans_ctx;
  translated : translated_crate;  (** The definitions to extract. *)
  file_graph : FileGraph.t Lazy.t;
      (** The dependency graph between the Rust modules of the crate, computed
          on demand. *)
  crate_name : string;
      (** The name of the crate, as used in file and module names (camel case).
      *)
  namespace : string;  (** The namespace the definitions are extracted in. *)
  dest_dir : string;  (** The output directory ([-dest]). *)
  subdir : string option;  (** [-subdir], if provided. *)
  full_dest_dir : string;
      (** The directory for the generated definitions: [dest_dir], or
          [dest_dir/subdir] with [-subdir]. *)
  import_prefix : string;
      (** The prefix of the names of the generated modules, delimiter included
          (e.g. [Crate.]). *)
}

(** {1 The output of a layout} *)

(** Which declarations a file holds, among the declaration groups it is given
    (see {!definitions.groups}).

    Build values of this type from {!no_decls} or {!all_decls}. *)
type decl_filter = {
  extract_types : bool;
  extract_decreases_clauses : bool;
  extract_template_decreases_clauses : bool;
  extract_fun_decls : bool;
  extract_trait_decls : bool;
  extract_trait_impls : bool;
  extract_transparent : bool;
      (** If [true], extract the transparent declarations, otherwise ignore. *)
  extract_opaque : bool;
      (** If [true], extract the opaque declarations, otherwise ignore.

          For now, this controls only the opaque *functions*, not the opaque
          globals or types. TODO: update this. This is not trivial if we want to
          extract the opaque types in an opaque module, because some non-opaque
          types may refer to opaque types and vice-versa. *)
  extract_globals : bool;
      (** If [true], generate a definition/declaration for top-level (global)
          declarations *)
  interface : bool;
      (** [true] if we generate an interface file, [false] otherwise. For now,
          this only impacts whether we use [val] or [assume val] for the opaque
          definitions. In the future, we might want to extract all the
          declarations in an interface file, together with an implementation
          file if needed. *)
}

(** The filter which extracts nothing. *)
let no_decls : decl_filter =
  {
    extract_types = false;
    extract_decreases_clauses = false;
    extract_template_decreases_clauses = false;
    extract_fun_decls = false;
    extract_trait_decls = false;
    extract_trait_impls = false;
    extract_transparent = false;
    extract_opaque = false;
    extract_globals = false;
    interface = false;
  }

(** The filter which extracts everything, with the decreases clauses the user
    asked for. *)
let all_decls () : decl_filter =
  {
    extract_types = true;
    extract_decreases_clauses = !Config.extract_decreases_clauses;
    extract_template_decreases_clauses =
      !Config.extract_template_decreases_clauses;
    extract_fun_decls = true;
    extract_trait_decls = true;
    extract_trait_impls = true;
    extract_transparent = true;
    extract_opaque = true;
    extract_globals = true;
    interface = false;
  }

(** A file of extracted definitions. *)
type definitions = {
  header : string;
      (** A message for the header of the file, after the name of the crate
          (e.g. [": type definitions"]). *)
  groups : LlbcAst.declaration_group list option;
      (** The declaration groups to extract, in order. [None] stands for all the
          groups of the crate. *)
  filter : decl_filter;  (** What we extract from [groups]. *)
  in_namespace : bool;
      (** Whether the definitions are inside the namespace of the crate
          ({!env.namespace}). *)
  open_namespace : bool;  (** Whether the file opens that namespace. *)
  noncomputable : bool;
      (** If [true] we insert a [noncomputable section] instruction at the top
          of the file *)
}

(** What a file contains. *)
type contents =
  | Definitions of definitions
  | ImportsOnly of { header : string option }
      (** Only the imports of the file ({!file.imports}), for instance for an
          entry point. [header] is as in {!definitions.header}; with [None] the
          file has no header at all. *)

(** A file to write. *)
type file = {
  path : string;  (** Where we write it. Its directory is created if needed. *)
  module_name : string;  (** The name of the module the file defines. *)
  imports : string list;  (** The modules it imports. *)
  includes : string list;
      (** The modules it imports and re-exports (in the backends which make a
          difference). They come after [imports]. *)
  contents : contents;
  protect_user_file : bool;
      (** If [true], we refuse to overwrite an existing file which was not
          generated by Aeneas. *)
}

(** The result of a layout. *)
type layout = {
  files : file list;
      (** The files to write, in this order. A file comes after the files it
          imports. *)
  report : string Lazy.t option;
      (** A description of the plan for [-dump-file-graph], if the layout has
          more to say than the list of files. *)
}

(** {1 The signature of a layout} *)

module type S = sig
  (** The name of the layout, for the logs. *)
  val name : string

  (** Decide which files to write. This doesn't write anything. *)
  val plan : env -> layout
end

type t = (module S)

(** {1 Helpers for the layouts} *)

(** The separator in the names of the generated modules. *)
let module_delimiter () : string =
  match Config.backend () with
  | FStar -> "."
  | Coq -> "_"
  | Lean -> "."
  | HOL4 -> "_"

(** The separator between the components of a module name in the path of its
    file: in Lean, a module is in a subdirectory. *)
let file_delimiter () : string =
  if Config.backend () = Lean then "/" else module_delimiter ()

(** The extension of the regular files. *)
let file_ext () : string =
  match Config.backend () with
  | FStar -> ".fst"
  | Coq -> ".v"
  | Lean -> ".lean"
  | HOL4 -> "Script.sml"

(** The extension of the files holding the opaque declarations. *)
let interface_ext () : string =
  match Config.backend () with
  | FStar -> ".fsti"
  | Coq -> ".v"
  | Lean -> ".lean"
  | HOL4 -> "Script.sml"

(** Returns the pair: (has opaque type decls, has opaque fun decls), where we
    ignore the external definitions that we map to definitions from the standard
    library. We need this to know whether to generate interface files, etc. *)
let has_opaque_decls (env : env) : bool * bool =
  let types, funs =
    LlbcAstUtils.crate_get_opaque_non_builtin_decls env.crate true
      env.trans_ctx.type_ctx.to_extract env.trans_ctx.fun_ctx.to_extract
  in
  [%ldebug
    "- opaque types:\n"
    ^ String.concat "\n\n"
        (List.map
           (fun (d : Types.type_decl) ->
             name_to_string env.trans_ctx d.item_meta.name)
           types)
    ^ "\n\n- opaque funs:\n"
    ^ String.concat "\n\n"
        (List.map
           (fun (d : LlbcAst.fun_decl) ->
             name_to_string env.trans_ctx d.item_meta.name)
           funs)];
  (types <> [], funs <> [])

(** Whether the definitions of a file which contains or imports opaque
    declarations must be marked as noncomputable. *)
let noncomputable_if_opaque (has_opaque : bool) : bool =
  has_opaque && not !Config.all_computable
