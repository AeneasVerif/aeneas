(** Emit a [manifest.json] file alongside the extracted backend output.

    The manifest lists every Lean function, type and global declaration produced
    by Aeneas with metadata mapping each item back to the original Rust source.
    It is a sidecar contract for downstream tooling (proof harnesses, audit
    dashboards, IDE plugins) that would otherwise have to reparse the generated
    Lean to recover information already on hand at extraction time.

    Trait declarations are deliberately out of scope for this version (their
    schema requires more design due to generics, parent bounds and associated
    items). The schema can be extended without breaking existing consumers. *)

module Meta = Charon.Meta

(* ------------------------------------------------------------------------ *)
(* Schema                                                                   *)
(* ------------------------------------------------------------------------ *)

type loc = { line : int; col : int }
type source_loc = { file : string; begin_loc : loc; end_loc : loc }

type loop_info = {
  loop_id_idx : int;  (** [LoopId.id] reified to a plain int *)
  loop_pos : int list;
  is_body : bool;
}

type trait_info = {
  trait_pattern : string option;
      (** [None] when the pattern computation failed. *)
  method_name : string;
  has_default : bool option;
}

(** One emitted Lean function declaration.

    Field omission convention on the JSON side:
    - [is_global_initializer]: emitted only when [true]
    - [loop_info], [parent_lean_id], [trait_info]: emitted only when [Some]
    - [num_loops]: emitted only on non-loop entries
    - [attrs]: emitted only when non-empty
    - [lang_item], [rust_pattern]: emitted only when [Some]
    - all other fields are always emitted

    Consumers should treat absence as the corresponding default. *)
type entry = {
  def_id : int;
  lean_id : string;
  rust_pattern : string option;
  is_local : bool;
  is_public : bool;
  has_body : bool;
  is_opaque : bool;
  kind : string;
  is_global_initializer : bool;
  loop_info : loop_info option;
  parent_lean_id : string option;
  num_loops : int option;
  lean_file : string;
  source : source_loc;
  attrs : string list;
  lang_item : string option;
  trait_info : trait_info option;
}

(** One emitted Lean type declaration. *)
type type_entry = {
  def_id : int;
  lean_id : string;
  rust_pattern : string option;
  is_local : bool;
  is_public : bool;
  kind : string;  (** "struct" | "enum" | "opaque" *)
  lean_file : string;
  source : source_loc;
  attrs : string list;
  lang_item : string option;
}

(** One emitted Lean global declaration. *)
type global_entry = {
  def_id : int;
  lean_id : string;
  rust_pattern : string option;
  is_local : bool;
  is_public : bool;
  init_def_id : int;
      (** [FunDeclId] of the synthetic initializer function (also present in
          [functions[]] with [is_global_initializer = true]). *)
  lean_file : string;
  source : source_loc;
  attrs : string list;
  lang_item : string option;
}

(** Describes where the generated backend files landed and how that location
    relates to the Rust crate they came from. *)
type output_info = {
  dest_dir : string;
      (** Path to the directory the user passed to [-dest]. Each [lean_file]
          field is relative to this. *)
  subdir : string option;
      (** Value of the [-subdir] option, if any. When set, the backend files
          actually live under [dest_dir/subdir/]. *)
  lean_files : string list;
      (** Every backend file that was written, in emission order, as paths
          relative to [dest_dir]. *)
  llbc_file : string;  (** Path to the [.llbc] input that was given to Aeneas. *)
}

type envelope = {
  aeneas_version : string;
  crate_name : string;
  output : output_info;
  functions : entry list;
  types : type_entry list;
  globals : global_entry list;
}

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(* ------------------------------------------------------------------------ *)

(** Accumulator carried by [extraction_ctx] throughout extraction. Each
    [extract_file] call updates the per-file fields; each emitted declaration
    appends to the per-kind list. The fields are stored in reverse order (newest
    first) and reversed at envelope-build time. *)
type state = {
  mutable function_entries : entry list;
  mutable type_entries : type_entry list;
  mutable global_entries : global_entry list;
  mutable lean_files : string list;
  mutable current_lean_file : string;
  mutable current_lean_namespace : string;
  dest_dir : string;
}

let make_state ~(dest_dir : string) : state =
  {
    function_entries = [];
    type_entries = [];
    global_entries = [];
    lean_files = [];
    current_lean_file = "";
    current_lean_namespace = "";
    dest_dir;
  }

(* ------------------------------------------------------------------------ *)
(* Schema-level helpers                                                     *)
(* ------------------------------------------------------------------------ *)

let file_name_to_string (fn : Meta.file_name) : string =
  match fn with
  | Virtual s | Local s | NotReal s -> s

let span_to_source (span : Meta.span) : source_loc =
  let d = span.data in
  {
    file = file_name_to_string d.file.name;
    begin_loc = { line = d.beg_loc.line; col = d.beg_loc.col };
    end_loc = { line = d.end_loc.line; col = d.end_loc.col };
  }

let attr_info_to_strings (ai : Meta.attr_info) : string list =
  let attr_to_string (a : Meta.attribute) : string option =
    match a with
    | AttrOpaque -> Some "charon::opaque"
    | AttrExclude -> Some "charon::exclude"
    | AttrRename s -> Some ("charon::rename(" ^ s ^ ")")
    | AttrVariantsPrefix s -> Some ("charon::variants_prefix(" ^ s ^ ")")
    | AttrVariantsSuffix s -> Some ("charon::variants_suffix(" ^ s ^ ")")
    | AttrDocComment _ -> None
    | AttrUnknown { path; args = None } -> Some path
    | AttrUnknown { path; args = Some a } -> Some (path ^ "(" ^ a ^ ")")
  in
  List.filter_map attr_to_string ai.attributes

(** Derive the [kind] string for a [Pure.fun_decl] entry. Loop wrappers and
    bodies (where [loop_id <> None]) override the [src]-derived kind.

    PrePasses' [remove_vtables] strips three of the five VTable variants before
    extraction; the remaining two ([VTableInstanceMonoItem],
    [VTableMethodPreShimItem]) are kept defensively. *)
let kind_of_def (def : Pure.fun_decl) : string =
  match def.loop_id with
  | Some (_, true) -> "loop_body"
  | Some (_, false) -> "loop"
  | None -> (
      match def.src with
      | TopLevelItem -> "top_level"
      | ClosureItem _ -> "closure"
      | TraitDeclItem _ -> "trait_decl_method"
      | TraitImplItem _ -> "trait_impl_method"
      | VTableTyItem _ -> "vtable_ty"
      | VTableInstanceItem _ -> "vtable_instance"
      | VTableMethodShimItem -> "vtable_method_shim"
      | VTableInstanceMonoItem -> "vtable_instance_mono"
      | VTableMethodPreShimItem _ -> "vtable_method_pre_shim")

let kind_of_type_decl (def : Pure.type_decl) : string =
  match def.kind with
  | Struct _ -> "struct"
  | Enum _ -> "enum"
  | Opaque -> "opaque"

let trait_info_of_src
    (lookup_trait_pattern : Pure.trait_decl_id -> string option)
    (src : Pure.item_source) : trait_info option =
  match src with
  | TraitDeclItem (tref, name, has_default) ->
      Some
        {
          trait_pattern = lookup_trait_pattern tref.id;
          method_name = name;
          has_default = Some has_default;
        }
  | TraitImplItem (_, tref, name, _) ->
      Some
        {
          trait_pattern = lookup_trait_pattern tref.id;
          method_name = name;
          has_default = None;
        }
  | _ -> None

(* ------------------------------------------------------------------------ *)
(* Conversions to JSON                                                      *)
(* ------------------------------------------------------------------------ *)

let loc_to_json (l : loc) : Yojson.Basic.t =
  `Assoc [ ("line", `Int l.line); ("col", `Int l.col) ]

let source_to_json (s : source_loc) : Yojson.Basic.t =
  `Assoc
    [
      ("file", `String s.file);
      ("begin", loc_to_json s.begin_loc);
      ("end", loc_to_json s.end_loc);
    ]

let loop_to_json (li : loop_info) : Yojson.Basic.t =
  `Assoc
    [
      ("id", `Int li.loop_id_idx);
      ("pos", `List (List.map (fun i -> `Int i) li.loop_pos));
      ("is_body", `Bool li.is_body);
    ]

let trait_to_json (ti : trait_info) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  (match ti.trait_pattern with
  | None -> ()
  | Some s -> push "trait_pattern" (`String s));
  push "method" (`String ti.method_name);
  (match ti.has_default with
  | None -> ()
  | Some b -> push "has_default" (`Bool b));
  `Assoc (List.rev !fields)

let entry_to_json (e : entry) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "def_id" (`Int e.def_id);
  push "lean_id" (`String e.lean_id);
  (match e.rust_pattern with
  | None -> ()
  | Some s -> push "rust_pattern" (`String s));
  push "is_local" (`Bool e.is_local);
  push "is_public" (`Bool e.is_public);
  push "has_body" (`Bool e.has_body);
  push "is_opaque" (`Bool e.is_opaque);
  push "kind" (`String e.kind);
  if e.is_global_initializer then push "is_global_initializer" (`Bool true);
  (match e.loop_info with
  | None -> ()
  | Some li -> push "loop" (loop_to_json li));
  (match e.parent_lean_id with
  | None -> ()
  | Some p -> push "parent_lean_id" (`String p));
  (match e.num_loops with
  | None -> ()
  | Some n -> push "num_loops" (`Int n));
  push "lean_file" (`String e.lean_file);
  push "source" (source_to_json e.source);
  if e.attrs <> [] then
    push "attrs" (`List (List.map (fun s -> `String s) e.attrs));
  (match e.lang_item with
  | None -> ()
  | Some s -> push "lang_item" (`String s));
  (match e.trait_info with
  | None -> ()
  | Some ti -> push "trait" (trait_to_json ti));
  `Assoc (List.rev !fields)

let type_entry_to_json (e : type_entry) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "def_id" (`Int e.def_id);
  push "lean_id" (`String e.lean_id);
  (match e.rust_pattern with
  | None -> ()
  | Some s -> push "rust_pattern" (`String s));
  push "is_local" (`Bool e.is_local);
  push "is_public" (`Bool e.is_public);
  push "kind" (`String e.kind);
  push "lean_file" (`String e.lean_file);
  push "source" (source_to_json e.source);
  if e.attrs <> [] then
    push "attrs" (`List (List.map (fun s -> `String s) e.attrs));
  (match e.lang_item with
  | None -> ()
  | Some s -> push "lang_item" (`String s));
  `Assoc (List.rev !fields)

let global_entry_to_json (e : global_entry) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "def_id" (`Int e.def_id);
  push "lean_id" (`String e.lean_id);
  (match e.rust_pattern with
  | None -> ()
  | Some s -> push "rust_pattern" (`String s));
  push "is_local" (`Bool e.is_local);
  push "is_public" (`Bool e.is_public);
  push "init_def_id" (`Int e.init_def_id);
  push "lean_file" (`String e.lean_file);
  push "source" (source_to_json e.source);
  if e.attrs <> [] then
    push "attrs" (`List (List.map (fun s -> `String s) e.attrs));
  (match e.lang_item with
  | None -> ()
  | Some s -> push "lang_item" (`String s));
  `Assoc (List.rev !fields)

let output_to_json (o : output_info) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "dest_dir" (`String o.dest_dir);
  (match o.subdir with
  | None -> ()
  | Some s -> push "subdir" (`String s));
  push "llbc_file" (`String o.llbc_file);
  push "lean_files" (`List (List.map (fun s -> `String s) o.lean_files));
  `Assoc (List.rev !fields)

let envelope_to_json (env : envelope) : Yojson.Basic.t =
  `Assoc
    [
      ("aeneas_version", `String env.aeneas_version);
      ("crate", `String env.crate_name);
      ("output", output_to_json env.output);
      ("functions", `List (List.map entry_to_json env.functions));
      ("types", `List (List.map type_entry_to_json env.types));
      ("globals", `List (List.map global_entry_to_json env.globals));
    ]

(* ------------------------------------------------------------------------ *)
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let envelope_of_state ~(aeneas_version : string) ~(crate_name : string)
    ~(subdir : string option) ~(llbc_file : string) (s : state) : envelope =
  {
    aeneas_version;
    crate_name;
    output =
      {
        dest_dir = s.dest_dir;
        subdir;
        llbc_file;
        lean_files = List.rev s.lean_files;
      };
    functions = List.rev s.function_entries;
    types = List.rev s.type_entries;
    globals = List.rev s.global_entries;
  }

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Yojson.Basic.pretty_to_channel out (envelope_to_json env);
  output_char out '\n';
  close_out out
