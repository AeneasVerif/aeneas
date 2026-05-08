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
(*                                                                          *)
(* The state lives as a module-local ref rather than as a field on          *)
(* [extraction_ctx], so this feature touches no upstream record types. One  *)
(* aeneas process translates one crate, so a singleton is appropriate.      *)
(* Lifecycle: [init] at the start of [extract_translated_crate],            *)
(* [begin_file] at the top of every [extract_file], [record_*] called from  *)
(* the export-* hooks, [write_if_enabled] once at the end.                  *)
(* ------------------------------------------------------------------------ *)

type state = {
  mutable function_entries : entry list;
  mutable type_entries : type_entry list;
  mutable global_entries : global_entry list;
  mutable lean_files : string list;
  mutable current_lean_file : string;
  mutable current_lean_namespace : string;
  mutable dest_dir : string;
}

let make_state () : state =
  {
    function_entries = [];
    type_entries = [];
    global_entries = [];
    lean_files = [];
    current_lean_file = "";
    current_lean_namespace = "";
    dest_dir = "";
  }

(** The singleton accumulator. Reset at the top of [extract_translated_crate]
    via [init]; mutated through [begin_file] and the [record_*] helpers. *)
let state : state = make_state ()

let init ~(dest_dir : string) : unit =
  state.function_entries <- [];
  state.type_entries <- [];
  state.global_entries <- [];
  state.lean_files <- [];
  state.current_lean_file <- "";
  state.current_lean_namespace <- "";
  state.dest_dir <- dest_dir

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
(* Entry construction (depends on ExtractBase / TranslateCore)              *)
(* ------------------------------------------------------------------------ *)

(** Try to compute a name's [rust_pattern]. Returns [None] when the pattern
    computation raises [CFailure], so callers can omit the field rather than
    emit an empty-string fallback. *)
let try_name_to_pattern_string (span : Charon.Meta.span option)
    (trans_ctx : TranslateCore.trans_ctx) (name : Charon.Types.name) :
    string option =
  try Some (TranslateCore.name_to_pattern_string span trans_ctx name)
  with Errors.CFailure _ -> None

let qualify (basename : string) : string =
  if state.current_lean_namespace = "" then basename
  else state.current_lean_namespace ^ "." ^ basename

let entry_of_fun_decl (ctx : ExtractBase.extraction_ctx) (def : Pure.fun_decl) :
    entry =
  let span = def.item_meta.span in
  let lean_id =
    qualify (ExtractBase.ctx_get_local_function span def.def_id def.loop_id ctx)
  in
  let parent_lean_id =
    match def.loop_id with
    | None -> None
    | Some _ ->
        Some
          (qualify
             (ExtractBase.ctx_get_local_function span def.def_id None ctx))
  in
  let rust_pattern =
    try_name_to_pattern_string (Some span) ctx.trans_ctx def.item_meta.name
  in
  let loop_info : loop_info option =
    match def.loop_id with
    | None -> None
    | Some (lid, is_body) ->
        Some
          {
            loop_id_idx = Pure.LoopId.to_int lid;
            loop_pos = def.loop_pos;
            is_body;
          }
  in
  let num_loops =
    match def.loop_id with
    | None -> Some def.num_loops
    | Some _ -> None
  in
  let lookup_trait_pattern (id : Pure.trait_decl_id) : string option =
    match Pure.TraitDeclId.Map.find_opt id ctx.trans_trait_decls with
    | None -> None
    | Some d ->
        try_name_to_pattern_string (Some d.item_meta.span) ctx.trans_ctx
          d.item_meta.name
  in
  {
    def_id = Pure.FunDeclId.to_int def.def_id;
    lean_id;
    rust_pattern;
    is_local = def.item_meta.is_local;
    is_public = def.item_meta.attr_info.public;
    has_body = Option.is_some def.body;
    is_opaque = Option.is_none def.body;
    kind = kind_of_def def;
    is_global_initializer = def.is_global_decl_body;
    loop_info;
    parent_lean_id;
    num_loops;
    lean_file = state.current_lean_file;
    source = span_to_source span;
    attrs = attr_info_to_strings def.item_meta.attr_info;
    lang_item = def.item_meta.lang_item;
    trait_info = trait_info_of_src lookup_trait_pattern def.src;
  }

let type_entry_of_type_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : type_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_id = qualify (ExtractBase.ctx_get_local_type span def.def_id ctx);
    rust_pattern =
      try_name_to_pattern_string (Some span) ctx.trans_ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    is_public = def.item_meta.attr_info.public;
    kind = kind_of_type_decl def;
    lean_file = state.current_lean_file;
    source = span_to_source span;
    attrs = attr_info_to_strings def.item_meta.attr_info;
    lang_item = def.item_meta.lang_item;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_id = qualify (ExtractBase.ctx_get_global span def.def_id ctx);
    rust_pattern =
      try_name_to_pattern_string (Some span) ctx.trans_ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    is_public = def.item_meta.attr_info.public;
    init_def_id = Pure.FunDeclId.to_int def.body_id;
    lean_file = state.current_lean_file;
    source = span_to_source span;
    attrs = attr_info_to_strings def.item_meta.attr_info;
    lang_item = def.item_meta.lang_item;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when [-emit-manifest] is off)                     *)
(* ------------------------------------------------------------------------ *)

(** Record the file and namespace [extract_file] is about to write into. The
    [filename] should be the full path; we strip [state.dest_dir] to make
    [state.current_lean_file] relative. *)
let begin_file ~(filename : string) ~(namespace : string) : unit =
  if !Config.emit_manifest then begin
    let rel_lean_file =
      let dest = Filename.concat state.dest_dir "" in
      let plen = String.length dest in
      if String.length filename >= plen && String.sub filename 0 plen = dest
      then String.sub filename plen (String.length filename - plen)
      else Filename.basename filename
    in
    state.current_lean_file <- rel_lean_file;
    state.current_lean_namespace <- namespace;
    state.lean_files <- rel_lean_file :: state.lean_files
  end

let record_fun (ctx : ExtractBase.extraction_ctx) (def : Pure.fun_decl) : unit =
  if !Config.emit_manifest then
    state.function_entries <-
      entry_of_fun_decl ctx def :: state.function_entries

let record_type (ctx : ExtractBase.extraction_ctx) (def : Pure.type_decl) : unit
    =
  if !Config.emit_manifest then
    state.type_entries <- type_entry_of_type_decl ctx def :: state.type_entries

let record_global (ctx : ExtractBase.extraction_ctx) (def : Pure.global_decl) :
    unit =
  if !Config.emit_manifest then
    state.global_entries <-
      global_entry_of_global_decl ctx def :: state.global_entries

(* ------------------------------------------------------------------------ *)
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let envelope_of_state ~(aeneas_version : string) ~(crate_name : string)
    ~(subdir : string option) ~(llbc_file : string) : envelope =
  {
    aeneas_version;
    crate_name;
    output =
      {
        dest_dir = state.dest_dir;
        subdir;
        llbc_file;
        lean_files = List.rev state.lean_files;
      };
    functions = List.rev state.function_entries;
    types = List.rev state.type_entries;
    globals = List.rev state.global_entries;
  }

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Yojson.Basic.pretty_to_channel out (envelope_to_json env);
  output_char out '\n';
  close_out out

(** Convenience: write [<dest_dir>/manifest.json] (using [state.dest_dir]) only
    if [-emit-manifest] is on. *)
let write_if_enabled ~(aeneas_version : string) ~(crate_name : string)
    ~(subdir : string option) ~(llbc_file : string) : string option =
  if !Config.emit_manifest then begin
    let path = Filename.concat state.dest_dir "manifest.json" in
    write path
      (envelope_of_state ~aeneas_version ~crate_name ~subdir ~llbc_file);
    Some path
  end
  else None
