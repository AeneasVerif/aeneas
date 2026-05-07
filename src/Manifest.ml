(** Emit a [manifest.json] file alongside the extracted Lean files.

    The manifest lists every Lean function declaration produced by Aeneas (the
    main function plus any loop wrapper / loop body declarations) with enough
    metadata for downstream tools (proof harnesses, audit dashboards, IDE
    plugins, …) to map back to the original Rust item.

    Only functions are included in this version of the manifest. Types, traits,
    trait impls and globals are out of scope; the schema can be extended later
    without breaking existing consumers. *)

open Pure
module A = LlbcAst
module Meta = Charon.Meta

type loc = { line : int; col : int }
type source_loc = { file : string; begin_loc : loc; end_loc : loc }

type loop_info = {
  loop_id_idx : int;  (** [LoopId.id] reified to a plain int *)
  loop_pos : int list;
  is_body : bool;
}

type trait_info = {
  trait_pattern : string;
  method_name : string;
  has_default : bool option;
}

type entry = {
  lean_id : string;
  rust_pattern : string;
  is_local : bool;
  is_public : bool;
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

(** Describes where the generated Lean files landed and how that location
    relates to the Rust crate they came from. *)
type output_info = {
  dest_dir : string;
      (** Path to the directory the user passed to [-dest]. Each
          [entry.lean_file] is relative to this. *)
  subdir : string option;
      (** Value of the [-subdir] option, if any. When set, the Lean files
          actually live under [dest_dir/subdir/]. *)
  lean_files : string list;
      (** Every Lean file that was written, in emission order. Paths are
          relative to [dest_dir] (so they include [subdir/] when set), and are
          basenames in single-file mode. *)
  llbc_file : string;  (** Path to the [.llbc] input that was given to Aeneas. *)
}

type envelope = {
  aeneas_version : string;
  crate_name : string;
  output : output_info;
  functions : entry list;
}

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
  let base =
    [
      ("trait_pattern", `String ti.trait_pattern);
      ("method", `String ti.method_name);
    ]
  in
  let base =
    match ti.has_default with
    | None -> base
    | Some b -> base @ [ ("has_default", `Bool b) ]
  in
  `Assoc base

let entry_to_json (e : entry) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "lean_id" (`String e.lean_id);
  push "rust_pattern" (`String e.rust_pattern);
  push "is_local" (`Bool e.is_local);
  push "is_public" (`Bool e.is_public);
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
    ]

(* ------------------------------------------------------------------------ *)
(* Helpers to build entries from Pure.fun_decl values                       *)
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

(** Derive the kind string for a [Pure.fun_decl] entry, taking into account
    whether the declaration is the main function or a loop wrapper / body. *)
let kind_of_def (def : fun_decl) : string =
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

let trait_info_of_src (lookup_trait_pattern : trait_decl_id -> string)
    (src : item_source) : trait_info option =
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
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Yojson.Basic.pretty_to_channel out (envelope_to_json env);
  output_char out '\n';
  close_out out
