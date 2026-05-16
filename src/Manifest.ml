(** Emit a [manifest.json] file alongside the extracted Lean files.

    The manifest contains the Aeneas-only data which connects the Lean
    translation to the original Rust code. It does NOT duplicate any data
    already present in the input [.llbc] file.

    The [manifest.json] and the LLBC share the [def_id] field, as the join key
    linking each manifest entry back to its source declaration in the LLBC. *)

(* ------------------------------------------------------------------------ *)
(* Schema                                                                   *)
(*                                                                          *)
(* Each type carries [@@deriving to_yojson] so the JSON serialiser is       *)
(* auto-generated. Attributes:                                              *)
(*   [@key "name"]      – rename the JSON field                             *)
(*   [@yojson.option]   – omit the field entirely when the value is [None]  *)
(* ------------------------------------------------------------------------ *)

type loop_info = {
  loop_id_idx : int; [@key "id"]
  loop_pos : int list; [@key "pos"]
  is_body : bool;
}
[@@deriving to_yojson]

(** One emitted Lean function declaration.

    [loop] and [parent_lean_id] are present only on loop-wrapper / loop-body
    entries. Non-loop entries have neither. All other fields are always emitted.
*)
type entry = {
  def_id : int;
      (** Charon [FunDeclId] reified to a plain int. The single LLBC-derived
          field, kept as a join key. Several manifest entries can share the same
          [def_id]: a Rust fn with N loops produces 1 + 2N entries (the parent,
          plus a wrapper and body for each loop) all sharing the parent's
          [def_id]; their [lean_id] / [loop] field disambiguate. *)
  lean_id : string;
  lean_file : string;
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom (no body in
          the Pure AST). LLBC always carries a body field, so the
          opaque/non-opaque distinction is post-translation. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result] — i.e.
          the function can panic. Computed by the symbolic interpreter, not
          present in LLBC. *)
  can_diverge : bool;
      (** [true] when the function may not terminate (recursive, contains a
          loop, or transitively calls a divergent function). *)
  is_rec : bool;
      (** [true] when the function is part of a (mutually) recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]] (set by
          [PureMicroPasses.compute_reducible] for trivial wrapper bodies). *)
  loop : loop_info option; [@yojson.option] [@key "loop"]
  parent_lean_id : string option; [@yojson.option]
}
[@@deriving to_yojson]

(** One emitted Lean type declaration. The LLBC carries every other fact about a
    type Aeneas needs, so the manifest only records the join key, the chosen
    Lean name, and the file it was written into. *)
type type_entry = { def_id : int; lean_id : string; lean_file : string }
[@@deriving to_yojson]

(** One emitted Lean global declaration. [can_fail] is the only Aeneas-derived
    semantic fact (mirrors [Pure.global_decl.can_fail]). *)
type global_entry = {
  def_id : int;
  lean_id : string;
  lean_file : string;
  can_fail : bool;
}
[@@deriving to_yojson]

(** Output-routing info: where the manifest itself sits and which backend files
    Aeneas wrote, all chosen by Aeneas based on CLI flags. *)
type output_info = {
  dest_dir : string;
  subdir : string option; [@yojson.option]
  llbc_file : string;
  lean_files : string list;
}
[@@deriving to_yojson]

type envelope = {
  aeneas_version : string;
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. Aeneas only
          accepts an [.llbc] whose stamp matches the charon-ml version it was
          built against, so this is also the charon-ml version. *)
  crate_name : string; [@key "crate"]
      (** Identifier of the source Rust crate. Surfaces the LLBC's [crate.name]
          at the envelope level so the manifest is self-describing without
          requiring access to the [.llbc]. *)
  output : output_info;
  functions : entry list;
  types : type_entry list;
  globals : global_entry list;
}
[@@deriving to_yojson]

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(*                                                                          *)
(* The state lives as a module-local singleton rather than as a field on    *)
(* [extraction_ctx] so this feature touches no upstream record types. One   *)
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
(* Entry construction (depends on ExtractBase)                              *)
(* ------------------------------------------------------------------------ *)

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
  let loop =
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
  let eff = def.signature.fwd_info.effect_info in
  {
    def_id = Pure.FunDeclId.to_int def.def_id;
    lean_id;
    lean_file = state.current_lean_file;
    is_opaque = Option.is_none def.body;
    can_fail = eff.can_fail;
    can_diverge = eff.can_diverge;
    is_rec = eff.is_rec;
    reducible = def.backend_attributes.reducible;
    loop;
    parent_lean_id;
  }

let type_entry_of_type_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : type_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_id = qualify (ExtractBase.ctx_get_local_type span def.def_id ctx);
    lean_file = state.current_lean_file;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_id = qualify (ExtractBase.ctx_get_global span def.def_id ctx);
    lean_file = state.current_lean_file;
    can_fail = def.can_fail;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when [-emit-manifest] is off)                     *)
(* ------------------------------------------------------------------------ *)

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

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Yojson.Safe.pretty_to_channel out (envelope_to_yojson env);
  output_char out '\n';
  close_out out

let write_if_enabled ~(aeneas_version : string) ~(crate_name : string)
    ~(subdir : string option) ~(llbc_file : string) : string option =
  if !Config.emit_manifest then begin
    let path = Filename.concat state.dest_dir "manifest.json" in
    write path
      {
        aeneas_version;
        charon_version = Charon.CharonVersion.supported_charon_version;
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
      };
    Some path
  end
  else None
