(** Emit a [manifest.json] file alongside the extracted Lean files.

    The manifest contains the Aeneas-only data which connects the Lean translation
    to the orginal Rust code. It does NOT duplicate any data already present in 
    the input [.llbc] file.

    The [manifest.json] and the LLBC share the [def_id] field, as the join key 
    linking each manifest entry back to its source declaration in the LLBC. *)

(* ------------------------------------------------------------------------ *)
(* Schema                                                                   *)
(* ------------------------------------------------------------------------ *)

type loop_info = {
  loop_id_idx : int;  (** [LoopId.id] reified to a plain int *)
  loop_pos : int list;
  is_body : bool;
}

(** One emitted Lean function declaration.

    Field omission convention on the JSON side:
    - [loop_info], [parent_lean_id]: emitted only when [Some] (i.e. on
      loop-wrapper / loop-body entries — they identify each other)
    - [num_loops]: emitted only on non-loop entries
    - all other fields are always emitted *)
type entry = {
  def_id : int;
      (** Charon [FunDeclId] reified to a plain int. The single LLBC-derived
          field, kept as a join key. Several manifest entries can share the
          same [def_id]: a Rust fn with N loops produces 1 + 2N entries
          (the parent, plus a wrapper and body for each loop) all sharing
          the parent's [def_id]; their [lean_id] / [loop_info] disambiguate. *)
  lean_id : string;
  lean_file : string;
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom (no body
          in the Pure AST). LLBC always carries a body field, so the
          opaque/non-opaque distinction is post-translation. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result] —
          i.e. the function can panic. Computed by the symbolic interpreter,
          not present in LLBC. *)
  can_diverge : bool;
      (** [true] when the function may not terminate (recursive, contains a
          loop, or transitively calls a divergent function). *)
  is_rec : bool;
      (** [true] when the function is part of a (mutually) recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]] (set by
          [PureMicroPasses.compute_reducible] for trivial wrapper bodies). *)
  loop_info : loop_info option;
  parent_lean_id : string option;
  num_loops : int option;
}

(** One emitted Lean type declaration. The LLBC carries every fact about a
    type Aeneas needs, so the manifest only records the join key, the
    chosen Lean name, and the file it was written into. *)
type type_entry = { def_id : int; lean_id : string; lean_file : string }

(** One emitted Lean global declaration. [can_fail] is the only
    Aeneas-derived semantic fact (mirrors [Pure.global_decl.can_fail]). *)
type global_entry = {
  def_id : int;
  lean_id : string;
  lean_file : string;
  can_fail : bool;
}

(** Output-routing info: where the manifest itself sits and which backend
    files Aeneas wrote, all chosen by Aeneas based on CLI flags. *)
type output_info = {
  dest_dir : string;
  subdir : string option;
  lean_files : string list;
  llbc_file : string;  (** Path to the [.llbc] input — the join target. *)
}

type envelope = {
  aeneas_version : string;
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. Aeneas only
          accepts an [.llbc] whose stamp matches the charon-ml version it
          was built against, so this is also the charon-ml version. *)
  crate_name : string;
      (** Identifier of the source Rust crate. Surfaces the LLBC's
          [crate.name] at the envelope level so the manifest is
          self-describing without requiring access to the [.llbc]. *)
  output : output_info;
  functions : entry list;
  types : type_entry list;
  globals : global_entry list;
}

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
(* Conversions to JSON                                                      *)
(* ------------------------------------------------------------------------ *)

let loop_to_json (li : loop_info) : Yojson.Basic.t =
  `Assoc
    [
      ("id", `Int li.loop_id_idx);
      ("pos", `List (List.map (fun i -> `Int i) li.loop_pos));
      ("is_body", `Bool li.is_body);
    ]

let entry_to_json (e : entry) : Yojson.Basic.t =
  let fields = ref [] in
  let push k v = fields := (k, v) :: !fields in
  push "def_id" (`Int e.def_id);
  push "lean_id" (`String e.lean_id);
  push "lean_file" (`String e.lean_file);
  push "is_opaque" (`Bool e.is_opaque);
  push "can_fail" (`Bool e.can_fail);
  push "can_diverge" (`Bool e.can_diverge);
  push "is_rec" (`Bool e.is_rec);
  push "reducible" (`Bool e.reducible);
  (match e.loop_info with
  | None -> ()
  | Some li -> push "loop" (loop_to_json li));
  (match e.parent_lean_id with
  | None -> ()
  | Some p -> push "parent_lean_id" (`String p));
  (match e.num_loops with
  | None -> ()
  | Some n -> push "num_loops" (`Int n));
  `Assoc (List.rev !fields)

let type_entry_to_json (e : type_entry) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", `Int e.def_id);
      ("lean_id", `String e.lean_id);
      ("lean_file", `String e.lean_file);
    ]

let global_entry_to_json (e : global_entry) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", `Int e.def_id);
      ("lean_id", `String e.lean_id);
      ("lean_file", `String e.lean_file);
      ("can_fail", `Bool e.can_fail);
    ]

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
      ("charon_version", `String env.charon_version);
      ("crate", `String env.crate_name);
      ("output", output_to_json env.output);
      ("functions", `List (List.map entry_to_json env.functions));
      ("types", `List (List.map type_entry_to_json env.types));
      ("globals", `List (List.map global_entry_to_json env.globals));
    ]

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
    loop_info;
    parent_lean_id;
    num_loops;
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

let record_type (ctx : ExtractBase.extraction_ctx) (def : Pure.type_decl) :
    unit =
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
  }

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Yojson.Basic.pretty_to_channel out (envelope_to_json env);
  output_char out '\n';
  close_out out

let write_if_enabled ~(aeneas_version : string) ~(crate_name : string)
    ~(subdir : string option) ~(llbc_file : string) : string option =
  if !Config.emit_manifest then begin
    let path = Filename.concat state.dest_dir "manifest.json" in
    write path
      (envelope_of_state ~aeneas_version ~crate_name ~subdir ~llbc_file);
    Some path
  end
  else None
