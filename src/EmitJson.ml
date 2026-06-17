(** Emit a translation.json file alongside the extracted Lean files. This file
    contains the Aeneas data which connects the Lean translation to the Rust
    code. *)

type loop_info = {
  loop_id_idx : int; [@key "id"]
  loop_pos : int list; [@key "pos"]
  is_body : bool;
}
[@@deriving to_yojson]

(** Lean function declaration.

    [loop] and [parent_lean_name] are present only on loop-wrapper / loop-body
    entries. Non-loop entries have neither. All other fields are always emitted.
*)
type entry = {
  def_id : int;
      (** Charon [FunDeclId] reified to a plain int. *)
  lean_name : string;
  lean_file : string;
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result]. *)
  can_diverge : bool;
      (** [true] when the function may not terminate. *)
  is_rec : bool;
      (** [true] when the function is part of a mutually recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]]. *)
  loop : loop_info option; [@default None] [@key "loop"]
  parent_lean_name : string option; [@default None]
}
[@@deriving to_yojson]

(** Lean type declaration. *)
type type_entry = { def_id : int; lean_name : string; lean_file : string }
[@@deriving to_yojson]

(** Lean global declaration. *)
type global_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  can_fail : bool;
}
[@@deriving to_yojson]

(** Where the manifest itself sits and which backend files Aeneas wrote. *)
type output_info = {
  subdir : string option; [@default None]
  llbc_file : string;
      (** Basename of the [.llbc] input file. *)
  lean_files : string list;
      (** Lean files written, relative to the directory containing this file. *)
}
[@@deriving to_yojson]

type envelope = {
  aeneas_version : string;
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. *)
  crate_name : string; [@key "crate"]
      (** Identifier of the source Rust crate. *)
  output : output_info;
  functions : entry list;
  types : type_entry list;
  globals : global_entry list;
}
[@@deriving to_yojson]

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(*                                                                          *)
(* Lifecycle: [init_if_enabled] at the start of [extract_translated_crate], *)
(* [begin_file_if_enabled] at the top of every [extract_file],              *)
(* [record_*_if_enabled] called from the export-* hooks,                    *)
(* [write_if_enabled] once at the end.                                      *)
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

let init_if_enabled ~(dest_dir : string) : unit =
  if !Config.emit_json then begin
    state.function_entries <- [];
    state.type_entries <- [];
    state.global_entries <- [];
    state.lean_files <- [];
    state.current_lean_file <- "";
    state.current_lean_namespace <- "";
    state.dest_dir <- dest_dir
  end

(* ------------------------------------------------------------------------ *)
(* Entry construction                                                       *)
(* ------------------------------------------------------------------------ *)

let qualify (basename : string) : string =
  assert (state.current_lean_file <> "");
  if state.current_lean_namespace = "" then basename
  else state.current_lean_namespace ^ "." ^ basename

let entry_of_fun_decl (ctx : ExtractBase.extraction_ctx) (def : Pure.fun_decl) :
    entry =
  let span = def.item_meta.span in
  let lean_name =
    qualify (ExtractBase.ctx_get_local_function span def.def_id def.loop_id ctx)
  in
  let parent_lean_name =
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
    lean_name;
    lean_file = state.current_lean_file;
    is_opaque = Option.is_none def.body;
    can_fail = eff.can_fail;
    can_diverge = eff.can_diverge;
    is_rec = eff.is_rec;
    reducible = def.backend_attributes.reducible;
    loop;
    parent_lean_name;
  }

let type_entry_of_type_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : type_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_name = qualify (ExtractBase.ctx_get_local_type span def.def_id ctx);
    lean_file = state.current_lean_file;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_name = qualify (ExtractBase.ctx_get_global span def.def_id ctx);
    lean_file = state.current_lean_file;
    can_fail = def.can_fail;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when -emit-json is off)                           *)
(* ------------------------------------------------------------------------ *)

let begin_file_if_enabled ~(filename : string) ~(namespace : string) : unit =
  if !Config.emit_json then begin
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

let record_fun_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : unit =
  if !Config.emit_json then
    state.function_entries <-
      entry_of_fun_decl ctx def :: state.function_entries

let record_type_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : unit =
  if !Config.emit_json then
    state.type_entries <- type_entry_of_type_decl ctx def :: state.type_entries

let record_global_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : unit =
  if !Config.emit_json then
    state.global_entries <-
      global_entry_of_global_decl ctx def :: state.global_entries

(* ------------------------------------------------------------------------ *)
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out out)
    (fun () ->
      Yojson.Safe.pretty_to_channel out (envelope_to_yojson env);
      output_char out '\n')

let write_if_enabled ~(crate_name : string) ~(subdir : string option)
    ~(llbc_file : string) : string option =
  if !Config.emit_json then begin
    let path = Filename.concat state.dest_dir "translation.json" in
    write path
      {
        aeneas_version = Option.value GitVersion.commit ~default:"unknown";
        charon_version = Charon.CharonVersion.supported_charon_version;
        crate_name;
        output =
          {
            subdir;
            llbc_file = Filename.basename llbc_file;
            lean_files = List.rev state.lean_files;
          };
        functions = List.rev state.function_entries;
        types = List.rev state.type_entries;
        globals = List.rev state.global_entries;
      };
    Some path
  end
  else None
