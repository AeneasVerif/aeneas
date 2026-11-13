(** Emit translation.json which contains the Aeneas data which connects the Lean
    translation to the Rust code. *)

(* The types of the entries are defined in [ExternManifest], which also reads manifests. *)
open Manifest

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(*                                                                          *)
(* Lifecycle: [init_if_enabled] at the start of [extract_translated_crate], *)
(* [begin_file_if_enabled] at the top of every [extract_file],              *)
(* [record_*_if_enabled] called from the export-* hooks,                    *)
(* [write_if_enabled] once at the end.                                      *)
(* ------------------------------------------------------------------------ *)

type state = {
  mutable function_entries : function_entry list;
  mutable type_entries : type_entry list;
  mutable global_entries : global_entry list;
  mutable trait_decl_entries : trait_decl_entry list;
  mutable trait_impl_entries : trait_impl_entry list;
  mutable current_lean_file : string;
  mutable current_lean_module : string;
  mutable current_lean_namespace : string;
  mutable current_in_namespace : bool;
  mutable dest_dir : string;
}

let make_state () : state =
  {
    function_entries = [];
    type_entries = [];
    global_entries = [];
    trait_decl_entries = [];
    trait_impl_entries = [];
    current_lean_file = "";
    current_lean_module = "";
    current_lean_namespace = "";
    current_in_namespace = true;
    dest_dir = "";
  }

(* One Aeneas process translates one crate, so a module-local singleton. *)
let state : state = make_state ()

let init_if_enabled ~(dest_dir : string) : unit =
  if !Config.emit_json then state.dest_dir <- dest_dir

(* ------------------------------------------------------------------------ *)
(* Entry construction                                                       *)
(* ------------------------------------------------------------------------ *)

(** Add the Lean namespace to a short name to form the full Lean name. *)
let full_lean_name (basename : string) : string =
  if state.current_in_namespace then
    state.current_lean_namespace ^ "." ^ basename
  else basename

(** Extract the Rust source location (file + line range) from a span. *)
let source_of_span (span : Meta.span) : source =
  let data = span.data in
  let file =
    match data.file.name with
    | Virtual s | Local s | NotReal s -> s
  in
  { file; begin_line = data.beg_loc.line; end_line = data.end_loc.line }

(** The Rust name of an item as a name-matcher pattern, which identifies the
    item from another crate. *)
let rust_pattern (ctx : ExtractBase.extraction_ctx) (span : Meta.span)
    (name : Types.name) : string =
  TranslateCore.name_to_pattern_string (Some span) ctx.trans_ctx name

(** A name of the names map, without escaping, and qualified by the namespace if
    [qualify]. *)
let raw_name ?(qualify : bool = false) (ctx : ExtractBase.extraction_ctx)
    (span : Meta.span) (id : ExtractBase.id) : string =
  let n = ExtractBase.ctx_get_raw (Some span) id ctx in
  if qualify then full_lean_name n else n

let function_entry_of_fun_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : function_entry =
  let span = def.item_meta.span in
  let lean_name =
    full_lean_name
      (ExtractBase.ctx_get_local_function span def.def_id def.loop_id ctx)
  in
  let parent_lean_name =
    match def.loop_id with
    | None -> None
    | Some _ ->
        Some
          (full_lean_name
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
    lean_module = state.current_lean_module;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    rust_pattern = rust_pattern ctx span def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
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
  let type_id : Pure.type_id = TAdtId def.def_id in
  (* Tuple structs are extracted as tuples: they have no constructor nor field names *)
  let is_tuple =
    TypesUtils.type_decl_from_decl_id_is_tuple_struct
      ctx.trans_ctx.type_ctx.type_infos def.def_id
  in
  let constructor, fields, variants =
    match def.kind with
    | Struct fields when not is_tuple ->
        let fields =
          Pure.FieldId.mapi
            (fun fid (f : Pure.field) ->
              {
                rust = Option.value f.field_name ~default:"";
                lean = raw_name ctx span (FieldId (type_id, fid));
              })
            fields
        in
        (Some (raw_name ~qualify:true ctx span (StructId type_id)), fields, [])
    | Enum variants ->
        let variants =
          Pure.VariantId.mapi
            (fun vid (v : Pure.variant) ->
              {
                rust = v.variant_name;
                lean =
                  raw_name ~qualify:true ctx span (VariantId (type_id, vid));
              })
            variants
        in
        (None, [], variants)
    | _ -> (None, [], [])
  in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_local_type span def.def_id ctx);
    lean_file = state.current_lean_file;
    lean_module = state.current_lean_module;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    rust_pattern = rust_pattern ctx span def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    constructor;
    fields;
    variants;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_name = full_lean_name (ExtractBase.ctx_get_global span def.def_id ctx);
    lean_file = state.current_lean_file;
    lean_module = state.current_lean_module;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    rust_pattern = rust_pattern ctx span def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    can_fail = def.can_fail;
  }

let trait_decl_entry_of_trait_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : trait_decl_entry =
  let span = def.item_meta.span in
  let id = def.def_id in
  {
    def_id = Pure.TraitDeclId.to_int id;
    lean_name = full_lean_name (ExtractBase.ctx_get_trait_decl span id ctx);
    lean_file = state.current_lean_file;
    lean_module = state.current_lean_module;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    rust_pattern = rust_pattern ctx span def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    constructor = raw_name ~qualify:true ctx span (TraitDeclConstructorId id);
    parent_clauses =
      List.map
        (fun (c : Pure.trait_param) ->
          raw_name ctx span (TraitParentClauseId (id, c.clause_id)))
        def.parent_clauses;
    consts =
      List.map
        (fun (cid, rust, _) ->
          { rust; lean = raw_name ctx span (TraitConstId (id, cid)) })
        def.consts;
    types =
      List.map
        (fun (tid, rust) ->
          { rust; lean = raw_name ctx span (TraitTypeId (id, tid)) })
        def.types;
    methods =
      List.map
        (fun (m : Pure.trait_method) ->
          {
            rust = m.item_name;
            lean = raw_name ctx span (TraitMethodId (id, m.method_id));
          })
        def.methods;
  }

let trait_impl_entry_of_trait_impl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : trait_impl_entry =
  let span = def.item_meta.span in
  let impl_trait_id = def.impl_trait.trait_decl_id in
  let impl_trait_decl =
    Pure.TraitDeclId.Map.find impl_trait_id ctx.trans_trait_decls
  in
  (* The impl is identified by the implemented trait and its arguments, as in the builtin tables *)
  let rust_pattern =
    let llbc_impl =
      Pure.TraitImplId.Map.find def.def_id ctx.crate.trait_impls
    in
    let llbc_decl =
      Pure.TraitDeclId.Map.find impl_trait_id ctx.crate.trait_decls
    in
    LlbcAstUtils.trait_impl_with_crate_to_pattern_string (Some span) ctx.crate
      llbc_decl llbc_impl
  in
  {
    def_id = Pure.TraitImplId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_trait_impl span def.def_id ctx);
    lean_file = state.current_lean_file;
    lean_module = state.current_lean_module;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    rust_pattern;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    impl_trait_def_id = Pure.TraitDeclId.to_int impl_trait_id;
    impl_trait_rust_name =
      ExtractBase.name_to_string ctx impl_trait_decl.item_meta.name;
    impl_trait_is_builtin =
      Option.is_some impl_trait_decl.builtin_info
      || ExtractExternal.is_trait_decl ctx impl_trait_decl.item_meta.name;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when -emit-json is off)                           *)
(* ------------------------------------------------------------------------ *)

let begin_file_if_enabled ~(filename : string) ~(lean_module : string)
    ~(namespace : string) ~(in_namespace : bool) : unit =
  if !Config.emit_json then begin
    (* Record the Lean file relative to dest_dir. *)
    let basename = Filename.basename filename in
    let rel =
      match !Config.subdir with
      | None -> basename
      | Some subdir -> Filename.concat subdir basename
    in
    state.current_lean_file <- rel;
    state.current_lean_module <- lean_module;
    state.current_lean_namespace <- namespace;
    state.current_in_namespace <- in_namespace
  end

let record_fun_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : unit =
  if !Config.emit_json then
    state.function_entries <-
      function_entry_of_fun_decl ctx def :: state.function_entries

let record_type_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : unit =
  if !Config.emit_json then
    state.type_entries <- type_entry_of_type_decl ctx def :: state.type_entries

let record_global_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : unit =
  if !Config.emit_json then
    state.global_entries <-
      global_entry_of_global_decl ctx def :: state.global_entries

let record_trait_decl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : unit =
  if !Config.emit_json then
    state.trait_decl_entries <-
      trait_decl_entry_of_trait_decl ctx def :: state.trait_decl_entries

let record_trait_impl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : unit =
  if !Config.emit_json then
    state.trait_impl_entries <-
      trait_impl_entry_of_trait_impl ctx def :: state.trait_impl_entries

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

let write_if_enabled ~(crate_name : string) : string option =
  if !Config.emit_json then begin
    let path = Filename.concat state.dest_dir "translation.json" in
    write path
      {
        aeneas_version =
          (if !Config.emit_json_no_version then None
           else Some (Option.value GitVersion.commit ~default:"unknown"));
        charon_version = Charon.CharonVersion.supported_charon_version;
        crate_name;
        lean_modules = !Config.use_lean_modules;
        functions = List.rev state.function_entries;
        types = List.rev state.type_entries;
        globals = List.rev state.global_entries;
        trait_decls = List.rev state.trait_decl_entries;
        trait_impls = List.rev state.trait_impl_entries;
      };
    Some path
  end
  else None
