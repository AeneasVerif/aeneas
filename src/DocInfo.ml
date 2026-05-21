(** Extract documentation-relevant information from an LLBC crate as JSON.

    This module implements the [--doc-info] mode: it reads the LLBC crate
    (already parsed by Aeneas/Charon) and outputs a JSON file with all the
    information needed by the HTML documentation generator: function names,
    spans, visibility, opacity, source text, types, etc. *)

open LlbcAst
open Types

(** {1 JSON helpers} *)

let json_string s = `String s
let json_int i = `Int i
let json_bool b = `Bool b
let json_null = `Null

let json_opt f = function
  | None -> json_null
  | Some x -> f x

let json_list f l = `List (List.map f l)
let json_assoc l = `Assoc l

(** {1 Name pattern generation} *)

(** Convert a name to the pattern string used by Aeneas for matching (same logic
    as [name_to_pattern_string] in [TranslateCore]). Uses the convenience
    wrapper from [LlbcAstUtils]. *)
let name_to_pattern (crate : crate) (span : Meta.span) (n : name) : string =
  LlbcAstUtils.name_with_crate_to_pattern_string (Some span) crate n

(** {1 Span and name serialization} *)

let span_data_to_json (sd : Meta.span_data) : Yojson.Basic.t =
  let file_path =
    match sd.file.name with
    | Local p -> p
    | Virtual p -> p
    | NotReal s -> s
  in
  json_assoc
    [
      ("file", json_string file_path);
      ("crate_name", json_string sd.file.crate_name);
      ("begin_line", json_int sd.beg_loc.line);
      ("begin_col", json_int sd.beg_loc.col);
      ("end_line", json_int sd.end_loc.line);
      ("end_col", json_int sd.end_loc.col);
    ]

let span_to_json (span : Meta.span) : Yojson.Basic.t =
  json_assoc
    [
      ("data", span_data_to_json span.data);
      ("generated_from", json_opt span_data_to_json span.generated_from_span);
    ]

let path_elem_to_json fmt_env (pe : path_elem) : Yojson.Basic.t =
  match pe with
  | PeIdent (name, disamb) ->
      json_assoc
        [
          ("kind", json_string "Ident");
          ("name", json_string name);
          ("disambiguator", json_int (Disambiguator.to_int disamb));
        ]
  | PeImpl impl ->
      let impl_str = Print.impl_elem_to_string fmt_env impl in
      json_assoc
        [ ("kind", json_string "Impl"); ("text", json_string impl_str) ]
  | PeInstantiated _ -> json_assoc [ ("kind", json_string "Instantiated") ]

let name_to_json fmt_env (n : name) : Yojson.Basic.t =
  json_list (path_elem_to_json fmt_env) n

(** {1 Function declarations} *)

(** Extract function call targets from a single call site. *)
let call_target (c : call) : FunDeclId.id list =
  match c.func with
  | FnOpRegular { kind = FunId (FRegular fid); _ } -> [ fid ]
  | FnOpRegular { kind = TraitMethod (_, _, fid); _ } -> [ fid ]
  | _ -> []

(** Walk a block recursively to collect all called function ids. *)
let rec block_callees (b : block) : FunDeclId.id list =
  List.concat_map stmt_callees b.statements

and stmt_callees (s : statement) : FunDeclId.id list =
  match s.kind with
  | Call c -> call_target c
  | Switch sw -> switch_callees sw
  | Loop b -> block_callees b
  | _ -> []

and switch_callees (sw : switch) : FunDeclId.id list =
  match sw with
  | If (_, b1, b2) -> block_callees b1 @ block_callees b2
  | SwitchInt (_, _, branches, otherwise) ->
      List.concat_map (fun (_, b) -> block_callees b) branches
      @ block_callees otherwise
  | Match (_, branches, otherwise) -> (
      List.concat_map (fun (_, b) -> block_callees b) branches
      @
      match otherwise with
      | Some b -> block_callees b
      | None -> [])

(** Extract unique callee def_ids for a function declaration. *)
let fun_callees (fd : LlbcAst.fun_decl) : FunDeclId.id list =
  match fd.body with
  | None -> []
  | Some expr_body ->
      block_callees expr_body.body |> List.sort_uniq FunDeclId.compare_id

let fun_decl_to_json (crate : crate) fmt_env (fd : fun_decl) : Yojson.Basic.t =
  let meta = fd.item_meta in
  let has_attr_opaque =
    List.exists
      (fun (a : Meta.attribute) -> a = AttrOpaque)
      meta.attr_info.attributes
  in
  let callees = fun_callees fd in
  json_assoc
    [
      ("def_id", json_int (FunDeclId.to_int fd.def_id));
      ("name", name_to_json fmt_env meta.name);
      ("name_pattern", json_string (name_to_pattern crate meta.span meta.name));
      ("span", span_to_json meta.span);
      ("source_text", json_opt json_string meta.source_text);
      ("is_public", json_bool meta.attr_info.public);
      ("is_local", json_bool meta.is_local);
      ("is_opaque", json_bool (fd.body = None || has_attr_opaque));
      ("has_body", json_bool (fd.body <> None));
      ( "is_global_initializer",
        json_opt
          (fun id -> json_int (GlobalDeclId.to_int id))
          fd.is_global_initializer );
      ( "src",
        json_string
          (match fd.src with
          | TopLevelItem -> "TopLevel"
          | ClosureItem _ -> "Closure"
          | TraitDeclItem _ -> "TraitDeclItem"
          | TraitImplItem _ -> "TraitImplItem"
          | _ -> "Other") );
      ("callees", json_list (fun id -> json_int (FunDeclId.to_int id)) callees);
    ]

(** {1 Type declarations} *)

let type_decl_to_json (crate : crate) fmt_env (td : type_decl) : Yojson.Basic.t
    =
  let meta = td.item_meta in
  let kind_str =
    match td.kind with
    | Struct _ -> "Struct"
    | Enum _ -> "Enum"
    | Union _ -> "Union"
    | Alias _ -> "Alias"
    | Opaque -> "Opaque"
    | TDeclError _ -> "Error"
  in
  json_assoc
    [
      ("def_id", json_int (TypeDeclId.to_int td.def_id));
      ("name", name_to_json fmt_env meta.name);
      ("name_pattern", json_string (name_to_pattern crate meta.span meta.name));
      ("span", span_to_json meta.span);
      ("source_text", json_opt json_string meta.source_text);
      ("is_public", json_bool meta.attr_info.public);
      ("is_local", json_bool meta.is_local);
      ("kind", json_string kind_str);
    ]

(** {1 Global declarations} *)

let global_decl_to_json (crate : crate) fmt_env (gd : global_decl) :
    Yojson.Basic.t =
  let meta = gd.item_meta in
  json_assoc
    [
      ("def_id", json_int (GlobalDeclId.to_int gd.def_id));
      ("name", name_to_json fmt_env meta.name);
      ("name_pattern", json_string (name_to_pattern crate meta.span meta.name));
      ("span", span_to_json meta.span);
      ("source_text", json_opt json_string meta.source_text);
      ("is_public", json_bool meta.attr_info.public);
      ("is_local", json_bool meta.is_local);
    ]

(** {1 Trait declarations} *)

let trait_decl_to_json (crate : crate) fmt_env (td : trait_decl) :
    Yojson.Basic.t =
  let meta = td.item_meta in
  json_assoc
    [
      ("def_id", json_int (TraitDeclId.to_int td.def_id));
      ("name", name_to_json fmt_env meta.name);
      ("name_pattern", json_string (name_to_pattern crate meta.span meta.name));
      ("span", span_to_json meta.span);
      ("is_local", json_bool meta.is_local);
    ]

(** {1 Top-level extraction} *)

let crate_doc_info_to_json (crate : crate) : Yojson.Basic.t =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in

  (* Functions — iterate over the full map *)
  let functions =
    FunDeclId.Map.fold
      (fun _id (fd : fun_decl) acc -> fun_decl_to_json crate fmt_env fd :: acc)
      crate.fun_decls []
    |> List.rev
  in

  (* Types *)
  let types =
    TypeDeclId.Map.fold
      (fun _id (td : type_decl) acc ->
        type_decl_to_json crate fmt_env td :: acc)
      crate.type_decls []
    |> List.rev
  in

  (* Globals *)
  let globals =
    GlobalDeclId.Map.fold
      (fun _id (gd : global_decl) acc ->
        global_decl_to_json crate fmt_env gd :: acc)
      crate.global_decls []
    |> List.rev
  in

  (* Trait declarations *)
  let trait_decls =
    TraitDeclId.Map.fold
      (fun _id (td : trait_decl) acc ->
        trait_decl_to_json crate fmt_env td :: acc)
      crate.trait_decls []
    |> List.rev
  in

  json_assoc
    [
      ("crate_name", json_string crate.name);
      ("functions", `List functions);
      ("types", `List types);
      ("globals", `List globals);
      ("trait_decls", `List trait_decls);
    ]

(** Entry point: dump the doc-info JSON for a crate *)
let dump_doc_info (crate : crate) (dest : string) : unit =
  let json = crate_doc_info_to_json crate in
  let s = Yojson.Basic.pretty_to_string ~std:true json in
  if dest = "" then print_string s
  else
    let oc = open_out dest in
    output_string oc s;
    output_char oc '\n';
    close_out oc
