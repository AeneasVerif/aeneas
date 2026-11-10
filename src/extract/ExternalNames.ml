(** The mechanism which maps *external* identifiers (i.e., identifiers of
    definitions which we do not extract) to the models we use in the backends.

    This file contains the reader which loads lists of external names from JSON
    files (see the [-external-names] command-line option), and the name matcher
    maps which the rest of the compiler queries, built by merging the lists
    coming from the various sources. The packaged lists of builtin names
    (typically, Core/Std/Alloc) are in {!ExtractBuiltin}. *)

open Config
open NameMatcher (* TODO: include? *)

(* [ExtractBuiltin] transitively re-exports [ExtractName] (hence
   [NameMatcherMap]) and [ExtractBuiltinCore] (hence [mk_memoized]). *)
open ExtractBuiltin

let log = Logging.builtin_log

(** Raised when a list of external names can not be read. *)
exception Read_error of string

(** One list of external names, in the shapes the maps consume: either a file
    read by {!Json}, or the packaged lists of {!ExtractBuiltin}. *)
type t = {
  types : Pure.external_type_info list;
  functions : (pattern * Pure.external_fun_info) list;
  globals : Pure.external_global_info list;
  trait_decls : Pure.external_trait_decl_info list;
  trait_impls : (pattern * Pure.external_trait_impl_info) list;
}

(** Reading a list of external names from a JSON file. The types below are
    *wire* types: {!Json.load} turns them into the [Pure.external_*_info]
    records which the maps consume. *)
module Json = struct
  (** Raised while converting a single entry. *)
  exception Entry_error of string

  (** Raised by a conversion which does not want to register the entry. *)
  exception Ignore_entry

  (** Raised when an entry has no pattern, or one we cannot parse: unlike
      {!Entry_error}, this only drops the entry, with a warning (the message
      says why) - or, under [-warnings-as-errors], it is an error. *)
  exception Pattern_error of string

  (* ---------------------------------------------------------------------- *)
  (* The entries, as they are written in the files                          *)
  (* ---------------------------------------------------------------------- *)

  (** The value of a ["loop"] key, which is read for its presence only: a [null]
      value counts as absent, as everywhere else in the files, and the decoder
      takes any other value and keeps nothing of it. *)
  type loop_marker = unit

  let loop_marker_of_yojson (_ : Yojson.Safe.t) : (loop_marker, string) result =
    Ok ()

  (** A Rust name together with the name to use in the backend. *)
  type json_field = { rust : string; extract : string }

  (** An absent or [null] [body] means that the entry does not describe the body
      \- not that the type is opaque: the type keeps its LLBC kind, and its
      fields, constructor and variants get the names Aeneas computes (for Lean,
      the constructor is [<lean_name>.mk] and the variants are prefixed with
      [lean_name]); see {!ExtractTypes.extract_type_decl_register_names}. An
      ["enum"] body names only the variants it lists: the others get the same
      computed names, with a warning. *)
  and json_type_body = {
    kind : string;  (** ["struct"] or ["enum"] *)
    constructor : string option; [@default None]
        (** Structures only. Defaults to {!mk_struct_constructor}. *)
    fields : json_field list; [@default []]  (** Structures only. *)
    variants : json_field list; [@default []]
        (** Enumerations only: the [extract] names are *bare*. *)
    prefix_variant_names : bool; [@default true]
        (** Enumerations only: prefix the variant names with the extraction name
            of the type? See {!variant_extract_name}. *)
  }

  and json_type = {
    rust_pattern : string option; [@default None]
    lean_name : string;
    keep_params : bool list option; [@default None]
    mut_regions : int list option; [@default None]
        (** Defaults to Charon's analysis of the type. *)
    body : json_type_body option; [@default None]
  }

  and json_fun = {
    rust_pattern : string option; [@default None]
    lean_name : string;
    keep_params : bool list option; [@default None]
    keep_trait_clauses : bool list option; [@default None]
    can_fail : bool; [@default true]
    lift : bool; [@default true]
    loop : loop_marker option; [@default None]
  }

  and json_global = {
    rust_pattern : string option; [@default None]
    lean_name : string;
    can_fail : bool; [@default true]
  }

  (** The items of a trait are listed in its entry. The ones it leaves out get
      the names Aeneas computes. *)
  and json_trait_decl = {
    rust_pattern : string option; [@default None]
    lean_name : string;
    constructor : string option; [@default None]
        (** Defaults to {!mk_struct_constructor}. *)
    parent_clauses : string list; [@default []]
        (** Matched by position, so either all of them or none: see
            {!Extract.extract_trait_decl_register_parent_clause_names}. *)
    consts : json_field list; [@default []]
    types : json_field list; [@default []]
    methods : json_trait_method list; [@default []]
  }

  and json_trait_method = {
    rust : string;
    extract : string;
    has_default : bool; [@default false]
  }

  and json_trait_impl = {
    rust_pattern : string option; [@default None]
    lean_name : string;
    keep_params : bool list option; [@default None]
    keep_trait_clauses : bool list option; [@default None]
  }
  [@@deriving of_yojson { strict = false }]

  (* ---------------------------------------------------------------------- *)
  (* Decoding a bucket                                                      *)
  (* ---------------------------------------------------------------------- *)

  (** [ppx_deriving_yojson] reports the path of the field it could not decode,
      and nothing else (a path ending in, e.g., ["json_type.lean_name"]): we
      keep only the last component, as the bucket and the index of the entry
      already give the context. *)
  let decode_error_msg (msg : string) : string =
    let field =
      match String.rindex_opt msg '.' with
      | Some i -> String.sub msg (i + 1) (String.length msg - i - 1)
      | None -> msg
    in
    "invalid or missing field \"" ^ field ^ "\""

  (** Decode then convert the entries of a bucket, one by one, so that a failure
      can be attributed to a single entry. An absent bucket is empty. [conv]
      signals an ill-formed entry with {!Entry_error}, and drops one with
      {!Ignore_entry}.

      We do not catch [Failure] here: it would also catch the internal errors
      raised from inside a conversion. {!parse_entry_pattern} turns the one we
      do expect into a {!Pattern_error}. *)
  let read_bucket (file : string) (fields : (string * Yojson.Safe.t) list)
      (bucket : string) (of_json : Yojson.Safe.t -> ('r, string) result)
      (conv : 'r -> 'a) : 'a list =
    let rows =
      match List.assoc_opt bucket fields with
      | None | Some `Null -> []
      | Some (`List rows) -> rows
      | Some _ ->
          raise
            (Read_error (Printf.sprintf "%s: \"%s\" must be a list" file bucket))
    in
    let where = Printf.sprintf "%s: %s[%d]: " file bucket in
    let decode (i : int) (row : Yojson.Safe.t) : 'a option =
      let error (msg : string) = raise (Read_error (where i ^ msg)) in
      let is_object =
        match row with
        | `Assoc _ -> true
        | _ -> false
      in
      match of_json row with
      | Error _ when not is_object -> error "an entry must be an object"
      | Error msg -> error (decode_error_msg msg)
      | Ok row -> (
          try Some (conv row) with
          | Entry_error msg -> error msg
          | Ignore_entry -> None
          | Pattern_error msg ->
              (* This is a warning, but [Errors.warn] would raise a [CFailure]
                 under [-warnings-as-errors], which nothing catches here *)
              if !Config.warnings_as_errors then error msg
              else (
                log#swarning (where i ^ msg ^ "\nThis entry is ignored.\n");
                None))
    in
    List.filter_map Fun.id (List.mapi decode rows)

  (* ---------------------------------------------------------------------- *)
  (* Converting the entries                                                 *)
  (* ---------------------------------------------------------------------- *)

  (** [parse_pattern] raises [Failure] with a message which carries the position
      of the error inside the pattern: we turn it into a {!Pattern_error} so
      that {!read_bucket} can locate the entry and skip it with a warning (an
      error under [-warnings-as-errors]). *)
  let parse_entry_pattern (pattern : string) : pattern =
    try parse_pattern pattern
    with Failure msg ->
      raise
        (Pattern_error
           (msg
          ^ "\n\
             The name of this entry is not a pattern we can parse, so nothing \
             can be mapped to it."))

  (** The pattern of an entry. [-emit-json] leaves it out for the names which
      have no pattern: we skip these entries, with a warning (an error under
      [-warnings-as-errors]). *)
  let entry_pattern (rust_pattern : string option) : pattern =
    match rust_pattern with
    | Some pattern -> parse_entry_pattern pattern
    | None ->
        raise
          (Pattern_error
             "This entry has no \"rust_pattern\", so nothing can be mapped to \
              it.")

  (** The files store *bare* variant names, so we prefix them with the Lean name
      of their type unless the entry opted out (the files are for the Lean
      backend only). *)
  let variant_extract_name ~(prefix : bool) (type_name : string)
      (variant : string) : string =
    if prefix then type_name ^ "." ^ variant else variant

  let external_type_of_json (row : json_type) : Pure.external_type_info =
    let rust_name = entry_pattern row.rust_pattern in
    let body_info : Pure.external_type_body_info option =
      match row.body with
      | None -> None
      | Some body -> (
          match body.kind with
          | "struct" ->
              let constructor =
                Option.value body.constructor
                  ~default:(mk_struct_constructor row.lean_name)
              in
              let fields =
                List.map
                  (fun (f : json_field) -> (f.rust, f.extract))
                  body.fields
              in
              Some (Pure.Struct (constructor, fields))
          | "enum" ->
              let variants =
                List.map
                  (fun (v : json_field) : Pure.external_enum_variant_info ->
                    {
                      rust_variant_name = v.rust;
                      extract_variant_name =
                        variant_extract_name ~prefix:body.prefix_variant_names
                          row.lean_name v.extract;
                      fields = None;
                    })
                  body.variants
              in
              Some (Pure.Enum variants)
          | kind ->
              raise
                (Entry_error
                   ("unknown body kind: '" ^ kind
                  ^ "' (expected \"struct\" or \"enum\")")))
    in
    {
      rust_name;
      extract_name = row.lean_name;
      keep_params = row.keep_params;
      mut_regions = row.mut_regions;
      body_info;
    }

  let external_fun_of_json (row : json_fun) : pattern * Pure.external_fun_info =
    (* A row with a non-null ["loop"] key describes one of the declarations
       generated for a loop, under the Rust name of the *enclosing* definition:
       registering it would map that name to the loop. *)
    if row.loop <> None then raise Ignore_entry;
    ( entry_pattern row.rust_pattern,
      {
        keep_params = row.keep_params;
        keep_trait_clauses = row.keep_trait_clauses;
        extract_name = row.lean_name;
        can_fail = row.can_fail;
        (* [stateful] is never read: the effects map keeps only [can_fail]
           (see {!effect_info}). *)
        stateful = false;
        lift = row.lift;
        has_default = false;
      } )

  let external_global_of_json (row : json_global) : Pure.external_global_info =
    {
      rust_name = entry_pattern row.rust_pattern;
      extract_name = row.lean_name;
      can_fail = row.can_fail;
    }

  let external_trait_impl_of_json (row : json_trait_impl) :
      pattern * Pure.external_trait_impl_info =
    ( entry_pattern row.rust_pattern,
      {
        extract_name = row.lean_name;
        keep_params = row.keep_params;
        keep_trait_clauses = row.keep_trait_clauses;
      } )

  let external_trait_decl_of_json (row : json_trait_decl) :
      Pure.external_trait_decl_info =
    let field (f : json_field) = (f.rust, f.extract) in
    let method_ (m : json_trait_method) : string * Pure.external_fun_info =
      ( m.rust,
        {
          keep_params = None;
          keep_trait_clauses = None;
          extract_name = m.extract;
          can_fail = true;
          stateful = false;
          lift = true;
          has_default = m.has_default;
        } )
    in
    {
      rust_name = entry_pattern row.rust_pattern;
      extract_name = row.lean_name;
      constructor =
        Option.value row.constructor
          ~default:(mk_struct_constructor row.lean_name);
      parent_clauses = row.parent_clauses;
      consts = List.map field row.consts;
      types = List.map field row.types;
      methods = List.map method_ row.methods;
      packaged = false;
    }

  (* ---------------------------------------------------------------------- *)
  (* Loading a file                                                         *)
  (* ---------------------------------------------------------------------- *)

  (** Load a list of external names from a JSON file. Raises {!Read_error}.

      There is deliberately no version to check; the counterpart is that a field
      may never change meaning - a new one, with a backward-compatible default,
      is the only way to change what a file says. ["format_version"] stays
      reserved and, like any other key we do not know, is accepted and ignored.
  *)
  let load (file : string) : t =
    [%ldebug "Loading the list of external names from: " ^ file];
    let json =
      try Yojson.Safe.from_file file with
      (* [Sys_error] already names the file *)
      | Sys_error msg -> raise (Read_error msg)
      | Yojson.Json_error msg -> raise (Read_error (file ^ ": " ^ msg))
    in
    let fields =
      match json with
      | `Assoc fields -> fields
      | _ ->
          raise
            (Read_error (file ^ ": expected a JSON object at the top level"))
    in
    let read bucket of_json conv =
      read_bucket file fields bucket of_json conv
    in
    let types = read "types" json_type_of_yojson external_type_of_json in
    let functions = read "functions" json_fun_of_yojson external_fun_of_json in
    let globals =
      read "globals" json_global_of_yojson external_global_of_json
    in
    let trait_impls =
      read "trait_impls" json_trait_impl_of_yojson external_trait_impl_of_json
    in
    let trait_decls =
      read "trait_decls" json_trait_decl_of_yojson external_trait_decl_of_json
    in
    { types; functions; globals; trait_decls; trait_impls }
end

(* ------------------------------------------------------------------------ *)
(* The sources of external names                                            *)
(* ------------------------------------------------------------------------ *)

(** The lists given through [-external-names], in command-line order, filled in
    by {!load_files}. *)
let loaded_sources : t list ref = ref []

(** The packaged entries, i.e. the ones we ship. Memoized: {!merge_sources} is
    called once per map, and computing the packaged lists parses all their name
    patterns. *)
let builtin_source =
  mk_memoized (fun () : t ->
      {
        types = builtin_types ();
        functions = mk_builtin_funs ();
        globals = builtin_globals ();
        trait_decls = builtin_trait_decls_info ();
        trait_impls = builtin_trait_impls_info ();
      })

(** Load the files given through [-external-names]. This must be called *before*
    any of the maps below is forced: they are memoized, so forcing them first
    would ignore the imported entries. Raises {!Read_error}. *)
let load_files () : unit =
  loaded_sources := List.map Json.load !external_names_files

(** Concatenate one bucket over all the sources: the packaged entries first,
    then the files given through [-external-names], in command-line order. The
    order is what the diagnostics read back, as no entry may shadow another -
    see {!name_matcher_map_of_list}. *)
let merge_sources (get : t -> 'a list) : 'a list =
  List.concat_map get (builtin_source () :: !loaded_sources)

(* ------------------------------------------------------------------------ *)
(* The maps                                                                 *)
(* ------------------------------------------------------------------------ *)

(** Build a name matcher map out of a list of entries. A pattern may be mapped
    only once, across every source, so a second entry claiming one refuses the
    run rather than shadowing the first: a file cannot override a packaged name.
    [name] names an entry in the message. *)
let name_matcher_map_of_list ?name (ls : (pattern * 'a) list) :
    'a NameMatcherMap.t =
  let config : print_config = { tgt = TkPattern } in
  List.fold_left
    (fun m (pat, info) ->
      let key = pattern_to_string config pat in
      [%ldebug "About to add pattern: " ^ key];
      (* [replace] inserts and checks whether we replaced a pattern *)
      let m, old = NameMatcherMap.replace pat info m in
      (match old with
      | Some old ->
          let named =
            match name with
            | Some name -> " ('" ^ name old ^ "' and '" ^ name info ^ "')"
            | None -> ""
          in
          raise
            (Read_error
               ("two entries claim the pattern '" ^ key ^ "'" ^ named
              ^ ". A pattern may be mapped only once. Note that definitions"
              ^ " which differ only by their target share one pattern."))
      | None -> ());
      m)
    NameMatcherMap.empty ls

(* How the entries are named in the message above. *)
let global_extract_name (i : Pure.external_global_info) = i.extract_name
let type_extract_name (i : Pure.external_type_info) = i.extract_name
let fun_extract_name (i : Pure.external_fun_info) = i.extract_name
let trait_decl_extract_name (i : Pure.external_trait_decl_info) = i.extract_name
let trait_impl_extract_name (i : Pure.external_trait_impl_info) = i.extract_name

let mk_external_globals_map () : Pure.external_global_info NameMatcherMap.t =
  name_matcher_map_of_list ~name:global_extract_name
    (List.map
       (fun (info : Pure.external_global_info) -> (info.rust_name, info))
       (merge_sources (fun source -> source.globals)))

let external_globals_map = mk_memoized mk_external_globals_map

let mk_external_types_map () =
  name_matcher_map_of_list ~name:type_extract_name
    (List.map
       (fun (info : Pure.external_type_info) -> (info.rust_name, info))
       (merge_sources (fun source -> source.types)))

let external_types_map = mk_memoized mk_external_types_map

(** All the external trait declarations, in the order of {!merge_sources}. *)
let external_trait_decls : unit -> Pure.external_trait_decl_info list =
  mk_memoized (fun () -> merge_sources (fun source -> source.trait_decls))

let mk_external_trait_decls_map () =
  name_matcher_map_of_list ~name:trait_decl_extract_name
    (List.map
       (fun (info : Pure.external_trait_decl_info) -> (info.rust_name, info))
       (external_trait_decls ()))

let external_trait_decls_map = mk_memoized mk_external_trait_decls_map

let mk_external_trait_impls_map () =
  let m =
    name_matcher_map_of_list ~name:trait_impl_extract_name
      (merge_sources (fun source -> source.trait_impls))
  in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_trait_impls_map = mk_memoized mk_external_trait_impls_map

(** The external functions coming from the sources, plus the default trait
    methods, which we synthesize from the trait declarations - hence *after*
    they have been merged. *)
let external_funs : unit -> (pattern * Pure.external_fun_info) list =
  let mk () =
    let sep = backend_choice "_" "." in
    let default_methods =
      List.concat_map
        (fun (d : Pure.external_trait_decl_info) ->
          List.filter_map
            (fun ((fpat, f) : string * Pure.external_fun_info) ->
              if f.has_default then
                Some
                  ( d.rust_name @ [ PIdent (fpat, 0, []) ],
                    {
                      f with
                      extract_name =
                        d.extract_name ^ sep ^ f.extract_name ^ sep ^ "default";
                    } )
              else None)
            d.methods)
        (external_trait_decls ())
    in
    merge_sources (fun source -> source.functions) @ default_methods
  in
  mk_memoized mk

let mk_external_funs_map () =
  [%ldebug "Building the external funs map"];
  let m = name_matcher_map_of_list ~name:fun_extract_name (external_funs ()) in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_funs_map = mk_memoized mk_external_funs_map

type effect_info = { can_fail : bool }

let mk_external_fun_effects () : (pattern * effect_info) list =
  List.map
    (fun ((pattern, info) : _ * Pure.external_fun_info) ->
      (pattern, { can_fail = info.can_fail }))
    (external_funs ())

let mk_external_fun_effects_map () =
  [%ldebug "Building the external funs effects map"];
  (* No [name]: this map is derived from the same list as {!external_funs_map},
     which is built first and would have refused a duplicate already. *)
  name_matcher_map_of_list (if_backend mk_external_fun_effects [])

let external_fun_effects_map = mk_memoized mk_external_fun_effects_map
