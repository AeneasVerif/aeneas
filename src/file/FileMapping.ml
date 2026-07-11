(** Mapping from Rust source-file paths to Lean module paths.

    The functions operate on crate-relative paths as found in charon's
    [item_meta] spans (e.g. ["src/baz/bang.rs"]) and return Lean module-path
    components *without* the crate prefix (e.g. [["Baz"; "Bang"]]). The caller
    prepends the crate (and optional subdir) prefix.

    The mapping is a direct structural mirror of the crate's file tree: every
    source file maps to exactly one Lean file at the matching path, with each
    path component camel-cased and the extension swapped.

    Conventions:
    - ["src/foo.rs"] -> [["Foo"]]
    - ["src/baz/bang.rs"] -> [["Baz"; "Bang"]]
    - ["src/geometry/mod.rs"] -> [["Geometry"; "Mod"]]
    - ["src/geometry.rs"] -> [["Geometry"]]
    - ["src/lib.rs"] -> [["Lib"]]
    - ["src/main.rs"] -> [["Main"]]
    - ["src/cycle_x.rs"] -> [["CycleX"]] (snake_case -> CamelCase) *)

(** The Lean module-path components for a source file, without the crate prefix.

    Assumes a crate-relative path (a leading ["src/"] is stripped if present).
*)
let module_components_of_file (path : string) : string list =
  (* Split into path components, dropping empty and "." segments. *)
  let parts =
    String.split_on_char '/' path |> List.filter (fun s -> s <> "" && s <> ".")
  in
  (* Drop a leading "src" component. *)
  let parts =
    match parts with
    | "src" :: rest -> rest
    | _ -> parts
  in
  (* Strip the ".rs" extension from the last component. *)
  let parts =
    match List.rev parts with
    | [] -> []
    | last :: rrest ->
        let stem =
          match Filename.chop_suffix_opt ~suffix:".rs" last with
          | Some s -> s
          | None -> last
        in
        List.rev (stem :: rrest)
  in
  (* Charon always supplies a real local file path for local items, so a path that
     reduces to nothing means a broken upstream invariant. *)
  if parts = [] then
    [%craise_opt_span] None
      ("Cannot map the source file path to a Lean module: " ^ path);
  List.map StringUtils.to_camel_case parts

(** The module-path components for a merged (multi-file) SCC.

    The name is derived from the member files: each path is camel-cased like a
    single-file module and the results are concatenated in alphabetical order *)
let merged_module_components (paths : string list) : string list =
  if paths = [] then
    [%craise_opt_span] None "Empty file set for a merged (multi-file) module";
  let stems =
    List.map (fun p -> String.concat "" (module_components_of_file p)) paths
  in
  [ "Merge" ^ String.concat "" (List.sort String.compare stems) ]

(** The name of the modules extracted from a single rust module that must split
    up due to alternating opaque/non-opaque SCCs. *)
let layer_module_components (base : string list) ~(is_template : bool)
    ~(index : int) : string list =
  let word = if is_template then "Axioms" else "Part" in
  base @ [ word ^ string_of_int index ]

(** Assemble a dotted Lean module name from its components, e.g.
    [["Happy"; "Baz"; "Bang"]] -> ["Happy.Baz.Bang"]. *)
let dotted_module_name (components : string list) : string =
  String.concat "." components
