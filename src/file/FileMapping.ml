(** Mapping from Rust source-file paths to Lean module paths.

    The functions take the paths found in charon's [item_meta] spans and return
    Lean module-path components without the crate prefix (e.g.
    [["Baz"; "Bang"]]). The caller prepends the crate (and optional subdir)
    prefix.

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
    - ["src/cycle_x.rs"] -> [["CycleX"]] (snake_case -> CamelCase)
    - ["crates/mycrate/src/foo.rs"] -> [["Foo"]] (workspace member) *)

(** Split a source path into components below the crate's source root.

    Charon's paths are relative to the directory cargo was invoked from, which
    for a workspace is the *workspace* root — so ["src"] is not necessarily the
    first component ([crates/mycrate/src/foo.rs]). We therefore drop everything
    through the last ["src"] component rather than a leading one. Paths with no
    ["src"] at all are kept whole.

    ["."] and [".."] are resolved first; a [".."] with nothing to pop is
    dropped, since these paths only ever name a module and there is no root to
    escape to.

    The caveat of taking the last ["src"] is a Rust module literally named [src]
    ([src/src/mod.rs] loses a level). That is rare, and the placement collision
    guard in {!FilePlan.place_by_file} catches it if it ever matters. *)
let source_path_components (path : string) : string list =
  let parts =
    List.fold_left
      (fun acc p ->
        match p with
        | "" | "." -> acc
        | ".." -> (
            match acc with
            | [] -> []
            | _ :: rest -> rest)
        | _ -> p :: acc)
      []
      (String.split_on_char '/' path)
    |> List.rev
  in
  (* Everything after the last "src", or the whole path if there is none. *)
  let rec after_last_src acc rest =
    match rest with
    | [] -> acc
    | "src" :: tl -> after_last_src (Some tl) tl
    | _ :: tl -> after_last_src acc tl
  in
  match after_last_src None parts with
  | Some rest -> rest
  | None -> parts

(** The crate-relative source path, canonicalized: the inverse join of
    {!source_path_components}. Used to key file buckets so that paths reaching
    {!FileGraph} by different routes (a charon span vs. a reconstructed module
    path) agree. *)
let normalize_source_path (path : string) : string =
  String.concat "/" (source_path_components path)

(** The Lean module-path components for a source file, without the crate prefix.
*)
let module_components_of_file (path : string) : string list =
  let parts = source_path_components path in
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
