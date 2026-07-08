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

(** The module-path components for a merged (multi-file) SCC. *)
let merged_module_components (idx : int) : string list =
  [ "Merge" ^ string_of_int idx ]

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

(** Unit tests *)
let () =
  let mc = module_components_of_file in
  assert (mc "src/foo.rs" = [ "Foo" ]);
  assert (mc "src/baz/bang.rs" = [ "Baz"; "Bang" ]);
  assert (mc "src/geometry/mod.rs" = [ "Geometry"; "Mod" ]);
  assert (mc "src/geometry.rs" = [ "Geometry" ]);
  assert (mc "src/geometry/shapes.rs" = [ "Geometry"; "Shapes" ]);
  assert (mc "src/lib.rs" = [ "Lib" ]);
  assert (mc "src/main.rs" = [ "Main" ]);
  assert (mc "src/cycle_x.rs" = [ "CycleX" ]);
  assert (mc "src/rectypes/tree.rs" = [ "Rectypes"; "Tree" ]);
  assert (mc "src/a/b/mod.rs" = [ "A"; "B"; "Mod" ]);
  (* Tolerate a leading "./" and a missing "src/". *)
  assert (mc "./src/foo.rs" = [ "Foo" ]);
  assert (mc "foo.rs" = [ "Foo" ]);
  assert (merged_module_components 0 = [ "Merge0" ]);
  assert (merged_module_components 3 = [ "Merge3" ]);
  assert (
    layer_module_components [ "A" ] ~is_template:false ~index:1
    = [ "A"; "Part1" ]);
  assert (
    layer_module_components [ "A" ] ~is_template:true ~index:2
    = [ "A"; "Axioms2" ]);
  assert (
    layer_module_components [ "Geometry"; "Shapes" ] ~is_template:false ~index:3
    = [ "Geometry"; "Shapes"; "Part3" ]);
  assert (
    layer_module_components [ "FunsExternal" ] ~is_template:true ~index:1
    = [ "FunsExternal"; "Axioms1" ]);
  assert (dotted_module_name [ "Happy"; "Baz"; "Bang" ] = "Happy.Baz.Bang")
