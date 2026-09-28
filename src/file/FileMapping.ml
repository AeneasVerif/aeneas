(** Mapping from Rust source-file paths to Lean module paths.

    Charon gives source paths relative to the directory cargo ran in.
    {!infer_source_root} and {!relative_source_path} turn them into paths
    relative to the crate's source root (e.g. ["baz/bang.rs"]), and
    {!module_components_of_file} maps those to Lean module-path components
    without the crate prefix (e.g. [["Baz"; "Bang"]]). The caller prepends the
    crate (and optional subdir) prefix.

    The mapping directly mirrors the crate's file tree: every source file maps
    to exactly one Lean file at the mapped path, with each component
    camel-cased, invalid separators removed, and the extension swapped.

    Examples, for a crate whose source root is [src] ([crates/mycrate/src] for
    the workspace member):
    - ["src/foo.rs"] -> [["Foo"]]
    - ["src/baz/bang.rs"] -> [["Baz"; "Bang"]]
    - ["src/geometry/mod.rs"] -> [["Geometry"; "Mod"]]
    - ["src/geometry.rs"] -> [["Geometry"]]
    - ["src/lib.rs"] -> [["Lib"]]
    - ["src/main.rs"] -> [["Main"]]
    - ["src/cycle_x.rs"] -> [["CycleX"]] (snake_case -> CamelCase)
    - ["crates/mycrate/src/foo.rs"] -> [["Foo"]] (workspace member) *)

(** Split a path into its components, resolving ["."] and [".."]. A [".."] with
    nothing left to remove is dropped. *)
let path_components (path : string) : string list =
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

(** The crate's source root directory (the directory of [lib.rs] for a library
    with the standard layout), inferred from the [(Rust module, source file)]
    pairs of its items.

    An item of module [a::b] whose file is where Rust's module convention puts
    it, [R/a/b.rs] or [R/a/b/mod.rs], tells us the root is [R]: we take the
    first such item. Its file must match its module path, so an item in an
    unexpected file (an inline [mod] block, a [#[path]] attribute, a macro...)
    can't mislead us. Only if no item qualifies do we fall back to the crate
    root file: the directory of the file of a crate-level item. [None] if there
    is neither.

    TODO: rustc knows the crate root file, so we should eventually get Charon to
    return it in the LLBC and we can eliminate this whole inference pass. See
    https://github.com/AeneasVerif/charon/issues/1505. *)
let infer_source_root (items : (string list * string) list) : string list option
    =
  let root_of_nested_item ((modules, path) : string list * string) :
      string list option =
    let parts = path_components path in
    let chop_suffix (suffix : string list) : string list option =
      let n = List.length parts - List.length suffix in
      if n < 0 then None
      else
        let prefix, rest = Collections.List.split_at parts n in
        if rest = suffix then Some prefix else None
    in
    match List.rev modules with
    | [] -> None
    | m :: rev_parents ->
        let parents = List.rev rev_parents in
        List.find_map chop_suffix
          [ parents @ [ m ^ ".rs" ]; parents @ [ m; "mod.rs" ] ]
  in
  let root_of_crate_level_item ((modules, path) : string list * string) :
      string list option =
    match (modules, List.rev (path_components path)) with
    | [], _root_file :: rev_dir -> Some (List.rev rev_dir)
    | _ -> None
  in
  match List.find_map root_of_nested_item items with
  | Some root -> Some root
  | None -> List.find_map root_of_crate_level_item items

(** The path of a source file relative to the crate's source root, e.g.
    ["a/b.rs"] for [crates/mycrate/src/a/b.rs] with the root
    [["crates"; "mycrate"; "src"]]. {!FileGraph} uses it as the key of a source
    file. [None] if the file is not below the root. *)
let relative_source_path ~(root : string list) (path : string) : string option =
  let rec chop_prefix (prefix : string list) (parts : string list) =
    match (prefix, parts) with
    | [], parts -> Some parts
    | p :: prefix, x :: parts when p = x -> chop_prefix prefix parts
    | _ -> None
  in
  match chop_prefix root (path_components path) with
  | None | Some [] -> None
  | Some rel -> Some (String.concat "/" rel)

(** The Lean module-path components for a source file, without the crate prefix.
    [path] is relative to the crate's source root (see {!relative_source_path}).
*)
let module_components_of_file (path : string) : string list =
  let parts = path_components path in
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
     reduces to nothing means something went wrong. *)
  if parts = [] then
    [%craise_opt_span] None
      ("Cannot map the source file path to a Lean module: " ^ path);
  (* Rust file names can contain '-' or '.' (e.g. prost's generated
     [signal.proto.pq_ratchet.rs]), but Lean modules can't. *)
  let sanitize (c : char) : char =
    match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c
    | _ -> '_'
  in
  List.map (fun p -> StringUtils.to_camel_case (String.map sanitize p)) parts

(** The module-path components for a merged (multi-file) SCC.

    The name is derived from the member files: each path is camel-cased like a
    single-file module, and the results are sorted alphabetically, joined with
    ["_"] and given a ["_Bundle"] suffix, e.g. [Ping_Pong_Bundle] for [ping.rs]
    and [pong.rs]. *)
let merged_module_components (paths : string list) : string list =
  if paths = [] then
    [%craise_opt_span] None "Empty file set for a merged (multi-file) module";
  let stems =
    List.map (fun p -> String.concat "" (module_components_of_file p)) paths
  in
  [ String.concat "_" (List.sort String.compare stems) ^ "_Bundle" ]

(** The module path of layer number [index] of the module [base]. Whether or not
    the name is an opaque layer or not is determined by [is_opaque]. *)
let layer_module_components (base : string list) ~(is_opaque : bool)
    ~(index : int) : string list =
  let word = if is_opaque then "Opaques" else "Part" in
  base @ [ word ^ string_of_int index ]

(** Assemble a dotted Lean module name from its components, e.g.
    [["Happy"; "Baz"; "Bang"]] -> ["Happy.Baz.Bang"]. *)
let dotted_module_name (components : string list) : string =
  String.concat "." components
