(** Mapping from Rust module paths to Lean module paths.

    {!module_components} maps the path of a Rust module, without the crate name
    (e.g. [["baz"; "bang"]] for [crate::baz::bang]), to Lean module-path
    components without the crate prefix (e.g. [["Baz"; "Bang"]]). The caller
    prepends the crate (and optional subdir) prefix.

    The mapping mirrors the crate's module tree, whatever files the modules are
    in: inline [mod] blocks and [#[path]] modules are placed like the others.
    Each component is camel-cased, and the crate root module is [Lib].

    Examples:
    - [crate::foo] -> [["Foo"]]
    - [crate::baz::bang] -> [["Baz"; "Bang"]]
    - [crate::geometry] -> [["Geometry"]] (in [geometry.rs] or
      [geometry/mod.rs])
    - [crate] -> [["Lib"]] (in [lib.rs] or [main.rs])
    - [crate::cycle_x] -> [["CycleX"]] (snake_case -> CamelCase) *)

(** The path of a generated file relative to the directory [dir], e.g.
    ["Crate/A/Part1.lean"] for [out/Crate/A/Part1.lean] with [dir = "out"].
    [None] if the file is not in [dir]. *)
let relative_to ~(dir : string) (path : string) : string option =
  let prefix = if String.ends_with ~suffix:"/" dir then dir else dir ^ "/" in
  if String.starts_with ~prefix path then
    Some
      (String.sub path (String.length prefix)
         (String.length path - String.length prefix))
  else None

(** The Lean module-path components for a Rust module, not including the crate
    prefix. [module_path] is the module's path without the crate name, and [[]]
    stands for the crate root. *)
let module_components (module_path : string list) : string list =
  let sanitize (c : char) : char =
    match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c
    | _ -> '_'
  in
  match module_path with
  | [] -> [ "Lib" ]
  | _ ->
      List.map
        (fun m -> StringUtils.to_camel_case (String.map sanitize m))
        module_path

(** The number of modules from which a merged module is called [Extracted]
    instead of being named after its modules. *)
let max_bundle_name_modules = 8

(** The module-path components for a merged SCC of Rust modules.

    If one of the modules contains all the others (an inline submodule usually
    forms a cycle with its parent), the merged module is named after it, as if
    the others were part of it: [a] and [a::inner] give [A].

    Otherwise the name is derived from all the modules: each one is camel-cased,
    sorted alphabetically, joined with ["_"] and given a ["_Bundle"] suffix,
    e.g. [Ping_Pong_Bundle] for [ping] and [pong]. If there are at least
    [max_bundle_name_modules] modules we call it [Extracted] instead. *)
let merged_module_components (module_paths : string list list) : string list =
  if module_paths = [] then
    [%craise_opt_span] None "Empty module set for a merged module";
  let rec is_prefix (prefix : string list) (path : string list) : bool =
    match (prefix, path) with
    | [], _ -> true
    | p :: prefix, m :: path -> p = m && is_prefix prefix path
    | _ :: _, [] -> false
  in
  let contains_all (ancestor : string list) : bool =
    List.for_all (is_prefix ancestor) module_paths
  in
  let ancestor = List.find_opt contains_all module_paths in
  match ancestor with
  | Some ancestor -> module_components ancestor
  | None ->
      if List.length module_paths >= max_bundle_name_modules then
        [ "Extracted" ]
      else
        let stems =
          List.map
            (fun p -> String.concat "" (module_components p))
            module_paths
        in
        [ String.concat "_" (List.sort String.compare stems) ^ "_Bundle" ]

(** The module path of layer number [index] of the module [base]. Whether or not
    the name is an opaque layer or not is determined by [is_opaque]. *)
let layer_module_components (base : string list) ~(is_opaque : bool)
    ~(index : int) : string list =
  let word = if is_opaque then "Opaques" else "Part" in
  base @ [ word ^ string_of_int index ]

(** The module path [base] with [_index] added to its last component, to tell
    apart two modules with the same name. This is used when we need to
    disambiguate Lean modules that are generated with the same base path. *)
let indexed_module_components (base : string list) ~(index : int) : string list
    =
  match List.rev base with
  | last :: rest -> List.rev ((last ^ "_" ^ string_of_int index) :: rest)
  | [] -> [ "_" ^ string_of_int index ]

(** Assemble a dotted Lean module name from its components, e.g.
    [["Happy"; "Baz"; "Bang"]] -> ["Happy.Baz.Bang"]. *)
let dotted_module_name (components : string list) : string =
  String.concat "." components
