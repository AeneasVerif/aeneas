(** This file declares external identifiers that we catch to map them to
    definitions coming from the standard libraries in our backends.

    TODO: there misses trait **implementations** *)

open Config
open NameMatcher (* TODO: include? *)
include ExtractName (* TODO: only open? *)

let log = Logging.builtin_log

(** Small utility to memoize some computations *)
let mk_memoized (f : unit -> 'a) : unit -> 'a =
  let r = ref None in
  let g () =
    match !r with
    | Some x -> x
    | None ->
        let x = f () in
        r := Some x;
        x
  in
  g

let split_on_separator (s : string) : string list =
  Str.split (Str.regexp "\\(::\\|\\.\\)") s

let flatten_name (name : string list) : string =
  match backend () with
  | FStar | Coq | HOL4 -> String.concat "_" name
  | Lean -> String.concat "." name

(** Utility for Lean-only definitions **)
let mk_lean_only (funs : 'a list) : 'a list =
  match backend () with
  | Lean -> funs
  | _ -> []

let mk_not_lean (funs : 'a list) : 'a list =
  match backend () with
  | Lean -> []
  | _ -> funs

let () =
  assert (split_on_separator "x::y::z" = [ "x"; "y"; "z" ]);
  assert (split_on_separator "x.y.z" = [ "x"; "y"; "z" ])

(** Switch between two values depending on the target backend.

    We often compute the same value (typically: a name) if the target is F*, Coq
    or HOL4, and a different value if the target is Lean. *)
let backend_choice (fstar_coq_hol4 : 'a) (lean : 'a) : 'a =
  match backend () with
  | Coq | FStar | HOL4 -> fstar_coq_hol4
  | Lean -> lean

type type_variant_kind =
  | KOpaque
  | KStruct of (string * string option) list
      (** Contains the list of (field rust name, field extracted name) *)
  | KEnum of (string * string option) list

let mk_lean_struct_constructor (type_name : string) : string = type_name ^ ".mk"

let mk_struct_constructor (type_name : string) : string =
  let prefix =
    match backend () with
    | FStar -> "Mk"
    | Coq | HOL4 -> "mk"
    | Lean -> ""
  in
  let suffix =
    match backend () with
    | FStar | Coq | HOL4 -> ""
    | Lean -> ".mk"
  in
  prefix ^ type_name ^ suffix

let mk_fun ?(filter : bool list option = None) ?(can_fail = true)
    ?(stateful = false) ?(lift = true) ?(has_default = false)
    (rust_name : string) (extract_name : string) :
    pattern * Pure.builtin_fun_info =
  [%ldebug "About to parse pattern: " ^ rust_name];
  let rust_name =
    try parse_pattern rust_name
    with Failure _ ->
      raise (Failure ("Could not parse pattern: " ^ rust_name))
  in
  let f : Pure.builtin_fun_info =
    {
      filter_params = filter;
      extract_name;
      can_fail;
      stateful;
      lift;
      has_default;
    }
  in
  (rust_name, f)

let mk_type ?(keep_params : bool list option = None)
    ?(kind : type_variant_kind = KOpaque) ?(prefix_variant_names : bool = true)
    (rust_name : string) (extract_name : string) : Pure.builtin_type_info =
  let pattern = parse_pattern rust_name in
  let body_info : Pure.builtin_type_body_info option =
    match kind with
    | KOpaque -> None
    | KStruct fields ->
        let fields =
          List.map
            (fun (rname, name) ->
              ( rname,
                match name with
                | None ->
                    [%craise_opt_span] None
                      ("Missing Lean field name: type: '" ^ rust_name
                     ^ "', rust field: '" ^ rname ^ "'")
                | Some name -> name ))
            fields
        in
        let constructor = mk_lean_struct_constructor extract_name in
        Some (Struct (constructor, fields))
    | KEnum variants ->
        let variants =
          List.map
            (fun (variant, evariant) ->
              let evariant =
                match evariant with
                | Some variant -> variant
                | None -> variant
              in
              let extract_variant_name =
                if prefix_variant_names then extract_name ^ "." ^ evariant
                else evariant
              in
              ({
                 rust_variant_name = variant;
                 extract_variant_name;
                 fields = None;
               }
                : Pure.builtin_enum_variant_info))
            variants
        in
        Some (Enum variants)
  in
  { rust_name = pattern; extract_name; keep_params; body_info }

let mk_trait_decl ?(parent_clauses : string list = [])
    ?(consts : (string * string) list = [])
    ?(types : (string * string) list = [])
    ?(methods : (string * string) list = [])
    ?(default_methods : string list = []) (rust_name : string)
    (extract_name : string) : Pure.builtin_trait_decl_info =
  let rust_name = parse_pattern rust_name in
  let constructor = mk_lean_struct_constructor extract_name in
  let default_methods = Collections.StringSet.of_list default_methods in
  let methods =
    List.map
      (fun (rname, lname) ->
        ( rname,
          ({
             filter_params = None;
             extract_name = lname;
             can_fail = true;
             stateful = false;
             lift = true;
             has_default = Collections.StringSet.mem lname default_methods;
           }
            : Pure.builtin_fun_info) ))
      methods
  in
  {
    rust_name;
    extract_name;
    constructor;
    parent_clauses;
    consts;
    types;
    methods;
  }

let mk_trait_impl ?(filter_params : bool list option = None)
    (rust_name : string) (extract_name : string) :
    pattern * Pure.builtin_trait_impl_info =
  let rust_name = parse_pattern rust_name in
  (rust_name, { extract_name; filter_params })
