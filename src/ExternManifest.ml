(** The manifests of the external crates (option [-extern-crate]): the crates
    translated beforehand by Aeneas, whose items the writer names after their
    Lean definitions instead of emitting them (see {!ExtractExternal}). *)

open Manifest

(** The entries of the external crates, indexed by their Rust name (as printed
    in the manifest's [rust_name]). The writer looks the items up here: an item
    found here is named after its entry and not emitted. *)
let functions : (string, function_entry) Hashtbl.t = Hashtbl.create 64

let types : (string, type_entry) Hashtbl.t = Hashtbl.create 16
let globals : (string, global_entry) Hashtbl.t = Hashtbl.create 16
let trait_decls : (string, trait_decl_entry) Hashtbl.t = Hashtbl.create 16
let trait_impls : (string, trait_impl_entry) Hashtbl.t = Hashtbl.create 16

(** The Lean modules of the external crates, which the generated files import.
*)
let imported_modules_ref : string list ref = ref []

let imported_modules () : string list = !imported_modules_ref

(** Register the entries of the manifest [env] of crate [crate]. *)
let register (crate : string) (env : envelope) : unit =
  let add :
      'a. string -> (string, 'a) Hashtbl.t -> string -> string -> 'a -> unit =
   fun kind tbl rust_name lean_module entry ->
    if Hashtbl.mem tbl rust_name then
      failwith
        ("the " ^ kind ^ " " ^ rust_name
       ^ " is listed twice (in the manifest of crate " ^ crate
       ^ " or of another external crate)");
    Hashtbl.add tbl rust_name entry;
    if not (List.mem lean_module !imported_modules_ref) then
      imported_modules_ref := !imported_modules_ref @ [ lean_module ]
  in
  List.iter
    (fun (f : function_entry) ->
      (* Loop functions are only called by the function they belong to *)
      if f.loop = None then add "function" functions f.rust_name f.lean_module f)
    env.functions;
  List.iter
    (fun (t : type_entry) -> add "type" types t.rust_name t.lean_module t)
    env.types;
  List.iter
    (fun (g : global_entry) -> add "global" globals g.rust_name g.lean_module g)
    env.globals;
  List.iter
    (fun (d : trait_decl_entry) ->
      add "trait" trait_decls d.rust_name d.lean_module d)
    env.trait_decls;
  List.iter
    (fun (i : trait_impl_entry) ->
      add "trait impl" trait_impls i.rust_name i.lean_module i)
    env.trait_impls

(** Load the manifest at [path] of the external crate [crate] and register its
    entries. Raises [Failure] if the manifest is missing, invalid or
    incompatible with this translation. *)
let load ~(charon_version : string) (crate : string) (path : string) : unit =
  let fail msg =
    failwith ("-extern-crate " ^ crate ^ "=" ^ path ^ ": " ^ msg)
  in
  if not (Sys.file_exists path) then fail "file not found";
  let env =
    match envelope_of_yojson (Yojson.Safe.from_file path) with
    | Ok env -> env
    | Error msg -> fail ("invalid manifest (" ^ msg ^ ")")
    | exception Yojson.Json_error msg -> fail ("invalid JSON (" ^ msg ^ ")")
  in
  if env.crate_name <> crate then
    fail ("this is the manifest of crate '" ^ env.crate_name ^ "'");
  if env.charon_version <> charon_version then
    fail
      ("the crate was translated from the output of Charon "
     ^ env.charon_version ^ ", but this version of Aeneas uses Charon "
     ^ charon_version);
  if env.lean_modules <> !Config.use_lean_modules then
    fail
      ("the crate was translated "
      ^ (if env.lean_modules then "with" else "without")
      ^ " Lean modules, unlike this translation (option -use-lean-modules)");
  try register crate env with Failure msg -> fail msg

let is_empty () : bool =
  Hashtbl.length functions = 0
  && Hashtbl.length types = 0
  && Hashtbl.length globals = 0
  && Hashtbl.length trait_decls = 0
  && Hashtbl.length trait_impls = 0

let find_function = Hashtbl.find_opt functions
let find_type = Hashtbl.find_opt types
let find_global = Hashtbl.find_opt globals
let find_trait_decl = Hashtbl.find_opt trait_decls
let find_trait_impl = Hashtbl.find_opt trait_impls
