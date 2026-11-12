(** The manifest of a translated crate: the [translation.json] file written with
    [-emit-json], which records the Lean name of every translated item together
    with its Rust name.

    The manifest has two uses:
    - it connects the Lean translation to the Rust code (for tools);
    - it lets the translation of another crate reuse this translation: with
      [-extern-crate NAME=PATH], the items of crate [NAME] are mapped to the
      Lean definitions listed in its manifest, in the same way as the items of
      the standard library are mapped to the definitions of the Lean library
      (see {!ExtractBuiltin}). They are then neither re-declared nor
      axiomatized, and the generated files import the modules defining them.

    This module only depends on {!Pure}, {!NameMatcher} and {!Config}, so that
    the builtin tables can use the entries loaded here. *)

(** Rust source location of a declaration, taken from LLBC [item_meta.span]. *)
type source = {
  file : string;  (** Path to the Rust source file. *)
  begin_line : int;  (** First line of the declaration. *)
  end_line : int;  (** Last line of the declaration. *)
}
[@@deriving yojson { strict = false }]

type loop_info = {
  loop_id_idx : int; [@key "id"]
  loop_pos : int list; [@key "pos"]
  is_body : bool;
}
[@@deriving yojson { strict = false }]

(** A Rust name together with the Lean name it is translated to. *)
type name_pair = {
  rust : string;  (** The Rust name (of a field, variant, method...). *)
  lean : string;  (** The Lean name. *)
}
[@@deriving yojson { strict = false }]

(** Lean function declaration. *)
type function_entry = {
  def_id : int;  (** Charon [FunDeclId] reified to a plain int. *)
  lean_name : string;  (** Fully-qualified Lean name. *)
  lean_file : string;  (** Path relative to this manifest's directory. *)
  lean_module : string;
      (** The Lean module to import to use the declaration (for a template, the
          module of its filled copy). *)
  rust_name : string;  (** Fully-qualified Rust name (from [item_meta.name]). *)
  rust_pattern : string; [@default ""]
      (** The Rust name as a name-matcher pattern, used to identify the item
          from another crate. *)
  is_local : bool;
      (** [true] if defined in the current crate, [false] if external. *)
  source : source;  (** Rust source location (from [item_meta.span]). *)
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result]. *)
  can_diverge : bool;  (** [true] when the function may not terminate. *)
  is_rec : bool;
      (** [true] when the function is part of a mutually recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]]. *)
  loop : loop_info option; [@default None] [@key "loop"]
      (** Present only on loop-wrapper / loop-body entries *)
  parent_lean_name : string option; [@default None]
      (** Present only on loop-wrapper / loop-body entries *)
}
[@@deriving yojson { strict = false }]

(** Lean type declaration. *)
type type_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  lean_module : string;
  rust_name : string;
  rust_pattern : string; [@default ""]
  is_local : bool;
  source : source;
  constructor : string option; [@default None]
      (** For a structure: the fully-qualified name of its constructor. *)
  fields : name_pair list; [@default []]
      (** For a structure: the Lean name of each field. *)
  variants : name_pair list; [@default []]
      (** For an enumeration: the fully-qualified Lean name of each variant. *)
}
[@@deriving yojson { strict = false }]

(** Lean global declaration. *)
type global_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  lean_module : string;
  rust_name : string;
  rust_pattern : string; [@default ""]
  is_local : bool;
  source : source;
  can_fail : bool;
}
[@@deriving yojson { strict = false }]

(** Lean trait declaration. *)
type trait_decl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  lean_module : string;
  rust_name : string;
  rust_pattern : string; [@default ""]
  is_local : bool;
  source : source;
  constructor : string; [@default ""]
      (** The fully-qualified name of the structure's constructor. *)
  parent_clauses : string list; [@default []]
      (** The field name of each parent clause, in order. *)
  consts : name_pair list; [@default []]
      (** The field name of each associated constant. *)
  types : name_pair list; [@default []]
      (** The field name of each associated type. *)
  methods : name_pair list; [@default []]  (** The field name of each method. *)
}
[@@deriving yojson { strict = false }]

(** Lean trait implementation. *)
type trait_impl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  lean_module : string;
  rust_name : string;
  rust_pattern : string; [@default ""]
      (** The implemented trait with its generic arguments, as a name-matcher
          pattern (e.g. [a::Trait<a::Foo>]): this identifies the impl from
          another crate. *)
  is_local : bool;
  source : source;
  impl_trait_def_id : int;
      (** [TraitDeclId] of the implemented trait. A valid LLBC trait decl but
          has entry in [trait_decls] iff the trait is not builtin. *)
  impl_trait_rust_name : string;
      (** Full Rust path of the implemented trait. *)
  impl_trait_is_builtin : bool;
      (** [true] when the implemented trait is builtin. *)
}
[@@deriving yojson { strict = false }]

type envelope = {
  aeneas_version : string option; [@default None]
      (** Absent with [-emit-json-no-version]. *)
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. *)
  crate_name : string; [@key "crate"]
      (** Identifier of the source Rust crate. *)
  lean_modules : bool; [@default false]
      (** [true] if the files are Lean modules (option [-use-lean-modules]). *)
  functions : function_entry list;
  types : type_entry list;
  globals : global_entry list;
  trait_decls : trait_decl_entry list;
  trait_impls : trait_impl_entry list;
}
[@@deriving yojson { strict = false }]

(* ------------------------------------------------------------------------ *)
(* Loading the manifests of external crates                                 *)
(* ------------------------------------------------------------------------ *)

(** The entries of the external crates, in the form of the builtin tables (which
    {!ExtractBuiltin} extends with them). *)
let types : Pure.builtin_type_info list ref = ref []

let funs : (NameMatcher.pattern * Pure.builtin_fun_info) list ref = ref []
let globals : Pure.builtin_global_info list ref = ref []
let trait_decls : Pure.builtin_trait_decl_info list ref = ref []

let trait_impls : (NameMatcher.pattern * Pure.builtin_trait_impl_info) list ref
    =
  ref []

(** The Lean modules of the external crates, which the generated files import.
*)
let imported_modules : string list ref = ref []

(** [true] if the trait impl information comes from an external crate. *)
let is_extern_trait_impl (info : Pure.builtin_trait_impl_info) : bool =
  List.exists (fun (_, i) -> i == info) !trait_impls

(** Drop the information of an external crate found for a local trait impl.
    Defensive: a pattern with variables could match a local impl. (We compare
    physically: the builtin tables store the records registered here.) *)
let filter_trait_impl_info ~(is_local : bool)
    (info : Pure.builtin_trait_impl_info option) :
    Pure.builtin_trait_impl_info option =
  match info with
  | Some i when is_local && is_extern_trait_impl i -> None
  | _ -> info

let fun_info (lean_name : string) (can_fail : bool) : Pure.builtin_fun_info =
  {
    keep_params = None;
    keep_trait_clauses = None;
    extract_name = lean_name;
    can_fail;
    stateful = false;
    lift = true;
    has_default = false;
  }

let name_pairs : name_pair list -> (string * string) list =
  List.map (fun (p : name_pair) -> (p.rust, p.lean))

(** Register the entries of the manifest [env] of crate [crate]. *)
let register (crate : string) (env : envelope) : unit =
  let parse (rust_name : string) (pattern : string) : NameMatcher.pattern =
    if pattern = "" then
      failwith
        ("The manifest of crate " ^ crate ^ " has no pattern for " ^ rust_name
       ^ ": it was written by an older version of Aeneas")
    else
      try NameMatcher.parse_pattern pattern
      with _ ->
        failwith
          ("Could not parse the pattern '" ^ pattern ^ "' of " ^ rust_name
         ^ " in the manifest of crate " ^ crate)
  in
  let import (lean_module : string) =
    if not (List.mem lean_module !imported_modules) then
      imported_modules := !imported_modules @ [ lean_module ]
  in
  List.iter
    (fun (f : function_entry) ->
      (* Loop functions are only called by the function they belong to *)
      if f.loop = None then (
        import f.lean_module;
        funs :=
          (parse f.rust_name f.rust_pattern, fun_info f.lean_name f.can_fail)
          :: !funs))
    env.functions;
  List.iter
    (fun (t : type_entry) ->
      import t.lean_module;
      let body_info : Pure.builtin_type_body_info option =
        match (t.constructor, t.variants) with
        | Some cons, _ -> Some (Struct (cons, name_pairs t.fields))
        | None, [] -> None
        | None, variants ->
            Some
              (Enum
                 (List.map
                    (fun (p : name_pair) : Pure.builtin_enum_variant_info ->
                      {
                        rust_variant_name = p.rust;
                        extract_variant_name = p.lean;
                        fields = None;
                      })
                    variants))
      in
      types :=
        {
          Pure.rust_name = parse t.rust_name t.rust_pattern;
          extract_name = t.lean_name;
          keep_params = None;
          mut_regions = [];
          body_info;
        }
        :: !types)
    env.types;
  List.iter
    (fun (g : global_entry) ->
      import g.lean_module;
      (* The table of globals stores the pattern as a string: we only check it *)
      ignore (parse g.rust_name g.rust_pattern);
      globals :=
        {
          Pure.rust_name = g.rust_pattern;
          extract_name = g.lean_name;
          can_fail = g.can_fail;
        }
        :: !globals)
    env.globals;
  List.iter
    (fun (d : trait_decl_entry) ->
      import d.lean_module;
      trait_decls :=
        {
          Pure.rust_name = parse d.rust_name d.rust_pattern;
          extract_name = d.lean_name;
          constructor = d.constructor;
          parent_clauses = d.parent_clauses;
          consts = name_pairs d.consts;
          types = name_pairs d.types;
          methods =
            List.map
              (fun (p : name_pair) -> (p.rust, fun_info p.lean true))
              d.methods;
        }
        :: !trait_decls)
    env.trait_decls;
  List.iter
    (fun (i : trait_impl_entry) ->
      import i.lean_module;
      trait_impls :=
        ( parse i.rust_name i.rust_pattern,
          {
            Pure.extract_name = i.lean_name;
            keep_params = None;
            keep_trait_clauses = None;
          } )
        :: !trait_impls)
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
  register crate env
