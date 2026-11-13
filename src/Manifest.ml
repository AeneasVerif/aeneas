(** The format of the manifest of a translated crate: the [translation.json]
    file written with [-emit-json] (see {!EmitJson}), which records the Lean
    name of every translated item together with its Rust name, and read with
    [-extern-crate] (see {!ExternManifest}).

    This module only defines the format; it depends on no other module of
    Aeneas. *)

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
      (** The Rust name as a name-matcher pattern. *)
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
          pattern (e.g. [a::Trait<a::Foo>]), as in the builtin tables. *)
  is_local : bool;
  source : source;
  impl_trait_def_id : int;
      (** [TraitDeclId] of the implemented trait. A valid LLBC trait decl but
          has entry in [trait_decls] iff [impl_trait_is_builtin] is [false]. *)
  impl_trait_rust_name : string;
      (** Full Rust path of the implemented trait. *)
  impl_trait_is_builtin : bool;
      (** [true] when the implemented trait is builtin, or belongs to an
          external crate ([-extern-crate]). *)
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
