(** Define base utilities for the extraction *)

open Contexts
open Pure
open StringUtils
open Config
module F = Format
open ExtractBuiltin
open TranslateCore

(** The local logger *)
let log = Logging.extract_log

type region_group_info = {
  id : RegionGroupId.id;
      (** The id of the region group. Note that a simple way of generating
          unique names for backward functions is to use the region group ids. *)
  region_names : string option list;
      (** The names of the region variables included in this group. Note that
          names are not always available... *)
}

module StringSet = Collections.StringSet
module StringMap = Collections.StringMap

(** Characterizes a declaration.

    Is in particular useful to derive the proper keywords to introduce the
    declarations/definitions. *)
type decl_kind =
  | SingleNonRec
      (** A single, non-recursive definition.

          F*: [let x = ...] Coq: [Definition x := ...] *)
  | SingleRec
      (** A single, recursive definition.

          F*: [let rec x = ...] Coq: [Fixpoint x := ...] *)
  | MutRecFirst
      (** The first definition of a group of mutually-recursive definitions.

          F*: [type x0 = ... and x1 = ...] Coq:
          [Fixpoint x0 := ... with x1 := ...] *)
  | MutRecInner
      (** An inner definition in a group of mutually-recursive definitions. *)
  | MutRecLast
      (** The last definition in a group of mutually-recursive definitions.

          We need this because in some theorem provers like Coq, we need to
          delimit group of mutually recursive definitions (in particular, we
          need to insert an end delimiter). *)
  | Builtin
      (** An builtin definition.

          F*: [assume val x] Coq: [Axiom x : Type.] *)
  | Declared
      (** Declare a type in an interface or a module signature.

          Rem.: for now, in Coq, we don't declare module signatures: we thus
          assume the corresponding declarations.

          F*: [val x : Type0] Coq: [Axiom x : Type.] *)
[@@deriving show]

(** Return [true] if the declaration is the last from its group of declarations.

    We need this because in some provers (e.g., Coq), we need to delimit the end
    of a (group of) definition(s) (in Coq: with a "."). *)
let decl_is_last_from_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | MutRecLast | Builtin | Declared -> true
  | MutRecFirst | MutRecInner -> false

let decl_is_from_rec_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | Builtin | Declared -> false
  | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> true

let decl_is_from_mut_rec_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | Builtin | Declared -> false
  | MutRecFirst | MutRecInner | MutRecLast -> true

let decl_is_first_from_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | MutRecFirst | Builtin | Declared -> true
  | MutRecLast | MutRecInner -> false

(** Return [true] if the declaration is not the last from its group of
    declarations.

    We need this because in some provers (e.g., HOL4), we need to delimit the
    inner declarations (with `/\` for instance). *)
let decl_is_not_last_from_group (kind : decl_kind) : bool =
  not (decl_is_last_from_group kind)

type type_decl_kind = Enum | Struct | Tuple [@@deriving show]

(** Generics can be bound in two places: each item has its generics, and
    additionally within a trait decl or impl each method has its own generics
    (using `binder` above). We distinguish these two cases here. In charon, the
    distinction is made thanks to `de_bruijn_var`. Note that for the generics of
    a top-level `fun_decl` we always use `Item`; `Method` only refers to the
    inner binder found in the list of methods in a trait_decl/trait_impl. *)
type generic_origin = Item | Method [@@deriving show, ord]

(** We use identifiers to look for name clashes *)
and id =
  | GlobalId of A.GlobalDeclId.id
  | FunId of fun_id
  | TerminationMeasureId of (A.fun_id * LoopId.id option)
      (** The definition which provides the decreases/termination measure. We
          insert calls to this clause to prove/reason about termination: the
          body of those clauses must be defined by the user, in the proper
          files.

          More specifically:
          {ul
           {- in F*, this is the content of the [decreases] clause. Example:
              ========
              {[
                let rec sum (ls : list nat) : Tot nat (decreases ls) = ...
              ]}
           }
           {- in Lean, this is the content of the [termination_by] clause. }
          } *)
  | DecreasesProofId of (A.fun_id * LoopId.id option)
      (** The definition which provides the decreases/termination proof. We
          insert calls to this clause to prove/reason about termination: the
          body of those clauses must be defined by the user, in the proper
          files.

          More specifically:
          - F* doesn't use this.
          - in Lean, this is the tactic used by the [decreases_by] annotations.
      *)
  | TypeId of type_id
  | StructId of type_id
      (** We use this when we manipulate the names of the structure
          constructors.

          For instance, in F*:
          {[
            type pair = { x: nat; y : nat }
            let p : pair = Mkpair 0 1
          ]} *)
  | VariantId of type_id * VariantId.id
      (** If often happens that variant names must be unique (it is the case in
          F* ) which is why we register them here. *)
  | FieldId of type_id * FieldId.id
      (** If often happens that in the case of structures, the field names must
          be unique (it is the case in F* ) which is why we register them here.
      *)
  | FVarId of FVarId.id
  | TraitDeclId of TraitDeclId.id
  | TraitImplId of TraitImplId.id
  | TypeVarId of generic_origin * TypeVarId.id
  | ConstGenericVarId of generic_origin * ConstGenericVarId.id
  | LocalTraitClauseId of generic_origin * TraitClauseId.id
  | TraitDeclConstructorId of TraitDeclId.id
  | TraitMethodId of TraitDeclId.id * string
  | TraitItemId of TraitDeclId.id * string
      (** A trait associated item which is not a method *)
  | TraitParentClauseId of TraitDeclId.id * TraitClauseId.id
  | UnknownId
      (** Used for stored various strings like keywords, definitions which
          should always be in context, etc. and which can't be linked to one of
          the above.

          TODO: rename to "keyword" *)
[@@deriving show, ord]

module IdOrderedType = struct
  type t = id

  let compare = compare_id
  let to_string = show_id
  let pp_t = pp_id
  let show_t = show_id
end

module IdMap = Collections.MakeMap (IdOrderedType)
module IdSet = Collections.MakeSet (IdOrderedType)

(** The names map stores the mappings from names to identifiers and vice-versa.

    We use it for lookups (during the translation) and to check for name
    clashes.

    [id_to_name] is for debugging. *)
type names_map = {
  id_to_name : string IdMap.t;
  name_to_id : (id * Meta.span option) StringMap.t;
      (** The name to id map is used to look for name clashes, and generate nice
          debugging messages: if there is a name clash, it is useful to know
          precisely which identifiers are mapped to the same name... *)
  names_set : StringSet.t;
}

let empty_names_map : names_map =
  {
    id_to_name = IdMap.empty;
    name_to_id = StringMap.empty;
    names_set = StringSet.empty;
  }

(** Small helper to update an LLBC name if the rename attribute has been set *)
let rename_llbc_name (attr_info : Meta.attr_info) (llbc_name : llbc_name) :
    llbc_name =
  match attr_info.rename with
  | Some rename ->
      let name_prefix = List.tl (List.rev llbc_name) in
      List.rev (T.PeIdent (rename, Disambiguator.zero) :: name_prefix)
  | None -> llbc_name

(** Small helper to report name collision *)
let report_name_collision (id_to_string : id -> string)
    ((id1, span1) : id * Meta.span option) (id2 : id) (span2 : Meta.span option)
    (name : string) : unit =
  let span_to_string (span : Meta.span option) =
    match span with
    | None -> ""
    | Some span -> "\n  " ^ Errors.span_to_string span
  in
  let id1 = "\n- " ^ id_to_string id1 ^ span_to_string span1 in
  let id2 = "\n- " ^ id_to_string id2 ^ span_to_string span2 in
  let err =
    "Name clash detected: the following identifiers are bound to the same name \
     \"" ^ name ^ "\":" ^ id1 ^ id2
    ^ "\n\n\
       You may want to rename some of your definitions, or report an issue.\n\
       Note that you can change the name used in the generated code by using \
       the attribute #[aeneas::rename(\"NAME\")] or \
       #[charon::rename(\"NAME\")]. For instance:\n\n\
       ```\n\
       #![feature(register_tool)]\n\
       #![register_tool(aeneas)]\n\n\
       #[aeneas::rename(\"Bar\")]\n\
       type Foo = i32;\n\
       ```\n\n\
       Those attributes can be applied to type definitions, functions, \
       methods, trait\n\
       declarations or trait implementations. For more examples, see:\n\
       https://github.com/AeneasVerif/aeneas/blob/main/tests/src/rename_attribute.rs\n\n\n"
  in
  (* Register the error.

     We don't link this error to any span information because we already put
     the span information about the two problematic definitions in the error
     message above. *)
  [%save_error_opt_span] None err

let names_map_get_id_from_name (name : string) (nm : names_map) :
    (id * Meta.span option) option =
  StringMap.find_opt name nm.name_to_id

let names_map_check_collision (id_to_string : id -> string) (id : id)
    (span : Meta.span option) (name : string) (nm : names_map) : unit =
  match names_map_get_id_from_name name nm with
  | None -> () (* Ok *)
  | Some clash ->
      (* There is a clash: print a nice debugging message for the user *)
      report_name_collision id_to_string clash id span name

(** Insert bindings in a names map without checking for collisions *)
let names_map_add_unchecked ((id, span) : id * Meta.span option) (name : string)
    (nm : names_map) : names_map =
  (* Insert *)
  let id_to_name = IdMap.add id name nm.id_to_name in
  let name_to_id = StringMap.add name (id, span) nm.name_to_id in
  let names_set = StringSet.add name nm.names_set in
  { id_to_name; name_to_id; names_set }

let names_map_add (id_to_string : id -> string) ((id, span) : id * span option)
    (name : string) (nm : names_map) : names_map =
  (* Check if there is a clash *)
  names_map_check_collision id_to_string id span name nm;
  (* Sanity check *)
  (if StringSet.mem name nm.names_set then
     let err =
       "Error when registering the name for id: " ^ id_to_string id
       ^ ":\nThe chosen name is already in the names set: " ^ name
     in
     (* If we fail hard on errors, raise an exception *)
     [%save_error_opt_span] span err);
  (* Insert *)
  names_map_add_unchecked (id, span) name nm

(** The unsafe names map stores mappings from identifiers to names which might
    collide. For some backends and some names, it might be acceptable to have
    collisions. For instance, in Lean, different records can have fields with
    the same name because Lean uses the typing information to resolve the
    ambiguities.

    This map complements the {!type:names_map}, which checks for collisions. *)
type unsafe_names_map = { id_to_name : string IdMap.t }

let empty_unsafe_names_map = { id_to_name = IdMap.empty }

let unsafe_names_map_add (id : id) (name : string) (nm : unsafe_names_map) :
    unsafe_names_map =
  { id_to_name = IdMap.add id name nm.id_to_name }

(** Make a (variable) basename unique (by adding an index).

    We do this in an inefficient manner (by testing all indices starting from 0)
    but it shouldn't be a bottleneck.

    Also note that at some point, we thought about trying to reuse names of
    variables which are not used anymore, like here:
    {[
      let x = ... in
      ...
      let x0 = ... in // We could use the name "x" if [x] is not used below
      ...
    ]}

    However it is a good idea to keep things as they are for F*: as F* is
    designed for extrinsic proofs, a proof about a function follows this
    function's structure. The consequence is that we often end up copy-pasting
    function bodies. As in the proofs (in assertions and when calling lemmas) we
    often need to talk about the "past" (i.e., previous values), it is very
    useful to generate code where all variable names are assigned at most once.

    [append]: function to append an index to a string *)
let basename_to_unique_aux (collision : string -> bool)
    (append : string -> int -> string) (basename : string) : string =
  let rec gen (i : int) : string =
    let s = append basename i in
    if collision s then gen (i + 1) else s
  in
  if collision basename then gen 1 else basename

type names_maps = {
  names_map : names_map;
      (** The map for id to names, where we forbid name collisions (ex.: we
          always forbid function name collisions). *)
  unsafe_names_map : unsafe_names_map;
      (** The map for id to names, where we allow name collisions (ex.: we might
          allow record field name collisions). *)
  strict_names_map : names_map;
      (** This map is a sub-map of [names_map]. For the ids in this map we also
          forbid collisions with names in the [unsafe_names_map].

          We do so for keywords for instance, but also for types (in a
          dependently typed language, we might have an issue if the field of a
          record has, say, the name "u32", and another field of the same record
          refers to "u32" (for instance in its type). *)
}

(** Return [true] if we are strict on collisions for this id (i.e., we forbid
    collisions even with the ids in the unsafe names map) *)
let strict_collisions (id : id) : bool =
  match id with
  | UnknownId | TypeId _ -> true
  | _ -> false

(** We might not check for collisions for some specific ids (ex.: field names)
*)
let allow_collisions (id : id) : bool =
  match id with
  | FieldId _ | TraitParentClauseId _ | TraitItemId _ | TraitMethodId _ ->
      !Config.record_fields_short_names
  | FunId (Pure _ | FromLlbc (FunId (FBuiltin _), _)) ->
      (* We map several builtin functions to the same id *)
      true
  | _ -> false

(** The [id_to_string] function to print nice debugging messages if there are
    collisions *)
let names_maps_add (id_to_string : id -> string) (id : id)
    (span : Meta.span option) (name : string) (nm : names_maps) : names_maps =
  (* We do not use the same name map if we allow/disallow collisions.
     We notably use it for field names: some backends like Lean can use the
     type information to disambiguate field projections.

     Remark: we still need to check that those "unsafe" ids don't collide with
     the ids that we mark as "strict on collision".

     For instance, we don't allow naming a field "let". We enforce this by
     not checking collision between ids for which we permit collisions (ex.:
     between fields), but still checking collisions between those ids and the
     others (ex.: fields and keywords).
  *)
  if allow_collisions id then (
    (* Check with the ids which are considered to be strict on collisions *)
    names_map_check_collision id_to_string id span name nm.strict_names_map;
    {
      nm with
      unsafe_names_map = unsafe_names_map_add id name nm.unsafe_names_map;
    })
  else
    (* Remark: if we are strict on collisions:
       - we add the id to the strict collisions map
       - we check that the id doesn't collide with the unsafe map
       TODO: we might not check that:
       - a user defined function doesn't collide with an builtin function
       - two trait decl items don't collide with each other
    *)
    let strict_names_map =
      if strict_collisions id then
        names_map_add id_to_string (id, span) name nm.strict_names_map
      else nm.strict_names_map
    in
    let names_map = names_map_add id_to_string (id, span) name nm.names_map in
    { nm with strict_names_map; names_map }

(** The [id_to_string] function to print nice debugging messages if there are
    collisions *)
let names_maps_get (span : Meta.span option) (id_to_string : id -> string)
    (id : id) (nm : names_maps) : string =
  (* We do not use the same name map if we allow/disallow collisions *)
  let _map_to_string (m : string IdMap.t) : string =
    "[\n"
    ^ String.concat ","
        (List.map
           (fun (id, n) -> "\n  " ^ id_to_string id ^ " -> " ^ n)
           (IdMap.bindings m))
    ^ "\n]"
  in
  if allow_collisions id then (
    let m = nm.unsafe_names_map.id_to_name in
    match IdMap.find_opt id m with
    | Some s -> s
    | None ->
        let err = "Could not find: " ^ id_to_string id in
        [%save_error_opt_span] span err;
        "(%%%ERROR: unknown identifier\": " ^ id_to_string id ^ "\"%%%)")
  else
    let m = nm.names_map.id_to_name in
    match IdMap.find_opt id m with
    | Some s -> s
    | None -> (
        let err = "Could not find: " ^ id_to_string id in
        [%save_error_opt_span] span err;
        match backend () with
        | Lean -> "sorry /- " ^ err ^ "-/"
        | _ -> "(ERROR: " ^ id_to_string id ^ ")")

type names_map_init = {
  keywords : string list;
  builtin_adts : (builtin_ty * string) list;
  builtin_structs : (builtin_ty * string) list;
  builtin_variants : (builtin_ty * VariantId.id * string) list;
  builtin_llbc_functions : (A.builtin_fun_id * string) list;
  builtin_pure_functions : (pure_builtin_fun_id * string) list;
}

let names_maps_add_builtin_type (id_to_string : id -> string) (id : builtin_ty)
    (name : string) (nm : names_maps) : names_maps =
  names_maps_add id_to_string (TypeId (TBuiltin id)) None name nm

let names_maps_add_builtin_struct (id_to_string : id -> string)
    (id : builtin_ty) (name : string) (nm : names_maps) : names_maps =
  names_maps_add id_to_string (StructId (TBuiltin id)) None name nm

let names_maps_add_builtin_variant (id_to_string : id -> string)
    (id : builtin_ty) (variant_id : VariantId.id) (name : string)
    (nm : names_maps) : names_maps =
  names_maps_add id_to_string (VariantId (TBuiltin id, variant_id)) None name nm

let names_maps_add_function (id_to_string : id -> string)
    ((fid, span) : fun_id * span option) (name : string) (nm : names_maps) :
    names_maps =
  names_maps_add id_to_string (FunId fid) span name nm

let bool_name () = if backend () = Lean then "Bool" else "bool"
let char_name () = if backend () = Lean then "Char" else "char"
let str_name () = if backend () = Lean then "String" else "string"

(** Small helper to compute the name of an int type *)
let int_name (int_ty : integer_type) : string =
  let isize, usize, i_format, u_format =
    match backend () with
    | FStar | Coq | HOL4 ->
        ("isize", "usize", format_of_string "i%d", format_of_string "u%d")
    | Lean -> ("Isize", "Usize", format_of_string "I%d", format_of_string "U%d")
  in
  match int_ty with
  | Signed Isize -> isize
  | Signed I8 -> Printf.sprintf i_format 8
  | Signed I16 -> Printf.sprintf i_format 16
  | Signed I32 -> Printf.sprintf i_format 32
  | Signed I64 -> Printf.sprintf i_format 64
  | Signed I128 -> Printf.sprintf i_format 128
  | Unsigned Usize -> usize
  | Unsigned U8 -> Printf.sprintf u_format 8
  | Unsigned U16 -> Printf.sprintf u_format 16
  | Unsigned U32 -> Printf.sprintf u_format 32
  | Unsigned U64 -> Printf.sprintf u_format 64
  | Unsigned U128 -> Printf.sprintf u_format 128

let float_name (float_ty : float_type) : string =
  let format =
    match backend () with
    | FStar | Coq | HOL4 -> format_of_string "f%d"
    | Lean -> format_of_string "F%d"
  in
  match float_ty with
  | F16 -> Printf.sprintf format 16
  | F32 -> Printf.sprintf format 32
  | F64 -> Printf.sprintf format 64
  | F128 -> Printf.sprintf format 128

let scalar_name (ty : literal_type) : string =
  match ty with
  | TInt ty -> int_name (Signed ty)
  | TUInt ty -> int_name (Unsigned ty)
  | TFloat ty -> float_name ty
  | TBool -> (
      match backend () with
      | FStar | Coq | HOL4 -> "bool"
      | Lean -> "Bool")
  | TChar -> (
      match backend () with
      | FStar | Coq | HOL4 -> "char"
      | Lean -> "Char")

(** Extraction context.

    Note that the extraction context contains information coming from the LLBC
    AST (not only the pure AST). This is useful for naming, for instance: we use
    the region information to generate the names of the backward functions, etc.
*)
type extraction_ctx = {
  crate : A.crate;
  trans_ctx : trans_ctx;
  names_maps : names_maps;
  indent_incr : int;
      (** The indent increment we insert whenever we need to indent more *)
  use_dep_ite : bool;
      (** For Lean: do we use dependent-if then else expressions?

          Example:
          {[
            if h: b then ... else ...
            -- ^^
            -- makes the if then else dependent
          ]} *)
  trait_decl_id : trait_decl_id option;
      (** If we are extracting a trait declaration, identifies it *)
  trans_types : Pure.type_decl Pure.TypeDeclId.Map.t;
  trans_funs : pure_fun_translation A.FunDeclId.Map.t;
  trans_globals : Pure.global_decl Pure.GlobalDeclId.Map.t;
  builtin_sigs : Pure.fun_sig Builtin.BuiltinFunIdMap.t;
  functions_with_decreases_clause : PureUtils.FunLoopIdSet.t;
  trans_trait_decls : Pure.trait_decl Pure.TraitDeclId.Map.t;
  trans_trait_impls : Pure.trait_impl Pure.TraitImplId.Map.t;
  types_filter_type_args_map : bool list TypeDeclId.Map.t;
      (** The map to filter the type arguments for the builtin type definitions.

          We need this for type `Vec`, for instance, which takes a useless (in
          the context of the type translation) type argument for the allocator
          which is used, and which we want to remove.

          TODO: it would be cleaner to filter those types in a micro-pass,
          rather than at code generation time. *)
  funs_filter_type_args_map : bool list FunDeclId.Map.t;
      (** Same as {!types_filter_type_args_map}, but for functions *)
  trait_impls_filter_type_args_map : bool list TraitImplId.Map.t;
      (** Same as {!types_filter_type_args_map}, but for trait implementations
      *)
  extracted_opaque : bool ref;
      (** Set to true if at some point we extract a definition which is opaque,
          meaning we generate an axiom. If yes, and in case the user does not
          use the option [-split-files] we suggest it to the user. *)
}

let extraction_ctx_to_fmt_env (ctx : extraction_ctx) : PrintPure.fmt_env =
  TranslateCore.trans_ctx_to_pure_fmt_env ctx.trans_ctx

let extraction_ctx_to_llbc_fmt_env (ctx : extraction_ctx) : Print.fmt_env =
  TranslateCore.trans_ctx_to_fmt_env ctx.trans_ctx

let name_to_string (ctx : extraction_ctx) =
  PrintPure.name_to_string (extraction_ctx_to_fmt_env ctx)

let ty_to_string (ctx : extraction_ctx) =
  PrintPure.ty_to_string (extraction_ctx_to_fmt_env ctx) false

let llbc_generic_params_to_strings (ctx : extraction_ctx) =
  Print.Types.generic_params_to_strings (extraction_ctx_to_llbc_fmt_env ctx)

let llbc_generic_args_to_strings (ctx : extraction_ctx) =
  Print.Types.generic_args_to_strings (extraction_ctx_to_llbc_fmt_env ctx)

let trait_decl_id_to_string (ctx : extraction_ctx) =
  PrintPure.trait_decl_id_to_string (extraction_ctx_to_fmt_env ctx)

let trait_decl_ref_to_string (ctx : extraction_ctx) =
  PrintPure.trait_decl_ref_to_string (extraction_ctx_to_fmt_env ctx) false

let type_id_to_string (ctx : extraction_ctx) =
  PrintPure.type_id_to_string (extraction_ctx_to_fmt_env ctx)

let global_decl_id_to_string (ctx : extraction_ctx) =
  PrintPure.global_decl_id_to_string (extraction_ctx_to_fmt_env ctx)

let llbc_fun_id_to_string (ctx : extraction_ctx) =
  PrintPure.llbc_fun_id_to_string (extraction_ctx_to_fmt_env ctx)

let fun_id_to_string (ctx : extraction_ctx) =
  PrintPure.regular_fun_id_to_string (extraction_ctx_to_fmt_env ctx)

let adt_variant_to_string (span : Meta.span option) (ctx : extraction_ctx) =
  PrintPure.adt_variant_to_string ~span (extraction_ctx_to_fmt_env ctx)

let adt_field_to_string (span : Meta.span option) (ctx : extraction_ctx) =
  PrintPure.adt_field_to_string ~span (extraction_ctx_to_fmt_env ctx)

(** Debugging function, used when communicating name collisions to the user, and
    also to print ids for internal debugging (in case of lookup miss for
    instance). *)
let id_to_string (span : Meta.span option) (id : id) (ctx : extraction_ctx) :
    string =
  let trait_decl_id_to_string (id : A.TraitDeclId.id) : string =
    let trait_name = trait_decl_id_to_string ctx id in
    "trait_decl: " ^ trait_name ^ " (id: " ^ A.TraitDeclId.to_string id ^ ")"
  in
  match id with
  | GlobalId gid -> global_decl_id_to_string ctx gid
  | FunId fid -> fun_id_to_string ctx fid
  | DecreasesProofId (fid, lid) ->
      let fun_name = llbc_fun_id_to_string ctx fid in
      let loop =
        match lid with
        | None -> ""
        | Some lid -> ", loop: " ^ LoopId.to_string lid
      in
      "decreases proof for function: " ^ fun_name ^ loop
  | TerminationMeasureId (fid, lid) ->
      let fun_name = llbc_fun_id_to_string ctx fid in
      let loop =
        match lid with
        | None -> ""
        | Some lid -> ", loop: " ^ LoopId.to_string lid
      in
      "termination measure for function: " ^ fun_name ^ loop
  | TypeId id -> "type name: " ^ type_id_to_string ctx id
  | StructId id -> "struct constructor of: " ^ type_id_to_string ctx id
  | VariantId (id, variant_id) ->
      let type_name = type_id_to_string ctx id in
      let variant_name = adt_variant_to_string span ctx id (Some variant_id) in
      "type name: " ^ type_name ^ ", variant name: " ^ variant_name
  | FieldId (id, field_id) ->
      let type_name = type_id_to_string ctx id in
      let field_name = adt_field_to_string span ctx id field_id in
      "type name: " ^ type_name ^ ", field name: " ^ field_name
  | UnknownId -> "keyword"
  | FVarId id -> "var_id: " ^ FVarId.to_string id
  | TraitDeclId id -> "trait_decl_id: " ^ TraitDeclId.to_string id
  | TraitImplId id -> "trait_impl_id: " ^ TraitImplId.to_string id
  | TypeVarId (origin, id) ->
      "type_var_id: " ^ TypeVarId.to_string id ^ " from "
      ^ show_generic_origin origin
  | ConstGenericVarId (origin, id) ->
      "const_generic_var_id: "
      ^ ConstGenericVarId.to_string id
      ^ " from " ^ show_generic_origin origin
  | LocalTraitClauseId (origin, id) ->
      "local_trait_clause_id: " ^ TraitClauseId.to_string id ^ " from "
      ^ show_generic_origin origin
  | TraitDeclConstructorId id ->
      "trait_decl_constructor: " ^ trait_decl_id_to_string id
  | TraitParentClauseId (id, clause_id) ->
      "trait_parent_clause_id: " ^ trait_decl_id_to_string id ^ ", clause_id: "
      ^ TraitClauseId.to_string clause_id
  | TraitItemId (id, name) ->
      "trait_item_id: " ^ trait_decl_id_to_string id ^ ", type name: " ^ name
  | TraitMethodId (trait_decl_id, fun_name) ->
      trait_decl_id_to_string trait_decl_id ^ ", method name: " ^ fun_name

let ctx_add (span : Meta.span) (id : id) (name : string) (ctx : extraction_ctx)
    : extraction_ctx =
  let id_to_string (id : id) : string = id_to_string (Some span) id ctx in
  let names_maps =
    names_maps_add id_to_string id (Some span) name ctx.names_maps
  in
  { ctx with names_maps }

let ctx_get (span : Meta.span option) (id : id) (ctx : extraction_ctx) : string
    =
  let id_to_string (id : id) : string = id_to_string span id ctx in
  names_maps_get span id_to_string id ctx.names_maps

let ctx_get_global (span : Meta.span) (id : A.GlobalDeclId.id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (GlobalId id) ctx

let ctx_get_function (span : Meta.span) (id : fun_id) (ctx : extraction_ctx) :
    string =
  ctx_get (Some span) (FunId id) ctx

let ctx_get_local_function (span : Meta.span) (id : A.FunDeclId.id)
    (lp : LoopId.id option) (ctx : extraction_ctx) : string =
  ctx_get_function span (FromLlbc (FunId (FRegular id), lp)) ctx

let ctx_get_type (span : Meta.span option) (id : type_id) (ctx : extraction_ctx)
    : string =
  [%sanity_check_opt_span] span (id <> TTuple);
  ctx_get span (TypeId id) ctx

let ctx_get_local_type (span : Meta.span) (id : TypeDeclId.id)
    (ctx : extraction_ctx) : string =
  ctx_get_type (Some span) (TAdtId id) ctx

let ctx_get_builtin_type (span : Meta.span option) (id : builtin_ty)
    (ctx : extraction_ctx) : string =
  ctx_get_type span (TBuiltin id) ctx

let ctx_get_trait_constructor (span : Meta.span) (id : trait_decl_id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitDeclConstructorId id) ctx

let ctx_get_trait_decl (span : Meta.span) (id : trait_decl_id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitDeclId id) ctx

let ctx_get_trait_impl (span : Meta.span) (id : trait_impl_id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitImplId id) ctx

let ctx_get_trait_item (span : Meta.span) (id : trait_decl_id)
    (item_name : string) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitItemId (id, item_name)) ctx

let ctx_get_trait_const (span : Meta.span) (id : trait_decl_id)
    (item_name : string) (ctx : extraction_ctx) : string =
  ctx_get_trait_item span id item_name ctx

let ctx_get_trait_type (span : Meta.span) (id : trait_decl_id)
    (item_name : string) (ctx : extraction_ctx) : string =
  ctx_get_trait_item span id item_name ctx

let ctx_get_trait_method (span : Meta.span) (id : trait_decl_id)
    (item_name : string) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitMethodId (id, item_name)) ctx

let ctx_get_trait_parent_clause (span : Meta.span) (id : trait_decl_id)
    (clause : trait_clause_id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitParentClauseId (id, clause)) ctx

let ctx_get_var (span : Meta.span) (id : FVarId.id) (ctx : extraction_ctx) :
    string =
  ctx_get (Some span) (FVarId id) ctx

(** This warrants explanations. Charon supports several levels of nested
    binders; however there are currently only two cases where we bind
    non-lifetime variables: at the top-level of each item, and for each method
    inside a trait_decl/trait_impl. Moreover, we use `Free` vars to identify
    item-bound vars. This means that we can identify which binder a variable
    comes from without rigorously tracking binder levels, which is what this
    function does. Note that the `de_bruijn_id`s are wrong anyway because we
    kept charon's binding levels but forgot all the region binders. *)
let origin_from_de_bruijn_var (var : 'a de_bruijn_var) : generic_origin * 'a =
  match var with
  | Bound (_, id) -> (Method, id)
  | Free id -> (Item, id)

let ctx_get_type_var (span : Meta.span) (origin : generic_origin)
    (id : TypeVarId.id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TypeVarId (origin, id)) ctx

let ctx_get_const_generic_var (span : Meta.span) (origin : generic_origin)
    (id : ConstGenericVarId.id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (ConstGenericVarId (origin, id)) ctx

let ctx_get_local_trait_clause (span : Meta.span) (origin : generic_origin)
    (id : TraitClauseId.id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (LocalTraitClauseId (origin, id)) ctx

let ctx_get_field (span : Meta.span) (type_id : type_id) (field_id : FieldId.id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (FieldId (type_id, field_id)) ctx

let ctx_get_struct (span : Meta.span) (def_id : type_id) (ctx : extraction_ctx)
    : string =
  ctx_get (Some span) (StructId def_id) ctx

let ctx_get_variant (span : Meta.span) (def_id : type_id)
    (variant_id : VariantId.id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (VariantId (def_id, variant_id)) ctx

let ctx_get_decreases_proof (span : Meta.span) (def_id : A.FunDeclId.id)
    (loop_id : LoopId.id option) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (DecreasesProofId (FRegular def_id, loop_id)) ctx

let ctx_get_termination_measure (span : Meta.span) (def_id : A.FunDeclId.id)
    (loop_id : LoopId.id option) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TerminationMeasureId (FRegular def_id, loop_id)) ctx

(** Small helper to compute the name of a unary operation *)
let unop_name (unop : unop) : string =
  match unop with
  | Not ty -> (
      match backend () with
      | FStar -> (
          match ty with
          | None -> "not"
          | Some int_ty -> int_name int_ty ^ "_not")
      | Lean -> begin
          match ty with
          | None -> "¬"
          | Some _ -> "~~~"
        end
      | Coq -> if Option.is_none ty then "negb" else "scalar_not"
      | HOL4 -> "~")
  | Neg (int_ty : integer_type) -> (
      match backend () with
      | Lean -> "-."
      | _ -> int_name int_ty ^ "_neg")
  | ArrayToSlice -> (
      match backend () with
      | Lean -> "Array.to_slice"
      | _ -> "array_to_slice")
  | Cast _ ->
      (* We never directly use the unop name in this case *)
      raise (Failure "Unsupported")

(** Small helper to compute the name of a binary operation (note that many
    binary operations like "less than" are extracted to primitive operations,
    like [<]). *)
let named_binop_name (binop : E.binop) (int_ty : integer_type) : string =
  let binop_s =
    match binop with
    | Div _ -> "div"
    | Rem _ -> "rem"
    | Add _ -> "add"
    | Sub _ -> "sub"
    | Mul _ -> "mul"
    | Lt -> "lt"
    | Le -> "le"
    | Ge -> "ge"
    | Gt -> "gt"
    | BitXor -> "xor"
    | BitAnd -> "and"
    | BitOr -> "or"
    | Shl _ -> "shl"
    | Shr _ -> "shr"
    | _ -> raise (Failure "Unreachable")
  in
  (* Remark: the Lean case is actually not used *)
  match backend () with
  | Lean -> int_name int_ty ^ "." ^ binop_s
  | FStar | Coq | HOL4 -> int_name int_ty ^ "_" ^ binop_s

(** A list of keywords/identifiers used by the backend and with which we want to
    check collision.

    Remark: this is useful mostly to look for collisions when generating names
    for *variables*. *)
let keywords () =
  let named_unops =
    unop_name (Not None)
    :: List.map
         (fun it -> unop_name (Not (Some (Signed it))))
         T.all_signed_int_types
    @ List.map (fun it -> unop_name (Neg (Signed it))) T.all_signed_int_types
  in
  let named_binops =
    [ E.Div OPanic; Rem OPanic; Add OPanic; Sub OPanic; Mul OPanic ]
  in
  let named_binops =
    List.concat_map
      (fun bn -> List.map (fun it -> named_binop_name bn it) T.all_int_types)
      named_binops
  in
  let misc =
    match backend () with
    | FStar ->
        [
          "assert";
          "assert_norm";
          "assume";
          "else";
          "end";
          "fun";
          "fn";
          "FStar";
          "FStar.Mul";
          "if";
          "in";
          "include";
          "int";
          "let";
          "list";
          "match";
          "open";
          "rec";
          "scalar_cast";
          "then";
          "type";
          "Type0";
          "Type";
          "unit";
          "val";
          "with";
        ]
    | Coq ->
        [
          "assert";
          "Arguments";
          "Axiom";
          "char_of_byte";
          "Check";
          "Declare";
          "Definition";
          "else";
          "end";
          "End";
          "fun";
          "Fixpoint";
          "if";
          "in";
          "int";
          "Inductive";
          "Import";
          "let";
          "Lemma";
          "match";
          "Module";
          "not";
          "Notation";
          "Proof";
          "Qed";
          "rec";
          "Record";
          "Require";
          "Scope";
          "Search";
          "SearchPattern";
          "Set";
          "then";
          (* [tt] is unit *)
          "tt";
          "type";
          "Type";
          "unit";
          "with";
        ]
    | Lean ->
        [
          "Pi";
          "Prop";
          "Sort";
          "Type";
          "abbrev";
          "alias";
          "as";
          "at";
          "attribute";
          "axiom";
          "axioms";
          "begin";
          "break";
          "by";
          "calc";
          "catch";
          "class";
          "const";
          "constant";
          "constants";
          "continue";
          "decreasing_by";
          "def";
          "definition";
          "deriving";
          "do";
          "else";
          "end";
          "example";
          "exists";
          "export";
          "extends";
          "for";
          "forall";
          "from";
          "fun";
          "have";
          "hiding";
          "if";
          "import";
          "in";
          "include";
          "inductive";
          "infix";
          "infixl";
          "infixr";
          "instance";
          "lemma";
          "let";
          "local";
          "macro";
          "macro_rules";
          "match";
          "mut";
          "mutual";
          "namespace";
          "noncomputable";
          "notation";
          "omit";
          "opaque";
          "opaque_defs";
          "open";
          "override";
          "parameter";
          "parameters";
          "partial";
          "postfix";
          "precedence";
          "prefix";
          "prelude";
          "private";
          "protected";
          "raw";
          "record";
          "reduce";
          "renaming";
          "replacing";
          "reserve";
          "run_cmd";
          "section";
          "set_option";
          "simp";
          "structure";
          "syntax";
          "termination_by";
          "then";
          "theorem";
          "theory";
          "universe";
          "universes";
          "unless";
          "unsafe";
          "using";
          "using_well_founded";
          "variable";
          "variables";
          "where";
          "with";
        ]
    | HOL4 ->
        [
          "Axiom";
          "case";
          "Definition";
          "else";
          "End";
          "fix";
          "fix_exec";
          "fn";
          "fun";
          "if";
          "in";
          "int";
          "Inductive";
          "let";
          "of";
          "Proof";
          "QED";
          "then";
          "Theorem";
        ]
  in
  List.concat [ named_unops; named_binops; misc ]

let builtin_adts () : (builtin_ty * string) list =
  (* We voluntarily omit the type [Error]: it is never directly
     referenced in the generated translation, and easily collides
     with user-defined types *)
  match backend () with
  | Lean ->
      [
        (TResult, "Result");
        (TFuel, "Nat");
        (TArray, "Array");
        (TSlice, "Slice");
        (TStr, "Str");
        (TRawPtr Mut, "MutRawPtr");
        (TRawPtr Const, "ConstRawPtr");
      ]
  | Coq | FStar | HOL4 ->
      [
        (TResult, "result");
        (TFuel, if backend () = HOL4 then "num" else "nat");
        (TArray, "array");
        (TSlice, "slice");
        (TStr, "str");
        (TRawPtr Mut, "mut_raw_ptr");
        (TRawPtr Const, "const_raw_ptr");
      ]

let builtin_struct_constructors () : (builtin_ty * string) list =
  match backend () with
  | Lean -> [ (TArray, "Array.make") ]
  | Coq -> [ (TArray, "mk_array") ]
  | FStar -> [ (TArray, "mk_array") ]
  | HOL4 -> [ (TArray, "mk_array") ]

let builtin_variants () : (builtin_ty * VariantId.id * string) list =
  match backend () with
  | FStar ->
      [
        (TResult, result_ok_id, "Ok");
        (TResult, result_fail_id, "Fail");
        (TError, error_failure_id, "Failure");
        (TError, error_out_of_fuel_id, "OutOfFuel");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
      ]
  | Coq ->
      [
        (TResult, result_ok_id, "Ok");
        (TResult, result_fail_id, "Fail_");
        (TError, error_failure_id, "Failure");
        (TError, error_out_of_fuel_id, "OutOfFuel");
        (TFuel, fuel_zero_id, "O");
        (TFuel, fuel_succ_id, "S");
      ]
  | Lean ->
      [
        (TResult, result_ok_id, "ok");
        (TResult, result_fail_id, "fail");
        (TError, error_failure_id, "panic");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
      ]
  | HOL4 ->
      [
        (TResult, result_ok_id, "Ok");
        (TResult, result_fail_id, "Fail");
        (TError, error_failure_id, "Failure");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
      ]

let builtin_llbc_functions () : (A.builtin_fun_id * string) list =
  match backend () with
  | FStar | Coq | HOL4 ->
      [
        (ArrayToSliceShared, "array_to_slice");
        (ArrayToSliceMut, "array_to_slice_mut");
        (ArrayRepeat, "array_repeat");
        ( Index { is_array = true; mutability = RShared; is_range = false },
          "array_index_usize" );
        ( Index { is_array = true; mutability = RMut; is_range = false },
          "array_index_mut_usize" );
        ( Index { is_array = false; mutability = RShared; is_range = false },
          "slice_index_usize" );
        ( Index { is_array = false; mutability = RMut; is_range = false },
          "slice_index_mut_usize" );
      ]
  | Lean ->
      [
        (ArrayToSliceShared, "Array.to_slice");
        (ArrayToSliceMut, "Array.to_slice_mut");
        (ArrayRepeat, "Array.repeat");
        ( Index { is_array = true; mutability = RShared; is_range = false },
          "Array.index_usize" );
        ( Index { is_array = true; mutability = RMut; is_range = false },
          "Array.index_mut_usize" );
        ( Index { is_array = false; mutability = RShared; is_range = false },
          "Slice.index_usize" );
        ( Index { is_array = false; mutability = RMut; is_range = false },
          "Slice.index_mut_usize" );
      ]

let builtin_pure_functions () : (pure_builtin_fun_id * string) list =
  match backend () with
  | FStar ->
      [
        (Return, "return");
        (Fail, "fail");
        (Assert, "massert");
        (FuelDecrease, "decrease");
        (FuelEqZero, "is_zero");
        (UpdateAtIndex Slice, "slice_update_usize");
        (UpdateAtIndex Array, "array_update_usize");
        (ToResult, "return");
      ]
  | Coq ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [
        (Return, "return_");
        (Fail, "fail_");
        (Assert, "massert");
        (UpdateAtIndex Slice, "slice_update_usize");
        (UpdateAtIndex Array, "array_update_usize");
        (ToResult, "return_");
      ]
  | Lean ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [
        (Return, "return");
        (Fail, "fail_");
        (Assert, "massert");
        (UpdateAtIndex Slice, "Slice.update");
        (UpdateAtIndex Array, "Array.update");
        (ToResult, "↑");
      ]
  | HOL4 ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [
        (Return, "return");
        (Fail, "fail");
        (Assert, "massert");
        (UpdateAtIndex Slice, "slice_update_usize");
        (UpdateAtIndex Array, "array_update_usize");
        (ToResult, "return");
      ]

let names_map_init () : names_map_init =
  {
    keywords = keywords ();
    builtin_adts = builtin_adts ();
    builtin_structs = builtin_struct_constructors ();
    builtin_variants = builtin_variants ();
    builtin_llbc_functions = builtin_llbc_functions ();
    builtin_pure_functions = builtin_pure_functions ();
  }

(** Initialize names maps with a proper set of keywords/names coming from the
    target language/prover. *)
let initialize_names_maps () : names_maps =
  let init = names_map_init () in
  let int_names = List.map int_name T.all_int_types in
  let keywords =
    (* Remark: we don't put "str_name()" below because it clashes with
       "alloc::string::String", which we register elsewhere. *)
    List.concat [ [ bool_name (); char_name () ]; int_names; init.keywords ]
  in
  let names_set = StringSet.empty in
  let name_to_id = StringMap.empty in
  (* We fist initialize [id_to_name] as empty, because the id of a keyword is [UnknownId].
   * Also note that we don't need this mapping for keywords: we insert keywords only
   * to check collisions. *)
  let id_to_name = IdMap.empty in
  let names_map = { id_to_name; name_to_id; names_set } in
  let unsafe_names_map = empty_unsafe_names_map in
  let strict_names_map = empty_names_map in
  (* For debugging - we are creating bindings for builtin types and functions, so
   * it is ok if we simply use the "show" function (those aren't simply identified
   * by numbers) *)
  let id_to_string = show_id in
  (* Add the keywords as strict collisions *)
  let strict_names_map =
    List.fold_left
      (fun nm name ->
        (* There is duplication in the keywords so we don't check the collisions
           while registering them (what is important is that there are no collisions
           between keywords and user-defined identifiers) *)
        names_map_add_unchecked (UnknownId, None) name nm)
      strict_names_map keywords
  in
  let nm = { names_map; unsafe_names_map; strict_names_map } in
  (* Then we add:
   * - the builtin types
   * - the builtin struct constructors
   * - the builtin variants
   * - the builtin functions
   *)
  let nm =
    List.fold_left
      (fun nm (type_id, name) ->
        names_maps_add_builtin_type id_to_string type_id name nm)
      nm init.builtin_adts
  in
  let nm =
    List.fold_left
      (fun nm (type_id, name) ->
        names_maps_add_builtin_struct id_to_string type_id name nm)
      nm init.builtin_structs
  in
  let nm =
    List.fold_left
      (fun nm (type_id, variant_id, name) ->
        names_maps_add_builtin_variant id_to_string type_id variant_id name nm)
      nm init.builtin_variants
  in
  let builtin_functions =
    List.map
      (fun (fid, name) ->
        ((FromLlbc (Pure.FunId (FBuiltin fid), None), None), name))
      init.builtin_llbc_functions
    @ List.map
        (fun (fid, name) -> ((Pure fid, None), name))
        init.builtin_pure_functions
  in
  let nm =
    List.fold_left
      (fun nm (fid, name) -> names_maps_add_function id_to_string fid name nm)
      nm builtin_functions
  in
  (* Return *)
  nm

(** Compute the qualified for a type definition/declaration.

    For instance: "type", "and", etc.

    Remark: can return [None] for some backends like HOL4. *)
let type_decl_kind_to_qualif (span : Meta.span) (kind : decl_kind)
    (type_kind : type_decl_kind option) : string option =
  match backend () with
  | FStar -> (
      match kind with
      | SingleNonRec -> Some "type"
      | SingleRec -> Some "type"
      | MutRecFirst -> Some "type"
      | MutRecInner -> Some "and"
      | MutRecLast -> Some "and"
      | Builtin -> Some "assume type"
      | Declared -> Some "val")
  | Coq -> (
      match (kind, type_kind) with
      | SingleNonRec, Some Tuple -> Some "Definition"
      | SingleNonRec, Some Enum -> Some "Inductive"
      | SingleNonRec, Some Struct -> Some "Record"
      | (SingleRec | MutRecFirst), Some _ -> Some "Inductive"
      | (MutRecInner | MutRecLast), Some _ ->
          (* Coq doesn't support groups of mutually recursive definitions which mix
           * records and inductives: we convert everything to records if this happens
           *)
          Some "with"
      | (Builtin | Declared), None -> Some "Axiom"
      | SingleNonRec, None ->
          (* This is for traits *)
          Some "Record"
      | _ ->
          [%craise] span
            ("Unexpected: (" ^ show_decl_kind kind ^ ", "
            ^ Print.option_to_string show_type_decl_kind type_kind
            ^ ")"))
  | Lean -> (
      match kind with
      | SingleNonRec -> (
          match type_kind with
          | Some Tuple -> Some "def"
          | Some Struct -> Some "structure"
          | _ -> Some "inductive")
      | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> Some "inductive"
      | Builtin -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

(** Compute the qualified for a function definition/declaration.

    For instance: "let", "let rec", "and", etc.

    Remark: can return [None] for some backends like HOL4. *)
let fun_decl_kind_to_qualif (kind : decl_kind) : string option =
  match backend () with
  | FStar -> (
      match kind with
      | SingleNonRec -> Some "let"
      | SingleRec -> Some "let rec"
      | MutRecFirst -> Some "let rec"
      | MutRecInner -> Some "and"
      | MutRecLast -> Some "and"
      | Builtin -> Some "assume val"
      | Declared -> Some "val")
  | Coq -> (
      match kind with
      | SingleNonRec -> Some "Definition"
      | SingleRec -> Some "Fixpoint"
      | MutRecFirst -> Some "Fixpoint"
      | MutRecInner -> Some "with"
      | MutRecLast -> Some "with"
      | Builtin -> Some "Axiom"
      | Declared -> Some "Axiom")
  | Lean -> (
      match kind with
      | SingleNonRec -> Some "def"
      | SingleRec -> Some "def"
      | MutRecFirst -> Some "mutual def"
      | MutRecInner -> Some "def"
      | MutRecLast -> Some "def"
      | Builtin -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

(** Compute the qualifier to add after the definition. *)
let fun_decl_kind_to_post_qualif (kind : decl_kind) : string option =
  match backend () with
  | FStar | Coq | HOL4 -> None
  | Lean -> (
      match kind with
      | SingleNonRec | Builtin | Declared -> None
      | SingleRec | MutRecFirst | MutRecInner | MutRecLast ->
          Some "partial_fixpoint")

(** The type of types.

    TODO: move inside the formatter? *)
let type_keyword (span : Meta.span) =
  match backend () with
  | FStar -> "Type0"
  | Coq | Lean -> "Type"
  | HOL4 -> [%craise] span "Unexpected"

(** Helper *)
let name_last_elem_as_ident (span : Meta.span) (n : llbc_name) : string =
  match Collections.List.last n with
  | PeIdent (s, _) -> s
  | _ -> [%craise] span "Unexpected"

(** Helper

    Prepare a name. The first id elem is always the crate: if it is the local
    crate, we remove it. We ignore disambiguators (there may be collisions, but
    we check if there are). *)
let ctx_prepare_name (meta : T.item_meta) (ctx : extraction_ctx)
    (name : llbc_name) : llbc_name =
  (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
  match name with
  | [ _ ] -> name
  | (PeIdent (crate, _) as id) :: name ->
      if crate = ctx.crate.name then name else id :: name
  | _ ->
      [%craise] meta.span
        ("Unexpected name shape: "
        ^ TranslateCore.name_to_string ctx.trans_ctx name)

(** Helper *)
let ctx_compute_simple_name (meta : T.item_meta) (ctx : extraction_ctx)
    (name : llbc_name) : string list =
  (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
  let name = if meta.is_local then ctx_prepare_name meta ctx name else name in
  name_to_simple_name ctx.trans_ctx name

(** Helper *)
let ctx_compute_simple_type_name = ctx_compute_simple_name

(** Helper *)
let ctx_compute_type_name_no_suffix (ctx : extraction_ctx)
    (item_meta : Types.item_meta) (name : llbc_name) : string =
  let name = rename_llbc_name item_meta.attr_info name in
  flatten_name (ctx_compute_simple_type_name item_meta ctx name)

(** Provided a basename, compute a type name.

    This is an auxiliary helper that we use to compute type declaration names,
    but also for instance field and variant names when we need to add the name
    of the type as a prefix. *)
let ctx_compute_type_name (item_meta : Types.item_meta) (ctx : extraction_ctx)
    (name : llbc_name) =
  let name = ctx_compute_type_name_no_suffix ctx item_meta name in
  match backend () with
  | FStar -> StringUtils.lowercase_first_letter (name ^ "_t")
  | Coq | HOL4 -> name ^ "_t"
  | Lean -> name

(** Inputs:
    - type name
    - field id
    - field name

    Note that fields don't always have names, but we still need to generate some
    names if we want to extract the structures to records. For nameless fields,
    we generate a name based on the index.

    Note that in most situations we extract structures with nameless fields to
    tuples, meaning generating names by using indices shouldn't be too much of a
    problem. *)
let ctx_compute_field_name (def : type_decl) (field_meta : Meta.attr_info)
    (ctx : extraction_ctx) (def_name : llbc_name) (field_id : FieldId.id)
    (field_name : string option) : string =
  (* If the user did not provide a name, use the field index. *)
  let field_name_s =
    Option.value field_name ~default:(FieldId.to_string field_id)
  in
  (* Replace the name of the field if the user annotated it with the [rename] attribute. *)
  let field_name_s = Option.value field_meta.rename ~default:field_name_s in
  (* Prefix the name with the name of the type, if necessary (some backends don't
     support field name collisions) *)
  let def_name = rename_llbc_name def.item_meta.attr_info def_name in
  let name =
    if !Config.record_fields_short_names then
      if field_name = None then (* TODO: this is a bit ugly *)
        "_" ^ field_name_s
      else field_name_s
    else
      ctx_compute_type_name_no_suffix ctx def.item_meta def_name
      ^ "_" ^ field_name_s
  in
  match backend () with
  | Lean | HOL4 -> name
  | Coq | FStar -> StringUtils.lowercase_first_letter name

(** Inputs:
    - type name
    - variant name *)
let ctx_compute_variant_name (ctx : extraction_ctx) (def : type_decl)
    (variant : variant) : string =
  (* Replace the name of the variant if the user annotated it with the [rename] attribute. *)
  let variant =
    Option.value variant.variant_attr_info.rename ~default:variant.variant_name
  in
  match backend () with
  | FStar | Coq | HOL4 ->
      let variant = to_camel_case variant in
      (* Prefix the name of the variant with the name of the type, if necessary
         (some backends don't support collision of variant names) *)
      if !variant_concatenate_type_name then
        StringUtils.capitalize_first_letter
          (ctx_compute_type_name_no_suffix ctx def.item_meta def.item_meta.name
          ^ "_" ^ variant)
      else variant
  | Lean -> variant

(** Structure constructors are used when constructing structure values.

    For instance, in F*:
    {[
      type pair = { x : nat; y : nat }
      let p : pair = Mkpair 0 1
    ]}

    Inputs:
    - type name *)
let ctx_compute_struct_constructor (def : type_decl) (ctx : extraction_ctx)
    (basename : llbc_name) : string =
  let tname = ctx_compute_type_name def.item_meta ctx basename in
  ExtractBuiltin.mk_struct_constructor tname

let ctx_compute_fun_name_no_suffix (meta : T.item_meta) (ctx : extraction_ctx)
    (fname : llbc_name) : string =
  (* Check if the function is a method implementation for a blanket impl.
     If it is the case, add a path element to avoid name collisions *)
  let rec is_blanket_method (name : llbc_name) : bool =
    match name with
    | [] | [ _ ] -> false
    | [ PeImpl (ImplElemTrait impl_id); _ ] ->
        (* This is a trait impl method: check if the impl is a blanket impl *)
        let trait_impl =
          [%silent_unwrap] meta.span
            (TraitImplId.Map.find_opt impl_id ctx.trans_trait_impls)
        in
        let args = trait_impl.llbc_impl_trait.generics in
        begin
          match args.types with
          | TVar _ :: _ -> true
          | _ -> false
        end
    | _ :: name -> is_blanket_method name
  in
  let is_blanket = is_blanket_method fname in
  [%ldebug "fname: " ^ name_to_string ctx fname];
  let fname = ctx_compute_simple_name meta ctx fname in
  (* Add the blanket path elem if the method is a blanket method *)
  let fname =
    if is_blanket then
      let fname, last = Collections.List.pop_last fname in
      fname @ [ "Blanket"; last ]
    else fname
  in
  (* TODO: don't convert to snake case for Coq, HOL4, F* *)
  let fname = flatten_name fname in
  match backend () with
  | FStar | Coq | HOL4 -> StringUtils.lowercase_first_letter fname
  | Lean -> fname

(** Provided a basename, compute the name of a global declaration. *)
let ctx_compute_global_name (meta : T.item_meta) (ctx : extraction_ctx)
    (name : llbc_name) : string =
  let name = ctx_compute_simple_name meta ctx name in
  match Config.backend () with
  | Coq | FStar | HOL4 ->
      let parts = List.map to_snake_case name in
      String.concat "_" parts
  | Lean -> flatten_name name

(** Helper function: generate a suffix for a function name, i.e., generates a
    suffix like "_loop", "loop1", etc. to append to a function name. *)
let default_fun_loop_suffix (num_loops : int) (loop_id : LoopId.id option) :
    string =
  match loop_id with
  | None -> ""
  | Some loop_id ->
      (* If this is for a loop, generally speaking, we append the loop index.
         If this function admits only one loop, we omit it. *)
      if num_loops = 1 then "_loop" else "_loop" ^ LoopId.to_string loop_id

(** A helper function: generates a function suffix. TODO: move all those
    helpers. *)
let default_fun_suffix (num_loops : int) (loop_id : LoopId.id option) : string =
  (* We only generate a suffix for the functions we generate from the loops *)
  default_fun_loop_suffix num_loops loop_id

(** Compute the name of a regular (non-builtin) function.

    Inputs:
    - function basename (TODO: shouldn't appear for builtin functions?...)
    - number of loops in the function (useful to check if we need to use indices
      to derive unique names for the loops for instance - if there is exactly
      one loop, we don't need to use indices)
    - loop id (if pertinent) TODO: use the fun id for the builtin functions. *)
let ctx_compute_fun_name (meta : T.item_meta) (ctx : extraction_ctx)
    (fname : llbc_name) (num_loops : int) (loop_id : LoopId.id option) : string
    =
  let fname = ctx_compute_fun_name_no_suffix meta ctx fname in
  (* Compute the suffix *)
  let suffix = default_fun_suffix num_loops loop_id in
  (* Concatenate *)
  fname ^ suffix

let ctx_compute_trait_decl_name (ctx : extraction_ctx) (trait_decl : trait_decl)
    : string =
  let llbc_name =
    rename_llbc_name trait_decl.item_meta.attr_info trait_decl.item_meta.name
  in
  ctx_compute_type_name trait_decl.item_meta ctx llbc_name

let ctx_compute_trait_impl_name (ctx : extraction_ctx) (trait_decl : trait_decl)
    (trait_impl : trait_impl) : string =
  (* We derive the trait impl name from the implemented trait.
     For instance, if this implementation is an instance of `trait::Trait`
     for `<foo::Foo, u32>`, we generate the name: "trait.TraitFooFooU32Inst".
     Importantly, it is to be noted that the name is independent of the place
     where the instance has been defined (it is indepedent of the file, etc.).

     Note that if the user provided a [rename] attribute, we simply use that.
  *)
  let name =
    match trait_impl.item_meta.attr_info.rename with
    | None ->
        let name =
          let params = trait_impl.llbc_generics in
          let args = trait_impl.llbc_impl_trait.generics in
          let name =
            ctx_prepare_name trait_impl.item_meta ctx trait_decl.item_meta.name
          in
          let name = rename_llbc_name trait_impl.item_meta.attr_info name in
          let name =
            trait_name_with_generics_to_simple_name ctx.trans_ctx name params
              args
          in
          (* We detect blanket impls and add a "blanket" suffix to avoid name
             clashes. *)
          let name =
            match args.types with
            | TVar _ :: _ -> name @ [ "Blanket" ]
            | _ -> name
          in
          name
        in
        flatten_name name
    | Some name -> name
  in
  (* Additional modifications to make sure we comply with the backends restrictions *)
  match backend () with
  | FStar -> StringUtils.lowercase_first_letter name
  | Coq | HOL4 | Lean -> name

let ctx_compute_trait_decl_constructor (ctx : extraction_ctx)
    (trait_decl : trait_decl) : string =
  let name = ctx_compute_trait_decl_name ctx trait_decl in
  ExtractBuiltin.mk_struct_constructor name

(** Helper to derive names for parent trait clauses and for variables for trait
    instances.

    We derive the name from the type of the clause (i.e., the trait ref the
    clause implements). For instance, if a trait clause is for the trait ref
    "Trait<Box<usize>", we generate a name like "traitBoxUsizeInst". This is
    more meaningful that giving it a generic name with an index (such as
    "parent_clause_1" or "inst3").

    Because we want to be precise when deriving the name, we use the original
    LLBC types, that is the types from before the translation to pure, which
    simplifies types like boxes and references. *)
let ctx_compute_trait_clause_name (ctx : extraction_ctx)
    (current_def_name : Types.name) (params : Types.generic_params)
    (clauses : Types.trait_param list) (clause_id : trait_clause_id) : string =
  (* We derive the name of the clause from the trait instance.
     For instance, if the clause gives us an instance of `Foo<u32>`,
     we generate a name along the lines of "fooU32Inst".
  *)
  let clause =
    (* If the current def and the trait decl referenced by the clause
       are in the same namespace, we try to simplify the names. We do so by
       removing the common prefixes in their names.

       For instance, if we have:
       {[
         // This is file traits.rs
         trait Parent {}

         trait Child : Parent {}
       ]}
       For the parent clause of trait [Child] we would like to generate
       the name: "ParentInst", rather than "traitParentInst".
    *)
    let prefix = Some current_def_name in
    let clause =
      List.find (fun (c : Types.trait_param) -> c.clause_id = clause_id) clauses
    in
    (* Note that we ignore the binder *)
    let clause_trait = clause.trait.binder_value in
    (* *)
    let trait_id = clause_trait.id in
    (* The declaration may be missing because of an error *)
    match TraitDeclId.Map.find_opt trait_id ctx.crate.trait_decls with
    | None -> [ "clause" ]
    | Some impl_trait_decl ->
        let args = clause_trait.generics in
        trait_name_with_generics_to_simple_name ctx.trans_ctx ~prefix
          impl_trait_decl.item_meta.name params args
  in
  String.concat "" clause

let ctx_compute_trait_parent_clause_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (clause : trait_param) : string =
  (* We derive the name of the clause from the trait instance.
     For instance, if the clause gives us an instance of `Foo<u32>`,
     we generate a name along the lines of "fooU32Inst".
  *)
  (* We need to lookup the LLBC definitions, to have the original instantiation *)
  let clause =
    let current_def_name = trait_decl.item_meta.name in
    let params = trait_decl.llbc_generics in
    ctx_compute_trait_clause_name ctx current_def_name params
      trait_decl.llbc_parent_clauses clause.clause_id
  in
  let clause =
    if !Config.record_fields_short_names then clause
    else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ clause
  in
  let clause = clause ^ "Inst" in
  match backend () with
  | FStar -> StringUtils.lowercase_first_letter clause
  | Coq | HOL4 | Lean -> clause

let ctx_compute_trait_type_name (ctx : extraction_ctx) (trait_decl : trait_decl)
    (item : string) : string =
  let name =
    if !Config.record_fields_short_names then item
    else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ item
  in
  (* Constants are usually all capital letters.
     Some backends do not support field names starting with a capital letter,
     and it may be weird to lowercase everything (especially as it may lead
     to more name collisions): we add a prefix when necessary.
     For instance, it gives: "U" -> "tU"
     Note that for some backends we prepend the type name (because those backends
     can't disambiguate fields coming from different ADTs if they have the same
     names), and thus don't need to add a prefix starting with a lowercase.
  *)
  match backend () with
  | FStar -> "t" ^ name
  | Coq | Lean | HOL4 -> name

let ctx_compute_trait_const_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) : string =
  let name =
    if !Config.record_fields_short_names then item
    else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ item
  in
  (* See [trait_type_name] *)
  match backend () with
  | FStar -> "c" ^ name
  | Coq | Lean | HOL4 -> name

let ctx_compute_trait_method_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) : string =
  if !Config.record_fields_short_names then item
  else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ item

let ctx_compute_trait_type_clause_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) (clause : trait_param) : string =
  (* TODO: improve - it would be better to not use indices *)
  ctx_compute_trait_type_name ctx trait_decl item
  ^ "_clause_"
  ^ TraitClauseId.to_string clause.clause_id

(** Generates the name of the termination measure used to prove/reason about
    termination. The generated code uses this clause where needed, but its body
    must be defined by the user.

    F* and Lean only.

    Inputs:
    - function id: this is especially useful to identify whether the function is
      an builtin function or a local function
    - function basename
    - the number of loops in the parent function. This is used for the same
      purpose as in [llbc_name].
    - loop identifier, if this is for a loop *)
let ctx_compute_termination_measure_name (meta : T.item_meta)
    (ctx : extraction_ctx) (_fid : A.FunDeclId.id) (fname : llbc_name)
    (num_loops : int) (loop_id : LoopId.id option) : string =
  let fname = ctx_compute_fun_name_no_suffix meta ctx fname in
  let lp_suffix = default_fun_loop_suffix num_loops loop_id in
  (* Compute the suffix *)
  let suffix =
    match Config.backend () with
    | FStar -> "_decreases"
    | Lean -> "_terminates"
    | Coq | HOL4 -> [%craise] meta.span "Unexpected"
  in
  (* Concatenate *)
  fname ^ lp_suffix ^ suffix

(** Generates the name of the proof used to prove/reason about termination. The
    generated code uses this clause where needed, but its body must be defined
    by the user.

    Lean only.

    Inputs:
    - function id: this is especially useful to identify whether the function is
      an builtin function or a local function
    - function basename
    - the number of loops in the parent function. This is used for the same
      purpose as in [llbc_name].
    - loop identifier, if this is for a loop *)
let ctx_compute_decreases_proof_name (meta : T.item_meta) (ctx : extraction_ctx)
    (_fid : A.FunDeclId.id) (fname : llbc_name) (num_loops : int)
    (loop_id : LoopId.id option) : string =
  let fname = ctx_compute_fun_name_no_suffix meta ctx fname in
  let lp_suffix = default_fun_loop_suffix num_loops loop_id in
  (* Compute the suffix *)
  let suffix =
    match Config.backend () with
    | Lean -> "_decreases"
    | FStar | Coq | HOL4 -> [%craise] meta.span "Unexpected"
  in
  (* Concatenate *)
  fname ^ lp_suffix ^ suffix

(** Generates a variable basename.

    Inputs:
    - the set of names used in the context so far
    - the basename we got from the symbolic execution, if we have one
    - the type of the variable (can be useful for heuristics, in order not to
      always use "x" for instance, whenever naming anonymous variables)

    Note that once the formatter generated a basename, we add an index if
    necessary to prevent name clashes: the burden of name clashes checks is thus
    on the caller's side. *)
let ctx_compute_var_basename (span : Meta.span) (ctx : extraction_ctx)
    (basename : string option) (ty : ty) : string =
  (* Small helper to derive var names from ADT type names.

     We do the following:
     - convert the type name to snake case
     - take the first letter of every "letter group"
     Ex.: "HashMap" -> "hash_map" -> "hm"
  *)
  let name_from_type_ident (name : string) : string =
    let cl = to_snake_case name in
    let cl = String.split_on_char '_' cl in
    let cl = List.filter (fun s -> String.length s > 0) cl in
    [%sanity_check] span (List.length cl > 0);
    let cl = List.map (fun s -> s.[0]) cl in
    StringUtils.string_of_chars cl
  in
  (* If there is a basename, we use it *)
  match basename with
  | Some basename -> (
      (* This should be a no-op *)
      match Config.backend () with
      | Lean -> basename
      | FStar | Coq | HOL4 -> to_snake_case basename)
  | None -> (
      (* No basename: we use the first letter of the type *)
      match ty with
      | TAdt (type_id, generics) -> (
          match type_id with
          | TTuple ->
              (* The "pair" case is frequent enough to have its special treatment *)
              if List.length generics.types = 2 then "p" else "t"
          | TBuiltin TResult -> "r"
          | TBuiltin TError -> ConstStrings.error_basename
          | TBuiltin TFuel -> ConstStrings.fuel_basename
          | TBuiltin TSum -> "s"
          | TBuiltin TLoopResult -> "r"
          | TBuiltin TArray -> "a"
          | TBuiltin TSlice -> "s"
          | TBuiltin TStr -> "s"
          | TBuiltin (TRawPtr _) -> "p"
          | TAdtId adt_id ->
              let def =
                TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
              in
              (* Derive the var name from the last ident of the type name
                 Ex.: ["hashmap"; "HashMap"] ~~> "HashMap" -> "hash_map" -> "hm"
              *)
              (* The name shouldn't be empty, and its last element should
               * be an ident *)
              let cl = Collections.List.last def.item_meta.name in
              name_from_type_ident (TypesUtils.as_ident cl))
      | TVar _ -> (
          (* TODO: use "t" also for F* *)
          match backend () with
          | FStar -> "x" (* lacking inspiration here... *)
          | Coq | Lean | HOL4 -> "t" (* lacking inspiration here... *))
      | TLiteral lty -> (
          match lty with
          | TBool -> "b"
          | TChar -> "c"
          | TInt _ | TUInt _ -> "i"
          | TFloat _ -> "fl")
      | TArrow _ -> "f"
      | TTraitType (_, name) -> name_from_type_ident name
      | Error -> "x")

(** Generates a type variable basename. *)
let ctx_compute_type_var_basename (_ctx : extraction_ctx) (basename : string) :
    string =
  (* Rust type variables are snake-case and start with a capital letter *)
  match backend () with
  | FStar ->
      (* This is *not* a no-op: this removes the capital letter *)
      to_snake_case basename
  | HOL4 ->
      (* In HOL4, type variable names must start with "'" *)
      "'" ^ to_snake_case basename
  | Coq | Lean -> basename

(** Generates a const generic variable basename. *)
let ctx_compute_const_generic_var_basename (_ctx : extraction_ctx)
    (basename : string) : string =
  (* Rust type variables are snake-case and start with a capital letter *)
  match backend () with
  | FStar | HOL4 ->
      (* This is *not* a no-op: this removes the capital letter *)
      to_snake_case basename
  | Coq | Lean -> basename

(** Return a base name for a trait clause. We might add a suffix to prevent
    collisions.

    In the traduction we explicitely manipulate the trait clause instances, that
    is we introduce one input variable for each trait clause. *)
let ctx_compute_trait_clause_basename (ctx : extraction_ctx)
    (current_def_name : Types.name) (params : Types.generic_params)
    (clause_id : trait_clause_id) : string =
  (* This is similar to {!ctx_compute_trait_parent_clause_name}: we
     derive the name from the trait reference (i.e., from the type) *)
  let clause =
    ctx_compute_trait_clause_name ctx current_def_name params
      params.trait_clauses clause_id
  in
  let clause = clause ^ "Inst" in
  match backend () with
  | FStar | Coq | HOL4 -> StringUtils.lowercase_first_letter clause
  | Lean -> clause

let trait_self_clause_basename = "self_clause"

(** Appends an index to a name - we use this to generate unique names: when
    doing so, the role of the formatter is just to concatenate indices to names,
    the responsability of finding a proper index is delegated to helper
    functions. *)
let name_append_index (basename : string) (i : int) : string =
  basename ^ string_of_int i

let basename_to_unique (ctx : extraction_ctx) (name : string) =
  let collision s =
    (* Note that we ignore the "unsafe" names which contain in particular
       field names: we want to allow using field names for variables if
       the backend allows such collisions *)
    StringSet.mem s ctx.names_maps.names_map.names_set
    || StringSet.mem s ctx.names_maps.strict_names_map.names_set
  in

  basename_to_unique_aux collision name_append_index name

(** Generate a unique type variable name and add it to the context *)
let ctx_add_type_var (span : Meta.span) (origin : generic_origin)
    (basename : string) (id : TypeVarId.id) (ctx : extraction_ctx) :
    extraction_ctx * string =
  let name = ctx_compute_type_var_basename ctx basename in
  let name = basename_to_unique ctx name in
  let ctx = ctx_add span (TypeVarId (origin, id)) name ctx in
  (ctx, name)

(** Generate a unique const generic variable name and add it to the context *)
let ctx_add_const_generic_var (span : Meta.span) (origin : generic_origin)
    (basename : string) (id : ConstGenericVarId.id) (ctx : extraction_ctx) :
    extraction_ctx * string =
  let name = ctx_compute_const_generic_var_basename ctx basename in
  let name = basename_to_unique ctx name in
  let ctx = ctx_add span (ConstGenericVarId (origin, id)) name ctx in
  (ctx, name)

(** See {!ctx_add_type_var} *)
let ctx_add_type_vars (span : Meta.span) (origin : generic_origin)
    (vars : (string * TypeVarId.id) list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (name, id) -> ctx_add_type_var span origin name id ctx)
    ctx vars

(** Generate a unique variable name and add it to the context *)
let ctx_add_var (span : Meta.span) (basename : string) (id : FVarId.id)
    (ctx : extraction_ctx) : extraction_ctx * string =
  let name = basename_to_unique ctx basename in
  let ctx = ctx_add span (FVarId id) name ctx in
  (ctx, name)

(** Generate a unique trait clause name and add it to the context *)
let ctx_add_local_trait_clause (span : Meta.span) (origin : generic_origin)
    (basename : string) (id : TraitClauseId.id) (ctx : extraction_ctx) :
    extraction_ctx * string =
  let name = basename_to_unique ctx basename in
  let ctx = ctx_add span (LocalTraitClauseId (origin, id)) name ctx in
  (ctx, name)

(** See {!ctx_add_var} *)
let ctx_add_vars (span : Meta.span) (vars : fvar list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (v : fvar) ->
      let name = ctx_compute_var_basename span ctx v.basename v.ty in
      ctx_add_var span name v.id ctx)
    ctx vars

let ctx_add_type_params (span : Meta.span) (origin : generic_origin)
    (vars : type_param list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (var : type_param) ->
      ctx_add_type_var span origin var.name var.index ctx)
    ctx vars

let ctx_add_const_generic_params (span : Meta.span) (origin : generic_origin)
    (vars : const_generic_param list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (var : const_generic_param) ->
      ctx_add_const_generic_var span origin var.name var.index ctx)
    ctx vars

(** Returns the lists of names for:
    - the type variables
    - the const generic variables
    - the trait clauses

    For the [current_name_def] and the [llbc_generics]: we use them to derive
    pretty names for the trait clauses. See {!ctx_compute_trait_clause_name} for
    additional information. *)
let ctx_add_local_trait_clauses (span : Meta.span)
    (current_def_name : Types.name) (origin : generic_origin)
    (llbc_generics : Types.generic_params) (clauses : trait_param list)
    (ctx : extraction_ctx) : extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (c : trait_param) ->
      let basename =
        ctx_compute_trait_clause_basename ctx current_def_name llbc_generics
          c.clause_id
      in
      ctx_add_local_trait_clause span origin basename c.clause_id ctx)
    ctx clauses

(** Returns the lists of names for:
    - the type variables
    - the const generic variables
    - the trait clauses

    For the [current_name_def] and the [llbc_generics]: we use them to derive
    pretty names for the trait clauses. See {!ctx_compute_trait_clause_name} for
    additional information. *)
let ctx_add_generic_params (span : Meta.span) (current_def_name : Types.name)
    (origin : generic_origin) (llbc_generics : Types.generic_params)
    (generics : generic_params) (ctx : extraction_ctx) :
    extraction_ctx * string list * string list * string list =
  let { types; const_generics; trait_clauses } = generics in
  let ctx, tys = ctx_add_type_params span origin types ctx in
  let ctx, cgs = ctx_add_const_generic_params span origin const_generics ctx in
  let ctx, tcs =
    ctx_add_local_trait_clauses span current_def_name origin llbc_generics
      trait_clauses ctx
  in
  (ctx, tys, cgs, tcs)

let ctx_add_decreases_proof (def : fun_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  let name = rename_llbc_name def.item_meta.attr_info def.item_meta.name in
  let name =
    ctx_compute_decreases_proof_name def.item_meta ctx def.def_id name
      def.num_loops def.loop_id
  in
  ctx_add def.item_meta.span
    (DecreasesProofId (FRegular def.def_id, def.loop_id))
    name ctx

let ctx_add_termination_measure (def : fun_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  let name = rename_llbc_name def.item_meta.attr_info def.item_meta.name in
  let name =
    ctx_compute_termination_measure_name def.item_meta ctx def.def_id name
      def.num_loops def.loop_id
  in
  ctx_add def.item_meta.span
    (TerminationMeasureId (FRegular def.def_id, def.loop_id))
    name ctx

let ctx_add_global_decl_and_body (def : global_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  (* TODO: update once the body id can be an option *)
  let decl = GlobalId def.def_id in

  (* Check if the global corresponds to an builtin global that we should map
     to a custom definition in our standard library (for instance, happens
     with "core::num::usize::MAX") *)
  match def.builtin_info with
  | Some info ->
      (* Yes: register the custom binding *)
      ctx_add def.item_meta.span decl info.global_name ctx
  | None ->
      (* Not the case: "standard" registration *)
      let name = rename_llbc_name def.item_meta.attr_info def.item_meta.name in
      let name = ctx_compute_global_name def.item_meta ctx name in

      let body = FunId (FromLlbc (FunId (FRegular def.body_id), None)) in
      (* If this is a provided constant (i.e., the default value for a constant
         in a trait declaration) we add a suffix. Otherwise there is a clash
         between the name for the default constant and the name for the field
         in the trait declaration *)
      let suffix =
        match def.src with
        | TraitDeclItem (_, _, true) -> "_default"
        | _ -> ""
      in
      let ctx = ctx_add def.item_meta.span decl (name ^ suffix) ctx in
      let ctx = ctx_add def.item_meta.span body (name ^ suffix ^ "_body") ctx in
      ctx

(** - [is_trait_decl_field]: [true] if we are computing the name of a field in a
      trait declaration, [false] if we are computing the name of a function
      declaration. *)
let ctx_compute_fun_name (def : fun_decl) (is_trait_decl_field : bool)
    (ctx : extraction_ctx) : string =
  (* Rename the function, if the user added a [rename] attribute.

     We have to do something peculiar for the implementation of trait
     methods, by looking up the meta information of the method *declaration*
     because this is where the attribute is.

     Note that if the user also added an attribute for the *implementation*,
     we keep this one.
  *)
  let item_meta =
    match def.src with
    | TraitImplItem (_, trait_decl_ref, item_name, _) -> (
        if Option.is_some def.item_meta.attr_info.rename then def.item_meta
        else
          (* Lookup the declaration. TODO: the trait item impl info
             should directly give us the id of the method declaration. *)
          match
            TraitDeclId.Map.find_opt trait_decl_ref.id ctx.trans_trait_decls
          with
          | None -> def.item_meta
          | Some trait_decl -> (
              match
                List.find_opt
                  (fun (name, _) -> name = item_name)
                  trait_decl.methods
              with
              | None -> def.item_meta
              | Some (_, bound_fn) ->
                  Option.value
                    (Option.map
                       (fun (def : A.fun_decl) -> def.item_meta)
                       (FunDeclId.Map.find_opt bound_fn.binder_value.fun_id
                          ctx.trans_ctx.fun_ctx.fun_decls))
                    ~default:def.item_meta))
    | _ -> def.item_meta
  in
  let llbc_name = rename_llbc_name item_meta.attr_info def.item_meta.name in
  [%ldebug "llbc_name after renaming: " ^ name_to_string ctx llbc_name];
  (* When a trait method has a default implementation, this becomes a [fun_decl]
     that we may want to extract. By default, its name is [Trait::method], which
     for lean creates a name clash with the method name as a field in the trait
     struct. We therefore rename these function items to avoid the name clash by
     adding the "default" suffix.
  *)
  let llbc_name =
    if is_trait_decl_field then llbc_name
    else
      match def.src with
      | TraitDeclItem (_, _, true) ->
          llbc_name @ [ PeIdent ("default", Disambiguator.zero) ]
      | _ -> llbc_name
  in
  [%ldebug
    "llbc_name after adding 'default' suffix (for default methods): "
    ^ name_to_string ctx llbc_name];
  ctx_compute_fun_name def.item_meta ctx llbc_name def.num_loops def.loop_id

(* TODO: move to Extract *)
let ctx_add_fun_decl (def : fun_decl) (ctx : extraction_ctx) : extraction_ctx =
  (* Sanity check: the function should not be a global body - those are handled
   * separately *)
  [%sanity_check] def.item_meta.span (not def.is_global_decl_body);
  let def_id = def.def_id in
  (* Add the function name *)
  let def_name = ctx_compute_fun_name def false ctx in
  let fun_id = (Pure.FunId (FRegular def_id), def.loop_id) in
  ctx_add def.item_meta.span (FunId (FromLlbc fun_id)) def_name ctx

let ctx_compute_type_decl_name (ctx : extraction_ctx) (def : type_decl) : string
    =
  ctx_compute_type_name def.item_meta ctx def.item_meta.name
