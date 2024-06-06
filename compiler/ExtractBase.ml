(** Define base utilities for the extraction *)

open Contexts
open Pure
open StringUtils
open Config
module F = Format
open ExtractBuiltin
open TranslateCore
open Errors

(** The local logger *)
let log = Logging.extract_log

type region_group_info = {
  id : RegionGroupId.id;
      (** The id of the region group.
          Note that a simple way of generating unique names for backward
          functions is to use the region group ids.
       *)
  region_names : string option list;
      (** The names of the region variables included in this group.
          Note that names are not always available...
       *)
}

module StringSet = Collections.StringSet
module StringMap = Collections.StringMap

(** Characterizes a declaration.

    Is in particular useful to derive the proper keywords to introduce the
    declarations/definitions.
 *)
type decl_kind =
  | SingleNonRec
      (** A single, non-recursive definition.

          F*:  [let x = ...]
          Coq: [Definition x := ...]
       *)
  | SingleRec
      (** A single, recursive definition.

          F*:  [let rec x = ...]
          Coq: [Fixpoint x := ...]
       *)
  | MutRecFirst
      (** The first definition of a group of mutually-recursive definitions.

          F*:  [type x0 = ... and x1 = ...]
          Coq: [Fixpoint x0 := ... with x1 := ...]
       *)
  | MutRecInner
      (** An inner definition in a group of mutually-recursive definitions. *)
  | MutRecLast
      (** The last definition in a group of mutually-recursive definitions.

          We need this because in some theorem provers like Coq, we need to
          delimit group of mutually recursive definitions (in particular, we
          need to insert an end delimiter).
       *)
  | Assumed
      (** An assumed definition.

         F*:  [assume val x]
         Coq: [Axiom x : Type.]
      *)
  | Declared
      (** Declare a type in an interface or a module signature.

          Rem.: for now, in Coq, we don't declare module signatures: we
          thus assume the corresponding declarations.

          F*:  [val x : Type0]
          Coq: [Axiom x : Type.]
       *)
[@@deriving show]

(** Return [true] if the declaration is the last from its group of declarations.

    We need this because in some provers (e.g., Coq), we need to delimit the
    end of a (group of) definition(s) (in Coq: with a ".").
 *)
let decl_is_last_from_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | MutRecLast | Assumed | Declared -> true
  | MutRecFirst | MutRecInner -> false

let decl_is_from_rec_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | Assumed | Declared -> false
  | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> true

let decl_is_from_mut_rec_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | Assumed | Declared -> false
  | MutRecFirst | MutRecInner | MutRecLast -> true

let decl_is_first_from_group (kind : decl_kind) : bool =
  match kind with
  | SingleNonRec | SingleRec | MutRecFirst | Assumed | Declared -> true
  | MutRecLast | MutRecInner -> false

(** Return [true] if the declaration is not the last from its group of declarations.

    We need this because in some provers (e.g., HOL4), we need to delimit
    the inner declarations (with `/\` for instance).
 *)
let decl_is_not_last_from_group (kind : decl_kind) : bool =
  not (decl_is_last_from_group kind)

type type_decl_kind = Enum | Struct | Tuple [@@deriving show]

(** We use identifiers to look for name clashes *)
type id =
  | GlobalId of A.GlobalDeclId.id
  | FunId of fun_id
  | TerminationMeasureId of (A.fun_id * LoopId.id option)
      (** The definition which provides the decreases/termination measure.
          We insert calls to this clause to prove/reason about termination:
          the body of those clauses must be defined by the user, in the
          proper files.

          More specifically:
          - in F*, this is the content of the [decreases] clause.
            Example:
            ========
            {[
              let rec sum (ls : list nat) : Tot nat (decreases ls) = ...
            ]}
          - in Lean, this is the content of the [termination_by] clause.
       *)
  | DecreasesProofId of (A.fun_id * LoopId.id option)
      (** The definition which provides the decreases/termination proof.
          We insert calls to this clause to prove/reason about termination:
          the body of those clauses must be defined by the user, in the
          proper files.

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
          ]}
       *)
  | VariantId of type_id * VariantId.id
      (** If often happens that variant names must be unique (it is the case in
          F* ) which is why we register them here.
       *)
  | FieldId of type_id * FieldId.id
      (** If often happens that in the case of structures, the field names
          must be unique (it is the case in F* ) which is why we register
          them here.
       *)
  | TypeVarId of TypeVarId.id
  | ConstGenericVarId of ConstGenericVarId.id
  | VarId of VarId.id
  | TraitDeclId of TraitDeclId.id
  | TraitImplId of TraitImplId.id
  | LocalTraitClauseId of TraitClauseId.id
  | TraitDeclConstructorId of TraitDeclId.id
  | TraitMethodId of TraitDeclId.id * string
  | TraitItemId of TraitDeclId.id * string
      (** A trait associated item which is not a method *)
  | TraitParentClauseId of TraitDeclId.id * TraitClauseId.id
  | TraitItemClauseId of TraitDeclId.id * string * TraitClauseId.id
  | TraitSelfClauseId
      (** Specifically for the clause: [Self : Trait].

          For now, we forbid provided methods (methods in trait declarations
          with a default implementation) from being overriden in trait implementations.
          We extract trait provided methods such that they take an instance of
          the trait as input: this instance is given by the trait self clause.

          For instance:
          {[
            //
            // Rust
            //
            trait ToU64 {
              fn to_u64(&self) -> u64;

              // Provided method
              fn is_pos(&self) -> bool {
                self.to_u64() > 0
              }
            }

            //
            // Generated code
            //
            struct ToU64 (T : Type) {
              to_u64 : T -> u64;
            }

            //                    The trait self clause
            //                    vvvvvvvvvvvvvvvvvvvvvv
            let is_pos (T : Type) (trait_self : ToU64 T) (self : T) : bool =
              trait_self.to_u64 self > 0
          ]}
       *)
  | UnknownId
      (** Used for stored various strings like keywords, definitions which
          should always be in context, etc. and which can't be linked to one
          of the above.

          TODO: rename to "keyword"
       *)
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

    We use it for lookups (during the translation) and to check for name clashes.

    [id_to_name] is for debugging.
  *)
type names_map = {
  id_to_name : string IdMap.t;
  name_to_id : (id * Meta.span option) StringMap.t;
      (** The name to id map is used to look for name clashes, and generate nice
          debugging messages: if there is a name clash, it is useful to know
          precisely which identifiers are mapped to the same name...
       *)
  names_set : StringSet.t;
}

let empty_names_map : names_map =
  {
    id_to_name = IdMap.empty;
    name_to_id = StringMap.empty;
    names_set = StringSet.empty;
  }

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
    ^ "\nYou may want to rename some of your definitions, or report an issue."
  in
  (* Register the error.

     We don't link this error to any span information because we already put
     the span information about the two problematic definitions in the error
     message above. *)
  save_error __FILE__ __LINE__ None err

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
     save_error __FILE__ __LINE__ span err);
  (* Insert *)
  names_map_add_unchecked (id, span) name nm

(** The unsafe names map stores mappings from identifiers to names which might
    collide. For some backends and some names, it might be acceptable to have
    collisions. For instance, in Lean, different records can have fields with
    the same name because Lean uses the typing information to resolve the
    ambiguities.

    This map complements the {!type:names_map}, which checks for collisions.
  *)
type unsafe_names_map = { id_to_name : string IdMap.t }

let empty_unsafe_names_map = { id_to_name = IdMap.empty }

let unsafe_names_map_add (id : id) (name : string) (nm : unsafe_names_map) :
    unsafe_names_map =
  { id_to_name = IdMap.add id name nm.id_to_name }

(** Make a (variable) basename unique (by adding an index).

    We do this in an inefficient manner (by testing all indices starting from
    0) but it shouldn't be a bottleneck.

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
    function's structure. The consequence is that we often end up
    copy-pasting function bodies. As in the proofs (in assertions and
    when calling lemmas) we often need to talk about the "past" (i.e.,
    previous values), it is very useful to generate code where all variable
    names are assigned at most once.

    [append]: function to append an index to a string
 *)
let basename_to_unique_aux (collision : string -> bool)
    (append : string -> int -> string) (basename : string) : string =
  let rec gen (i : int) : string =
    let s = append basename i in
    if collision s then gen (i + 1) else s
  in
  if collision basename then gen 1 else basename

type names_maps = {
  names_map : names_map;
      (** The map for id to names, where we forbid name collisions
          (ex.: we always forbid function name collisions). *)
  unsafe_names_map : unsafe_names_map;
      (** The map for id to names, where we allow name collisions
          (ex.: we might allow record field name collisions). *)
  strict_names_map : names_map;
      (** This map is a sub-map of [names_map]. For the ids in this map we also
          forbid collisions with names in the [unsafe_names_map].

          We do so for keywords for instance, but also for types (in a dependently
          typed language, we might have an issue if the field of a record has, say,
          the name "u32", and another field of the same record refers to "u32"
          (for instance in its type).
       *)
}

(** Return [true] if we are strict on collisions for this id (i.e., we forbid
    collisions even with the ids in the unsafe names map) *)
let strict_collisions (id : id) : bool =
  match id with UnknownId | TypeId _ -> true | _ -> false

(** We might not check for collisions for some specific ids (ex.: field names) *)
let allow_collisions (id : id) : bool =
  match id with
  | FieldId _ | TraitItemClauseId _ | TraitParentClauseId _ | TraitItemId _
  | TraitMethodId _ ->
      !Config.record_fields_short_names
  | FunId (Pure _ | FromLlbc (FunId (FAssumed _), _)) ->
      (* We map several assumed functions to the same id *)
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
       - a user defined function doesn't collide with an assumed function
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
  let map_to_string (m : string IdMap.t) : string =
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
        let err =
          "Could not find: " ^ id_to_string id ^ "\nNames map:\n"
          ^ map_to_string m
        in
        save_error __FILE__ __LINE__ span err;
        "(%%%ERROR: unknown identifier\": " ^ id_to_string id ^ "\"%%%)")
  else
    let m = nm.names_map.id_to_name in
    match IdMap.find_opt id m with
    | Some s -> s
    | None ->
        let err =
          "Could not find: " ^ id_to_string id ^ "\nNames map:\n"
          ^ map_to_string m
        in
        save_error __FILE__ __LINE__ span err;
        "(ERROR: \"" ^ id_to_string id ^ "\")"

type names_map_init = {
  keywords : string list;
  assumed_adts : (assumed_ty * string) list;
  assumed_structs : (assumed_ty * string) list;
  assumed_variants : (assumed_ty * VariantId.id * string) list;
  assumed_llbc_functions : (A.assumed_fun_id * string) list;
  assumed_pure_functions : (pure_assumed_fun_id * string) list;
}

let names_maps_add_assumed_type (id_to_string : id -> string) (id : assumed_ty)
    (name : string) (nm : names_maps) : names_maps =
  names_maps_add id_to_string (TypeId (TAssumed id)) None name nm

let names_maps_add_assumed_struct (id_to_string : id -> string)
    (id : assumed_ty) (name : string) (nm : names_maps) : names_maps =
  names_maps_add id_to_string (StructId (TAssumed id)) None name nm

let names_maps_add_assumed_variant (id_to_string : id -> string)
    (id : assumed_ty) (variant_id : VariantId.id) (name : string)
    (nm : names_maps) : names_maps =
  names_maps_add id_to_string (VariantId (TAssumed id, variant_id)) None name nm

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
  | Isize -> isize
  | I8 -> Printf.sprintf i_format 8
  | I16 -> Printf.sprintf i_format 16
  | I32 -> Printf.sprintf i_format 32
  | I64 -> Printf.sprintf i_format 64
  | I128 -> Printf.sprintf i_format 128
  | Usize -> usize
  | U8 -> Printf.sprintf u_format 8
  | U16 -> Printf.sprintf u_format 16
  | U32 -> Printf.sprintf u_format 32
  | U64 -> Printf.sprintf u_format 64
  | U128 -> Printf.sprintf u_format 128

let scalar_name (ty : literal_type) : string =
  match ty with
  | TInteger ty -> int_name ty
  | TBool -> (
      match backend () with FStar | Coq | HOL4 -> "bool" | Lean -> "Bool")
  | TChar -> (
      match backend () with FStar | Coq | HOL4 -> "char" | Lean -> "Char")

(** Extraction context.

    Note that the extraction context contains information coming from the
    LLBC AST (not only the pure AST). This is useful for naming, for instance:
    we use the region information to generate the names of the backward
    functions, etc.
 *)
type extraction_ctx = {
  (* mutable _span : Meta.span; *)
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
          ]}
        *)
  trait_decl_id : trait_decl_id option;
      (** If we are extracting a trait declaration, identifies it *)
  is_provided_method : bool;
  trans_types : Pure.type_decl Pure.TypeDeclId.Map.t;
  trans_funs : pure_fun_translation A.FunDeclId.Map.t;
  functions_with_decreases_clause : PureUtils.FunLoopIdSet.t;
  trans_trait_decls : Pure.trait_decl Pure.TraitDeclId.Map.t;
  trans_trait_impls : Pure.trait_impl Pure.TraitImplId.Map.t;
  types_filter_type_args_map : bool list TypeDeclId.Map.t;
      (** The map to filter the type arguments for the builtin type
          definitions.

          We need this for type `Vec`, for instance, which takes a useless
          (in the context of the type translation) type argument for the
          allocator which is used, and which we want to remove.

          TODO: it would be cleaner to filter those types in a micro-pass,
          rather than at code generation time.
        *)
  funs_filter_type_args_map : bool list FunDeclId.Map.t;
      (** Same as {!types_filter_type_args_map}, but for functions *)
  trait_impls_filter_type_args_map : bool list TraitImplId.Map.t;
      (** Same as {!types_filter_type_args_map}, but for trait implementations *)
}

let extraction_ctx_to_fmt_env (ctx : extraction_ctx) : PrintPure.fmt_env =
  TranslateCore.trans_ctx_to_pure_fmt_env ctx.trans_ctx

let name_to_string (ctx : extraction_ctx) =
  PrintPure.name_to_string (extraction_ctx_to_fmt_env ctx)

let trait_decl_id_to_string (ctx : extraction_ctx) =
  PrintPure.trait_decl_id_to_string (extraction_ctx_to_fmt_env ctx)

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

(** Debugging function, used when communicating name collisions to the user,
    and also to print ids for internal debugging (in case of lookup miss for
    instance).
 *)
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
  | TypeVarId id -> "type_var_id: " ^ TypeVarId.to_string id
  | ConstGenericVarId id ->
      "const_generic_var_id: " ^ ConstGenericVarId.to_string id
  | VarId id -> "var_id: " ^ VarId.to_string id
  | TraitDeclId id -> "trait_decl_id: " ^ TraitDeclId.to_string id
  | TraitImplId id -> "trait_impl_id: " ^ TraitImplId.to_string id
  | LocalTraitClauseId id ->
      "local_trait_clause_id: " ^ TraitClauseId.to_string id
  | TraitDeclConstructorId id ->
      "trait_decl_constructor: " ^ trait_decl_id_to_string id
  | TraitParentClauseId (id, clause_id) ->
      "trait_parent_clause_id: " ^ trait_decl_id_to_string id ^ ", clause_id: "
      ^ TraitClauseId.to_string clause_id
  | TraitItemClauseId (id, item_name, clause_id) ->
      "trait_item_clause_id: " ^ trait_decl_id_to_string id ^ ", item name: "
      ^ item_name ^ ", clause_id: "
      ^ TraitClauseId.to_string clause_id
  | TraitItemId (id, name) ->
      "trait_item_id: " ^ trait_decl_id_to_string id ^ ", type name: " ^ name
  | TraitMethodId (trait_decl_id, fun_name) ->
      trait_decl_id_to_string trait_decl_id ^ ", method name: " ^ fun_name
  | TraitSelfClauseId -> "trait_self_clause"

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
  sanity_check_opt_span __FILE__ __LINE__ (id <> TTuple) span;
  ctx_get span (TypeId id) ctx

let ctx_get_local_type (span : Meta.span) (id : TypeDeclId.id)
    (ctx : extraction_ctx) : string =
  ctx_get_type (Some span) (TAdtId id) ctx

let ctx_get_assumed_type (span : Meta.span option) (id : assumed_ty)
    (ctx : extraction_ctx) : string =
  ctx_get_type span (TAssumed id) ctx

let ctx_get_trait_constructor (span : Meta.span) (id : trait_decl_id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitDeclConstructorId id) ctx

let ctx_get_trait_self_clause (span : Meta.span) (ctx : extraction_ctx) : string
    =
  ctx_get (Some span) TraitSelfClauseId ctx

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

let ctx_get_trait_item_clause (span : Meta.span) (id : trait_decl_id)
    (item : string) (clause : trait_clause_id) (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TraitItemClauseId (id, item, clause)) ctx

let ctx_get_var (span : Meta.span) (id : VarId.id) (ctx : extraction_ctx) :
    string =
  ctx_get (Some span) (VarId id) ctx

let ctx_get_type_var (span : Meta.span) (id : TypeVarId.id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (TypeVarId id) ctx

let ctx_get_const_generic_var (span : Meta.span) (id : ConstGenericVarId.id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (ConstGenericVarId id) ctx

let ctx_get_local_trait_clause (span : Meta.span) (id : TraitClauseId.id)
    (ctx : extraction_ctx) : string =
  ctx_get (Some span) (LocalTraitClauseId id) ctx

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
  | Not -> (
      match backend () with
      | FStar -> "not"
      | Lean -> "¬"
      | Coq -> "negb"
      | HOL4 -> "~")
  | Neg (int_ty : integer_type) -> (
      match backend () with Lean -> "-." | _ -> int_name int_ty ^ "_neg")
  | Cast _ ->
      (* We never directly use the unop name in this case *)
      raise (Failure "Unsupported")

(** Small helper to compute the name of a binary operation (note that many
    binary operations like "less than" are extracted to primitive operations,
    like [<]).
 *)
let named_binop_name (binop : E.binop) (int_ty : integer_type) : string =
  let binop_s =
    match binop with
    | Div -> "div"
    | Rem -> "rem"
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Lt -> "lt"
    | Le -> "le"
    | Ge -> "ge"
    | Gt -> "gt"
    | BitXor -> "xor"
    | BitAnd -> "and"
    | BitOr -> "or"
    | Shl -> "shl"
    | Shr -> "shr"
    | _ -> raise (Failure "Unreachable")
  in
  (* Remark: the Lean case is actually not used *)
  match backend () with
  | Lean -> int_name int_ty ^ "." ^ binop_s
  | FStar | Coq | HOL4 -> int_name int_ty ^ "_" ^ binop_s

(** A list of keywords/identifiers used by the backend and with which we
    want to check collision.

    Remark: this is useful mostly to look for collisions when generating
    names for *variables*.
 *)
let keywords () =
  let named_unops =
    unop_name Not
    :: List.map (fun it -> unop_name (Neg it)) T.all_signed_int_types
  in
  let named_binops = [ E.Div; Rem; Add; Sub; Mul ] in
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

let assumed_adts () : (assumed_ty * string) list =
  let state =
    if !use_state then
      match backend () with
      | Lean -> [ (TState, "State") ]
      | Coq | FStar | HOL4 -> [ (TState, "state") ]
    else []
  in
  (* We voluntarily omit the type [Error]: it is never directly
     referenced in the generated translation, and easily collides
     with user-defined types *)
  let adts =
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
  in
  state @ adts

let assumed_struct_constructors () : (assumed_ty * string) list =
  match backend () with
  | Lean -> [ (TArray, "Array.make") ]
  | Coq -> [ (TArray, "mk_array") ]
  | FStar -> [ (TArray, "mk_array") ]
  | HOL4 -> [ (TArray, "mk_array") ]

let assumed_variants () : (assumed_ty * VariantId.id * string) list =
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
        (TResult, result_ok_id, "Result.ok");
        (TResult, result_fail_id, "Result.fail");
        (* For panic: we omit the prefix "Error." because the type is always
           clear from the context. Also, "Error" is often used by user-defined
           types (when we omit the crate as a prefix). *)
        (TError, error_failure_id, ".panic");
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

let assumed_llbc_functions () : (A.assumed_fun_id * string) list =
  match backend () with
  | FStar | Coq | HOL4 ->
      [
        (ArrayIndexShared, "array_index_usize");
        (ArrayIndexMut, "array_index_mut_usize");
        (ArrayToSliceShared, "array_to_slice");
        (ArrayToSliceMut, "array_to_slice_mut");
        (ArrayRepeat, "array_repeat");
        (SliceIndexShared, "slice_index_usize");
        (SliceIndexMut, "slice_index_mut_usize");
      ]
  | Lean ->
      [
        (ArrayIndexShared, "Array.index_usize");
        (ArrayIndexMut, "Array.index_mut_usize");
        (ArrayToSliceShared, "Array.to_slice");
        (ArrayToSliceMut, "Array.to_slice_mut");
        (ArrayRepeat, "Array.repeat");
        (SliceIndexShared, "Slice.index_usize");
        (SliceIndexMut, "Slice.index_mut_usize");
      ]

let assumed_pure_functions () : (pure_assumed_fun_id * string) list =
  match backend () with
  | FStar ->
      [
        (Return, "return");
        (Fail, "fail");
        (Assert, "massert");
        (FuelDecrease, "decrease");
        (FuelEqZero, "is_zero");
      ]
  | Coq ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return_"); (Fail, "fail_"); (Assert, "massert") ]
  | Lean ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return"); (Fail, "fail_"); (Assert, "massert") ]
  | HOL4 ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return"); (Fail, "fail"); (Assert, "massert") ]

let names_map_init () : names_map_init =
  {
    keywords = keywords ();
    assumed_adts = assumed_adts ();
    assumed_structs = assumed_struct_constructors ();
    assumed_variants = assumed_variants ();
    assumed_llbc_functions = assumed_llbc_functions ();
    assumed_pure_functions = assumed_pure_functions ();
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
  (* For debugging - we are creating bindings for assumed types and functions, so
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
   * - the assumed types
   * - the assumed struct constructors
   * - the assumed variants
   * - the assumed functions
   *)
  let nm =
    List.fold_left
      (fun nm (type_id, name) ->
        names_maps_add_assumed_type id_to_string type_id name nm)
      nm init.assumed_adts
  in
  let nm =
    List.fold_left
      (fun nm (type_id, name) ->
        names_maps_add_assumed_struct id_to_string type_id name nm)
      nm init.assumed_structs
  in
  let nm =
    List.fold_left
      (fun nm (type_id, variant_id, name) ->
        names_maps_add_assumed_variant id_to_string type_id variant_id name nm)
      nm init.assumed_variants
  in
  let assumed_functions =
    List.map
      (fun (fid, name) ->
        ((FromLlbc (Pure.FunId (FAssumed fid), None), None), name))
      init.assumed_llbc_functions
    @ List.map
        (fun (fid, name) -> ((Pure fid, None), name))
        init.assumed_pure_functions
  in
  let nm =
    List.fold_left
      (fun nm (fid, name) -> names_maps_add_function id_to_string fid name nm)
      nm assumed_functions
  in
  (* Return *)
  nm

(** Compute the qualified for a type definition/declaration.

    For instance: "type", "and", etc.

    Remark: can return [None] for some backends like HOL4.
 *)
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
      | Assumed -> Some "assume type"
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
      | (Assumed | Declared), None -> Some "Axiom"
      | SingleNonRec, None ->
          (* This is for traits *)
          Some "Record"
      | _ ->
          craise __FILE__ __LINE__ span
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
      | Assumed -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

(** Compute the qualified for a function definition/declaration.

    For instance: "let", "let rec", "and", etc.

    Remark: can return [None] for some backends like HOL4.
 *)
let fun_decl_kind_to_qualif (kind : decl_kind) : string option =
  match backend () with
  | FStar -> (
      match kind with
      | SingleNonRec -> Some "let"
      | SingleRec -> Some "let rec"
      | MutRecFirst -> Some "let rec"
      | MutRecInner -> Some "and"
      | MutRecLast -> Some "and"
      | Assumed -> Some "assume val"
      | Declared -> Some "val")
  | Coq -> (
      match kind with
      | SingleNonRec -> Some "Definition"
      | SingleRec -> Some "Fixpoint"
      | MutRecFirst -> Some "Fixpoint"
      | MutRecInner -> Some "with"
      | MutRecLast -> Some "with"
      | Assumed -> Some "Axiom"
      | Declared -> Some "Axiom")
  | Lean -> (
      match kind with
      | SingleNonRec -> Some "def"
      | SingleRec -> Some "divergent def"
      | MutRecFirst -> Some "mutual divergent def"
      | MutRecInner -> Some "divergent def"
      | MutRecLast -> Some "divergent def"
      | Assumed -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

(** The type of types.

    TODO: move inside the formatter?
 *)
let type_keyword (span : Meta.span) =
  match backend () with
  | FStar -> "Type0"
  | Coq | Lean -> "Type"
  | HOL4 -> craise __FILE__ __LINE__ span "Unexpected"

(** Helper *)
let name_last_elem_as_ident (span : Meta.span) (n : llbc_name) : string =
  match Collections.List.last n with
  | PeIdent (s, _) -> s
  | PeImpl _ -> craise __FILE__ __LINE__ span "Unexpected"

(** Helper

    Prepare a name.
    The first id elem is always the crate: if it is the local crate,
    we remove it. We ignore disambiguators (there may be collisions, but we
    check if there are).
 *)
let ctx_prepare_name (span : Meta.span) (ctx : extraction_ctx)
    (name : llbc_name) : llbc_name =
  (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
  match name with
  | (PeIdent (crate, _) as id) :: name ->
      if crate = ctx.crate.name then name else id :: name
  | _ ->
      craise __FILE__ __LINE__ span
        ("Unexpected name shape: "
        ^ TranslateCore.name_to_string ctx.trans_ctx name)

(** Helper *)
let ctx_compute_simple_name (span : Meta.span) (ctx : extraction_ctx)
    (name : llbc_name) : string list =
  (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
  let name = ctx_prepare_name span ctx name in
  name_to_simple_name ctx.trans_ctx name

(** Helper *)
let ctx_compute_simple_type_name = ctx_compute_simple_name

(** Helper *)

let ctx_compute_type_name_no_suffix (span : Meta.span) (ctx : extraction_ctx)
    (name : llbc_name) : string =
  flatten_name (ctx_compute_simple_type_name span ctx name)

(** Provided a basename, compute a type name. *)
let ctx_compute_type_name (span : Meta.span) (ctx : extraction_ctx)
    (name : llbc_name) =
  let name = ctx_compute_type_name_no_suffix span ctx name in
  match backend () with
  | FStar -> StringUtils.lowercase_first_letter (name ^ "_t")
  | Coq | HOL4 -> name ^ "_t"
  | Lean -> name

(** Inputs:
    - type name
    - field id
    - field name

    Note that fields don't always have names, but we still need to
    generate some names if we want to extract the structures to records...
    We might want to extract such structures to tuples, later, but field
    access then causes trouble because not all provers accept syntax like
    [x.3] where [x] is a tuple.
 *)
let ctx_compute_field_name (span : Meta.span) (ctx : extraction_ctx)
    (def_name : llbc_name) (field_id : FieldId.id) (field_name : string option)
    : string =
  let field_name_s =
    match field_name with
    | Some field_name -> field_name
    | None ->
        (* TODO: extract structs with no field names to tuples *)
        FieldId.to_string field_id
  in
  if !Config.record_fields_short_names then
    if field_name = None then (* TODO: this is a bit ugly *)
      "_" ^ field_name_s
    else field_name_s
  else
    let def_name =
      ctx_compute_type_name_no_suffix span ctx def_name ^ "_" ^ field_name_s
    in
    match backend () with
    | Lean | HOL4 -> def_name
    | Coq | FStar -> StringUtils.lowercase_first_letter def_name

(** Inputs:
    - type name
    - variant name
 *)
let ctx_compute_variant_name (span : Meta.span) (ctx : extraction_ctx)
    (def_name : llbc_name) (variant : string) : string =
  match backend () with
  | FStar | Coq | HOL4 ->
      let variant = to_camel_case variant in
      if !variant_concatenate_type_name then
        StringUtils.capitalize_first_letter
          (ctx_compute_type_name_no_suffix span ctx def_name ^ "_" ^ variant)
      else variant
  | Lean -> variant

(** Structure constructors are used when constructing structure values.

    For instance, in F*:
    {[
      type pair = { x : nat; y : nat }
      let p : pair = Mkpair 0 1
    ]}

    Inputs:
    - type name
*)
let ctx_compute_struct_constructor (span : Meta.span) (ctx : extraction_ctx)
    (basename : llbc_name) : string =
  let tname = ctx_compute_type_name span ctx basename in
  ExtractBuiltin.mk_struct_constructor tname

let ctx_compute_fun_name_no_suffix (span : Meta.span) (ctx : extraction_ctx)
    (fname : llbc_name) : string =
  let fname = ctx_compute_simple_name span ctx fname in
  (* TODO: don't convert to snake case for Coq, HOL4, F* *)
  let fname = flatten_name fname in
  match backend () with
  | FStar | Coq | HOL4 -> StringUtils.lowercase_first_letter fname
  | Lean -> fname

(** Provided a basename, compute the name of a global declaration. *)
let ctx_compute_global_name (span : Meta.span) (ctx : extraction_ctx)
    (name : llbc_name) : string =
  match Config.backend () with
  | Coq | FStar | HOL4 ->
      let parts =
        List.map to_snake_case (ctx_compute_simple_name span ctx name)
      in
      String.concat "_" parts
  | Lean -> flatten_name (ctx_compute_simple_name span ctx name)

(** Helper function: generate a suffix for a function name, i.e., generates
    a suffix like "_loop", "loop1", etc. to append to a function name.
 *)
let default_fun_loop_suffix (num_loops : int) (loop_id : LoopId.id option) :
    string =
  match loop_id with
  | None -> ""
  | Some loop_id ->
      (* If this is for a loop, generally speaking, we append the loop index.
         If this function admits only one loop, we omit it. *)
      if num_loops = 1 then "_loop" else "_loop" ^ LoopId.to_string loop_id

(** A helper function: generates a function suffix.
    TODO: move all those helpers.
*)
let default_fun_suffix (num_loops : int) (loop_id : LoopId.id option) : string =
  (* We only generate a suffix for the functions we generate from the loops *)
  default_fun_loop_suffix num_loops loop_id

(** Compute the name of a regular (non-assumed) function.

    Inputs:
    - function basename (TODO: shouldn't appear for assumed functions?...)
    - number of loops in the function (useful to check if we need to use
      indices to derive unique names for the loops for instance - if there is
      exactly one loop, we don't need to use indices)
    - loop id (if pertinent)
    TODO: use the fun id for the assumed functions.
 *)
let ctx_compute_fun_name (span : Meta.span) (ctx : extraction_ctx)
    (fname : llbc_name) (num_loops : int) (loop_id : LoopId.id option) : string
    =
  let fname = ctx_compute_fun_name_no_suffix span ctx fname in
  (* Compute the suffix *)
  let suffix = default_fun_suffix num_loops loop_id in
  (* Concatenate *)
  fname ^ suffix

let ctx_compute_trait_decl_name (ctx : extraction_ctx) (trait_decl : trait_decl)
    : string =
  ctx_compute_type_name trait_decl.span ctx trait_decl.llbc_name

let ctx_compute_trait_impl_name (ctx : extraction_ctx) (trait_decl : trait_decl)
    (trait_impl : trait_impl) : string =
  (* We derive the trait impl name from the implemented trait.
     For instance, if this implementation is an instance of `trait::Trait`
     for `<foo::Foo, u32>`, we generate the name: "trait.TraitFooFooU32Inst".
     Importantly, it is to be noted that the name is independent of the place
     where the instance has been defined (it is indepedent of the file, etc.).
  *)
  let name =
    let params = trait_impl.llbc_generics in
    let args = trait_impl.llbc_impl_trait.decl_generics in
    let name = ctx_prepare_name trait_impl.span ctx trait_decl.llbc_name in
    trait_name_with_generics_to_simple_name ctx.trans_ctx name params args
  in
  let name = flatten_name name in
  match backend () with
  | FStar -> StringUtils.lowercase_first_letter name
  | Coq | HOL4 | Lean -> name

let ctx_compute_trait_decl_constructor (ctx : extraction_ctx)
    (trait_decl : trait_decl) : string =
  let name = ctx_compute_trait_decl_name ctx trait_decl in
  ExtractBuiltin.mk_struct_constructor name

(** Helper to derive names for parent trait clauses and for variables
    for trait instances.

    We derive the name from the type of the clause (i.e., the trait ref
    the clause implements).
    For instance, if a trait clause is for the trait ref "Trait<Box<usize>",
    we generate a name like "traitBoxUsizeInst". This is more meaningful
    that giving it a generic name with an index (such as "parent_clause_1"
    or "inst3").

    Because we want to be precise when deriving the name, we use the
    original LLBC types, that is the types from before the translation
    to pure, which simplifies types like boxes and references.
 *)
let ctx_compute_trait_clause_name (ctx : extraction_ctx)
    (current_def_name : Types.name) (params : Types.generic_params)
    (clauses : Types.trait_clause list) (clause_id : trait_clause_id) : string =
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
      List.find
        (fun (c : Types.trait_clause) -> c.clause_id = clause_id)
        clauses
    in
    let trait_id = clause.trait_id in
    let impl_trait_decl = TraitDeclId.Map.find trait_id ctx.crate.trait_decls in
    let args = clause.clause_generics in
    trait_name_with_generics_to_simple_name ctx.trans_ctx ~prefix
      impl_trait_decl.name params args
  in
  String.concat "" clause

let ctx_compute_trait_parent_clause_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (clause : trait_clause) : string =
  (* We derive the name of the clause from the trait instance.
     For instance, if the clause gives us an instance of `Foo<u32>`,
     we generate a name along the lines of "fooU32Inst".
  *)
  (* We need to lookup the LLBC definitions, to have the original instantiation *)
  let clause =
    let current_def_name = trait_decl.llbc_name in
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
  match backend () with FStar -> "t" ^ name | Coq | Lean | HOL4 -> name

let ctx_compute_trait_const_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) : string =
  let name =
    if !Config.record_fields_short_names then item
    else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ item
  in
  (* See [trait_type_name] *)
  match backend () with FStar -> "c" ^ name | Coq | Lean | HOL4 -> name

let ctx_compute_trait_method_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) : string =
  if !Config.record_fields_short_names then item
  else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ item

let ctx_compute_trait_type_clause_name (ctx : extraction_ctx)
    (trait_decl : trait_decl) (item : string) (clause : trait_clause) : string =
  (* TODO: improve - it would be better to not use indices *)
  ctx_compute_trait_type_name ctx trait_decl item
  ^ "_clause_"
  ^ TraitClauseId.to_string clause.clause_id

(** Generates the name of the termination measure used to prove/reason about
    termination. The generated code uses this clause where needed,
    but its body must be defined by the user.

    F* and Lean only.

    Inputs:
    - function id: this is especially useful to identify whether the
      function is an assumed function or a local function
    - function basename
    - the number of loops in the parent function. This is used for
      the same purpose as in [llbc_name].
    - loop identifier, if this is for a loop
 *)
let ctx_compute_termination_measure_name (span : Meta.span)
    (ctx : extraction_ctx) (_fid : A.FunDeclId.id) (fname : llbc_name)
    (num_loops : int) (loop_id : LoopId.id option) : string =
  let fname = ctx_compute_fun_name_no_suffix span ctx fname in
  let lp_suffix = default_fun_loop_suffix num_loops loop_id in
  (* Compute the suffix *)
  let suffix =
    match Config.backend () with
    | FStar -> "_decreases"
    | Lean -> "_terminates"
    | Coq | HOL4 -> craise __FILE__ __LINE__ span "Unexpected"
  in
  (* Concatenate *)
  fname ^ lp_suffix ^ suffix

(** Generates the name of the proof used to prove/reason about
    termination. The generated code uses this clause where needed,
    but its body must be defined by the user.

    Lean only.

    Inputs:
    - function id: this is especially useful to identify whether the
      function is an assumed function or a local function
    - function basename
    - the number of loops in the parent function. This is used for
      the same purpose as in [llbc_name].
    - loop identifier, if this is for a loop
 *)
let ctx_compute_decreases_proof_name (span : Meta.span) (ctx : extraction_ctx)
    (_fid : A.FunDeclId.id) (fname : llbc_name) (num_loops : int)
    (loop_id : LoopId.id option) : string =
  let fname = ctx_compute_fun_name_no_suffix span ctx fname in
  let lp_suffix = default_fun_loop_suffix num_loops loop_id in
  (* Compute the suffix *)
  let suffix =
    match Config.backend () with
    | Lean -> "_decreases"
    | FStar | Coq | HOL4 -> craise __FILE__ __LINE__ span "Unexpected"
  in
  (* Concatenate *)
  fname ^ lp_suffix ^ suffix

(** Generates a variable basename.

    Inputs:
    - the set of names used in the context so far
    - the basename we got from the symbolic execution, if we have one
    - the type of the variable (can be useful for heuristics, in order
      not to always use "x" for instance, whenever naming anonymous
      variables)

    Note that once the formatter generated a basename, we add an index
    if necessary to prevent name clashes: the burden of name clashes checks
    is thus on the caller's side.
 *)
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
    sanity_check __FILE__ __LINE__ (List.length cl > 0) span;
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
          | TAssumed TResult -> "r"
          | TAssumed TError -> ConstStrings.error_basename
          | TAssumed TFuel -> ConstStrings.fuel_basename
          | TAssumed TArray -> "a"
          | TAssumed TSlice -> "s"
          | TAssumed TStr -> "s"
          | TAssumed TState -> ConstStrings.state_basename
          | TAssumed (TRawPtr _) -> "p"
          | TAdtId adt_id ->
              let def =
                TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
              in
              (* Derive the var name from the last ident of the type name
                 Ex.: ["hashmap"; "HashMap"] ~~> "HashMap" -> "hash_map" -> "hm"
              *)
              (* The name shouldn't be empty, and its last element should
               * be an ident *)
              let cl = Collections.List.last def.name in
              name_from_type_ident (TypesUtils.as_ident cl))
      | TVar _ -> (
          (* TODO: use "t" also for F* *)
          match backend () with
          | FStar -> "x" (* lacking inspiration here... *)
          | Coq | Lean | HOL4 -> "t" (* lacking inspiration here... *))
      | TLiteral lty -> (
          match lty with TBool -> "b" | TChar -> "c" | TInteger _ -> "i")
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

    In the traduction we explicitely manipulate the trait clause instances,
    that is we introduce one input variable for each trait clause.
 *)
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

(** Appends an index to a name - we use this to generate unique
    names: when doing so, the role of the formatter is just to concatenate
    indices to names, the responsability of finding a proper index is
    delegated to helper functions.
 *)
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
let ctx_add_type_var (span : Meta.span) (basename : string) (id : TypeVarId.id)
    (ctx : extraction_ctx) : extraction_ctx * string =
  let name = ctx_compute_type_var_basename ctx basename in
  let name = basename_to_unique ctx name in
  let ctx = ctx_add span (TypeVarId id) name ctx in
  (ctx, name)

(** Generate a unique const generic variable name and add it to the context *)
let ctx_add_const_generic_var (span : Meta.span) (basename : string)
    (id : ConstGenericVarId.id) (ctx : extraction_ctx) : extraction_ctx * string
    =
  let name = ctx_compute_const_generic_var_basename ctx basename in
  let name = basename_to_unique ctx name in
  let ctx = ctx_add span (ConstGenericVarId id) name ctx in
  (ctx, name)

(** See {!ctx_add_type_var} *)
let ctx_add_type_vars (span : Meta.span) (vars : (string * TypeVarId.id) list)
    (ctx : extraction_ctx) : extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (name, id) -> ctx_add_type_var span name id ctx)
    ctx vars

(** Generate a unique variable name and add it to the context *)
let ctx_add_var (span : Meta.span) (basename : string) (id : VarId.id)
    (ctx : extraction_ctx) : extraction_ctx * string =
  let name = basename_to_unique ctx basename in
  let ctx = ctx_add span (VarId id) name ctx in
  (ctx, name)

(** Generate a unique variable name for the trait self clause and add it to the context *)
let ctx_add_trait_self_clause (span : Meta.span) (ctx : extraction_ctx) :
    extraction_ctx * string =
  let basename = trait_self_clause_basename in
  let name = basename_to_unique ctx basename in
  let ctx = ctx_add span TraitSelfClauseId name ctx in
  (ctx, name)

(** Generate a unique trait clause name and add it to the context *)
let ctx_add_local_trait_clause (span : Meta.span) (basename : string)
    (id : TraitClauseId.id) (ctx : extraction_ctx) : extraction_ctx * string =
  let name = basename_to_unique ctx basename in
  let ctx = ctx_add span (LocalTraitClauseId id) name ctx in
  (ctx, name)

(** See {!ctx_add_var} *)
let ctx_add_vars (span : Meta.span) (vars : var list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (v : var) ->
      let name = ctx_compute_var_basename span ctx v.basename v.ty in
      ctx_add_var span name v.id ctx)
    ctx vars

let ctx_add_type_params (span : Meta.span) (vars : type_var list)
    (ctx : extraction_ctx) : extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (var : type_var) -> ctx_add_type_var span var.name var.index ctx)
    ctx vars

let ctx_add_const_generic_params (span : Meta.span)
    (vars : const_generic_var list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (var : const_generic_var) ->
      ctx_add_const_generic_var span var.name var.index ctx)
    ctx vars

(** Returns the lists of names for:
    - the type variables
    - the const generic variables
    - the trait clauses

    For the [current_name_def] and the [llbc_generics]: we use them to derive
    pretty names for the trait clauses. See {!ctx_compute_trait_clause_name}
    for additional information.
  *)
let ctx_add_local_trait_clauses (span : Meta.span)
    (current_def_name : Types.name) (llbc_generics : Types.generic_params)
    (clauses : trait_clause list) (ctx : extraction_ctx) :
    extraction_ctx * string list =
  List.fold_left_map
    (fun ctx (c : trait_clause) ->
      let basename =
        ctx_compute_trait_clause_basename ctx current_def_name llbc_generics
          c.clause_id
      in
      ctx_add_local_trait_clause span basename c.clause_id ctx)
    ctx clauses

(** Returns the lists of names for:
    - the type variables
    - the const generic variables
    - the trait clauses

    For the [current_name_def] and the [llbc_generics]: we use them to derive
    pretty names for the trait clauses. See {!ctx_compute_trait_clause_name}
    for additional information.
  *)
let ctx_add_generic_params (span : Meta.span) (current_def_name : Types.name)
    (llbc_generics : Types.generic_params) (generics : generic_params)
    (ctx : extraction_ctx) :
    extraction_ctx * string list * string list * string list =
  let { types; const_generics; trait_clauses } = generics in
  let ctx, tys = ctx_add_type_params span types ctx in
  let ctx, cgs = ctx_add_const_generic_params span const_generics ctx in
  let ctx, tcs =
    ctx_add_local_trait_clauses span current_def_name llbc_generics
      trait_clauses ctx
  in
  (ctx, tys, cgs, tcs)

let ctx_add_decreases_proof (def : fun_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  let name =
    ctx_compute_decreases_proof_name def.span ctx def.def_id def.llbc_name
      def.num_loops def.loop_id
  in
  ctx_add def.span
    (DecreasesProofId (FRegular def.def_id, def.loop_id))
    name ctx

let ctx_add_termination_measure (def : fun_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  let name =
    ctx_compute_termination_measure_name def.span ctx def.def_id def.llbc_name
      def.num_loops def.loop_id
  in
  ctx_add def.span
    (TerminationMeasureId (FRegular def.def_id, def.loop_id))
    name ctx

let ctx_add_global_decl_and_body (def : A.global_decl) (ctx : extraction_ctx) :
    extraction_ctx =
  (* TODO: update once the body id can be an option *)
  let decl = GlobalId def.def_id in

  (* Check if the global corresponds to an assumed global that we should map
     to a custom definition in our standard library (for instance, happens
     with "core::num::usize::MAX") *)
  match match_name_find_opt ctx.trans_ctx def.name builtin_globals_map with
  | Some name ->
      (* Yes: register the custom binding *)
      ctx_add def.item_meta.span decl name ctx
  | None ->
      (* Not the case: "standard" registration *)
      let name = ctx_compute_global_name def.item_meta.span ctx def.name in

      let body = FunId (FromLlbc (FunId (FRegular def.body), None)) in
      (* If this is a provided constant (i.e., the default value for a constant
         in a trait declaration) we add a suffix. Otherwise there is a clash
         between the name for the default constant and the name for the field
         in the trait declaration *)
      let suffix =
        match def.kind with TraitItemProvided _ -> "_default" | _ -> ""
      in
      let ctx = ctx_add def.item_meta.span decl (name ^ suffix) ctx in
      let ctx = ctx_add def.item_meta.span body (name ^ suffix ^ "_body") ctx in
      ctx

let ctx_compute_fun_name (def : fun_decl) (ctx : extraction_ctx) : string =
  (* Add the function name *)
  ctx_compute_fun_name def.span ctx def.llbc_name def.num_loops def.loop_id

(* TODO: move to Extract *)
let ctx_add_fun_decl (def : fun_decl) (ctx : extraction_ctx) : extraction_ctx =
  (* Sanity check: the function should not be a global body - those are handled
   * separately *)
  sanity_check __FILE__ __LINE__ (not def.is_global_decl_body) def.span;
  (* Lookup the LLBC def to compute the region group information *)
  let def_id = def.def_id in
  (* Add the function name *)
  let def_name = ctx_compute_fun_name def ctx in
  let fun_id = (Pure.FunId (FRegular def_id), def.loop_id) in
  ctx_add def.span (FunId (FromLlbc fun_id)) def_name ctx

let ctx_compute_type_decl_name (ctx : extraction_ctx) (def : type_decl) : string
    =
  ctx_compute_type_name def.span ctx def.llbc_name
