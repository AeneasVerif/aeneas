open Identifiers
open Meta
module T = Types
module V = Values
module E = Expressions
module A = LlbcAst
module TypeDeclId = T.TypeDeclId
module TypeVarId = T.TypeVarId
module RegionGroupId = T.RegionGroupId
module VariantId = T.VariantId
module FieldId = T.FieldId
module SymbolicValueId = V.SymbolicValueId
module FunDeclId = A.FunDeclId
module GlobalDeclId = A.GlobalDeclId
module TraitDeclId = T.TraitDeclId
module TraitImplId = T.TraitImplId
module TraitClauseId = T.TraitClauseId
module Disambiguator = T.Disambiguator

(** We redefine identifiers for loop: in {!Values}, the identifiers are global
    (they monotonically increase across functions) while in {!module:Pure} we
    want the indices to start at 0 for every function. *)
module LoopId =
IdGen ()

(** We give an identifier to every phase of the synthesis (forward, backward for
    group of regions 0, etc.) *)
module SynthPhaseId =
IdGen ()

module BVarId = IdGen ()
module FVarId = IdGen ()
module ConstGenericVarId = T.ConstGenericVarId

type llbc_name = T.name [@@deriving show, ord]
type integer_type = T.integer_type [@@deriving show, ord]
type float_type = T.float_type [@@deriving show, ord]
type const_generic_param = T.const_generic_param [@@deriving show, ord]
type const_generic = T.const_generic [@@deriving show, ord]
type const_generic_var_id = T.const_generic_var_id [@@deriving show, ord]
type trait_decl_id = T.trait_decl_id [@@deriving show, ord]
type trait_impl_id = T.trait_impl_id [@@deriving show, ord]
type trait_clause_id = T.trait_clause_id [@@deriving show, ord]
type trait_item_name = T.trait_item_name [@@deriving show, ord]
type global_decl_id = T.global_decl_id [@@deriving show, ord]
type fun_decl_id = A.fun_decl_id [@@deriving show, ord]
type loop_id = LoopId.id [@@deriving show, ord]
type region_group_id = T.region_group_id [@@deriving show, ord]
type mutability = Mut | Const [@@deriving show, ord]
type loc = Meta.loc [@@deriving show, ord]
type file_name = Meta.file_name [@@deriving show, ord]
type span_data = Meta.span_data [@@deriving show, ord]
type span = Meta.span [@@deriving show, ord]
type ref_kind = Types.ref_kind [@@deriving show, ord]
type 'a de_bruijn_var = 'a Types.de_bruijn_var [@@deriving show, ord]
type llbc_fun_id = A.fun_id [@@deriving show, ord]
type binop = E.binop [@@deriving show, ord]

(** A DeBruijn index identifying a group of bound variables *)
type db_scope_id = int [@@deriving show, ord]

type bvar_id = BVarId.id [@@deriving show, ord]
type fvar_id = FVarId.id [@@deriving show, ord]

(*let ( fvar_id_counter,
      marked_fvar_ids,
      marked_fvar_ids_insert_from_int,
      fresh_fvar_id ) =
  FVarId.fresh_marked_stateful_generator ()

let reset_global_counters () = fvar_id_counter := FVarId.generator_zero
  let reset_fvar_id_counter () = fvar_id_counter := FVarId.generator_zero*)

(** The builtin types for the pure AST.

    In comparison with LLBC:
    - we removed [Box] (because it is translated as the identity: [Box T = T])
    - we added:
    - [Result]: the type used in the error monad. This allows us to have a
      unified treatment of expressions (especially when we have to unfold the
      monadic binds)
    - [Error]: the kind of error, in case of failure (used by [Result])
    - [Fuel]: the fuel, to control recursion (some theorem provers like Coq
      don't support semantic termination, in which case we can use a fuel
      parameter to do partial verification) *)
type builtin_ty =
  | TResult
  | TSum  (** sum type with two variants: left and right *)
  | TLoopResult
      (** A continue or a break.

          We introduce this provisionally: we eliminate it during a micro-pass
      *)
  | TError
  | TFuel
  | TArray
  | TSlice
  | TStr
  | TRawPtr of mutability
      (** The bool Raw pointers don't make sense in the pure world, but we don't
          know how to translate them yet and we have to handle some functions
          which use raw pointers in their signature (for instance some trait
          declarations for the slices). For now, we use a dedicated type to
          "mark" the raw pointers, and make sure that those functions are
          actually not used in the translation. *)
[@@deriving show, ord]

type array_or_slice = Array | Slice [@@deriving show, ord]

(** Identifiers of builtin functions that we use only in the pure translation *)
type pure_builtin_fun_id =
  | Return  (** The monadic return *)
  | Fail  (** The monadic fail *)
  | Assert  (** Assertion *)
  | Loop of int
      (** A loop operator.

          The integer represents the arity (by default the arity is 1, but for
          some small arities we may introduce dedicated loop operators). *)
  | RecLoopCall of int
      (** A recursive call to an outer loop. This is different from using a
          [Continue] in that it allows binding the result of the loop and doing
          something with it. We use this in the micro-passes, in preparation of
          a translation which transforms loops to recursive functions. *)
  | FuelDecrease
      (** Decrease fuel, provided it is non zero (used for F* ) - TODO: this is
          ugly *)
  | FuelEqZero  (** Test if some fuel is equal to 0 - TODO: ugly *)
  | UpdateAtIndex of array_or_slice
      (** Update an array or a slice at a given index.

          Note that in LLBC we only use an index function: if we want to modify
          an element in an array/slice, we create a mutable borrow to this
          element, then use the borrow to perform the update. The update
          functions are introduced in the pure code by a micro-pass. *)
  | ToResult
      (** Lifts a pure expression to a monadic expression.

          We use this when using `ok ...` would result in let-bindings getting
          simplified away (in a backend like Lean). *)
[@@deriving show, ord]

(* Builtin declarations coming from external libraries.

   Those are not too be understood as the builtin definitions like `U32`:
   the builtin declarations decribed with, e.g., `builtin_type_info`, are
   declarations coming from external libraries and which we should thus not
   extract (for instance: `std::vec::Vec`, `std::option::Option`, etc.).
*)

type builtin_variant_info = { fields : (string * string) list }
[@@deriving show, ord]

type builtin_enum_variant_info = {
  rust_variant_name : string;
  extract_variant_name : string;
  fields : string list option;
}
[@@deriving show, ord]

type builtin_type_body_info =
  | Struct of string * (string * string) list
    (* The constructor name and the map for the field names *)
  | Enum of builtin_enum_variant_info list
(* For every variant, a map for the field names *)
[@@deriving show, ord]

type builtin_type_info = {
  rust_name : NameMatcher.pattern;
  extract_name : string;
  keep_params : bool list option;
      (** We might want to filter some of the type parameters.

          For instance, `Vec` type takes a type parameter for the allocator,
          which we want to ignore. *)
  body_info : builtin_type_body_info option;
}
[@@deriving show, ord]

type builtin_global_info = { global_name : string } [@@deriving show]

type builtin_fun_info = {
  filter_params : bool list option;
  extract_name : string;
  can_fail : bool;
  stateful : bool;
  lift : bool;
      (** If the function can not fail, should we still lift it to the [Result]
          monad? This can make reasonings easier, as we can then use [progress]
          to do proofs in a Hoare-Logic style, rather than doing equational
          reasonings. *)
  has_default : bool;
      (** If this is a trait method: does this method have a default
          implementation? If yes, we might want to register it as well. *)
}
[@@deriving show]

type builtin_trait_decl_info = {
  rust_name : NameMatcher.pattern;
  extract_name : string;
  constructor : string;
  parent_clauses : string list;
  consts : (string * string) list;
  types : (string * string) list;
      (** Every type has:
          - a Rust name
          - an extraction name *)
  methods : (string * builtin_fun_info) list;
}
[@@deriving show]

type builtin_trait_impl_info = {
  extract_name : string;
  filter_params : bool list option;
}
[@@deriving show]

(* TODO: we should never directly manipulate [Return] and [Fail], but rather
 * the monadic functions [return] and [fail] (makes treatment of error and
 * state-error monads more uniform) *)
let result_ok_id = VariantId.of_int 0
let result_fail_id = VariantId.of_int 1
let option_some_id = T.option_some_id
let option_none_id = T.option_none_id
let sum_left_id = VariantId.of_int 0
let sum_right_id = VariantId.of_int 1
let loop_result_continue_id = VariantId.of_int 0
let loop_result_break_id = VariantId.of_int 1
let loop_result_fail_id = VariantId.of_int 2
let error_failure_id = VariantId.of_int 0
let error_out_of_fuel_id = VariantId.of_int 1

(* We don't always use those: it depends on the backend (we use natural numbers
   for the fuel: in Coq they are enumerations, but in F* they are primitive)
*)
let fuel_zero_id = VariantId.of_int 0
let fuel_succ_id = VariantId.of_int 1

type type_decl_id = TypeDeclId.id [@@deriving show, ord]
type type_var_id = TypeVarId.id [@@deriving show, ord]

(** Ancestor for iter visitor for [ty] *)
class ['self] iter_type_id_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_builtin_ty : 'env -> builtin_ty -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_type_id_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_builtin_ty : 'env -> builtin_ty -> builtin_ty = fun _ x -> x
  end

(** Ancestor for reduce visitor for [ty] *)
class virtual ['self] reduce_type_id_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_type_decl_id : 'env -> type_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_builtin_ty : 'env -> builtin_ty -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for [ty] *)
class virtual ['self] mapreduce_type_id_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_builtin_ty : 'env -> builtin_ty -> builtin_ty * 'a =
      fun _ x -> (x, self#zero)
  end

type type_id = TAdtId of type_decl_id | TTuple | TBuiltin of builtin_ty
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_type_id";
      variety = "iter";
      ancestors = [ "iter_type_id_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "map_type_id";
      variety = "map";
      ancestors = [ "map_type_id_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "reduce_type_id";
      variety = "reduce";
      ancestors = [ "reduce_type_id_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      polymorphic = false;
    },
  visitors
    {
      name = "mapreduce_type_id";
      variety = "mapreduce";
      ancestors = [ "mapreduce_type_id_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      polymorphic = false;
    }]

type literal_type = T.literal_type [@@deriving show, ord]

(** Ancestor for iter visitor for [ty] *)
class ['self] iter_ty_base =
  object (_self : 'self)
    inherit [_] iter_type_id
    inherit! [_] T.iter_const_generic
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_ty_base =
  object (_self : 'self)
    inherit [_] map_type_id
    inherit! [_] T.map_const_generic
  end

(** Ancestor for reduce visitor for [ty] *)
class virtual ['self] reduce_ty_base =
  object (_self : 'self)
    inherit [_] reduce_type_id
    inherit! [_] T.reduce_const_generic
  end

(** Ancestor for mapreduce visitor for [ty] *)
class virtual ['self] mapreduce_ty_base =
  object (_self : 'self)
    inherit [_] mapreduce_type_id
    inherit! [_] T.mapreduce_const_generic
  end

type ty =
  | TAdt of type_id * generic_args
      (** {!TAdt} encodes ADTs and tuples and builtin types.

          TODO: what about the ended regions? (ADTs may be parameterized with
          several region variables. When giving back an ADT value, we may be
          able to only give back part of the ADT. We need a way to encode such
          "partial" ADTs. *)
  | TVar of type_var_id de_bruijn_var
    (* Note: the `de_bruijn_id`s are incorrect, see comment on `translate_region_binder` *)
  | TLiteral of literal_type
  | TArrow of ty * ty
  | TTraitType of trait_ref * string
      (** The string is for the name of the associated type *)
  | Error

and trait_ref = {
  trait_id : trait_instance_id;
  trait_decl_ref : trait_decl_ref;
}

and fun_decl_ref = {
  fun_id : fun_decl_id;
  fun_generics : generic_args; (* The name: annoying field collisions... *)
}

and trait_decl_ref = {
  trait_decl_id : trait_decl_id;
  decl_generics : generic_args; (* The name: annoying field collisions... *)
}

and global_decl_ref = {
  global_id : global_decl_id;
  global_generics : generic_args; (* The name: annoying field collisions... *)
}

and generic_args = {
  types : ty list;
  const_generics : const_generic list;
  trait_refs : trait_ref list;
}

and trait_instance_id =
  | Self
  | TraitImpl of trait_impl_id * generic_args
  | Clause of trait_clause_id de_bruijn_var
    (* Note: the `de_bruijn_id`s are incorrect, see comment on `translate_region_binder` *)
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
  | UnknownTrait of string
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_ty";
      variety = "iter";
      ancestors = [ "iter_ty_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "map_ty";
      variety = "map";
      ancestors = [ "map_ty_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.map} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "reduce_ty";
      variety = "reduce";
      ancestors = [ "reduce_ty_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.reduce} *);
      polymorphic = false;
    },
  visitors
    {
      name = "mapreduce_ty";
      variety = "mapreduce";
      ancestors = [ "mapreduce_ty_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.mapreduce} *);
      polymorphic = false;
    }]

type type_param = T.type_param [@@deriving show, ord]

(** Ancestor for iter visitor for [type_decl] *)
class ['self] iter_type_decl_base =
  object (self : 'self)
    inherit [_] iter_ty

    method visit_type_param : 'env -> type_param -> unit =
      fun e var ->
        self#visit_type_var_id e var.index;
        self#visit_string e var.name

    method visit_const_generic_param : 'env -> const_generic_param -> unit =
      fun e var ->
        self#visit_const_generic_var_id e var.index;
        self#visit_string e var.name;
        self#visit_literal_type e var.ty

    method visit_item_meta : 'env -> T.item_meta -> unit = fun _ _ -> ()

    method visit_builtin_type_info : 'env -> builtin_type_info -> unit =
      fun _ _ -> ()

    method visit_trait_item_name : 'env -> trait_item_name -> unit =
      fun _ _ -> ()
  end

(** Ancestor for map visitor for [type_decl] *)
class ['self] map_type_decl_base =
  object (self : 'self)
    inherit [_] map_ty

    method visit_type_param : 'env -> type_param -> type_param =
      fun e var ->
        {
          index = self#visit_type_var_id e var.index;
          name = self#visit_string e var.name;
        }

    method visit_const_generic_param :
        'env -> const_generic_param -> const_generic_param =
      fun e var ->
        {
          index = self#visit_const_generic_var_id e var.index;
          name = self#visit_string e var.name;
          ty = self#visit_literal_type e var.ty;
        }

    method visit_item_meta : 'env -> T.item_meta -> T.item_meta = fun _ x -> x

    method visit_builtin_type_info :
        'env -> builtin_type_info -> builtin_type_info =
      fun _ x -> x

    method visit_trait_item_name : 'env -> trait_item_name -> trait_item_name =
      fun _ x -> x
  end

(** Ancestor for reduce visitor for [type_decl] *)
class virtual ['self] reduce_type_decl_base =
  object (self : 'self)
    inherit [_] reduce_ty

    method visit_type_param : 'env -> type_param -> 'a =
      fun e var ->
        let x0 = self#visit_type_var_id e var.index in
        let x1 = self#visit_string e var.name in
        self#plus x0 x1

    method visit_const_generic_param : 'env -> const_generic_param -> 'a =
      fun e var ->
        let x0 = self#visit_const_generic_var_id e var.index in
        let x1 = self#visit_string e var.name in
        let x2 = self#visit_literal_type e var.ty in
        self#plus (self#plus x0 x1) x2

    method visit_item_meta : 'env -> T.item_meta -> 'a = fun _ _ -> self#zero

    method visit_builtin_type_info : 'env -> builtin_type_info -> 'a =
      fun _ _ -> self#zero

    method visit_trait_item_name : 'env -> trait_item_name -> 'a =
      fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for [type_decl] *)
class virtual ['self] mapreduce_type_decl_base =
  object (self : 'self)
    inherit [_] mapreduce_ty

    method visit_type_param : 'env -> type_param -> type_param * 'a =
      fun e var ->
        let index, x0 = self#visit_type_var_id e var.index in
        let name, x1 = self#visit_string e var.name in
        ({ index; name }, self#plus x0 x1)

    method visit_const_generic_param :
        'env -> const_generic_param -> const_generic_param * 'a =
      fun e var ->
        let index, x0 = self#visit_const_generic_var_id e var.index in
        let name, x1 = self#visit_string e var.name in
        let ty, x2 = self#visit_literal_type e var.ty in
        ({ index; name; ty }, self#plus (self#plus x0 x1) x2)

    method visit_item_meta : 'env -> T.item_meta -> T.item_meta * 'a =
      fun _ x -> (x, self#zero)

    method visit_builtin_type_info :
        'env -> builtin_type_info -> builtin_type_info * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_item_name :
        'env -> trait_item_name -> trait_item_name * 'a =
      fun _ x -> (x, self#zero)
  end

type field = {
  field_name : string option;
  field_ty : ty;
  field_attr_info : (attr_info[@opaque]);
}

and variant = {
  variant_name : string;
  fields : field list;
  variant_attr_info : (attr_info[@opaque]);
}

and type_decl_kind = Struct of field list | Enum of variant list | Opaque

and trait_param = {
  clause_id : trait_clause_id;
  trait_id : trait_decl_id;
  generics : generic_args;
}

and generic_params = {
  types : type_param list;
  const_generics : const_generic_param list;
  trait_clauses : trait_param list;
}

and trait_type_constraint = {
  trait_ref : trait_ref;
  type_name : trait_item_name;
  ty : ty;
}

and predicates = { trait_type_constraints : trait_type_constraint list }
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_type_decl_base1";
      variety = "iter";
      ancestors = [ "iter_type_decl_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "map_type_decl_base1";
      variety = "map";
      ancestors = [ "map_type_decl_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.map} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "reduce_type_decl_base1";
      variety = "reduce";
      ancestors = [ "reduce_type_decl_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.reduce} *);
      polymorphic = false;
    },
  visitors
    {
      name = "mapreduce_type_decl_base1";
      variety = "mapreduce";
      ancestors = [ "mapreduce_type_decl_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.mapreduce} *);
      polymorphic = false;
    }]

(** Characterize an input parameter as explicit or implicit *)
type explicit = Explicit | Implicit

and known = Known | Unknown

and explicit_info = {
  explicit_types : explicit list;
  explicit_const_generics : explicit list;
}

and known_info = { known_types : known list; known_const_generics : known list }

and type_decl = {
  def_id : type_decl_id;
  name : string;
      (** We use the name only for printing purposes (for debugging): the name
          used at extraction time will be derived from the llbc_name. *)
  item_meta : T.item_meta;
  generics : generic_params;
  explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
  llbc_generics : (Types.generic_params[@opaque]);
      (** We use the LLBC generics to generate "pretty" names, for instance for
          the variables we introduce for the trait clauses: we derive those
          names from the types, and when doing so it is more meaningful to
          derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  kind : type_decl_kind;
  builtin_info : builtin_type_info option;
  preds : predicates;
}
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_type_decl";
      variety = "iter";
      ancestors = [ "iter_type_decl_base1" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "map_type_decl";
      variety = "map";
      ancestors = [ "map_type_decl_base1" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.map} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "reduce_type_decl";
      variety = "reduce";
      ancestors = [ "reduce_type_decl_base1" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.reduce} *);
      polymorphic = false;
    },
  visitors
    {
      name = "mapreduce_type_decl";
      variety = "mapreduce";
      ancestors = [ "mapreduce_type_decl_base1" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.mapreduce} *);
      polymorphic = false;
    }]

type scalar_value = V.scalar_value [@@deriving show, ord]
type literal = V.literal [@@deriving show, ord]
type field_proj_kind = E.field_proj_kind [@@deriving show, ord]
type field_id = FieldId.id [@@deriving show, ord]

(* TODO: we might want to redefine field_proj_kind here, to prevent field accesses
 * on enumerations.
 * Also: tuples...
 * Rmk: projections are actually only used as span-data.
 *)
type mprojection_elem = { pkind : field_proj_kind; field_id : field_id }
[@@deriving show, ord]

(** "Meta" place.

    Meta-data retrieved from the symbolic execution, which gives provenance
    information about the values. We use this to generate names for the
    variables we introduce. *)
type mplace =
  | PlaceLocal of E.LocalId.id * string option
  | PlaceGlobal of global_decl_ref
  | PlaceProjection of mplace * mprojection_elem
[@@deriving show, ord]

type variant_id = VariantId.id [@@deriving show, ord]

(** A variable *)
type var = {
  basename : string option;
      (** The "basename" is used to generate a meaningful name for the variable
          (by potentially adding an index to uniquely identify it). *)
  ty : ty;
}
[@@deriving show, ord]

(** A free variable *)
type fvar = {
  id : fvar_id;
  basename : string option;
      (** The "basename" is used to generate a meaningful name for the variable
          (by potentially adding an index to uniquely identify it). *)
  ty : ty;
}
[@@deriving show, ord]

(** Ancestor for {!iter_tpat} visitor *)
class ['self] iter_tpat_base =
  object (self : 'self)
    inherit [_] iter_type_decl
    method visit_fvar_id : 'env -> fvar_id -> unit = fun _ _ -> ()
    method visit_bvar_id : 'env -> bvar_id -> unit = fun _ _ -> ()
    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()

    method visit_var : 'env -> var -> unit =
      fun e var ->
        self#visit_option self#visit_string e var.basename;
        self#visit_ty e var.ty

    method visit_fvar : 'env -> fvar -> unit =
      fun e var ->
        self#visit_fvar_id e var.id;
        self#visit_option self#visit_string e var.basename;
        self#visit_ty e var.ty

    method visit_llbc_fun_id : 'env -> llbc_fun_id -> unit = fun _ _ -> ()

    method visit_pure_builtin_fun_id : 'env -> pure_builtin_fun_id -> unit =
      fun _ _ -> ()

    method visit_binop : 'env -> binop -> unit = fun _ _ -> ()
    method visit_field_id : 'env -> field_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_tpat} visitor *)
class ['self] map_tpat_base =
  object (self : 'self)
    inherit [_] map_type_decl
    method visit_fvar_id : 'env -> fvar_id -> fvar_id = fun _ x -> x
    method visit_bvar_id : 'env -> bvar_id -> bvar_id = fun _ x -> x
    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x
    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
    method visit_loop_id : 'env -> loop_id -> loop_id = fun _ x -> x

    method visit_var : 'env -> var -> var =
      fun e var ->
        {
          basename = self#visit_option self#visit_string e var.basename;
          ty = self#visit_ty e var.ty;
        }

    method visit_fvar : 'env -> fvar -> fvar =
      fun e var ->
        {
          id = self#visit_fvar_id e var.id;
          basename = self#visit_option self#visit_string e var.basename;
          ty = self#visit_ty e var.ty;
        }

    method visit_llbc_fun_id : 'env -> llbc_fun_id -> llbc_fun_id = fun _ x -> x

    method visit_pure_builtin_fun_id :
        'env -> pure_builtin_fun_id -> pure_builtin_fun_id =
      fun _ x -> x

    method visit_binop : 'env -> binop -> binop = fun _ x -> x
    method visit_field_id : 'env -> field_id -> field_id = fun _ x -> x
  end

(** Ancestor for {!reduce_tpat} visitor *)
class virtual ['self] reduce_tpat_base =
  object (self : 'self)
    inherit [_] reduce_type_decl
    method visit_fvar_id : 'env -> fvar_id -> 'a = fun _ _ -> self#zero
    method visit_bvar_id : 'env -> bvar_id -> 'a = fun _ _ -> self#zero
    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero
    method visit_variant_id : 'env -> variant_id -> 'a = fun _ _ -> self#zero
    method visit_loop_id : 'env -> loop_id -> 'a = fun _ _ -> self#zero

    method visit_var : 'env -> var -> 'a =
      fun e var ->
        let x1 = self#visit_option self#visit_string e var.basename in
        let x2 = self#visit_ty e var.ty in
        self#plus x1 x2

    method visit_fvar : 'env -> fvar -> 'a =
      fun e var ->
        let x0 = self#visit_fvar_id e var.id in
        let x1 = self#visit_option self#visit_string e var.basename in
        let x2 = self#visit_ty e var.ty in
        self#plus (self#plus x0 x1) x2

    method visit_llbc_fun_id : 'env -> llbc_fun_id -> 'a = fun _ _ -> self#zero

    method visit_pure_builtin_fun_id : 'env -> pure_builtin_fun_id -> 'a =
      fun _ _ -> self#zero

    method visit_binop : 'env -> binop -> 'a = fun _ _ -> self#zero
    method visit_field_id : 'env -> field_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_tpat} visitor *)
class virtual ['self] mapreduce_tpat_base =
  object (self : 'self)
    inherit [_] mapreduce_type_decl

    method visit_fvar_id : 'env -> fvar_id -> fvar_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_bvar_id : 'env -> bvar_id -> bvar_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_mplace : 'env -> mplace -> mplace * 'a =
      fun _ x -> (x, self#zero)

    method visit_variant_id : 'env -> variant_id -> variant_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_loop_id : 'env -> loop_id -> loop_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_var : 'env -> var -> var * 'a =
      fun e var ->
        let basename, x1 = self#visit_option self#visit_string e var.basename in
        let ty, x2 = self#visit_ty e var.ty in
        ({ basename; ty }, self#plus x1 x2)

    method visit_fvar : 'env -> fvar -> fvar * 'a =
      fun e var ->
        let id, x0 = self#visit_fvar_id e var.id in
        let basename, x1 = self#visit_option self#visit_string e var.basename in
        let ty, x2 = self#visit_ty e var.ty in
        ({ id; basename; ty }, self#plus (self#plus x0 x1) x2)

    method visit_llbc_fun_id : 'env -> llbc_fun_id -> llbc_fun_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_pure_builtin_fun_id :
        'env -> pure_builtin_fun_id -> pure_builtin_fun_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_binop : 'env -> binop -> binop * 'a = fun _ x -> (x, self#zero)

    method visit_field_id : 'env -> field_id -> field_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** A pattern (which appears on the left of assignments, in matches, etc.). *)
type pat =
  | PConstant of literal
      (** {!PConstant} is necessary because we merge the switches over integer
          values and the matches over enumerations *)
  | PBound of var * mplace option
      (** The index of the variable is determined by its position (it is the
          index given by a depth-first search, which is consistent with the way
          visitors work). *)
  | PIgnored  (** Ignored value: [_]. *)
  | POpen of fvar * mplace option
      (** We replace [PBound] with [POpen] when opening binders.

          When we open a binder (say, the expression [let x = v in e]) by
          replacing the bound variables (in [e]) with free variables, we also
          substitute those bound variables in the pattern used in the binder.
          This both provides useful information as to where the variables come
          from, and is also necessary when closing the term back, to properly
          figure out how to compute the indices of the bound variables.

          Ex.: We want to simplify the expression (1) [let (x, y) = v in y] into
          [let (_, y) = v in y]. If we use DeBruijn indices the expression (1)
          looks like: [let (PBound, PBound) = v in BVar (0, 1)], while the
          expression (2) looks like: [let (_, PBound) = v in BVar (0, 0)]. Note
          that in [BVar (0, 1)] the first number (the 0) identifies the
          scope/level of the variable (how many binder groups we have to
          traverse) while the second number (the 1) identifies the variable in
          the binder group. We resort to this representation because a binder
          group like a let-binding can bind several variables at once (see the
          explanations in [bvar]).

          We first open the expression [let (POpen, POpen) = v in BVar 1],
          producing the pattern (let's pretend we identify free variables with
          names rather than indices) [(x, y)] and the expression [y]. We then
          update the pattern to [(_,y)] and close the expression by reforming
          the let: [y] now has the index 0 and we get the expected expression:
          [let (_, BVar) = v in BVar 0]. *)
  | PAdt of adt_pat

and adt_pat = { variant_id : variant_id option; fields : tpat list }

and tpat = { pat : pat; ty : ty }
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_tpat";
      variety = "iter";
      ancestors = [ "iter_tpat_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "map_tpat";
      variety = "map";
      ancestors = [ "map_tpat_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      polymorphic = false;
    },
  visitors
    {
      name = "reduce_tpat";
      variety = "reduce";
      ancestors = [ "reduce_tpat_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      polymorphic = false;
    },
  visitors
    {
      name = "mapreduce_tpat";
      variety = "mapreduce";
      ancestors = [ "mapreduce_tpat_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      polymorphic = false;
    }]

type unop =
  | Not of integer_type option
  | Neg of integer_type
  | Cast of literal_type * literal_type
  | ArrayToSlice

and fn_ptr_kind =
  | FunId of llbc_fun_id
  | TraitMethod of trait_ref * string * fun_decl_id
      (** The fun decl id is not really needed and only provided for convenience
          purposes *)

(** A function id for a non-builtin function *)
and regular_fun_id = fn_ptr_kind * loop_id option

(** A function identifier *)
and fun_id =
  | FromLlbc of regular_fun_id
      (** A function coming from LLBC.

          The loop id is [None] if the function is actually the auxiliary
          function generated from a loop.

          The region group id is the backward id:: [Some] if the function is a
          backward function, [None] if it is a forward function. *)
  | Pure of pure_builtin_fun_id
      (** A function only used in the pure translation *)

(** A function or an operation id *)
and fun_or_op_id =
  | Fun of fun_id
  | Unop of unop
  | Binop of binop * integer_type

(** An identifier for an ADT constructor *)
and adt_cons_id = { adt_id : type_id; variant_id : variant_id option }

(** Projection - Note that generally speaking we avoid using projections of
    tuple fields (because not all backends support it). *)
and projection = { adt_id : type_id; field_id : field_id }

and qualif_id =
  | FunOrOp of fun_or_op_id  (** A function or an operation *)
  | Global of global_decl_id
  | AdtCons of adt_cons_id  (** A function or ADT constructor identifier *)
  | Proj of projection  (** Field projector *)
  | TraitConst of trait_ref * string  (** A trait associated constant *)

(** An instantiated qualifier.

    Note that for now we have a clear separation between types and expressions,
    which explains why we have the [generics] field: a function or ADT
    constructor is always fully instantiated. *)
and qualif = { id : qualif_id; generics : generic_args }
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_qualif";
      variety = "iter";
      ancestors = [ "iter_tpat" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    },
  visitors
    {
      name = "map_qualif";
      variety = "map";
      ancestors = [ "map_tpat" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    },
  visitors
    {
      name = "reduce_qualif";
      variety = "reduce";
      ancestors = [ "reduce_tpat" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
    },
  visitors
    {
      name = "mapreduce_qualif";
      variety = "mapreduce";
      ancestors = [ "mapreduce_tpat" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
    }]

(** Ancestor for {!iter_expr} visitor *)
class ['self] iter_expr_base =
  object (_self : 'self)
    inherit [_] iter_qualif
    inherit! [_] iter_type_id
    method visit_span : 'env -> Meta.span -> unit = fun _ _ -> ()
    method visit_db_scope_id : 'env -> db_scope_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_expr} visitor *)
class ['self] map_expr_base =
  object (_self : 'self)
    inherit [_] map_qualif
    inherit! [_] map_type_id
    method visit_span : 'env -> Meta.span -> Meta.span = fun _ x -> x
    method visit_db_scope_id : 'env -> db_scope_id -> db_scope_id = fun _ x -> x
  end

(** Ancestor for {!reduce_expr} visitor *)
class virtual ['self] reduce_expr_base =
  object (self : 'self)
    inherit [_] reduce_qualif
    inherit! [_] reduce_type_id
    method visit_span : 'env -> Meta.span -> 'a = fun _ _ -> self#zero
    method visit_db_scope_id : 'env -> db_scope_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_expr} visitor *)
class virtual ['self] mapreduce_expr_base =
  object (self : 'self)
    inherit [_] mapreduce_qualif
    inherit! [_] mapreduce_type_id

    method visit_span : 'env -> Meta.span -> Meta.span * 'a =
      fun _ x -> (x, self#zero)

    method visit_db_scope_id : 'env -> db_scope_id -> db_scope_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** **Rk.:** here, {!expr} is not at all equivalent to the expressions used in
    LLBC. They are lambda-calculus expressions, and are thus actually more
    general than the LLBC statements, in a sense. *)
type expr =
  | FVar of fvar_id  (** a free variable *)
  | BVar of bvar  (** a bound variable *)
  | CVar of const_generic_var_id  (** a const generic var *)
  | Const of literal
  | App of texpr * texpr
      (** Application of a function to an argument.

          The function calls are still quite structured. Change that?... We
          might want to have a "normal" lambda calculus app (with head and
          argument): this would allow us to replace some field accesses with
          calls to projectors over fields (when there are clashes of field
          names, some provers like F* get pretty bad...) *)
  | Lambda of tpat * texpr  (** Lambda abstraction: [λ x => e] *)
  | Qualif of qualif  (** A top-level qualifier *)
  | Let of bool * tpat * texpr * texpr
      (** Let binding.

          TODO: the boolean should be replaced by an enum: sometimes we use the
          error-monad, sometimes we use the state-error monad (and we should do
          this an a per-function basis! For instance, arithmetic functions are
          always in the error monad, they shouldn't use the state-error monad).

          The boolean controls whether the let is monadic or not. For instance,
          in F*:
          - non-monadic: [let x = ... in ...]
          - monadic: [x <-- ...; ...]

          Note that we are quite general for the left-value on purpose; this is
          used in several situations:

          1. When deconstructing a tuple:
          {[
            let (x, y) = p in ...
          ]}
          (not all languages have syntax like [p.0], [p.1]... and it is more
          readable anyway).

          2. When expanding an enumeration with one variant. In this case,
          {!Let} has to be understood as:
          {[
            let Cons x tl = ls in
            ...
          ]}

          Note that later, depending on the language we extract to, we can
          eventually update it to something like this (for F*, for instance):
          {[
            let x = Cons?.v ls in
            let tl = Cons?.tl ls in
            ...
          ]} *)
  | Switch of texpr * switch_body
  | Loop of loop  (** See the comments for {!loop} *)
  | StructUpdate of struct_update  (** See the comments for {!struct_update} *)
  | Meta of emeta * texpr  (** Meta-information *)
  | EError of Meta.span option * string

and switch_body = If of texpr * texpr | Match of match_branch list
and match_branch = { pat : tpat; branch : texpr }

(** A loop.

    This is later expanded to an explicit call to a loop fixed-point operator.
*)
and loop = {
  loop_id : loop_id;
  span : span; [@opaque]
  output_tys : ty list;  (** The types of the output values. *)
  num_output_values : int;
      (** The number of output values.

          The outputs are divided between the output values, which come from the
          output symbolic values, and the output continuations, which come from
          the output abstractions. The output values come first in the list of
          outputs. *)
  inputs : texpr list;
      (** The inputs of the loop, coming from the input symbolic values and the
          input abstractions.

          Those should be variables bound in the [loop_body]. *)
  num_input_conts : int;
      (** The number of input continuations.

          This is similar to [num_output_values], with the difference that here
          we count the number of input continuations, because for the inputs the
          *continuations* come first (while for the outputs the *values* come
          first). *)
  loop_body : loop_body;
}

(** A loop body.

    We see loop bodies as functions, while a loop itself is a loop fixed-point
    operator applied to such a loop body. *)
and loop_body = {
  inputs : tpat list;  (** Binders for the inputs of the loop body. *)
  loop_body : texpr;
}

(** Structure creation/update.

    This expression is not strictly necessary, but allows for nice syntax, which
    is important to work easily with the generated code.

    If {!init} is [None], it defines a structure creation:
    {[
      { x := 3; y := true; }
    ]}

    If {!init} is [Some], it defines a structure update:
    {[
      { s with x := 3 }
    ]}

    We also use struct updates to encode array aggregates, so that whenever the
    user writes code like:
    {[
      let a : [u32; 2] = [0, 1];
      ...
    ]}
    this gets encoded to:
    {[
      let a : Array u32 2 = Array.mk [0, 1] in
      ...
    ]} *)
and struct_update = {
  struct_id : type_id;
  init : texpr option;
  updates : (field_id * texpr) list;
}

and texpr = { e : expr; ty : ty }

and bvar = {
  scope : db_scope_id;
      (** The scope (or level) of the variable identifies the number of external
          binder groups we have to traverse to reach the binder group the
          variable comes from *)
  id : bvar_id;
      (** This id identifies the variable in the binder group in which it is
          bound.

          We need to use two identifiers because binder groups can bind several
          variables at once, meaning the scope is not enough to identify a
          variable.

          Ex.:
          {[
            let (x, y) = v in // this binder group has level 1
            let z = 3 in // this binder group has level 0
            // Counting the levels from here:
            // - z is represented as (0, 0)
            // - x is represented as (1, 0)
            // - y is represented as (1, 1)
            ...
          ]} *)
}

(** Meta-value (converted to an expression). *)
and mvalue = texpr

(** Variable used in meta-information.

    We use the type [texpr] so that the variable id gets properly updated by the
    functions which open/close binders. *)
and mvar = texpr

(** Meta-information stored in the AST.

    There are two kinds of information:
    - information about assignments and names: we use those during the first
      pure micro-pass to derive pretty names, then get rid of them.
    - information about type annotations: we insert them during the last
      micro-pass to guide the generation of code. *)
and emeta =
  | Assignment of mplace * mvalue * mplace option
      (** Information about an assignment which occured in LLBC. We use this to
          guide the heuristics which derive pretty names.

          The first mplace stores the destination. The mvalue stores the value
          which is put in the destination The second (optional) mplace stores
          the origin. *)
  | SymbolicAssignments of (mvar * mvalue) list
      (** Informationg linking a variable (from the pure AST) to an expression.

          We use this to guide the heuristics which derive pretty names. *)
  | SymbolicPlaces of (mvar * string) list
      (** Informationg linking a variable (from the pure AST) to a name.

          We generate this information by exploring the context, and use it to
          derive pretty names. *)
  | MPlace of mplace  (** Meta-information about the origin of a value *)
  | Tag of string  (** A tag - typically used for debugging *)
  | TypeAnnot
      (** The presence of this marker means that we should insert a
          type-annotation when extracting the code. This is necessart because,
          for instance, the constructor to use for an expression [{ v := ... }]
          may be ambiguous, especially for backends like Lean which allow
          collisions between field names.

          Those markers are introduced during a micro-pass. *)
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_expr";
      variety = "iter";
      ancestors = [ "iter_expr_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    },
  visitors
    {
      name = "map_expr";
      variety = "map";
      ancestors = [ "map_expr_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    },
  visitors
    {
      name = "reduce_expr";
      variety = "reduce";
      ancestors = [ "reduce_expr_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
    },
  visitors
    {
      name = "mapreduce_expr";
      variety = "mapreduce";
      ancestors = [ "mapreduce_expr_base" ];
      monomorphic = [ "env" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
    }]

(** Information about the "effect" of a function *)
type fun_effect_info = {
  can_fail : bool;  (** [true] if the return type is a [result] *)
  can_diverge : bool;
      (** [true] if the function can diverge (i.e., not terminate). It happens
          if the function is recursive or contains a loop but also if it
          (transitively) calls a function which can diverge. *)
  is_rec : bool;
      (** [true] if the function is recursive (or in a mutually recursive group)
      *)
}
[@@deriving show]

(** Meta information about a function signature *)
type fun_sig_info = {
  effect_info : fun_effect_info;
  ignore_output : bool;
      (** In case we merge the forward/backward functions: should we ignore the
          output (happens for forward functions if the output type is [unit] and
          there are non-filtered backward functions)? *)
}
[@@deriving show]

type back_sg_info = {
  inputs : (string option * ty) list;
      (** The additional inputs of the backward function *)
  outputs : ty list;
      (** The "decomposed" list of outputs.

          The list contains all the types of all the given back values (there is
          at most one type per forward input argument).

          Ex.:
          {[
            fn choose<'a, T>(b : bool, x : &'a mut T, y : &'a mut T) -> &'a mut T;
          ]}
          Decomposed outputs:
          - forward function: [[T]]
          - backward function: [[T; T]] (for "x" and "y")

          Non-decomposed ouputs (if the function can fail, but is not stateful):
          - [result T]
          - [[result (T * T)]] *)
  output_names : string option list;
      (** The optional names for the backward outputs. We derive those from the
          names of the inputs of the original LLBC function. *)
  effect_info : fun_effect_info;
  filter : bool;  (** Should we filter this backward function? *)
}
[@@deriving show]

(** A *decomposed* function type (without parameters).

    This is a helper type used by the translation. *)
type decomposed_fun_type = {
  fwd_inputs : ty list;
      (** The types of the inputs of the forward function.

          Note that those input types take include the [fuel] parameter, if the
          function uses fuel for termination, and the [state] parameter, if the
          function is stateful.

          For instance, if we have the following Rust function:
          {[
            fn f (x : int)
          ]}

          If we translate it to a stateful function which uses fuel we get:
          {[
            val f : nat -> int -> state -> result (state * unit);
          ]}

          In particular, the list of input types is: [[nat; int; state]]. *)
  fwd_output : ty;
      (** The "pure" output type of the forward function.

          Note that this type doesn't contain the "effect" of the function
          (i.e., we haven't added the [state] if it is a stateful function and
          haven't wrapped the type in a [result]). Also, this output type is
          only about the forward function (it doesn't contain the type of the
          closures we return for the backward functions, in case we merge the
          forward and backward functions). *)
  back_sg : back_sg_info RegionGroupId.Map.t;
      (** Information about the backward functions *)
  fwd_info : fun_sig_info;
      (** Additional information about the forward function *)
}
[@@deriving show]

(** A *decomposed* function signature.

    This is a helper type used by the translation. *)
type decomposed_fun_sig = {
  generics : generic_params;
      (** TODO: we should analyse the signature to make the type parameters
          implicit whenever possible *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance for
          the variables we introduce for the trait clauses: we derive those
          names from the types, and when doing so it is more meaningful to
          derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  fun_ty : decomposed_fun_type;  (** The type itself *)
}
[@@deriving show]

(** A function signature.

    We have the following cases:
    - forward function: [in_ty0 -> ... -> in_tyn -> out_ty] (* pure function *)
      [in_ty0 -> ... -> in_tyn -> result out_ty] (* error-monad *)
      [in_ty0 -> ... -> in_tyn -> state -> result (state & out_ty)] (*
      state-error *)
    - backward function:
      [in_ty0 -> ... -> in_tyn -> back_in0 -> ... back_inm -> (back_out0 & ... &
       back_outp)] (* pure function *)
      [in_ty0 -> ... -> in_tyn -> back_in0 -> ... back_inm -> result (back_out0
       & ... & back_outp)] (* error-monad *)
      [in_ty0 -> ... -> in_tyn -> state -> back_in0 -> ... back_inm -> state ->
       result (state & (back_out0 & ... & back_outp))] (* state-error *)

    Note that a stateful backward function may take two states as inputs: the
    state received by the associated forward function, and the state at which
    the backward is called. This leads to code of the following shape:

    {[
      (st1, y)  <-- f_fwd x st0; // st0 is the state upon calling f_fwd
      ... // the state may be updated
      (st3, x') <-- f_back x st0 y' st2; // st2 is the state upon calling f_back
    ]}

    The function's type should be given by [mk_arrows sig.inputs sig.output]. We
    provide additional meta-information with {!fun_sig.info}:
    - we divide between forward inputs and backward inputs (i.e., inputs
      specific to the forward functions, and additional inputs necessary if the
      signature is for a backward function)
    - we have booleans to give us the fact that the function takes a state as
      input, or can fail, etc. without having to inspect the signature
    - etc. *)
type fun_sig = {
  generics : generic_params;
  explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
  known_from_trait_refs : known_info;
      (** Information about which (implicit) parameters can be infered from the
          trait refs only *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance for
          the variables we introduce for the trait clauses: we derive those
          names from the types, and when doing so it is more meaningful to
          derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  inputs : ty list;
      (** The types of the inputs.

          Note that those input types take into account the [fuel] parameter, if
          the function uses fuel for termination, and the [state] parameter, if
          the function is stateful.

          For instance, if we have the following Rust function:
          {[
            fn f (x : int)
          ]}

          If we translate it to a stateful function which uses fuel we get:
          {[
            val f : nat -> int -> state -> result (state * unit);
          ]}

          In particular, the list of input types is: [[nat; int; state]].

          *Remark*: the fuel and state parameters are introduced during a micro
          pass, so if we use fuel and state the signature evolves during the
          compilation. *)
  output : ty;
      (** The output type.

          Note that this type contains the "effect" of the function (i.e., it is
          not just a purification of the Rust return type). For instance, it
          will be a tuple with a [state] if the function is stateful, and will
          be wrapped in a [result] if the function can fail. *)
  fwd_info : fun_sig_info;
      (** Additional information about the forward function. *)
  back_effect_info : fun_effect_info RegionGroupId.Map.t;
}
[@@deriving show]

(** An instantiated function signature. See {!fun_sig} *)
type inst_fun_sig = { inputs : ty list; output : ty } [@@deriving show]

type fun_body = {
  inputs : tpat list;
      (** Note that we consider the inputs as a single binder group when
          computing de bruijn indices *)
  body : texpr;
}
[@@deriving show]

type item_source = T.item_source [@@deriving show]

(** Attributes to add to the generated code *)
type backend_attributes = {
  reducible : bool;  (** Lean "reducible" attribute *)
}
[@@deriving show]

(** A value of type `T` bound by generic parameters. Used in any context where
    we're adding generic parameters that aren't on the top-level item, e.g.
    trait methods. *)
type 'a binder = {
  binder_value : 'a;
  binder_generics : generic_params;
  binder_preds : predicates;
  binder_llbc_generics : Types.generic_params;
  binder_explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
}
[@@deriving show, ord]

type fun_decl = {
  def_id : FunDeclId.id;
  item_meta : T.item_meta;
  builtin_info : builtin_fun_info option;
  src : item_source;
  backend_attributes : backend_attributes;
  num_loops : int;
      (** The number of loops in the parent forward function (basically the
          number of loops appearing in the original Rust functions, unless some
          loops are duplicated because we don't join the control-flow after a
          branching) *)
  loop_id : LoopId.id option;
      (** [Some] if this definition was generated for a loop *)
  name : string;
      (** We use the name only for printing purposes (for debugging): the name
          used at extraction time will be derived from the llbc_name. *)
  signature : fun_sig;
  is_global_decl_body : bool;
  body : fun_body option;
}
[@@deriving show]

type global_decl = {
  def_id : GlobalDeclId.id;
  span : span;
  item_meta : T.item_meta;
  builtin_info : builtin_global_info option;
  name : string;
      (** We use the name only for printing purposes (for debugging): the name
          used at extraction time will be derived from the llbc_name. *)
  llbc_generics : Types.generic_params;
      (** See the comment for [llbc_generics] in fun_decl. *)
  generics : generic_params;
  explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
  preds : predicates;
  ty : ty;
  src : item_source;
  body_id : FunDeclId.id;
}
[@@deriving show]

type trait_decl = {
  def_id : trait_decl_id;
  name : string;
  item_meta : T.item_meta;
  builtin_info : builtin_trait_decl_info option;
  generics : generic_params;
  explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance for
          the variables we introduce for the trait clauses: we derive those
          names from the types, and when doing so it is more meaningful to
          derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  parent_clauses : trait_param list;
  llbc_parent_clauses : Types.trait_param list;
  consts : (trait_item_name * ty) list;
  types : trait_item_name list;
  methods : (trait_item_name * fun_decl_ref binder) list;
}
[@@deriving show]

type trait_impl = {
  def_id : trait_impl_id;
  name : string;
  item_meta : T.item_meta;
  builtin_info : builtin_trait_impl_info option;
  impl_trait : trait_decl_ref;
  llbc_impl_trait : Types.trait_decl_ref;
      (** Same remark as for {!field:llbc_generics}. *)
  generics : generic_params;
  explicit_info : explicit_info;
      (** Information about which inputs parameters are explicit/implicit *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance for
          the variables we introduce for the trait clauses: we derive those
          names from the types, and when doing so it is more meaningful to
          derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  parent_trait_refs : trait_ref list;
  consts : (trait_item_name * global_decl_ref) list;
  types : (trait_item_name * ty) list;
  methods : (trait_item_name * fun_decl_ref binder) list;
}
[@@deriving show]
