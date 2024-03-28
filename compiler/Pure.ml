open Identifiers
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
    (they monotonically increase across functions) while in {!module:Pure} we want
    the indices to start at 0 for every function.
    Also, we can't reuse the indices from {!LlbcAst} because we may have duplicated
    some loops and we need a unique index for each loop.
 *)
module LoopId =
IdGen ()

(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)
module SynthPhaseId =
IdGen ()

(** Pay attention to the fact that we also define a {!E.VarId} module in Values *)
module VarId =
IdGen ()

module ConstGenericVarId = T.ConstGenericVarId

type llbc_name = T.name [@@deriving show, ord]
type integer_type = T.integer_type [@@deriving show, ord]
type const_generic_var = T.const_generic_var [@@deriving show, ord]
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
type span = Meta.span [@@deriving show, ord]
type meta = Meta.meta [@@deriving show, ord]
type expr_result_kind = { ok : bool; return : bool } [@@deriving show, ord]

(** The assumed types for the pure AST.

    In comparison with LLBC:
    - we removed [Box] (because it is translated as the identity: [Box T = T])
    - we added:
      - [Result]: the type used in the error monad. This allows us to have a
        unified treatment of expressions (especially when we have to unfold the
        monadic binds)
      - [Error]: the kind of error, in case of failure (used by [Result])
      - [Fuel]: the fuel, to control recursion (some theorem provers like Coq
        don't support semantic termination, in which case we can use a fuel
        parameter to do partial verification)
      - [State]: the type of the state, when using state-error monads. Note that
        this state is opaque to Aeneas (the user can define it, or leave it as
        assumed)

    TODO: add a prefix "T"
  *)
type assumed_ty =
  | TState
  (* TODO: merge Result and ExprResult *)
  | TResult
  | TExprResult of expr_result_kind
      (** Same as TResult, but also contains a node for *return* *)
  | TError
  | TFuel
  | TArray
  | TSlice
  | TStr
  | TRawPtr of mutability
      (** The bool
          Raw pointers don't make sense in the pure world, but we don't know
          how to translate them yet and we have to handle some functions which
          use raw pointers in their signature (for instance some trait declarations
          for the slices). For now, we use a dedicated type to "mark" the raw pointers,
          and make sure that those functions are actually not used in the translation.
       *)
[@@deriving show, ord]

(* TODO: we should never directly manipulate [Return] and [Fail], but rather
 * the monadic functions [return] and [fail] (makes treatment of error and
 * state-error monads more uniform) *)
let result_ok_id = VariantId.of_int 0
let result_return_id = VariantId.of_int 1
let result_fail_id = VariantId.of_int 2
let option_some_id = T.option_some_id
let option_none_id = T.option_none_id
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
    method visit_assumed_ty : 'env -> assumed_ty -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_type_id_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_assumed_ty : 'env -> assumed_ty -> assumed_ty = fun _ x -> x
  end

(** Ancestor for reduce visitor for [ty] *)
class virtual ['self] reduce_type_id_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_type_decl_id : 'env -> type_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_assumed_ty : 'env -> assumed_ty -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for [ty] *)
class virtual ['self] mapreduce_type_id_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_assumed_ty : 'env -> assumed_ty -> assumed_ty * 'a =
      fun _ x -> (x, self#zero)
  end

type type_id = TAdtId of type_decl_id | TTuple | TAssumed of assumed_ty
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_type_id";
        variety = "iter";
        ancestors = [ "iter_type_id_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_type_id";
        variety = "map";
        ancestors = [ "map_type_id_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_type_id";
        variety = "reduce";
        ancestors = [ "reduce_type_id_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_type_id";
        variety = "mapreduce";
        ancestors = [ "mapreduce_type_id_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        polymorphic = false;
      }]

type literal_type = T.literal_type [@@deriving show, ord]

(** Ancestor for iter visitor for [ty] *)
class ['self] iter_ty_base =
  object (_self : 'self)
    inherit [_] iter_type_id
    inherit! [_] T.iter_const_generic
    method visit_type_var_id : 'env -> type_var_id -> unit = fun _ _ -> ()
    method visit_trait_decl_id : 'env -> trait_decl_id -> unit = fun _ _ -> ()
    method visit_trait_impl_id : 'env -> trait_impl_id -> unit = fun _ _ -> ()

    method visit_trait_clause_id : 'env -> trait_clause_id -> unit =
      fun _ _ -> ()

    method visit_trait_item_name : 'env -> trait_item_name -> unit =
      fun _ _ -> ()
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_ty_base =
  object (_self : 'self)
    inherit [_] map_type_id
    inherit! [_] T.map_const_generic
    method visit_type_var_id : 'env -> type_var_id -> type_var_id = fun _ x -> x

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id =
      fun _ x -> x

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id =
      fun _ x -> x

    method visit_trait_clause_id : 'env -> trait_clause_id -> trait_clause_id =
      fun _ x -> x

    method visit_trait_item_name : 'env -> trait_item_name -> trait_item_name =
      fun _ x -> x
  end

(** Ancestor for reduce visitor for [ty] *)
class virtual ['self] reduce_ty_base =
  object (self : 'self)
    inherit [_] reduce_type_id
    inherit! [_] T.reduce_const_generic
    method visit_type_var_id : 'env -> type_var_id -> 'a = fun _ _ -> self#zero

    method visit_trait_decl_id : 'env -> trait_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_impl_id : 'env -> trait_impl_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_clause_id : 'env -> trait_clause_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_item_name : 'env -> trait_item_name -> 'a =
      fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for [ty] *)
class virtual ['self] mapreduce_ty_base =
  object (self : 'self)
    inherit [_] mapreduce_type_id
    inherit! [_] T.mapreduce_const_generic

    method visit_type_var_id : 'env -> type_var_id -> type_var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_clause_id
        : 'env -> trait_clause_id -> trait_clause_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_item_name
        : 'env -> trait_item_name -> trait_item_name * 'a =
      fun _ x -> (x, self#zero)
  end

type ty =
  | TAdt of type_id * generic_args
      (** {!TAdt} encodes ADTs and tuples and assumed types.

          TODO: what about the ended regions? (ADTs may be parameterized
          with several region variables. When giving back an ADT value, we may
          be able to only give back part of the ADT. We need a way to encode
          such "partial" ADTs.
       *)
  | TVar of type_var_id
  | TLiteral of literal_type
  | TArrow of ty * ty
  | TTraitType of trait_ref * generic_args * string
      (** The string is for the name of the associated type *)

and trait_ref = {
  trait_id : trait_instance_id;
  generics : generic_args;
  trait_decl_ref : trait_decl_ref;
}

and trait_decl_ref = {
  trait_decl_id : trait_decl_id;
  decl_generics : generic_args; (* The name: annoying field collisions... *)
}

and generic_args = {
  types : ty list;
  const_generics : const_generic list;
  trait_refs : trait_ref list;
}

and trait_instance_id =
  | Self
  | TraitImpl of trait_impl_id
  | Clause of trait_clause_id
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
  | ItemClause of
      trait_instance_id * trait_decl_id * trait_item_name * trait_clause_id
  | TraitRef of trait_ref
  | UnknownTrait of string
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.map} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_ty";
        variety = "reduce";
        ancestors = [ "reduce_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.reduce} *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_ty";
        variety = "mapreduce";
        ancestors = [ "mapreduce_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.mapreduce} *);
        polymorphic = false;
      }]

type field = { field_name : string option; field_ty : ty } [@@deriving show]
type variant = { variant_name : string; fields : field list } [@@deriving show]

type type_decl_kind = Struct of field list | Enum of variant list | Opaque
[@@deriving show]

type type_var = T.type_var [@@deriving show]

type trait_clause = {
  clause_id : trait_clause_id;
  trait_id : trait_decl_id;
  generics : generic_args;
}
[@@deriving show]

type generic_params = {
  types : type_var list;
  const_generics : const_generic_var list;
  trait_clauses : trait_clause list;
}
[@@deriving show]

type trait_type_constraint = {
  trait_ref : trait_ref;
  generics : generic_args;
  type_name : trait_item_name;
  ty : ty;
}
[@@deriving show, ord]

type predicates = { trait_type_constraints : trait_type_constraint list }
[@@deriving show]

type type_decl = {
  def_id : TypeDeclId.id;
  is_local : bool;
  llbc_name : llbc_name;
      (** The original name coming from the LLBC declaration *)
  name : string;
      (** We use the name only for printing purposes (for debugging):
          the name used at extraction time will be derived from the
          llbc_name.
       *)
  meta : meta;
  generics : generic_params;
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance
          for the variables we introduce for the trait clauses: we derive
          those names from the types, and when doing so it is more meaningful
          to derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  kind : type_decl_kind;
  preds : predicates;
}
[@@deriving show]

type scalar_value = V.scalar_value [@@deriving show, ord]
type literal = V.literal [@@deriving show, ord]

(** Because we introduce a lot of temporary variables, the list of variables
    is not fixed: we thus must carry all its information with the variable
    itself.
 *)
type var = {
  id : VarId.id;
  basename : string option;
      (** The "basename" is used to generate a meaningful name for the variable
          (by potentially adding an index to uniquely identify it).
       *)
  ty : ty;
}
[@@deriving show]

(* TODO: we might want to redefine field_proj_kind here, to prevent field accesses
 * on enumerations.
 * Also: tuples...
 * Rmk: projections are actually only used as meta-data.
 * *)
type mprojection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }
[@@deriving show]

type mprojection = mprojection_elem list [@@deriving show]

(** "Meta" place.

    Meta-data retrieved from the symbolic execution, which gives provenance
    information about the values. We use this to generate names for the variables
    we introduce.
 *)
type mplace = {
  var_id : E.VarId.id;
  name : string option;
  projection : mprojection;
}
[@@deriving show]

type variant_id = VariantId.id [@@deriving show]

(** Ancestor for {!iter_typed_pattern} visitor *)
class ['self] iter_typed_pattern_base =
  object (_self : 'self)
    inherit [_] iter_ty
    method visit_var : 'env -> var -> unit = fun _ _ -> ()
    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_typed_pattern} visitor *)
class ['self] map_typed_pattern_base =
  object (_self : 'self)
    inherit [_] map_ty
    method visit_var : 'env -> var -> var = fun _ x -> x
    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x
    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
  end

(** Ancestor for {!reduce_typed_pattern} visitor *)
class virtual ['self] reduce_typed_pattern_base =
  object (self : 'self)
    inherit [_] reduce_ty
    method visit_var : 'env -> var -> 'a = fun _ _ -> self#zero
    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero
    method visit_variant_id : 'env -> variant_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_typed_pattern} visitor *)
class virtual ['self] mapreduce_typed_pattern_base =
  object (self : 'self)
    inherit [_] mapreduce_ty
    method visit_var : 'env -> var -> var * 'a = fun _ x -> (x, self#zero)

    method visit_mplace : 'env -> mplace -> mplace * 'a =
      fun _ x -> (x, self#zero)

    method visit_variant_id : 'env -> variant_id -> variant_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** A pattern (which appears on the left of assignments, in matches, etc.). *)
type pattern =
  | PatConstant of literal
      (** {!PatConstant} is necessary because we merge the switches over integer
          values and the matches over enumerations *)
  | PatVar of var * mplace option
  | PatDummy  (** Ignored value: [_]. *)
  | PatAdt of adt_pattern

and adt_pattern = {
  variant_id : variant_id option;
  field_values : typed_pattern list;
}

and typed_pattern = { value : pattern; ty : ty }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_pattern";
        variety = "iter";
        ancestors = [ "iter_typed_pattern_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_typed_pattern";
        variety = "map";
        ancestors = [ "map_typed_pattern_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_typed_pattern";
        variety = "reduce";
        ancestors = [ "reduce_typed_pattern_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_typed_pattern";
        variety = "mapreduce";
        ancestors = [ "mapreduce_typed_pattern_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        polymorphic = false;
      }]

type unop = Not | Neg of integer_type | Cast of literal_type * literal_type
[@@deriving show, ord]

(** Identifiers of assumed functions that we use only in the pure translation *)
type pure_assumed_fun_id =
  | Return  (** The monadic return *)
  | Fail  (** The monadic fail *)
  | Assert  (** Assertion *)
  | FuelDecrease
      (** Decrease fuel, provided it is non zero (used for F* ) - TODO: this is ugly *)
  | FuelEqZero  (** Test if some fuel is equal to 0 - TODO: ugly *)
[@@deriving show, ord]

type fun_id_or_trait_method_ref =
  | FunId of A.fun_id
  | TraitMethod of trait_ref * string * fun_decl_id
      (** The fun decl id is not really needed and here for convenience purposes *)
[@@deriving show, ord]

(** A function id for a non-assumed function *)
type regular_fun_id = fun_id_or_trait_method_ref * LoopId.id option
[@@deriving show, ord]

(** A function identifier *)
type fun_id =
  | FromLlbc of regular_fun_id
      (** A function coming from LLBC.

          The loop id is [None] if the function is actually the auxiliary function
          generated from a loop.

          The region group id is the backward id:: [Some] if the function is a
          backward function, [None] if it is a forward function.
       *)
  | Pure of pure_assumed_fun_id
      (** A function only used in the pure translation *)
[@@deriving show, ord]

(** A function or an operation id *)
type fun_or_op_id =
  | Fun of fun_id
  | Unop of unop
  | Binop of E.binop * integer_type
[@@deriving show, ord]

(** An identifier for an ADT constructor *)
type adt_cons_id = { adt_id : type_id; variant_id : variant_id option }
[@@deriving show]

(** Projection - For now we don't support projection of tuple fields
    (because not all the backends have syntax for this).
 *)
type projection = { adt_id : type_id; field_id : FieldId.id } [@@deriving show]

type qualif_id =
  | FunOrOp of fun_or_op_id  (** A function or an operation *)
  | Global of global_decl_id
  | AdtCons of adt_cons_id  (** A function or ADT constructor identifier *)
  | Proj of projection  (** Field projector *)
  | TraitConst of trait_ref * generic_args * string
      (** A trait associated constant *)
[@@deriving show]

(** An instantiated qualifier.

    Note that for now we have a clear separation between types and expressions,
    which explains why we have the [generics] field: a function or ADT
    constructor is always fully instantiated.
 *)
type qualif = { id : qualif_id; generics : generic_args } [@@deriving show]

type field_id = FieldId.id [@@deriving show, ord]
type var_id = VarId.id [@@deriving show, ord]

(** Ancestor for {!iter_expression} visitor *)
class ['self] iter_expression_base =
  object (_self : 'self)
    inherit [_] iter_typed_pattern
    inherit! [_] iter_type_id
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_qualif : 'env -> qualif -> unit = fun _ _ -> ()
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()
    method visit_field_id : 'env -> field_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_expression} visitor *)
class ['self] map_expression_base =
  object (_self : 'self)
    inherit [_] map_typed_pattern
    inherit! [_] map_type_id
    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x
    method visit_qualif : 'env -> qualif -> qualif = fun _ x -> x
    method visit_loop_id : 'env -> loop_id -> loop_id = fun _ x -> x
    method visit_field_id : 'env -> field_id -> field_id = fun _ x -> x
  end

(** Ancestor for {!reduce_expression} visitor *)
class virtual ['self] reduce_expression_base =
  object (self : 'self)
    inherit [_] reduce_typed_pattern
    inherit! [_] reduce_type_id
    method visit_var_id : 'env -> var_id -> 'a = fun _ _ -> self#zero
    method visit_qualif : 'env -> qualif -> 'a = fun _ _ -> self#zero
    method visit_loop_id : 'env -> loop_id -> 'a = fun _ _ -> self#zero
    method visit_field_id : 'env -> field_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_expression} visitor *)
class virtual ['self] mapreduce_expression_base =
  object (self : 'self)
    inherit [_] mapreduce_typed_pattern
    inherit! [_] mapreduce_type_id

    method visit_var_id : 'env -> var_id -> var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_qualif : 'env -> qualif -> qualif * 'a =
      fun _ x -> (x, self#zero)

    method visit_loop_id : 'env -> loop_id -> loop_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_field_id : 'env -> field_id -> field_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** **Rk.:** here, {!expression} is not at all equivalent to the expressions
    used in LLBC. They are lambda-calculus expressions, and are thus actually
    more general than the LLBC statements, in a sense.
 *)
type expression =
  | Var of var_id  (** a variable *)
  | CVar of const_generic_var_id  (** a const generic var *)
  | Const of literal
  | App of texpression * texpression
      (** Application of a function to an argument.

          The function calls are still quite structured.
          Change that?... We might want to have a "normal" lambda calculus
          app (with head and argument): this would allow us to replace some
          field accesses with calls to projectors over fields (when there
          are clashes of field names, some provers like F* get pretty bad...)
       *)
  | Lambda of typed_pattern * texpression  (** Lambda abstraction: [λ x => e] *)
  | Qualif of qualif  (** A top-level qualifier *)
  | Let of bool * typed_pattern * texpression * texpression
      (** Let binding.

          TODO: the boolean should be replaced by an enum: sometimes we use
          the error-monad, sometimes we use the state-error monad (and we
          should do this an a per-function basis! For instance, arithmetic
          functions are always in the error monad, they shouldn't use the
          state-error monad).

          The boolean controls whether the let is monadic or not.
          For instance, in F*:
          - non-monadic: [let x = ... in ...]
          - monadic:     [x <-- ...; ...]

          Note that we are quite general for the left-value on purpose; this
          is used in several situations:

          1. When deconstructing a tuple:
          {[
            let (x, y) = p in ...
          ]}
          (not all languages have syntax like [p.0], [p.1]... and it is more
          readable anyway).

          2. When expanding an enumeration with one variant.
          In this case, {!Let} has to be understood as:
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
          ]}
       *)
  | Switch of texpression * switch_body
  | Loop of loop  (** See the comments for {!loop} *)
  | StructUpdate of struct_update  (** See the comments for {!struct_update} *)
  | Meta of (emeta[@opaque]) * texpression  (** Meta-information *)

and switch_body = If of texpression * texpression | Match of match_branch list
and match_branch = { pat : typed_pattern; branch : texpression }

(** In {!SymbolicToPure}, whenever we encounter a loop we insert a {!loop}
    node, which contains the end of the function (i.e., the call to the
    loop function) as well as the *body* of the loop translation (to be
    more precise, the bodies of the loop forward and backward function).
    We later split the function definition in {!PureMicroPasses}, to
    remove this node.

    Note that the loop body is a forward body if the function is
    a forward function, and a backward body (for the corresponding region
    group) if the function is a backward function.
 *)
and loop = {
  fun_end : texpression;
  loop_id : loop_id;
  meta : meta; [@opaque]
  fuel0 : var_id;
  fuel : var_id;
  input_state : var_id option;
  inputs : var list;
  inputs_lvs : typed_pattern list;
      (** The inputs seen as patterns. See {!fun_body}. *)
  output_ty : ty;  (** The output type of the loop *)
  loop_body : texpression;
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

    We also use struct updates to encode array aggregates, so that whenever
    the user writes code like:
    {[
      let a : [u32; 2] = [0, 1];
      ...
    ]}
    this gets encoded to:
    {[
      let a : Array u32 2 = Array.mk [0, 1] in
      ...
    ]}
 *)
and struct_update = {
  struct_id : type_id;
  init : var_id option;
  updates : (field_id * texpression) list;
}

and texpression = { e : expression; ty : ty }

(** Meta-value (converted to an expression). It is important that the content
    is opaque.

    TODO: is it possible to mark the whole mvalue type as opaque?
 *)
and mvalue = (texpression[@opaque])

(** Meta-information stored in the AST *)
and emeta =
  | Assignment of mplace * mvalue * mplace option
      (** Information about an assignment which occured in LLBC.
          We use this to guide the heuristics which derive pretty names.

          The first mplace stores the destination.
          The mvalue stores the value which is put in the destination
          The second (optional) mplace stores the origin.
        *)
  | SymbolicAssignment of (var_id[@opaque]) * mvalue
      (** Informationg linking a variable (from the pure AST) to an
          expression.

          We use this to guide the heuristics which derive pretty names.
        *)
  | MPlace of mplace  (** Meta-information about the origin of a value *)
  | Tag of string  (** A tag - typically used for debugging *)
[@@deriving
  show,
    visitors
      {
        name = "iter_expression";
        variety = "iter";
        ancestors = [ "iter_expression_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_expression";
        variety = "map";
        ancestors = [ "map_expression_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "reduce_expression";
        variety = "reduce";
        ancestors = [ "reduce_expression_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      },
    visitors
      {
        name = "mapreduce_expression";
        variety = "mapreduce";
        ancestors = [ "mapreduce_expression_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      }]

(** Information about the "effect" of a function *)
type fun_effect_info = {
  stateful_group : bool;
      (** [true] if the function group is stateful. By *function group*, we mean
          the set [{ forward function } U { backward functions }].

          We need this because of the option {!val:Config.backward_no_state_update}:
          if it is [true], then in case of a backward function {!stateful} might be
          [false], but we might need to know whether the corresponding forward function
          is stateful or not.
       *)
  stateful : bool;  (** [true] if the function is stateful (updates a state) *)
  can_fail : bool;  (** [true] if the return type is a [result] *)
  can_diverge : bool;
      (** [true] if the function can diverge (i.e., not terminate) *)
  is_rec : bool;
      (** [true] if the function is recursive (or in a mutually recursive group) *)
}
[@@deriving show]

type inputs_info = {
  has_fuel : bool;
  num_inputs_no_fuel_no_state : int;
      (** The number of input types ignoring the fuel (if used)
          and ignoring the state (if used) *)
  num_inputs_with_fuel_no_state : int;
      (** The number of input types, with the fuel (if used)
          and ignoring the state (if used) *)
  num_inputs_with_fuel_with_state : int;
      (** The number of input types, with fuel and state (if used) *)
}
[@@deriving show]

(** Meta information about a function signature *)
type fun_sig_info = {
  fwd_info : inputs_info;
      (** Information about the inputs of the forward function *)
  effect_info : fun_effect_info;
  ignore_output : bool;
      (** In case we merge the forward/backward functions: should we ignore
          the output (happens for forward functions if the output type is
          [unit] and there are non-filtered backward functions)?
       *)
}
[@@deriving show]

type back_sg_info = {
  inputs : (string option * ty) list;
      (** The additional inputs of the backward function *)
  inputs_no_state : (string option * ty) list;
  outputs : ty list;
      (** The "decomposed" list of outputs.

          The list contains all the types of
          all the given back values (there is at most one type per forward
          input argument).

          Ex.:
          {[
            fn choose<'a, T>(b : bool, x : &'a mut T, y : &'a mut T) -> &'a mut T;
          ]}
          Decomposed outputs:
          - forward function:  [[T]]
          - backward function: [[T; T]] (for "x" and "y")

          Non-decomposed ouputs (if the function can fail, but is not stateful):
          - [result T]
          - [[result (T * T)]]
       *)
  output_names : string option list;
      (** The optional names for the backward outputs.
          We derive those from the names of the inputs of the original LLBC
          function. *)
  effect_info : fun_effect_info;
  filter : bool;  (** Should we filter this backward function? *)
}
[@@deriving show]

(** A *decomposed* function signature. *)
type decomposed_fun_sig = {
  generics : generic_params;
      (** TODO: we should analyse the signature to make the type parameters implicit whenever possible *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance
          for the variables we introduce for the trait clauses: we derive
          those names from the types, and when doing so it is more meaningful
          to derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  fwd_inputs : ty list;
      (** The types of the inputs of the forward function.

          Note that those input types include the [fuel] parameter,
          if the function uses fuel for termination, and the [state] parameter,
          if the function is stateful.

          For instance, if we have the following Rust function:
          {[
            fn f(x : int);
          ]}

          If we translate it to a stateful function which uses fuel we get:
          {[
            val f : nat -> int -> state -> result (state * unit);
          ]}

          In particular, the list of input types is: [[nat; int; state]].
       *)
  fwd_output : ty;
      (** The "pure" output type of the forward function.

          Note that this type doesn't contain the "effect" of the function (i.e.,
          we haven't added the [state] if it is a stateful function and haven't
          wrapped the type in a [result]). Also, this output type is only about
          the forward function (it doesn't contain the type of the closures we
          return for the backward functions, in case we merge the forward and
          backward functions).
       *)
  back_sg : back_sg_info RegionGroupId.Map.t;
      (** Information about the backward functions *)
  fwd_info : fun_sig_info;
      (** Additional information about the forward function *)
}
[@@deriving show]

(** A function signature.

    We have the following cases:
    - forward function:
      [in_ty0 -> ... -> in_tyn -> out_ty]                           (* pure function *)
      [in_ty0 -> ... -> in_tyn -> result out_ty]                    (* error-monad *)
      [in_ty0 -> ... -> in_tyn -> state -> result (state & out_ty)] (* state-error *)
    - backward function:
      [in_ty0 -> ... -> in_tyn -> back_in0 -> ... back_inm -> (back_out0 & ... & back_outp)] (* pure function *)
      [in_ty0 -> ... -> in_tyn -> back_in0 -> ... back_inm ->
       result (back_out0 & ... & back_outp)] (* error-monad *)
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

    The function's type should be given by [mk_arrows sig.inputs sig.output].
    We provide additional meta-information with {!fun_sig.info}:
    - we divide between forward inputs and backward inputs (i.e., inputs specific
      to the forward functions, and additional inputs necessary if the signature is
      for a backward function)
    - we have booleans to give us the fact that the function takes a state as
      input, or can fail, etc. without having to inspect the signature
    - etc.
 *)
type fun_sig = {
  generics : generic_params;
      (** TODO: we should analyse the signature to make the type parameters implicit whenever possible *)
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance
          for the variables we introduce for the trait clauses: we derive
          those names from the types, and when doing so it is more meaningful
          to derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  inputs : ty list;
      (** The types of the inputs.

          Note that those input types take into account the [fuel] parameter,
          if the function uses fuel for termination, and the [state] parameter,
          if the function is stateful.

          For instance, if we have the following Rust function:
          {[
            fn f(x : int);
          ]}

          If we translate it to a stateful function which uses fuel we get:
          {[
            val f : nat -> int -> state -> result (state * unit);
          ]}

          In particular, the list of input types is: [[nat; int; state]].
       *)
  output : ty;
      (** The output type.

          Note that this type contains the "effect" of the function (i.e., it is
          not just a purification of the Rust return type). For instance, it will
          be a tuple with a [state] if the function is stateful, and will be wrapped
          in a [result] if the function can fail.
       *)
  fwd_info : fun_sig_info;
      (** Additional information about the forward function. *)
  back_effect_info : fun_effect_info RegionGroupId.Map.t;
}
[@@deriving show]

(** An instantiated function signature. See {!fun_sig} *)
type inst_fun_sig = { inputs : ty list; output : ty } [@@deriving show]

type fun_body = {
  inputs : var list;
  inputs_lvs : typed_pattern list;
      (** The inputs seen as patterns. Allows to make transformations, for example
          to replace unused variables by [_] *)
  body : texpression;
}
[@@deriving show]

type item_kind = A.item_kind [@@deriving show]

type fun_decl = {
  def_id : FunDeclId.id;
  is_local : bool;
  meta : meta;
  kind : item_kind;
  num_loops : int;
      (** The number of loops in the parent forward function (basically the number
          of loops appearing in the original Rust functions, unless some loops are
          duplicated because we don't join the control-flow after a branching)
       *)
  loop_id : LoopId.id option;
      (** [Some] if this definition was generated for a loop *)
  llbc_name : llbc_name;  (** The original LLBC name. *)
  name : string;
      (** We use the name only for printing purposes (for debugging):
          the name used at extraction time will be derived from the
          llbc_name.
       *)
  signature : fun_sig;
  is_global_decl_body : bool;
  body : fun_body option;
}
[@@deriving show]

type trait_decl = {
  def_id : trait_decl_id;
  is_local : bool;
  llbc_name : llbc_name;
  name : string;
  meta : meta;
  generics : generic_params;
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance
          for the variables we introduce for the trait clauses: we derive
          those names from the types, and when doing so it is more meaningful
          to derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  parent_clauses : trait_clause list;
  llbc_parent_clauses : Types.trait_clause list;
  consts : (trait_item_name * (ty * global_decl_id option)) list;
  types : (trait_item_name * (trait_clause list * ty option)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id option) list;
}
[@@deriving show]

type trait_impl = {
  def_id : trait_impl_id;
  is_local : bool;
  llbc_name : llbc_name;
  name : string;
  meta : meta;
  impl_trait : trait_decl_ref;
  llbc_impl_trait : Types.trait_decl_ref;
      (** Same remark as for {!field:llbc_generics}. *)
  generics : generic_params;
  llbc_generics : Types.generic_params;
      (** We use the LLBC generics to generate "pretty" names, for instance
          for the variables we introduce for the trait clauses: we derive
          those names from the types, and when doing so it is more meaningful
          to derive them from the original LLBC types from before the
          simplification of types like boxes and references. *)
  preds : predicates;
  parent_trait_refs : trait_ref list;
  consts : (trait_item_name * (ty * global_decl_id)) list;
  types : (trait_item_name * (trait_ref list * ty)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id) list;
}
[@@deriving show]
