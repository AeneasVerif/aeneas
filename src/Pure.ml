open Identifiers
open Names
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

module SynthPhaseId = IdGen ()
(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)

module VarId = IdGen ()
(** Pay attention to the fact that we also define a [VarId] module in Values *)

type integer_type = T.integer_type [@@deriving show, ord]

(** The assumed types for the pure AST.

    In comparison with CFIM:
    - we removed `Box` (because it is translated as the identity: `Box T == T`)
    - we added:
      - `Result`: the type used in the error monad. This allows us to have a
        unified treatment of expressions (especially when we have to unfold the
        monadic binds)
      - `State`: the type of the state, when using state-error monads. Note that
        this state is opaque to Aeneas (the user can define it, or leave it as
        assumed)
  *)
type assumed_ty = State | Result | Vec | Option [@@deriving show, ord]

(* TODO: we should never directly manipulate `Return` and `Fail`, but rather
 * the monadic functions `return` and `fail` (makes treatment of error and
 * state-error monads more uniform) *)
let result_return_id = VariantId.of_int 0

let result_fail_id = VariantId.of_int 1

let option_some_id = T.option_some_id

let option_none_id = T.option_none_id

type type_id = AdtId of TypeDeclId.id | Tuple | Assumed of assumed_ty
[@@deriving show, ord]

(** Ancestor for iter visitor for [ty] *)
class ['self] iter_ty_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_id : 'env -> TypeVarId.id -> unit = fun _ _ -> ()

    method visit_type_id : 'env -> type_id -> unit = fun _ _ -> ()

    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for [ty] *)
class ['self] map_ty_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_id : 'env -> TypeVarId.id -> TypeVarId.id = fun _ id -> id

    method visit_type_id : 'env -> type_id -> type_id = fun _ id -> id

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ ity -> ity
  end

type ty =
  | Adt of type_id * ty list
      (** [Adt] encodes ADTs and tuples and assumed types.
       
          TODO: what about the ended regions? (ADTs may be parameterized
          with several region variables. When giving back an ADT value, we may
          be able to only give back part of the ADT. We need a way to encode
          such "partial" ADTs.
       *)
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Integer of integer_type
  | Str
  | Array of ty (* TODO: this should be an assumed type?... *)
  | Slice of ty (* TODO: this should be an assumed type?... *)
  | Arrow of ty * ty
[@@deriving
  show,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      }]

type field = { field_name : string option; field_ty : ty } [@@deriving show]

type variant = { variant_name : string; fields : field list } [@@deriving show]

type type_decl_kind = Struct of field list | Enum of variant list | Opaque
[@@deriving show]

type type_var = T.type_var [@@deriving show]

type type_decl = {
  def_id : TypeDeclId.id;
  name : name;
  type_params : type_var list;
  kind : type_decl_kind;
}
[@@deriving show]

type scalar_value = V.scalar_value [@@deriving show]

type constant_value = V.constant_value [@@deriving show]

type var = {
  id : VarId.id;
  basename : string option;
      (** The "basename" is used to generate a meaningful name for the variable
          (by potentially adding an index to uniquely identify it).
       *)
  ty : ty;
}
[@@deriving show]
(** Because we introduce a lot of temporary variables, the list of variables
    is not fixed: we thus must carry all its information with the variable
    itself.
 *)

(* TODO: we might want to redefine field_proj_kind here, to prevent field accesses
 * on enumerations.
 * Also: tuples... *)
type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }
[@@deriving show]

type projection = projection_elem list [@@deriving show]

type mplace = { name : string option; projection : projection }
[@@deriving show]
(** "Meta" place.

    Meta-data retrieved from the symbolic execution, which gives provenance
    information about the values. We use this to generate names for the variables
    we introduce.
 *)

type place = { var : VarId.id; projection : projection } [@@deriving show]

(** Ancestor for [iter_var_or_dummy] visitor *)
class ['self] iter_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_constant_value : 'env -> constant_value -> unit = fun _ _ -> ()

    method visit_var : 'env -> var -> unit = fun _ _ -> ()

    method visit_place : 'env -> place -> unit = fun _ _ -> ()

    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()

    method visit_ty : 'env -> ty -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_var_or_dummy] visitor *)
class ['self] map_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_constant_value : 'env -> constant_value -> constant_value =
      fun _ x -> x

    method visit_var : 'env -> var -> var = fun _ x -> x

    method visit_place : 'env -> place -> place = fun _ x -> x

    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x

    method visit_ty : 'env -> ty -> ty = fun _ x -> x
  end

(** Ancestor for [reduce_var_or_dummy] visitor *)
class virtual ['self] reduce_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_constant_value : 'env -> constant_value -> 'a =
      fun _ _ -> self#zero

    method visit_var : 'env -> var -> 'a = fun _ _ -> self#zero

    method visit_place : 'env -> place -> 'a = fun _ _ -> self#zero

    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero

    method visit_ty : 'env -> ty -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for [mapreduce_var_or_dummy] visitor *)
class virtual ['self] mapreduce_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_constant_value : 'env -> constant_value -> constant_value * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_var : 'env -> var -> var * 'a = fun _ x -> (x, self#zero)

    method visit_place : 'env -> place -> place * 'a = fun _ x -> (x, self#zero)

    method visit_mplace : 'env -> mplace -> mplace * 'a =
      fun _ x -> (x, self#zero)

    method visit_ty : 'env -> ty -> ty * 'a = fun _ x -> (x, self#zero)
  end

type var_or_dummy =
  | Var of var * mplace option
  | Dummy  (** Ignored value: `_`. *)
[@@deriving
  show,
    visitors
      {
        name = "iter_var_or_dummy";
        variety = "iter";
        ancestors = [ "iter_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_var_or_dummy";
        variety = "map";
        ancestors = [ "map_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.map] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_var_or_dummy";
        variety = "reduce";
        ancestors = [ "reduce_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.reduce] *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_var_or_dummy";
        variety = "mapreduce";
        ancestors = [ "mapreduce_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.reduce] *);
        polymorphic = false;
      }]

(** A left value (which appears on the left of assignments *)
type lvalue =
  | LvConcrete of constant_value
      (** [LvConcrete] is necessary because we merge the switches over integer
        values and the matches over enumerations *)
  | LvVar of var_or_dummy
  | LvAdt of adt_lvalue

and adt_lvalue = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_lvalue list;
}

and typed_lvalue = { value : lvalue; ty : ty }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_lvalue";
        variety = "iter";
        ancestors = [ "iter_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_typed_lvalue";
        variety = "map";
        ancestors = [ "map_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_typed_lvalue";
        variety = "reduce";
        ancestors = [ "reduce_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_typed_lvalue";
        variety = "mapreduce";
        ancestors = [ "mapreduce_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        polymorphic = false;
      }]

type rvalue =
  | RvConcrete of constant_value
  | RvPlace of place
  | RvAdt of adt_rvalue

and adt_rvalue = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_rvalue list;
}

and typed_rvalue = { value : rvalue; ty : ty }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_rvalue";
        variety = "iter";
        ancestors = [ "iter_typed_lvalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_typed_rvalue";
        variety = "map";
        ancestors = [ "map_typed_lvalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_typed_rvalue";
        variety = "reduce";
        ancestors = [ "reduce_typed_lvalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_typed_rvalue";
        variety = "mapreduce";
        ancestors = [ "mapreduce_typed_lvalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        polymorphic = false;
      }]

type unop = Not | Neg of integer_type [@@deriving show, ord]

type fun_id =
  | Regular of A.fun_id * T.RegionGroupId.id option
      (** Backward id: `Some` if the function is a backward function, `None`
          if it is a forward function.

          TODO: we need to redefine A.fun_id here, to add `fail` and
          `return` (important to get a unified treatment of the state-error
          monad). For now, when using the state-error monad: extraction
          works only if we unfold all the monadic let-bindings, and we
          then replace the content of the occurrences of `Return` to also
          return the state (which is really super ugly).
       *)
  | Unop of unop
  | Binop of E.binop * integer_type
[@@deriving show, ord]

(** Meta-information stored in the AST *)
type meta = Assignment of mplace * typed_rvalue [@@deriving show]

(** Ancestor for [iter_expression] visitor *)
class ['self] iter_expression_base =
  object (_self : 'self)
    inherit [_] iter_typed_rvalue

    method visit_meta : 'env -> meta -> unit = fun _ _ -> ()

    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()

    method visit_scalar_value : 'env -> scalar_value -> unit = fun _ _ -> ()

    method visit_id : 'env -> VariantId.id -> unit = fun _ _ -> ()

    method visit_fun_id : 'env -> fun_id -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_expression] visitor *)
class ['self] map_expression_base =
  object (_self : 'self)
    inherit [_] map_typed_rvalue

    method visit_meta : 'env -> meta -> meta = fun _ x -> x

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x

    method visit_scalar_value : 'env -> scalar_value -> scalar_value =
      fun _ x -> x

    method visit_id : 'env -> VariantId.id -> VariantId.id = fun _ x -> x

    method visit_fun_id : 'env -> fun_id -> fun_id = fun _ x -> x
  end

(** Ancestor for [reduce_expression] visitor *)
class virtual ['self] reduce_expression_base =
  object (self : 'self)
    inherit [_] reduce_typed_rvalue

    method visit_meta : 'env -> meta -> 'a = fun _ _ -> self#zero

    method visit_integer_type : 'env -> integer_type -> 'a =
      fun _ _ -> self#zero

    method visit_scalar_value : 'env -> scalar_value -> 'a =
      fun _ _ -> self#zero

    method visit_id : 'env -> VariantId.id -> 'a = fun _ _ -> self#zero

    method visit_fun_id : 'env -> fun_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for [mapreduce_expression] visitor *)
class virtual ['self] mapreduce_expression_base =
  object (self : 'self)
    inherit [_] mapreduce_typed_rvalue

    method visit_meta : 'env -> meta -> meta * 'a = fun _ x -> (x, self#zero)

    method visit_integer_type : 'env -> integer_type -> integer_type * 'a =
      fun _ x -> (x, self#zero)

    method visit_scalar_value : 'env -> scalar_value -> scalar_value * 'a =
      fun _ x -> (x, self#zero)

    method visit_id : 'env -> VariantId.id -> VariantId.id * 'a =
      fun _ x -> (x, self#zero)

    method visit_fun_id : 'env -> fun_id -> fun_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in CFIM. They are lambda-calculus expressions, and are thus actually
    more general than the CFIM statements, in a sense.
 *)
type expression =
  | Value of typed_rvalue * mplace option
  | Call of call
      (** The function calls are still quite structured.
          Change that?... We might want to have a "normal" lambda calculus
          app (with head and argument): this would allow us to replace some
          field accesses with calls to projectors over fields (when there
          are clashes of field names, some provers like F* get pretty bad...)
       *)
  | Let of bool * typed_lvalue * texpression * texpression
      (** Let binding.
      
          TODO: the boolean should be replaced by an enum: sometimes we use
          the error-monad, sometimes we use the state-error monad (and we
          do this an a per-function basis! For instance, arithmetic functions
          are always in the error monad).

          The boolean controls whether the let is monadic or not.
          For instance, in F*:
          - non-monadic: `let x = ... in ...`
          - monadic:     `x <-- ...; ...`

          Note that we are quite general for the left-value on purpose; this
          is used in several situations:

          1. When deconstructing a tuple:
          ```
          let (x, y) = p in ...
          ```
          (not all languages have syntax like `p.0`, `p.1`... and it is more
          readable anyway).
          
          2. When expanding an enumeration with one variant.
          
          In this case, [Deconstruct] has to be understood as:
          ```
          let Cons x tl = ls in
          ...
          ```
          
          Note that later, depending on the language we extract to, we can
          eventually update it to something like this (for F*, for instance):
          ```
          let x = Cons?.v ls in
          let tl = Cons?.tl ls in
          ...
          ```
       *)
  | Switch of texpression * switch_body
  | Meta of meta * texpression  (** Meta-information *)

and call = {
  func : fun_id;
  type_params : ty list;
  args : texpression list;
      (** Note that immediately after we converted the symbolic AST to a pure AST,
          some functions may have no arguments. For instance:
          ```
          fn f();
          ```
          We later add a unit argument.
       *)
}

and switch_body = If of texpression * texpression | Match of match_branch list

and match_branch = { pat : typed_lvalue; branch : texpression }

and texpression = { e : expression; ty : ty }
[@@deriving
  show,
    visitors
      {
        name = "iter_expression";
        variety = "iter";
        ancestors = [ "iter_expression_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_expression";
        variety = "map";
        ancestors = [ "map_expression_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "reduce_expression";
        variety = "reduce";
        ancestors = [ "reduce_expression_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
      },
    visitors
      {
        name = "mapreduce_expression";
        variety = "mapreduce";
        ancestors = [ "mapreduce_expression_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
      }]

type fun_sig = {
  type_params : type_var list;
  inputs : ty list;
  outputs : ty list;
      (** The list of outputs.

          Immediately after the translation from symbolic to pure we have this
          the following:
          In case of a forward function, the list will have length = 1.
          However, in case of backward function, the list may have length > 1.
          If the length is > 1, it gets extracted to a tuple type. Followingly,
          we could not use a list because we can encode tuples, but here we
          want to account for the fact that we immediately deconstruct the tuple
          upon calling the backward function (because the backward function is
          called to update a set of values in the environment).
          
          After the "to monadic" pass, the list has size exactly one (and we
          use the `Result` type).
       *)
}

type inst_fun_sig = { inputs : ty list; outputs : ty list }

type fun_decl = {
  def_id : FunDeclId.id;
  back_id : T.RegionGroupId.id option;
  basename : fun_name;
      (** The "base" name of the function.
  
          The base name is the original name of the Rust function. We add suffixes
          (to identify the forward/backward functions) later.
       *)
  signature : fun_sig;
  inputs : var list;
  inputs_lvs : typed_lvalue list;
      (** The inputs seen as lvalues. Allows to make transformations, for example
          to replace unused variables by `_` *)
  body : texpression;
}
