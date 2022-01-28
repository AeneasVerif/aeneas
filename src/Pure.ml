open Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module TypeDefId = T.TypeDefId
module TypeVarId = T.TypeVarId
module RegionId = T.RegionId
module VariantId = T.VariantId
module FieldId = T.FieldId
module SymbolicValueId = V.SymbolicValueId
module FunDefId = A.FunDefId

module SynthPhaseId = IdGen ()
(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)

module VarId = IdGen ()
(** Pay attention to the fact that we also define a [VarId] module in Values *)

(* TODO
   (** The assumed types for the pure AST.

       In comparison with CFIM:
       - we removed `Box` (because it is translated as the identity: `Box T == T`)
       - we added `Result`, which is the type used in the error monad. This allows
         us to have a unified treatment of expressions.
     *)
   type assumed_ty = unit

   type type_id = AdtId of TypeDefId.id | Tuple | Assumed of assumed_ty
   [@@deriving show, ord]
*)

type ty =
  | Adt of T.type_id * ty list
      (** [Adt] encodes ADTs and tuples and assumed types.
       
          TODO: what about the ended regions? (ADTs may be parameterized
          with several region variables. When giving back an ADT value, we may
          be able to only give back part of the ADT. We need a way to encode
          such "partial" ADTs.
          
          TODO: we may want to redefine type_id here, to remove some types like
          boxe. But on the other hand, it might introduce a lot of administrative
          manipulations just to remove boxe...
       *)
  | TypeVar of TypeVarId.id
  | Bool
  | Char
  | Integer of T.integer_type
  | Str
  | Array of ty (* TODO: there should be a constant with the array *)
  | Slice of ty
[@@deriving
  show,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "T.iter_ty_base" ];
        (* Reusing the visitor from Types.ml *)
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "T.map_ty_base" ];
        (* Reusing the visitor from Types.ml *)
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      }]

type field = { field_name : string; field_ty : ty } [@@deriving show]

type variant = { variant_name : string; fields : field list } [@@deriving show]

type type_def_kind = Struct of field list | Enum of variant list
[@@deriving show]

type type_var = T.type_var [@@deriving show]

type type_def = {
  def_id : TypeDefId.id;
  name : name;
  type_params : type_var list;
  kind : type_def_kind;
}
[@@deriving show]

type scalar_value = V.scalar_value

type constant_value = V.constant_value

type var = {
  id : VarId.id;
  basename : string option;
      (** The "basename" is used to generate a meaningful name for the variable
          (by potentially adding an index to uniquely identify it).
       *)
  ty : ty;
}
(** Because we introduce a lot of temporary variables, the list of variables
    is not fixed: we thus must carry all its information with the variable
    itself.
 *)

type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }

type projection = projection_elem list

type mplace = { name : string option; projection : projection }
(** "Meta" place.

    Meta-data retrieved from the symbolic execution, which gives provenance
    information about the values. We use this to generate names for the variables
    we introduce.
 *)

type place = { var : VarId.id; projection : projection }

(** Ancestor for [iter_var_or_dummy] iter visitor *)
class ['self] iter_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_var : 'env -> var -> unit = fun _ _ -> ()

    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()

    method visit_ty : 'env -> ty -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_var_or_dummy] visitor *)
class ['self] map_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_var : 'env -> var -> var = fun _ x -> x

    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x

    method visit_ty : 'env -> ty -> ty = fun _ x -> x
  end

(** Ancestor for [reduce_var_or_dummy] visitor *)
class virtual ['self] reduce_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_var : 'env -> var -> 'a = fun _ _ -> self#zero

    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero

    method visit_ty : 'env -> ty -> 'a = fun _ _ -> self#zero
  end

type var_or_dummy =
  | Var of var * mplace option
  | Dummy  (** Ignored value: `_`. *)
[@@deriving
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
      }]

(** A left value (which appears on the left of assignments *)
type lvalue = LvVar of var_or_dummy | LvAdt of adt_lvalue

and adt_lvalue = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_lvalue list;
}

and typed_lvalue = { value : lvalue; ty : ty }
[@@deriving
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
(** In most situations we won't use the type in [typed_rvalue].
    Note that it is still necessary to have some useful informations
    about ADTs, though.
 *)

type unop = Not | Neg of T.integer_type

type fun_id =
  | Regular of A.fun_id * T.RegionGroupId.id option
      (** Backward id: `Some` if the function is a backward function, `None`
          if it is a forward function *)
  | Unop of unop
  | Binop of E.binop * T.integer_type

(** Meta-information stored in the AST *)
type meta = Assignment of mplace * typed_rvalue

(** Ancestor for [iter_expression] iter visitor *)
class ['self] iter_expression_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_ty : 'env -> ty -> unit = fun _ _ -> ()

    method visit_typed_rvalue : 'env -> typed_rvalue -> unit = fun _ _ -> ()

    method visit_typed_lvalue : 'env -> typed_lvalue -> unit = fun _ _ -> ()

    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()

    method visit_meta : 'env -> meta -> unit = fun _ _ -> ()

    method visit_integer_type : 'env -> T.integer_type -> unit = fun _ _ -> ()

    method visit_scalar_value : 'env -> scalar_value -> unit = fun _ _ -> ()

    method visit_id : 'env -> VariantId.id -> unit = fun _ _ -> ()

    method visit_fun_id : 'env -> fun_id -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_expression] map visitor *)
class ['self] map_expression_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_ty : 'env -> ty -> ty = fun _ x -> x

    method visit_typed_rvalue : 'env -> typed_rvalue -> typed_rvalue =
      fun _ x -> x

    method visit_typed_lvalue : 'env -> typed_lvalue -> typed_lvalue =
      fun _ x -> x

    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x

    method visit_meta : 'env -> meta -> meta = fun _ x -> x

    method visit_integer_type : 'env -> T.integer_type -> T.integer_type =
      fun _ x -> x

    method visit_scalar_value : 'env -> scalar_value -> scalar_value =
      fun _ x -> x

    method visit_id : 'env -> VariantId.id -> VariantId.id = fun _ x -> x

    method visit_fun_id : 'env -> fun_id -> fun_id = fun _ x -> x
  end

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in CFIM. They are lambda-calculus expressions, and are thus actually
    more general than the CFIM statements, in a sense.
    
    TODO: actually when I defined [expression] I still had Rust in mind, so
    it is not a "textbook" lambda calculus expression (still quite constrained).
    As we want to do transformations on it, through micro-passes, it would be
    good to update it and make it more "regular".
    
    TODO: remove `Return` and `Fail` (they should be "normal" values, I think)
 *)
type expression =
  | Return of typed_rvalue
  | Fail
  | Value of typed_rvalue * mplace option
  | Call of call
  | Let of typed_lvalue * expression * expression
      (** Let binding.
      
          TODO: add a boolean to control whether the let is monadic or not.
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
  | Switch of typed_rvalue * mplace option * switch_body
  | Meta of meta * expression  (** Meta-information *)

and call = {
  func : fun_id;
  type_params : ty list;
  args : expression list;
      (** Note that immediately after we converted the symbolic AST to a pure AST,
          some functions may have no arguments. For instance:
          ```
          fn f();
          ```
          We later add a unit argument.
       *)
}

and switch_body =
  | If of expression * expression
  | SwitchInt of T.integer_type * (scalar_value * expression) list * expression
  | Match of match_branch list

and match_branch = { pat : typed_lvalue; branch : expression }
[@@deriving
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
      }]

type fun_sig = {
  type_params : type_var list;
  inputs : ty list;
  outputs : ty list;
      (** The list of outputs.

          In case of a forward function, the list will have length = 1.
          However, in case of backward function, the list may have length > 1.
          If the length is > 1, it gets extracted to a tuple type. Followingly,
          we could not use a list because we can encode tuples, but here we
          want to account for the fact that we immediately deconstruct the tuple
          upon calling the backward function (because the backward function is
          called to update a set of values in the environment).
       *)
}

type inst_fun_sig = { inputs : ty list; outputs : ty list }

type fun_def = {
  def_id : FunDefId.id;
  back_id : T.RegionGroupId.id option;
  basename : name;
      (** The "base" name of the function.
  
          The base name is the original name of the Rust function. We add suffixes
          (to identify the forward/backward functions) later.
       *)
  signature : fun_sig;
  inputs : var list;
  body : expression;
}
