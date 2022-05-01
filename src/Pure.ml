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

    In comparison with LLBC:
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
 * Also: tuples...
 * Rmk: projections are actually only used as meta-data.
 * *)
type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }
[@@deriving show]

type projection = projection_elem list [@@deriving show]

type mplace = {
  var_id : V.VarId.id;
  name : string option;
  projection : projection;
}
[@@deriving show]
(** "Meta" place.

    Meta-data retrieved from the symbolic execution, which gives provenance
    information about the values. We use this to generate names for the variables
    we introduce.
 *)

type variant_id = VariantId.id [@@deriving show]

(** Ancestor for [iter_var_or_dummy] visitor *)
class ['self] iter_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_constant_value : 'env -> constant_value -> unit = fun _ _ -> ()

    method visit_var : 'env -> var -> unit = fun _ _ -> ()

    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()

    method visit_ty : 'env -> ty -> unit = fun _ _ -> ()

    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_typed_rvalue] visitor *)
class ['self] map_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_constant_value : 'env -> constant_value -> constant_value =
      fun _ x -> x

    method visit_var : 'env -> var -> var = fun _ x -> x

    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x

    method visit_ty : 'env -> ty -> ty = fun _ x -> x

    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
  end

(** Ancestor for [reduce_typed_rvalue] visitor *)
class virtual ['self] reduce_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_constant_value : 'env -> constant_value -> 'a =
      fun _ _ -> self#zero

    method visit_var : 'env -> var -> 'a = fun _ _ -> self#zero

    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero

    method visit_ty : 'env -> ty -> 'a = fun _ _ -> self#zero

    method visit_variant_id : 'env -> variant_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for [mapreduce_typed_rvalue] visitor *)
class virtual ['self] mapreduce_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_constant_value : 'env -> constant_value -> constant_value * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_var : 'env -> var -> var * 'a = fun _ x -> (x, self#zero)

    method visit_mplace : 'env -> mplace -> mplace * 'a =
      fun _ x -> (x, self#zero)

    method visit_ty : 'env -> ty -> ty * 'a = fun _ x -> (x, self#zero)

    method visit_variant_id : 'env -> variant_id -> variant_id * 'a =
      fun _ x -> (x, self#zero)
  end

type var_or_dummy =
  | Var of var * mplace option
      (** Rk.: the mdplace is actually always a variable (i.e.: there are no projections).

          We use [mplace] because it leads to a more uniform treatment of the meta
          information.
       *)
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

(** A pattern (which appears on the left of assignments, in matches, etc.). *)
type pattern =
  | PatConcrete of constant_value
      (** [PatConcrete] is necessary because we merge the switches over integer
          values and the matches over enumerations *)
  | PatVar of var_or_dummy
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
        ancestors = [ "iter_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_typed_pattern";
        variety = "map";
        ancestors = [ "map_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_typed_pattern";
        variety = "reduce";
        ancestors = [ "reduce_var_or_dummy" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_typed_pattern";
        variety = "mapreduce";
        ancestors = [ "mapreduce_var_or_dummy" ];
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

type adt_cons_id = { adt_id : type_id; variant_id : variant_id option }
[@@deriving show]
(** An identifier for an ADT constructor *)

type proj_kind = { adt_id : type_id; field_id : FieldId.id } [@@deriving show]
(** Projection kind - For now we don't support projection of tuple fields 
    (because not all the backends have syntax for this).
    
    TODO: rename
 *)

type qualif_id =
  | Func of fun_id
  | AdtCons of adt_cons_id  (** A function or ADT constructor identifier *)
  | Proj of proj_kind  (** Field projector *)
[@@deriving show]

type qualif = {
  id : qualif_id;
  type_params : ty list; (* TODO: rename to type_args *)
}
[@@deriving show]
(** An instantiated qualified.

    Note that for now we have a clear separation between types and expressions,
    which explains why we have the `type_params` field: a function or ADT
    constructor is always fully instantiated.
 *)

type var_id = VarId.id [@@deriving show]

(** Ancestor for [iter_expression] visitor *)
class ['self] iter_expression_base =
  object (_self : 'self)
    inherit [_] iter_typed_pattern

    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()

    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()

    method visit_qualif : 'env -> qualif -> unit = fun _ _ -> ()
  end

(** Ancestor for [map_expression] visitor *)
class ['self] map_expression_base =
  object (_self : 'self)
    inherit [_] map_typed_pattern

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x

    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x

    method visit_qualif : 'env -> qualif -> qualif = fun _ x -> x
  end

(** Ancestor for [reduce_expression] visitor *)
class virtual ['self] reduce_expression_base =
  object (self : 'self)
    inherit [_] reduce_typed_pattern

    method visit_integer_type : 'env -> integer_type -> 'a =
      fun _ _ -> self#zero

    method visit_var_id : 'env -> var_id -> 'a = fun _ _ -> self#zero

    method visit_qualif : 'env -> qualif -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for [mapreduce_expression] visitor *)
class virtual ['self] mapreduce_expression_base =
  object (self : 'self)
    inherit [_] mapreduce_typed_pattern

    method visit_integer_type : 'env -> integer_type -> integer_type * 'a =
      fun _ x -> (x, self#zero)

    method visit_var_id : 'env -> var_id -> var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_qualif : 'env -> qualif -> qualif * 'a =
      fun _ x -> (x, self#zero)
  end

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in LLBC. They are lambda-calculus expressions, and are thus actually
    more general than the LLBC statements, in a sense.
 *)
type expression =
  | Local of var_id
      (** Local variable - TODO: we name it "Local" because "Var" is used
          in [var_or_dummy]: change the name. Maybe rename `Var` and `Dummy`
          in `var_or_dummy` to `PatVar` and `PatDummy`.
       *)
  | Const of constant_value
  | App of texpression * texpression
      (** Application of a function to an argument.

          The function calls are still quite structured.
          Change that?... We might want to have a "normal" lambda calculus
          app (with head and argument): this would allow us to replace some
          field accesses with calls to projectors over fields (when there
          are clashes of field names, some provers like F* get pretty bad...)
       *)
  | Abs of typed_pattern * texpression  (** Lambda abstraction: `fun x -> e` *)
  | Qualif of qualif  (** A top-level qualifier *)
  | Let of bool * typed_pattern * texpression * texpression
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
  | Meta of (meta[@opaque]) * texpression  (** Meta-information *)

and switch_body = If of texpression * texpression | Match of match_branch list

and match_branch = { pat : typed_pattern; branch : texpression }

and texpression = { e : expression; ty : ty }

and mvalue = (texpression[@opaque])
(** Meta-value (converted to an expression). It is important that the content
    is opaque.
    
    TODO: is it possible to mark the whole mvalue type as opaque?
 *)

and meta =
  | Assignment of mplace * mvalue * mplace option
      (** Meta-information stored in the AST.

          The first mplace stores the destination.
          The mvalue stores the value which is put in the destination
          The second (optional) mplace stores the origin.
        *)
  | MPlace of mplace  (** Meta-information about the origin of a value *)
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

type fun_body = {
  inputs : var list;
  inputs_lvs : typed_pattern list;
      (** The inputs seen as patterns. Allows to make transformations, for example
          to replace unused variables by `_` *)
  body : texpression;
}

type fun_decl = {
  def_id : FunDeclId.id;
  back_id : T.RegionGroupId.id option;
  basename : fun_name;
      (** The "base" name of the function.
  
          The base name is the original name of the Rust function. We add suffixes
          (to identify the forward/backward functions) later.
       *)
  signature : fun_sig;
  body : fun_body option;
}
