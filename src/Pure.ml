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

type ty =
  | Adt of T.type_id * ty list
      (** [Adt] encodes ADTs and tuples and assumed types.
       
          TODO: what about the ended regions? (ADTs may be parameterized
          with several region variables. When giving back an ADT value, we may
          be able to only give back part of the ADT. We need a way to encode
          such "partial" ADTs.
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

type var = { id : VarId.id; ty : ty }
(** Because we introduce a lot of temporary variables, the list of variables
    is not fixed: we thus must carry all its information with the variable
    itself.
    
    TODO: add a field for the basename.
 *)

type var_or_dummy = Var of var | Dummy  (** Ignored value: `_` *)

(** A left value (which appears on the left of assignments *)
type lvalue =
  | LvVar of var_or_dummy
  | LvTuple of typed_lvalue list
      (** Rk.: for now we don't support general ADTs *)

and typed_lvalue = { value : lvalue; ty : ty }

type projection_elem = { pkind : E.field_proj_kind; field_id : FieldId.id }

type projection = projection_elem list

type place = { var : VarId.id; projection : projection }

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

type call = {
  func : fun_id;
  type_params : ty list;
  args : typed_rvalue list;
      (** Note that at this point, some functions have no arguments. For instance:
          ```
          fn f();
          ```

          In the extracted code, we add a unit argument. This is unit argument is
          added later, when going from the "pure" AST to the "extracted" AST.
       *)
}

type let_bindings =
  | Call of typed_lvalue list * call
      (** The called function and the tuple of returned values. *)
  | Assign of typed_lvalue * typed_rvalue
      (** Variable assignment: the introduced pattern and the place we read *)
  | Deconstruct of
      var_or_dummy list * (TypeDefId.id * VariantId.id) option * typed_rvalue
      (** This is used in two cases.

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
          
          Later, depending on the language we extract to, we can eventually
          update it to something like this (for F*, for instance):
          ```
          let x = Cons?.v ls in
          let tl = Cons?.tl ls in
          ...
          ```
          
          Note that we prefer not handling this case through a match.
          TODO: actually why not encoding it as a match internally, then
          generating the `let Cons ... = ... in ...` upon outputting the
          code if we detect there is exactly one variant?...
       *)

(** **Rk.:** here, [expression] is not at all equivalent to the expressions
    used in CFIM. They are lambda-calculus expressions, and are thus actually
    more general than the CFIM statements, in a sense.
 *)
type expression =
  | Return of typed_rvalue
  | Panic
  | Let of let_bindings * expression
      (** Let bindings include the let-bindings introduced because of function calls *)
  | Switch of typed_rvalue * switch_body

and switch_body =
  | If of expression * expression
  | SwitchInt of T.integer_type * (scalar_value * expression) list * expression
  | Match of match_branch list

and match_branch = {
  variant_id : VariantId.id;
  vars : var_or_dummy list;
  branch : expression;
}

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
  basename : name;
      (** The "base" name of the function.
  
          The base name is the original name of the Rust function. We add suffixes
          (to identify the forward/backward functions) later.
       *)
  signature : fun_sig;
  inputs : var list;
  body : expression;
}
