open Identifiers
open Names
module PV = PrimitiveValues
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

(** We redefine identifiers for loop: in {!Values}, the identifiers are global
    (they monotonically increase across functions) while in {!module:Pure} we want
    the indices to start at 0 for every function.
 *)
module LoopId = IdGen ()

type loop_id = LoopId.id [@@deriving show, ord]

(** We give an identifier to every phase of the synthesis (forward, backward
    for group of regions 0, etc.) *)
module SynthPhaseId = IdGen ()

(** Pay attention to the fact that we also define a {!E.VarId} module in Values *)
module VarId = IdGen ()

type integer_type = T.integer_type [@@deriving show, ord]

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
  *)
type assumed_ty = State | Result | Error | Fuel | Vec | Option
[@@deriving show, ord]

(* TODO: we should never directly manipulate [Return] and [Fail], but rather
 * the monadic functions [return] and [fail] (makes treatment of error and
 * state-error monads more uniform) *)
let result_return_id = VariantId.of_int 0
let result_fail_id = VariantId.of_int 1
let option_some_id = T.option_some_id
let option_none_id = T.option_none_id
let error_failure_id = VariantId.of_int 0
let error_out_of_fuel_id = VariantId.of_int 1

(* We don't always use those: it depends on the backend (we use natural numbers
   for the fuel: in Coq they are enumerations, but in F* they are primitive)
*)
let fuel_zero_id = VariantId.of_int 0
let fuel_succ_id = VariantId.of_int 1

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
      (** {!Adt} encodes ADTs and tuples and assumed types.
       
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
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
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
type primitive_value = V.primitive_value [@@deriving show]

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
    inherit [_] VisitorsRuntime.iter

    method visit_primitive_value : 'env -> primitive_value -> unit =
      fun _ _ -> ()

    method visit_var : 'env -> var -> unit = fun _ _ -> ()
    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()
    method visit_ty : 'env -> ty -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_typed_pattern} visitor *)
class ['self] map_typed_pattern_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_primitive_value : 'env -> primitive_value -> primitive_value =
      fun _ x -> x

    method visit_var : 'env -> var -> var = fun _ x -> x
    method visit_mplace : 'env -> mplace -> mplace = fun _ x -> x
    method visit_ty : 'env -> ty -> ty = fun _ x -> x
    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
  end

(** Ancestor for {!reduce_typed_pattern} visitor *)
class virtual ['self] reduce_typed_pattern_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_primitive_value : 'env -> primitive_value -> 'a =
      fun _ _ -> self#zero

    method visit_var : 'env -> var -> 'a = fun _ _ -> self#zero
    method visit_mplace : 'env -> mplace -> 'a = fun _ _ -> self#zero
    method visit_ty : 'env -> ty -> 'a = fun _ _ -> self#zero
    method visit_variant_id : 'env -> variant_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_typed_pattern} visitor *)
class virtual ['self] mapreduce_typed_pattern_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_primitive_value
        : 'env -> primitive_value -> primitive_value * 'a =
      fun _ x -> (x, self#zero)

    method visit_var : 'env -> var -> var * 'a = fun _ x -> (x, self#zero)

    method visit_mplace : 'env -> mplace -> mplace * 'a =
      fun _ x -> (x, self#zero)

    method visit_ty : 'env -> ty -> ty * 'a = fun _ x -> (x, self#zero)

    method visit_variant_id : 'env -> variant_id -> variant_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** A pattern (which appears on the left of assignments, in matches, etc.). *)
type pattern =
  | PatConstant of primitive_value
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

type unop = Not | Neg of integer_type | Cast of integer_type * integer_type
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

(** A function id for a non-assumed function *)
type regular_fun_id = A.fun_id * LoopId.id option * T.RegionGroupId.id option
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
  | Global of GlobalDeclId.id
  | AdtCons of adt_cons_id  (** A function or ADT constructor identifier *)
  | Proj of projection  (** Field projector *)
[@@deriving show]

(** An instantiated qualified.

    Note that for now we have a clear separation between types and expressions,
    which explains why we have the [type_params] field: a function or ADT
    constructor is always fully instantiated.
 *)
type qualif = { id : qualif_id; type_args : ty list } [@@deriving show]

type var_id = VarId.id [@@deriving show, ord]

(** Ancestor for {!iter_expression} visitor *)
class ['self] iter_expression_base =
  object (_self : 'self)
    inherit [_] iter_typed_pattern
    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_qualif : 'env -> qualif -> unit = fun _ _ -> ()
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!map_expression} visitor *)
class ['self] map_expression_base =
  object (_self : 'self)
    inherit [_] map_typed_pattern

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x

    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x
    method visit_qualif : 'env -> qualif -> qualif = fun _ x -> x
    method visit_loop_id : 'env -> loop_id -> loop_id = fun _ x -> x
  end

(** Ancestor for {!reduce_expression} visitor *)
class virtual ['self] reduce_expression_base =
  object (self : 'self)
    inherit [_] reduce_typed_pattern

    method visit_integer_type : 'env -> integer_type -> 'a =
      fun _ _ -> self#zero

    method visit_var_id : 'env -> var_id -> 'a = fun _ _ -> self#zero
    method visit_qualif : 'env -> qualif -> 'a = fun _ _ -> self#zero
    method visit_loop_id : 'env -> loop_id -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for {!mapreduce_expression} visitor *)
class virtual ['self] mapreduce_expression_base =
  object (self : 'self)
    inherit [_] mapreduce_typed_pattern

    method visit_integer_type : 'env -> integer_type -> integer_type * 'a =
      fun _ x -> (x, self#zero)

    method visit_var_id : 'env -> var_id -> var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_qualif : 'env -> qualif -> qualif * 'a =
      fun _ x -> (x, self#zero)

    method visit_loop_id : 'env -> loop_id -> loop_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** **Rk.:** here, {!expression} is not at all equivalent to the expressions
    used in LLBC. They are lambda-calculus expressions, and are thus actually
    more general than the LLBC statements, in a sense.
 *)
type expression =
  | Var of var_id  (** a variable *)
  | Const of primitive_value
  | App of texpression * texpression
      (** Application of a function to an argument.

          The function calls are still quite structured.
          Change that?... We might want to have a "normal" lambda calculus
          app (with head and argument): this would allow us to replace some
          field accesses with calls to projectors over fields (when there
          are clashes of field names, some provers like F* get pretty bad...)
       *)
  | Abs of typed_pattern * texpression  (** Lambda abstraction: [fun x -> e] *)
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
  | Meta of (meta[@opaque]) * texpression  (** Meta-information *)

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
  fuel0 : var_id;
  fuel : var_id;
  input_state : var_id option;
  inputs : var list;
  inputs_lvs : typed_pattern list;
      (** The inputs seen as patterns. See {!fun_body}. *)
  back_output_tys : ty list option;
      (** The types of the given back values, if we ar esynthesizing a backward
          function *)
  loop_body : texpression;
}

and texpression = { e : expression; ty : ty }

(** Meta-value (converted to an expression). It is important that the content
    is opaque.
    
    TODO: is it possible to mark the whole mvalue type as opaque?
 *)
and mvalue = (texpression[@opaque])

(** Meta-information stored in the AST *)
and meta =
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
          if it is [true], then in case of a backward function {!stateful} is [false],
          but we might need to know whether the corresponding forward function
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

(** Meta information about a function signature *)
type fun_sig_info = {
  has_fuel : bool;
  (* TODO: add [num_fwd_inputs_no_fuel_no_state] *)
  num_fwd_inputs_with_fuel_no_state : int;
      (** The number of input types for forward computation, with the fuel (if used)
          and ignoring the state (if used) *)
  num_fwd_inputs_with_fuel_with_state : int;
      (** The number of input types for forward computation, with fuel and state (if used) *)
  num_back_inputs_no_state : int option;
      (** The number of additional inputs for the backward computation (if pertinent),
          ignoring the state (if there is one) *)
  num_back_inputs_with_state : int option;
      (** The number of additional inputs for the backward computation (if pertinent),
          with the state (if there is one) *)
  effect_info : fun_effect_info;
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
  type_params : type_var list;
  inputs : ty list;
      (** The input types.

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
  doutputs : ty list;
      (** The "decomposed" list of outputs.

          In case of a forward function, the list has length = 1, for the
          type of the returned value.
          
          In case of backward function, the list contains all the types of
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
  info : fun_sig_info;  (** Additional information *)
}
[@@deriving show]

(** An instantiated function signature. See {!fun_sig} *)
type inst_fun_sig = {
  inputs : ty list;
  output : ty;
  doutputs : ty list;
  info : fun_sig_info;
}
[@@deriving show]

type fun_body = {
  inputs : var list;
  inputs_lvs : typed_pattern list;
      (** The inputs seen as patterns. Allows to make transformations, for example
          to replace unused variables by [_] *)
  body : texpression;
}
[@@deriving show]

type fun_decl = {
  def_id : FunDeclId.id;
  num_loops : int;
      (** The number of loops in the parent forward function (basically the number
          of loops appearing in the original Rust functions, unless some loops are
          duplicated because we don't join the control-flow after a branching)
       *)
  loop_id : LoopId.id option;
      (** [Some] if this definition was generated for a loop *)
  back_id : T.RegionGroupId.id option;
  basename : fun_name;
      (** The "base" name of the function.
  
          The base name is the original name of the Rust function. We add suffixes
          (to identify the forward/backward functions) later.
       *)
  signature : fun_sig;
  is_global_decl_body : bool;
  body : fun_body option;
}
[@@deriving show]
