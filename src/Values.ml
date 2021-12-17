open Identifiers
open Types

(* TODO: I often write "abstract" (value, borrow content, etc.) while I should
 * write "abstraction" (because those values are not abstract, they simply are
 * inside abstractions) *)

module VarId = IdGen ()

module BorrowId = IdGen ()

module SymbolicValueId = IdGen ()

module AbstractionId = IdGen ()

module RegionId = IdGen ()

(** A variable *)

type big_int = Z.t

let big_int_of_yojson (json : Yojson.Safe.t) : (big_int, string) result =
  match json with
  | `Int i -> Ok (Z.of_int i)
  | `Intlit is -> Ok (Z.of_string is)
  | _ -> Error "not an integer or an integer literal"

let big_int_to_yojson (i : big_int) = `Intlit (Z.to_string i)

let pp_big_int (fmt : Format.formatter) (bi : big_int) : unit =
  Format.pp_print_string fmt (Z.to_string bi)

let show_big_int (bi : big_int) : string = Z.to_string bi

type scalar_value = { value : big_int; int_ty : integer_type } [@@deriving show]
(** A scalar value

    Note that we use unbounded integers everywhere.
    We then harcode the boundaries for the different types.
 *)

(** A constant value *)
type constant_value =
  | Scalar of scalar_value
  | Bool of bool
  | Char of char
  | String of string
[@@deriving show]

type symbolic_value = { sv_id : SymbolicValueId.id; sv_ty : rty }
[@@deriving show]
(** Symbolic value *)

type symbolic_proj_comp = {
  svalue : symbolic_value;  (** The symbolic value itself *)
  rset_ended : RegionId.set_t;
      (** The regions used in the symbolic value which have already ended *)
}
[@@deriving show]
(** A complementary projector over a symbolic value.
    
    "Complementary" stands for the fact that it is a projector over all the
    regions *but* the ones which are listed in the projector.
*)

(** Ancestor for iter visitor for [typed_value] *)
class ['self] iter_typed_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_constant_value : 'env -> constant_value -> unit = fun _ _ -> ()

    method visit_erased_region : 'env -> erased_region -> unit = fun _ _ -> ()

    method visit_symbolic_proj_comp : 'env -> symbolic_proj_comp -> unit =
      fun _ _ -> ()

    method visit_ety : 'env -> ety -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for [typed_value] *)
class ['self] map_typed_value_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_constant_value : 'env -> constant_value -> constant_value =
      fun _ cv -> cv

    method visit_erased_region : 'env -> erased_region -> erased_region =
      fun _ r -> r

    method visit_symbolic_proj_comp
        : 'env -> symbolic_proj_comp -> symbolic_proj_comp =
      fun _ sv -> sv

    method visit_ety : 'env -> ety -> ety = fun _ ty -> ty
  end

(** An untyped value, used in the environments *)
type value =
  | Concrete of constant_value  (** Concrete (non-symbolic) value *)
  | Adt of adt_value  (** Enumerations and structures *)
  | Bottom  (** No value (uninitialized or moved value) *)
  | Borrow of borrow_content  (** A borrowed value *)
  | Loan of loan_content  (** A loaned value *)
  | Symbolic of symbolic_proj_comp  (** Unknown (symbolic) value *)

and adt_value = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_value list;
}

and borrow_content =
  | SharedBorrow of (BorrowId.id[@opaque])  (** A shared value *)
  | MutBorrow of (BorrowId.id[@opaque]) * typed_value
      (** A mutably borrowed value *)
  | InactivatedMutBorrow of (BorrowId.id[@opaque])
      (** An inactivated mut borrow.

          This is used to model two-phase borrows. When evaluating a two-phase
          mutable borrow, we first introduce an inactivated borrow which behaves
          like a shared borrow, until the moment we actually *use* the borrow:
          at this point, we end all the other shared borrows (or inactivated borrows
          - though there shouldn't be any other inactivated borrows if the program
          is well typed) of this value and replace the inactivated borrow with a
          mutable borrow.
       *)

and loan_content =
  | SharedLoan of (BorrowId.set_t[@opaque]) * typed_value
  | MutLoan of (BorrowId.id[@opaque])

and typed_value = { value : value; ty : ety }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_value";
        variety = "iter";
        ancestors = [ "iter_typed_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_typed_value";
        variety = "map";
        ancestors = [ "map_typed_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]
(** "Regular" typed value (we map variables to typed values) *)

type abstract_shared_borrows =
  | AsbSet of BorrowId.set_t
  | AsbProjReborrows of symbolic_value * rty
  | AsbUnion of abstract_shared_borrows * abstract_shared_borrows
      (** TODO: explanations *)
[@@deriving show]

type aproj =
  | AProjLoans of symbolic_value
  | AProjBorrows of symbolic_value * rty
[@@deriving show]

type region = RegionVarId.id Types.region [@@deriving show]

(** Ancestor for iter visitor for [typed_avalue] *)
class ['self] iter_typed_avalue_base =
  object (self : 'self)
    inherit [_] iter_typed_value

    method visit_region : 'env -> region -> unit = fun _ _ -> ()

    method visit_aproj : 'env -> aproj -> unit = fun _ _ -> ()

    method visit_abstract_shared_borrows
        : 'env -> abstract_shared_borrows -> unit =
      fun _ _ -> ()

    method visit_rty : 'env -> rty -> unit = fun _ _ -> ()
  end

(** Ancestor for MAP visitor for [typed_avalue] *)
class ['self] map_typed_avalue_base =
  object (self : 'self)
    inherit [_] map_typed_value

    method visit_region : 'env -> region -> region = fun _ r -> r

    method visit_aproj : 'env -> aproj -> aproj = fun _ p -> p

    method visit_abstract_shared_borrows
        : 'env -> abstract_shared_borrows -> abstract_shared_borrows =
      fun _ asb -> asb

    method visit_rty : 'env -> rty -> rty = fun _ ty -> ty
  end

(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)
type avalue =
  | AConcrete of constant_value
  | AAdt of adt_avalue
  | ABottom
  | ALoan of aloan_content
  | ABorrow of aborrow_content
  | ASymbolic of aproj

and adt_avalue = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_avalue list;
}

(** A loan content as stored in an abstraction.

    Note that the children avalues are independent of the parent avalues.
    For instance, the child avalue contained in an [AMutLoan] will likely
    contain other, independent loans. We keep track of the hierarchy because
    we need it to properly instantiate the backward functions when generating
    the pure translation.
*)
and aloan_content =
  | AMutLoan of (BorrowId.id[@opaque]) * typed_avalue
  | ASharedLoan of (BorrowId.set_t[@opaque]) * typed_value * typed_avalue
  | AEndedMutLoan of { given_back : typed_value; child : typed_avalue }
  | AEndedSharedLoan of typed_value * typed_avalue
  | AIgnoredMutLoan of (BorrowId.id[@opaque]) * typed_avalue
  | AEndedIgnoredMutLoan of { given_back : typed_avalue; child : typed_avalue }
  | AIgnoredSharedLoan of abstract_shared_borrows

(** Note that when a borrow content is ended, it is replaced by Bottom (while
    we need to track ended loans more precisely, especially because of their
    children values).

    Note that contrary to [aloan_content], here the children avalues are
    note independent of the parent avalues. For instance, a value
    `AMutBorrow (_, AMutBorrow (_, ...)` (ignoring the types) really is
    to be seen like a `mut_borrow ... (mut_borrow ...)`.
    
    TODO: be more precise about the ignored borrows (keep track of the borrow
    ids)
*)
and aborrow_content =
  | AMutBorrow of (BorrowId.id[@opaque]) * typed_avalue
  | ASharedBorrow of (BorrowId.id[@opaque])
  | AIgnoredMutBorrow of typed_avalue
  | AIgnoredSharedBorrow of abstract_shared_borrows

(* TODO: we may want to merge this with typed_value - would prevent some issues
   when accessing fields... *)
and typed_avalue = { value : avalue; ty : rty }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_avalue";
        variety = "iter";
        ancestors = [ "iter_typed_avalue_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_typed_avalue";
        variety = "map";
        ancestors = [ "map_typed_avalue_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]

type abs = {
  abs_id : (AbstractionId.id[@opaque]);
  parents : (AbstractionId.set_t[@opaque]);  (** The parent abstractions *)
  acc_regions : (RegionId.set_t[@opaque]);
      (** Union of the regions owned by the (transitive) parent abstractions and
          by the current abstraction *)
  regions : (RegionId.set_t[@opaque]);  (** Regions owned by this abstraction *)
  avalues : typed_avalue list;  (** The values in this abstraction *)
}
[@@deriving
  show,
    visitors
      {
        name = "iter_abs";
        variety = "iter";
        ancestors = [ "iter_typed_avalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_abs";
        variety = "map";
        ancestors = [ "map_typed_avalue" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]
(** Abstractions model the parts in the borrow graph where the borrowing relations
    have been abstracted because of a function call.
    
    In order to model the relations between the borrows, we use "abstraction values",
    which are a special kind of value.
*)
