open Identifiers
open Types

(** TODO: do we put the type variable/variable/region names everywhere
    (to not have to perform lookups by using the ids?)
    No: it is good not to duplicate and to use ids. This allows to split/
    make very explicit the role of variables/identifiers/binders/etc.
 *)

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

(** Polymorphic visitor *)
class virtual ['self] iter_'r_ty_base =
  object (self : 'self)
    method visit_ty : 'env 'r. ('env -> 'r -> unit) -> 'env -> 'r ty -> unit =
      fun visit_'r env ty -> ()
  end

(** A generic, untyped value, used in the environments.

    Parameterized by:
    - 'ty: type
    - 'sv: symbolic value
    - 'bc: borrow content
    - 'lc: loan content

    Can be specialized for "regular" values or values in abstractions *)
type ('r, 'sv, 'bc, 'lc) g_value =
  | Concrete of (constant_value[@opaque])  (** Concrete (non-symbolic) value *)
  | Adt of ('r, 'sv, 'bc, 'lc) g_adt_value
      (** Enumerations, structures, tuples, assumed types. Note that units
          are encoded as 0-tuples  *)
  | Bottom  (** No value (uninitialized or moved value) *)
  | Borrow of 'bc  (** A borrowed value *)
  | Loan of 'lc  (** A loaned value *)
  | Symbolic of 'sv  (** Unknown value *)

and ('r, 'sv, 'bc, 'lc) g_adt_value = {
  variant_id : VariantId.id option; [@opaque]
  field_values : ('r, 'sv, 'bc, 'lc) g_typed_value list;
}

(** "Generic" ADT value (not "GADT" value) *)

and ('r, 'sv, 'bc, 'lc) g_typed_value = {
  value : ('r, 'sv, 'bc, 'lc) g_value;
  ty : 'r ty;
}
[@@deriving
  show,
    visitors
      {
        name = "iter_g_typed_value";
        variety = "iter";
        ancestors = [ "iter_'r_ty_base" ];
        polymorphic = true;
        concrete = true;
      }]

class virtual ['self] iter_typed_value_base =
  object (self : 'self)
    inherit [_] iter_g_typed_value

    method visit_erased_region : 'env. 'env -> erased_region -> unit =
      fun env _ -> ()

    method visit_symbolic_proj_comp : 'env. 'env -> symbolic_proj_comp -> unit =
      fun env _ -> ()
  end

type value =
  (erased_region, symbolic_proj_comp, borrow_content, loan_content) g_value
(** "Regular" value *)

and adt_value =
  (erased_region, symbolic_proj_comp, borrow_content, loan_content) g_adt_value

and typed_value =
  ( erased_region,
    symbolic_proj_comp,
    borrow_content,
    loan_content )
  g_typed_value
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_value";
        variety = "iter";
        ancestors = [ "iter_typed_value_base" ];
        polymorphic = true;
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
      }]
(** "Regular" typed value (we map variables to typed values) *)

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
[@@deriving show]

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

type avalue =
  (RegionVarId.id region, aproj, aborrow_content, aloan_content) g_value
(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)

and aadt_value =
  (RegionVarId.id region, aproj, aborrow_content, aloan_content) g_adt_value

and typed_avalue =
  (RegionVarId.id region, aproj, aborrow_content, aloan_content) g_typed_value
[@@deriving show]

and aloan_content =
  | AMutLoan of BorrowId.id * typed_avalue
  | ASharedLoan of BorrowId.set_t * typed_value * typed_avalue
  | AEndedMutLoan of { given_back : typed_value; child : typed_avalue }
  | AEndedSharedLoan of typed_value * typed_avalue
  | AIgnoredMutLoan of BorrowId.id * typed_avalue
  | AIgnoredSharedLoan of abstract_shared_borrows
[@@deriving show]

(** Note that when a borrow content is ended, it is replaced by Bottom (while
    we need to track ended loans more precisely, especially because of their
    children values) *)
and aborrow_content =
  | AMutBorrow of BorrowId.id * typed_avalue
  | ASharedBorrow of BorrowId.id
  | AIgnoredMutBorrow of typed_avalue
  | AEndedIgnoredMutLoan of { given_back : typed_avalue; child : typed_avalue }
  | AIgnoredSharedBorrow of abstract_shared_borrows
[@@deriving show]

type abs = {
  abs_id : AbstractionId.id;
  parents : AbstractionId.set_t;  (** The parent abstractions *)
  acc_regions : RegionId.set_t;
      (** Union of the regions owned by the (transitive) parent abstractions and
          by the current abstraction *)
  regions : RegionId.set_t;  (** Regions owned by this abstraction *)
  avalues : typed_avalue list;  (** The values in this abstraction *)
}
[@@deriving show]
(** Abstractions model the parts in the borrow graph where the borrowing relations
    have been abstracted because of a function call.
    
    In order to model the relations between the borrows, we use "abstraction values",
    which are a special kind of value.
*)
