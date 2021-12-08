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

type avalue =
  | AConcrete of constant_value
  | AAdt of aadt_value
  | ABottom
  | ALoan of aloan_content
  | ABorrow of aborrow_content
  | ASymbolic of aproj
      (** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)

(* TODO: rename to adt_avalue? *)
and aadt_value = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_avalue list;
}

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
    children values) *)
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

(*
(** Polymorphic version of the map visitor for [g_typed_value].

    The polymorphic visitor generated by the visitors macro caused some
    trouble, especially because the map functions allowed to change the
    type parameters (for instance the typed of `visit_'ty` was:
    `'env 'r_0 'r_1. 'env -> 'r_0 ty -> 'r_1 ty`, which prevented from
    initializing it as `fun ty -> ty`).

    TODO: this is now useless...
*)
class virtual ['self] map_g_typed_value =
  object (self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_Concrete
        : 'env 'r 'sv 'bc 'lc.
          'env -> constant_value -> ('r, 'sv, 'bc, 'lc) g_value =
      fun _env cv -> Concrete cv

    method visit_Bottom
        : 'env 'r 'sv 'bc 'lc. 'env -> ('r, 'sv, 'bc, 'lc) g_value =
      fun _env -> Bottom

    method visit_Borrow
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'bc -> 'bc) -> 'env -> 'bc -> ('r, 'sv, 'bc, 'lc) g_value =
      fun visit_'bc env bc -> Borrow (visit_'bc env bc)

    method visit_Loan
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'lc -> 'lc) -> 'env -> 'lc -> ('r, 'sv, 'bc, 'lc) g_value =
      fun visit_'lc env lc -> Loan (visit_'lc env lc)

    method visit_Symbolic
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'sv -> 'sv) -> 'env -> 'sv -> ('r, 'sv, 'bc, 'lc) g_value =
      fun visit_'sv env sv -> Symbolic (visit_'sv env sv)

    method visit_g_value
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'sv -> 'sv) ->
          ('env -> 'bc -> 'bc) ->
          ('env -> 'lc -> 'lc) ->
          'env ->
          ('r, 'sv, 'bc, 'lc) g_value ->
          ('r, 'sv, 'bc, 'lc) g_value =
      fun visit_'sv visit_'bc visit_'lc env v ->
        match v with
        | Concrete cv -> self#visit_Concrete env cv
        | Adt av ->
            Adt (self#visit_g_adt_value visit_'sv visit_'bc visit_'lc env av)
        | Bottom -> self#visit_Bottom env
        | Borrow bc -> self#visit_Borrow visit_'bc env bc
        | Loan lc -> self#visit_Loan visit_'lc env lc
        | Symbolic sv -> self#visit_Symbolic visit_'sv env sv

    method visit_g_adt_value
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'sv -> 'sv) ->
          ('env -> 'bc -> 'bc) ->
          ('env -> 'lc -> 'lc) ->
          'env ->
          ('r, 'sv, 'bc, 'lc) g_adt_value ->
          ('r, 'sv, 'bc, 'lc) g_adt_value =
      fun visit_'sv visit_'bc visit_'lc env av ->
        let variant_id = av.variant_id in
        let field_values =
          self#visit_list
            (self#visit_g_typed_value visit_'sv visit_'bc visit_'lc)
            env av.field_values
        in
        { variant_id; field_values }

    method visit_g_typed_value
        : 'env 'r 'sv 'bc 'lc.
          ('env -> 'sv -> 'sv) ->
          ('env -> 'bc -> 'bc) ->
          ('env -> 'lc -> 'lc) ->
          'env ->
          ('r, 'sv, 'bc, 'lc) g_typed_value ->
          ('r, 'sv, 'bc, 'lc) g_typed_value =
      fun visit_'sv visit_'bc visit_'lc env v ->
        let value =
          self#visit_g_value visit_'sv visit_'bc visit_'lc env v.value
        in
        let ty = self#visit_ty env v.ty in
        { value; ty }

    method visit_ty : 'env 'r. 'env -> 'r ty -> 'r ty = fun _env ty -> ty
  end

(** Map iterator for typed values.

    Unfortunately, we can't rely on [map_g_typed_value]: polymorphic visitors
    don't work in our case, because we sometimes have to reimplement methods
    like `visit_Loan`. For instance, when implementing `update_borrow`, we
    can't simply reimplement `visit_Borrow` because we need a method which
    returns a value or a typed value.
 *)
class ['self] map_typed_value =
  object (self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_Concrete : 'env -> constant_value -> value =
      fun _env cv -> Concrete cv

    method visit_Bottom : 'env -> value = fun _env -> Bottom

    method visit_Borrow : 'env -> borrow_content -> value =
      fun env bc -> Borrow (self#visit_borrow_content env bc)

    method visit_Loan : 'env -> loan_content -> value =
      fun env lc -> Loan (self#visit_loan_content env lc)

    method visit_Symbolic : 'env -> symbolic_proj_comp -> value =
      fun env sv -> Symbolic (self#visit_symbolic_proj_comp env sv)

    method visit_value : 'env -> value -> value =
      fun env v ->
        match v with
        | Concrete cv -> self#visit_Concrete env cv
        | Adt av -> Adt (self#visit_adt_value env av)
        | Bottom -> self#visit_Bottom env
        | Borrow bc -> self#visit_Borrow env bc
        | Loan lc -> self#visit_Loan env lc
        | Symbolic sv -> self#visit_Symbolic env sv

    method visit_adt_value : 'env -> adt_value -> adt_value =
      fun env av ->
        let variant_id = av.variant_id in
        let field_values =
          self#visit_list self#visit_typed_value env av.field_values
        in
        { variant_id; field_values }

    method visit_typed_value : 'env -> typed_value -> typed_value =
      fun env v ->
        let value = self#visit_value env v.value in
        let ty = self#visit_ety env v.ty in
        { value; ty }

    method visit_ety : 'env -> ety -> ety = fun _env ty -> ty

    method visit_symbolic_proj_comp
        : 'env -> symbolic_proj_comp -> symbolic_proj_comp =
      fun _env sv -> sv

    method visit_borrow_content : 'env -> borrow_content -> borrow_content =
      fun env bc ->
        match bc with
        | SharedBorrow bid -> self#visit_SharedBorrow env bid
        | MutBorrow (bid, v) -> self#visit_MutBorrow env bid v
        | InactivatedMutBorrow bid -> self#visit_InactivatedMutBorrow env bid

    method visit_SharedBorrow : 'env -> BorrowId.id -> borrow_content =
      fun _env bid -> SharedBorrow bid

    method visit_MutBorrow
        : 'env -> BorrowId.id -> typed_value -> borrow_content =
      fun env bid v ->
        let v = self#visit_typed_value env v in
        MutBorrow (bid, v)

    method visit_InactivatedMutBorrow : 'env -> BorrowId.id -> borrow_content =
      fun _env bid -> InactivatedMutBorrow bid

    method visit_loan_content : 'env -> loan_content -> loan_content =
      fun env lc ->
        match lc with
        | SharedLoan (bids, v) -> self#visit_SharedLoan env bids v
        | MutLoan bid -> self#visit_MutLoan env bid

    method visit_SharedLoan
        : 'env -> BorrowId.set_t -> typed_value -> loan_content =
      fun env bids v ->
        let v = self#visit_typed_value env v in
        SharedLoan (bids, v)

    method visit_MutLoan : 'env -> BorrowId.id -> loan_content =
      fun _env bid -> MutLoan bid
  end

class ['self] map_typed_avalue =
  object (self : 'self)
    inherit [_] map_typed_value

    method visit_a_Concrete : 'env -> constant_value -> avalue =
      fun _env cv -> Concrete cv

    method visit_a_Bottom : 'env -> avalue = fun _env -> Bottom

    method visit_a_Borrow : 'env -> aborrow_content -> avalue =
      fun env bc -> Borrow (self#visit_aborrow_content env bc)

    method visit_a_Loan : 'env -> aloan_content -> avalue =
      fun env lc -> Loan (self#visit_aloan_content env lc)

    method visit_a_Symbolic : 'env -> aproj -> avalue =
      fun env sv -> Symbolic (self#visit_aproj env sv)

    method visit_avalue : 'env -> avalue -> avalue =
      fun env v ->
        match v with
        | Concrete cv -> self#visit_a_Concrete env cv
        | Adt av -> Adt (self#visit_aadt_value env av)
        | Bottom -> self#visit_a_Bottom env
        | Borrow bc -> self#visit_a_Borrow env bc
        | Loan lc -> self#visit_a_Loan env lc
        | Symbolic sv -> self#visit_a_Symbolic env sv

    method visit_aadt_value : 'env -> aadt_value -> aadt_value =
      fun env av ->
        let variant_id = av.variant_id in
        let field_values =
          self#visit_list self#visit_typed_avalue env av.field_values
        in
        { variant_id; field_values }

    method visit_typed_avalue : 'env -> typed_avalue -> typed_avalue =
      fun env v ->
        let value = self#visit_avalue env v.value in
        let ty = self#visit_rty env v.ty in
        { value; ty }

    method visit_rty : 'env -> rty -> rty = fun _env ty -> ty

    method visit_aproj : 'env -> aproj -> aproj = fun _env sv -> sv

    method visit_aborrow_content : 'env -> aborrow_content -> aborrow_content =
      fun env bc ->
        match bc with
        | AMutBorrow (bid, v) -> self#visit_AMutBorrow env bid v
        | ASharedBorrow bid -> self#visit_ASharedBorrow env bid
        | AIgnoredMutBorrow v -> self#visit_AIgnoredMutBorrow env v
        | AIgnoredSharedBorrow asb -> self#visit_AIgnoredSharedBorrow env asb

    method visit_AMutBorrow
        : 'env -> BorrowId.id -> typed_avalue -> aborrow_content =
      fun env bid av ->
        let av = self#visit_typed_avalue env av in
        AMutBorrow (bid, av)

    method visit_ASharedBorrow : 'env -> BorrowId.id -> aborrow_content =
      fun _env bid -> ASharedBorrow bid

    method visit_AIgnoredMutBorrow : 'env -> typed_avalue -> aborrow_content =
      fun env av ->
        let av = self#visit_typed_avalue env av in
        AIgnoredMutBorrow av

    method visit_AIgnoredSharedBorrow
        : 'env -> abstract_shared_borrows -> aborrow_content =
      fun _env asb -> AIgnoredSharedBorrow asb

    method visit_aloan_content : 'env -> aloan_content -> aloan_content =
      fun env lc ->
        match lc with
        | AMutLoan (bid, av) -> self#visit_AMutLoan env bid av
        | ASharedLoan (bids, v, av) -> self#visit_ASharedLoan env bids v av
        | AEndedMutLoan { given_back; child } ->
            self#visit_AEndedMutLoan env given_back child
        | AEndedSharedLoan (v, av) -> self#visit_AEndedSharedLoan env v av
        | AIgnoredMutLoan (bids, v) -> self#visit_AIgnoredMutLoan env bids v
        | AEndedIgnoredMutLoan { given_back; child } ->
            self#visit_AEndedIgnoredMutLoan env given_back child
        | AIgnoredSharedLoan asb -> self#visit_AIgnoredSharedLoan env asb

    method visit_AMutLoan : 'env -> BorrowId.id -> typed_avalue -> aloan_content
        =
      fun env bid av ->
        let av = self#visit_typed_avalue env av in
        AMutLoan (bid, av)

    method visit_ASharedLoan
        : 'env -> BorrowId.set_t -> typed_value -> typed_avalue -> aloan_content
        =
      fun env bids v av ->
        let v = self#visit_typed_value env v in
        let av = self#visit_typed_avalue env av in
        ASharedLoan (bids, v, av)

    method visit_AEndedMutLoan
        : 'env -> typed_value -> typed_avalue -> aloan_content =
      fun env given_back child ->
        let given_back = self#visit_typed_value env given_back in
        let child = self#visit_typed_avalue env child in
        AEndedMutLoan { given_back; child }

    method visit_AEndedSharedLoan
        : 'env -> typed_value -> typed_avalue -> aloan_content =
      fun env v av ->
        let v = self#visit_typed_value env v in
        let av = self#visit_typed_avalue env av in
        AEndedSharedLoan (v, av)

    method visit_AIgnoredMutLoan
        : 'env -> BorrowId.id -> typed_avalue -> aloan_content =
      fun env id av ->
        let av = self#visit_typed_avalue env av in
        AIgnoredMutLoan (id, av)

    method visit_AEndedIgnoredMutLoan
        : 'env -> typed_avalue -> typed_avalue -> aloan_content =
      fun env given_back child ->
        let given_back = self#visit_typed_avalue env given_back in
        let child = self#visit_typed_avalue env child in
        AEndedIgnoredMutLoan { given_back; child }

    method visit_AIgnoredSharedLoan
        : 'env -> abstract_shared_borrows -> aloan_content =
      fun _env asb -> AIgnoredSharedLoan asb
  end
 *)
