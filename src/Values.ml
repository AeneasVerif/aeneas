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

(** Polymorphic iter visitor *)
class ['self] iter_'r_ty_base =
  object (self : 'self)
    method visit_ty : 'env 'r. ('env -> 'r -> unit) -> 'env -> 'r ty -> unit =
      fun _visit_'r _env _ty -> ()
  end

(*(** Polymorphic map visitor *)
  class ['self] map_'r_ty_base =
    object (self : 'self)
      method visit_ty
          : 'env 'r_0 'r_1. ('env -> 'r_0 -> 'r_1) -> 'env -> 'r_0 ty -> 'r_1 ty =
        fun _visit_'r _env ty ->
          (* We should use a ty visitor, but in practice we don't need to
           * visit types, and for the non-generic visit methods (which will
           * preserve 'r_0) we will override this method with identity *)
          raise Errors.Unimplemented
  end*)

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
        (* Heirs expect a polymorphic class *)
        concrete = true;
      }
  (* visitors
     {
       name = "map_g_typed_value";
       variety = "map";
       ancestors = [ "map_'r_ty_base" ];
       polymorphic = true;
       (* Heirs expect a polymorphic class *)
       concrete = true;
     }*)]

class ['self] iter_typed_value_base =
  object (self : 'self)
    inherit [_] iter_g_typed_value

    method visit_erased_region : 'env. 'env -> erased_region -> unit =
      fun _env _ -> ()

    method visit_symbolic_proj_comp : 'env. 'env -> symbolic_proj_comp -> unit =
      fun _env _ -> ()
  end

(*class ['self] map_typed_value_base =
    object (self : 'self)
      inherit [_] map_g_typed_value

      method visit_erased_region : 'env. 'env -> erased_region -> erased_region =
        fun _env r -> r

      method visit_symbolic_proj_comp
          : 'env. 'env -> symbolic_proj_comp -> symbolic_proj_comp =
        fun _env pc -> pc
  end*)

type value =
  (erased_region, symbolic_proj_comp, borrow_content, loan_content) g_value
(** "Regular" value *)

and adt_value =
  (erased_region, symbolic_proj_comp, borrow_content, loan_content) g_adt_value

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
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }
  (* visitors
     {
       name = "map_typed_value_incomplete";
       variety = "map";
       ancestors = [ "map_typed_value_base" ];
       nude = true (* Don't inherit [VisitorsRuntime.iter] *);
       concrete = true;
     }*)]
(** "Regular" typed value (we map variables to typed values) *)

(*(** Override some undefined functions *)
  class ['self] map_typed_value =
    object (self : 'self)
      inherit [_] map_typed_value_incomplete

      method! visit_typed_value (env : 'env) (tv : typed_value) : typed_value =
        let value = self#visit_value env tv.value in
        (* Ignore the type *)
        let ty = tv.ty in
        { value; ty }
  end*)

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

class ['self] iter_typed_avalue_base =
  object (self : 'self)
    inherit [_] iter_g_typed_value

    method visit_region : 'env. 'env -> region -> unit = fun _env _r -> ()

    method visit_aproj : 'env. 'env -> aproj -> unit = fun env _ -> ()

    method visit_typed_value : 'env. 'env -> typed_value -> unit =
      fun _env _v -> ()

    method visit_abstract_shared_borrows
        : 'env. 'env -> abstract_shared_borrows -> unit =
      fun _env _asb -> ()
  end

(*class ['self] map_typed_avalue_base =
    object (self : 'self)
      inherit [_] map_g_typed_value

      method visit_region : 'env. 'env -> region -> region = fun _env r -> r

      method visit_aproj : 'env. 'env -> aproj -> aproj = fun env p -> p

      method visit_typed_value : 'env. 'env -> typed_value -> typed_value =
        fun _env v -> v

      method visit_abstract_shared_borrows
          : 'env. 'env -> abstract_shared_borrows -> abstract_shared_borrows =
        fun _env asb -> asb
  end*)

type avalue = (region, aproj, aborrow_content, aloan_content) g_value
(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)

and aadt_value = (region, aproj, aborrow_content, aloan_content) g_adt_value

and aloan_content =
  | AMutLoan of (BorrowId.id[@opaque]) * typed_avalue
  | ASharedLoan of (BorrowId.set_t[@opaque]) * typed_value * typed_avalue
  | AEndedMutLoan of { given_back : typed_value; child : typed_avalue }
  | AEndedSharedLoan of typed_value * typed_avalue
  | AIgnoredMutLoan of (BorrowId.id[@opaque]) * typed_avalue
  | AIgnoredSharedLoan of abstract_shared_borrows

(** Note that when a borrow content is ended, it is replaced by Bottom (while
    we need to track ended loans more precisely, especially because of their
    children values) *)
and aborrow_content =
  | AMutBorrow of (BorrowId.id[@opaque]) * typed_avalue
  | ASharedBorrow of (BorrowId.id[@opaque])
  | AIgnoredMutBorrow of typed_avalue
  | AEndedIgnoredMutLoan of { given_back : typed_avalue; child : typed_avalue }
  | AIgnoredSharedBorrow of abstract_shared_borrows

and typed_avalue = (region, aproj, aborrow_content, aloan_content) g_typed_value
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_avalue";
        variety = "iter";
        ancestors = [ "iter_typed_avalue_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }
  (* visitors
     {
       name = "map_typed_avalue_incomplete";
       variety = "map";
       ancestors = [ "map_typed_avalue_base" ];
       nude = true (* Don't inherit [VisitorsRuntime.iter] *);
       concrete = true;
     }*)]

(*(** Override some undefined functions *)
  class ['self] map_typed_avalue =
    object (self : 'self)
      inherit [_] map_typed_avalue_incomplete

      method! visit_typed_avalue (env : 'env) (tv : typed_avalue) : typed_avalue =
        let value = self#visit_avalue env tv.value in
        (* Ignore the type *)
        let ty = tv.ty in
        { value; ty }
  end*)

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

(** Monomorphic version of the map visitor for [g_typed_value].

    The type variables are quantified at the level of the class (not at the
    level of each method). As a consequence, the visit methods don't need to
    take closures as parameters.

    The polymorphic visitor generated by the visitors macro caused some
    trouble: it was in some cases not possible to override a function
    to refine the behaviour of a visitor. With this version, it is
    possible. Note that this works only because the polymorphism of
    [g_value], [g_adt_value], etc. is "uniform": the type instantiation
    is always the same.

*)
class virtual ['self] map_g_typed_value =
  object (self : 'self)
    inherit [_] VisitorsRuntime.map

    method virtual visit_'sv : 'monomorphic. 'env -> 'sv -> 'sv

    method virtual visit_'bc : 'monomorphic. 'env -> 'bc -> 'bc

    method virtual visit_'lc : 'monomorphic. 'env -> 'lc -> 'lc

    method visit_Concrete
        : 'monomorphic. 'env -> constant_value -> ('r, 'sv, 'bc, 'lv) g_value =
      fun _env cv -> Concrete cv

    method visit_Adt
        : 'monomorphic.
          'env -> ('r, 'sv, 'bc, 'lc) g_adt_value -> ('r, 'sv, 'bc, 'lc) g_value
        =
      fun env av ->
        let av = self#visit_g_adt_value env av in
        Adt av

    method visit_Bottom : 'monomorphic. 'env -> ('r, 'sv, 'bc, 'lv) g_value =
      fun _env -> Bottom

    method visit_Borrow
        : 'monomorphic. 'env -> 'bc -> ('r, 'sv, 'bc, 'lv) g_value =
      fun env bc -> Borrow (self#visit_'bc env bc)

    method visit_Loan : 'monomorphic. 'env -> 'lc -> ('r, 'sv, 'bc, 'lv) g_value
        =
      fun env lc -> Loan (self#visit_'lc env lc)

    method visit_Symbolic
        : 'monomorphic. 'env -> 'sv -> ('r, 'sv, 'bc, 'lv) g_value =
      fun env sv -> Symbolic (self#visit_'sv env sv)

    method visit_g_value
        : 'monomorphic.
          'env -> ('r, 'sv, 'bc, 'lv) g_value -> ('r, 'sv, 'bc, 'lv) g_value =
      fun env v ->
        match v with
        | Concrete cv -> self#visit_Concrete env cv
        | Adt av -> Adt (self#visit_g_adt_value env av)
        | Bottom -> self#visit_Bottom env
        | Borrow bc -> self#visit_Borrow env bc
        | Loan lc -> self#visit_Loan env lc
        | Symbolic sv -> self#visit_Symbolic env sv

    method visit_g_adt_value
        : 'monomorphic.
          'env ->
          ('r, 'sv, 'bc, 'lv) g_adt_value ->
          ('r, 'sv, 'bc, 'lv) g_adt_value =
      fun env av ->
        let variant_id = av.variant_id in
        let field_values =
          self#visit_list self#visit_g_typed_value env av.field_values
        in
        { variant_id; field_values }

    method visit_g_typed_value
        : 'monomorphic.
          'env ->
          ('r, 'sv, 'bc, 'lv) g_typed_value ->
          ('r, 'sv, 'bc, 'lv) g_typed_value =
      fun env v ->
        let value = self#visit_g_value env v.value in
        let ty = self#visit_ty env v.ty in
        { value; ty }

    method visit_ty : 'monomorphic. 'env -> 'r ty -> 'r ty = fun _env ty -> ty
  end
