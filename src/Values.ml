open Identifiers
open Types

(* TODO: I often write "abstract" (value, borrow content, etc.) while I should
 * write "abstraction" (because those values are not abstract, they simply are
 * inside abstractions) *)

module VarId = IdGen ()

module BorrowId = IdGen ()

module SymbolicValueId = IdGen ()

module AbstractionId = IdGen ()

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
(** A symbolic value *)

(** Ancestor for [typed_value] iter visitor *)
class ['self] iter_typed_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter

    method visit_constant_value : 'env -> constant_value -> unit = fun _ _ -> ()

    method visit_erased_region : 'env -> erased_region -> unit = fun _ _ -> ()

    method visit_symbolic_value : 'env -> symbolic_value -> unit = fun _ _ -> ()

    method visit_ety : 'env -> ety -> unit = fun _ _ -> ()
  end

(** Ancestor for [typed_value] map visitor for *)
class ['self] map_typed_value_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_constant_value : 'env -> constant_value -> constant_value =
      fun _ cv -> cv

    method visit_erased_region : 'env -> erased_region -> erased_region =
      fun _ r -> r

    method visit_symbolic_value : 'env -> symbolic_value -> symbolic_value =
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
  | Symbolic of symbolic_value
      (** Borrow projector over a symbolic value.
      
          Note that contrary to the abstraction-values case, symbolic values
          appearing in regular values are interpreted as *borrow* projectors,
          they can never be *loan* projectors.
       *)

and adt_value = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_value list;
}

and borrow_content =
  | SharedBorrow of (BorrowId.id[@opaque])  (** A shared value *)
  | MutBorrow of (BorrowId.id[@opaque]) * typed_value
      (** A mutably borrowed value. *)
  | InactivatedMutBorrow of (BorrowId.id[@opaque])
      (** An inactivated mut borrow.

          This is used to model [two-phase borrows](https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html).
          When evaluating a two-phase mutable borrow, we first introduce an inactivated
          borrow which behaves like a shared borrow, until the moment we actually *use*
          the borrow: at this point, we end all the other shared borrows (or inactivated
          borrows - though there shouldn't be any other inactivated borrows if the program
          is well typed) of this value and replace the inactivated borrow with a
          mutable borrow.
          
          A simple use case of two-phase borrows:
          ```
          let mut v = Vec::new();
          v.push(v.len());
          ```
          
          This gets desugared to (something similar to) the following MIR:
          ```
          v = Vec::new();
          v1 = &mut v;
          v2 = &v; // We need this borrow, but v has already been mutably borrowed!
          l = Vec::len(move v2);
          Vec::push(move v1, move l); // In practice, v1 gets activated only here
          ```
       *)

and loan_content =
  | SharedLoan of (BorrowId.Set.t[@opaque]) * typed_value
  | MutLoan of (BorrowId.id[@opaque])
      (** TODO: we might want to add a set of borrow ids (useful for inactivated
          borrows, and extremely useful when giving shared values to abstractions).
       *)

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

(** When giving shared borrows to functions (i.e., inserting shared borrows inside
    abstractions) we need to reborrow the shared values. When doing so, we lookup
    the shared values and apply some special projections to the shared value
    (until we can't go further, i.e., we find symbolic values which may get
    expanded upon reading them later), which don't generate avalues but
    sets of borrow ids and symbolic values.
    
    Note that as shared values can't get modified it is ok to forget the
    structure of the values we projected, and only keep the set of borrows
    (and symbolic values).
    
    TODO: we may actually need to remember the structure, in order to know
    which borrows are inside which other borrows...
*)
type abstract_shared_borrow =
  | AsbBorrow of (BorrowId.id[@opaque])
  | AsbProjReborrows of (symbolic_value[@opaque]) * (rty[@opaque])
[@@deriving show]

type abstract_shared_borrows = abstract_shared_borrow list [@@deriving show]
(** A set of abstract shared borrows *)

(** Ancestor for [aproj] iter visitor *)
class ['self] iter_aproj_base =
  object (_self : 'self)
    inherit [_] iter_typed_value

    method visit_rty : 'env -> rty -> unit = fun _ _ -> ()
  end

(** Ancestor for [aproj] map visitor *)
class ['self] map_aproj_base =
  object (_self : 'self)
    inherit [_] map_typed_value

    method visit_rty : 'env -> rty -> rty = fun _ ty -> ty
  end

type aproj =
  | AProjLoans of symbolic_value
  | AProjBorrows of symbolic_value * rty
      (** Note that an AProjBorrows only operates on a value which is not below
          a shared loan: under a shared loan, we use [abstract_shared_borrow]. *)
  | AEndedProjLoans of aproj option
      (** When ending a proj_loans over a symbolic value, we may need to insert
          (and keep track of) a proj_borrows over the given back value, if the
          symbolic value was consumed by an abstraction then updated.
       *)
  | AEndedProjBorrows
  (* TODO: remove AEndedProjBorrows? We might need it for synthesis, to contain
   * meta values *)
  | AIgnoredProjBorrows
[@@deriving
  show,
    visitors
      {
        name = "iter_aproj";
        variety = "iter";
        ancestors = [ "iter_aproj_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_aproj";
        variety = "map";
        ancestors = [ "map_aproj_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]

type region = RegionVarId.id Types.region [@@deriving show]

(** Ancestor for [typed_avalue] iter visitor *)
class ['self] iter_typed_avalue_base =
  object (_self : 'self)
    inherit [_] iter_aproj

    method visit_id : 'env -> BorrowId.id -> unit = fun _ _ -> ()

    method visit_region : 'env -> region -> unit = fun _ _ -> ()

    method visit_abstract_shared_borrows
        : 'env -> abstract_shared_borrows -> unit =
      fun _ _ -> ()
  end

(** Ancestor for [typed_avalue] map visitor *)
class ['self] map_typed_avalue_base =
  object (_self : 'self)
    inherit [_] map_aproj

    method visit_id : 'env -> BorrowId.id -> BorrowId.id = fun _ id -> id

    method visit_region : 'env -> region -> region = fun _ r -> r

    method visit_abstract_shared_borrows
        : 'env -> abstract_shared_borrows -> abstract_shared_borrows =
      fun _ asb -> asb
  end

(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph:
    part of it is thus "abstracted" away.
*)
type avalue =
  | AConcrete of constant_value
      (** TODO: remove
          Note that this case is not used in the projections to keep track of the
          borrow graph (because there are no borrows in "concrete" values!) but
          to correctly instantiate the backward functions (we may give back some
          values at different moments: we need to remember what those values were
          precisely). Also note that even though avalues and values are not the
          same, once values are projected to avalues, those avalues still have
          the structure of the original values (this is necessary, again, to
          correctly instantiate the backward functions)
       *)
  | AAdt of adt_avalue
  | ABottom
  | ALoan of aloan_content
  | ABorrow of aborrow_content
  | ASymbolic of aproj
  | AIgnored
      (** A value which doesn't contain borrows, or which borrows we
          don't own and thus ignore *)

and adt_avalue = {
  variant_id : (VariantId.id option[@opaque]);
  field_values : typed_avalue list;
}

(** A loan content as stored in an abstraction.

    Note that the children avalues are independent of the parent avalues.
    For instance, the child avalue contained in an [AMutLoan] will likely
    contain other, independent loans.
    Keeping track of the hierarchy is not necessary to maintain the borrow graph
    (which is the primary role of the abstractions), but it is necessary
    to properly instantiate the backward functions when generating the pure
    translation.
*)
and aloan_content =
  | AMutLoan of (BorrowId.id[@opaque]) * typed_avalue
      (** A mutable loan owned by an abstraction.
         
          Example:
          ========
          ```
          fn f<'a>(...) -> &'a mut &'a mut u32;
          
          let px = f(...);
          ```
          
          We get (after some symbolic exansion):
          ```
          abs0 {
            a_mut_loan l0 (a_mut_loan l1)
          }
          px -> mut_borrow l0 (mut_borrow @s1)
          ```
       *)
  | ASharedLoan of (BorrowId.Set.t[@opaque]) * typed_value * typed_avalue
      (** A shared loan owned by an abstraction.

          Example:
          ========
          ```
          fn f<'a>(...) -> &'a u32;
          
          let px = f(...);
          ```
          
          We get:
          ```
          abs0 { a_shared_loan {l0} @s0 ⊥ }
          px -> shared_loan l0
          ```
     *)
  | AEndedMutLoan of { child : typed_avalue; given_back : typed_avalue }
      (** An ended mutable loan in an abstraction.
          We need it because abstractions must keep track of the values
          we gave back to them, so that we can correctly instantiate
          backward functions.
      
          Example:
          ========
          ```
          abs0 { a_mut_loan l0 ⊥ }
          x -> mut_borrow l0 (U32 3)
          ```
          
          After ending `l0`:
          
          ```
          abs0 { a_ended_mut_loan { given_back = U32 3; child = ⊥; }
          x -> ⊥
          ```
      
          TODO: in the formalization, given_back was initially a typed value
          (not an avalue). It seems more consistent to use a value, especially
          because then the invariants about the borrows are simpler (otherwise,
          there may be borrow ids duplicated in the context, which is very
          annoying).
          I think the original idea was that using values would make it
          simple to instantiate the backward function (because projecting
          deconstructs a bit the values with which we feed the function).
       *)
  | AEndedSharedLoan of typed_value * typed_avalue
      (** Similar to [AEndedMutLoan] but in this case there are no avalues to
          give back. Actually, we could probably forget the shared value
          altogether (and just keep the child avalue).
       *)
  | AIgnoredMutLoan of (BorrowId.id[@opaque]) * typed_avalue
      (** An ignored mutable loan.
      
          We need to keep track of ignored mutable loans, because we may have
          to apply projections on the values given back to those loans (say
          you have a borrow of type `&'a mut &'b mut`, in the abstraction 'b,
          the outer loan is ignored, however you need to keep track of it so
          that when ending the borrow corresponding to 'a you can correctly
          project on the inner value).
       
          Example:
          ========
          ```
          fn f<'a,'b>(...) -> &'a mut &'b mut u32;
          let x = f(...);
          
          > abs'a { a_mut_loan l0 (a_ignored_mut_loan l1 ⊥) }
          > abs'b { a_ignored_mut_loan l0 (a_mut_loan l1 ⊥) }
          > x -> mut_borrow l0 (mut_borrow l1 @s1)
          ```
       *)
  | AEndedIgnoredMutLoan of { child : typed_avalue; given_back : typed_avalue }
      (** Similar to [AEndedMutLoan], for ignored loans *)
  | AIgnoredSharedLoan of typed_avalue
      (** An ignored shared loan.
      
          Example:
          ========
          ```
          fn f<'a,'b>(...) -> &'a &'b u32;
          let x = f(...);
          
          > abs'a { a_shared_loan {l0} (shared_borrow l1) (a_ignored_shared_loan ⊥) }
          > abs'b { a_ignored_shared_loan (a_shared_loan {l1} @s1 ⊥) }
          > x -> shared_borrow l0
          ```
       *)

(** Note that when a borrow content is ended, it is replaced by ⊥ (while
    we need to track ended loans more precisely, especially because of their
    children values).

    Note that contrary to [aloan_content], here the children avalues are
    note independent of the parent avalues. For instance, a value
    `AMutBorrow (_, AMutBorrow (_, ...)` (ignoring the types) really is
    to be seen like a `mut_borrow ... (mut_borrow ...)`.
    
    TODO: be more precise about the ignored borrows (keep track of the borrow
    ids)?
*)
and aborrow_content =
  | AMutBorrow of (BorrowId.id[@opaque]) * typed_avalue
      (** A mutable borrow owned by an abstraction.
      
          Is used when an abstraction "consumes" borrows, when giving borrows
          as arguments to a function.

          Example:
          ========
          ```
          fn f<'a>(px : &'a mut u32);
          
          > x -> mut_loan l0
          > px -> mut_borrow l0 (U32 0)
          
          f(move px);
          
          > x -> mut_loan l0
          > px -> ⊥
          > abs0 { a_mut_borrow l0 (U32 0) }
          ```
     *)
  | ASharedBorrow of (BorrowId.id[@opaque])
      (** A shared borrow owned by an abstraction.
    
          Example:
          ========
          ```
          fn f<'a>(px : &'a u32);
          
          > x -> shared_loan {l0} (U32 0)
          > px -> shared_borrow l0
          
          f(move px);
          
          > x -> shared_loan {l0} (U32 0)
          > px -> ⊥
          > abs0 { a_shared_borrow l0 }
          ```
     *)
  | AIgnoredMutBorrow of BorrowId.id option * typed_avalue
      (** An ignored mutable borrow.
      
          We need to keep track of ignored mut borrows because when ending such
          borrows, we need to project the loans of the given back value to
          insert them in the proper abstractions.
          
          Note that we need to do so only for borrows consumed by parent
          abstractions (hence the optional borrow id).

          Example:
          ========
          ```
          fn f<'a,'b>(ppx : &'a mut &'b mut u32);
          
          > x -> mut_loan l0
          > px -> mut_loan l1
          > ppx -> mut_borrow l1 (mut_borrow l0 (U32 0))

          f(move ppx);

          > x -> mut_loan l0
          > px -> mut_loan l1
          > ppx -> ⊥
          > abs'a { a_mut_borrow l1 (a_ignored_mut_borrow None (U32 0)) } // TODO: duplication
          > abs'b {parents={abs'a}} { a_ignored_mut_borrow (Some l1) (a_mut_borrow l0 (U32 0)) }
          
          ... // abs'a ends
          
          > x -> mut_loan l0
          > px -> @s0
          > ppx -> ⊥
          > abs'b {
          >   a_ended_ignored_mut_borrow (a_proj_loans (@s0 <: &'b mut u32)) // <-- loan projector
          >                              (a_mut_borrow l0 (U32 0))
          > }
          
          ... // `@s0` gets expanded to `&mut l2 @s1`

          > x -> mut_loan l0
          > px -> &mut l2 @s1
          > ppx -> ⊥
          > abs'b {
          >   a_ended_ignored_mut_borrow (a_mut_loan l2) // <-- loan l2 is here
          >                              (a_mut_borrow l0 (U32 0))
          > }
          
          ```

          Note that we could use AIgnoredMutLoan in the case the borrow id is not
          None, which would allow us to simplify the rules (to not have rules
          to specifically handle the case of AIgnoredMutBorrow with Some borrow
          id) and also remove the AEndedIgnoredMutBorrow variant.
          For now, the rules are implemented and it allows us to make the avalues
          more precise and clearer, so we will keep it that way.
   
          TODO: this is annoying, we are duplicating information. Maybe we
          could introduce an "Ignored" value? We have to pay attention to
          two things:
          - introducing ⊥ when ignoring a value is not always possible, because
            we check whether the borrowed value contains ⊥ when giving back a
            borrowed value (if it is the case we give back ⊥, otherwise we
            introduce a symbolic value). This is necessary when ending nested
            borrows with the same lifetime: when ending the inner borrow we
            actually give back a value, however when ending the outer borrow
            we need to give back ⊥.
            TODO: actually we don't do that anymore, we check if the borrowed
            avalue contains ended regions (which is cleaner and more robust).
          - we may need to remember the precise values given to the
            abstraction so that we can properly call the backward functions
            when generating the pure translation.
       *)
  | AEndedIgnoredMutBorrow of {
      child : typed_avalue;
      given_back_loans_proj : typed_avalue;
    }  (** See the explanations for [AIgnoredMutBorrow] *)
  | AProjSharedBorrow of abstract_shared_borrows
      (** A projected shared borrow.

          When giving shared borrows as arguments to function calls, we
          introduce new borrows to keep track of the fact that the function
          might reborrow values inside. Note that as shared values are immutable,
          we don't really need to remember the structure of the shared values.

          Example:
          ========
          Below, when calling `f`, we need to introduce one shared borrow per
          borrow in the argument.
          ```
          fn f<'a,'b>(pppx : &'a &'b &'c mut u32);

          > x    -> mut_loan l0
          > px   -> shared_loan {l1} (mut_borrow l0 (U32 0))
          > ppx  -> shared_loan {l2} (shared_borrow l1)
          > pppx -> shared_borrow l2

          f(move pppx);

          > x    -> mut_loan l0
          > px   -> shared_loan {l1, l3, l4} (mut_borrow l0 (U32 0))
          > ppx  -> shared_loan {l2} (shared_borrow l1)
          > pppx -> ⊥
          > abs'a { a_proj_shared_borrow {l2} }
          > abs'b { a_proj_shared_borrow {l3} } // l3 reborrows l1
          > abs'c { a_proj_shared_borrow {l4} } // l4 reborrows l0
          ```
       *)

(* TODO: we may want to merge this with typed_value - would prevent some issues
   when accessing fields....

   TODO: the type of avalues doesn't make sense for loan avalues: they currently
   are typed as `& (mut) T` instead of `T`...
*)
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
  parents : (AbstractionId.Set.t[@opaque]);  (** The parent abstractions *)
  regions : (RegionId.Set.t[@opaque]);  (** Regions owned by this abstraction *)
  ancestors_regions : (RegionId.Set.t[@opaque]);
      (** Union of the regions owned by this abstraction's ancestors (not
          including the regions of this abstraction itself) *)
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
