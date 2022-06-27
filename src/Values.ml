open Identifiers
open Types

(* TODO: I often write "abstract" (value, borrow content, etc.) while I should
 * write "abstraction" (because those values are not abstract, they simply are
 * inside abstractions) *)

module VarId = IdGen ()
module BorrowId = IdGen ()
module SymbolicValueId = IdGen ()
module AbstractionId = IdGen ()
module FunCallId = IdGen ()

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

(** The kind of a symbolic value, which precises how the value was generated *)
type sv_kind =
  | FunCallRet  (** The value is the return value of a function call *)
  | FunCallGivenBack
      (** The value is a borrowed value given back by an abstraction
          (happens when giving a borrow to a function: when the abstraction
          introduced to model the function call ends we reintroduce a symbolic
          value in the context for the value modified by the abstraction through
          the borrow).
       *)
  | SynthInput
      (** The value is an input value of the function whose body we are
          currently synthesizing.
       *)
  | SynthRetGivenBack
      (** The value is a borrowed value that the function whose body we are
          synthesizing returned, and which was given back because we ended
          one of the lifetimes of this function (we do this to synthesize
          the backward functions).
       *)
  | SynthInputGivenBack
      (** The value was given back upon ending one of the input abstractions *)
[@@deriving show]

type symbolic_value = {
  sv_kind : sv_kind;
  sv_id : SymbolicValueId.id;
  sv_ty : rty;
}
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
  | SharedBorrow of mvalue * (BorrowId.id[@opaque])
      (** A shared borrow.
      
          We remember the shared value which was borrowed as a meta value.
          This is necessary for synthesis: upon translating to "pure" values,
          we can't perform any lookup because we don't have an environment
          anymore. Note that it is ok to keep the shared value and copy
          the shared value this way, because shared values are immutable
          for as long as they are shared (i.e., as long as we can use the
          shared borrow).
       *)
  | MutBorrow of (BorrowId.id[@opaque]) * typed_value
      (** A mutably borrowed value. *)
  | InactivatedMutBorrow of mvalue * (BorrowId.id[@opaque])
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
          
          The meta-value is used for the same purposes as with shared borrows,
          at the exception that in case of inactivated borrows it is not
          *necessary* for the synthesis: we keep it only as meta-information.
          To be more precise:
          - when generating the synthesized program, we may need to convert
            shared borrows to pure values
          - we never need to do so for inactivated borrows: such borrows must
            be activated at the moment we use them (meaning we convert a *mutable*
            borrow to a pure value). However, we save meta-data about the assignments,
            which is used to make the code cleaner: when generating this meta-data,
            we may need to convert inactivated borrows to pure values, in which
            situation we convert the meta-value we stored in the inactivated
            borrow.
       *)

and loan_content =
  | SharedLoan of (BorrowId.Set.t[@opaque]) * typed_value
  | MutLoan of (BorrowId.id[@opaque])
      (** TODO: we might want to add a set of borrow ids (useful for inactivated
          borrows, and extremely useful when giving shared values to abstractions).
       *)

and mvalue = typed_value
(** "Meta"-value: information we store for the synthesis.

     Note that we never automatically visit the meta-values with the
     visitors: they really are meta information, and shouldn't be considered
     as part of the environment during a symbolic execution.
     
     TODO: we may want to create wrappers, to prevent accidently mixing meta
     values and regular values.
 *)

and typed_value = { value : value; ty : ety }
[@@deriving
  show,
    visitors
      {
        name = "iter_typed_value_visit_mvalue";
        variety = "iter";
        ancestors = [ "iter_typed_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_typed_value_visit_mvalue";
        variety = "map";
        ancestors = [ "map_typed_value_base" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]
(** "Regular" typed value (we map variables to typed values) *)

(** We have to override the [visit_mvalue] method, to ignore meta-values *)
class ['self] iter_typed_value =
  object (_self : 'self)
    inherit [_] iter_typed_value_visit_mvalue
    method! visit_mvalue : 'env -> mvalue -> unit = fun _ _ -> ()
  end

(** We have to override the [visit_mvalue] method, to ignore meta-values *)
class ['self] map_typed_value =
  object (_self : 'self)
    inherit [_] map_typed_value_visit_mvalue
    method! visit_mvalue : 'env -> mvalue -> mvalue = fun _ x -> x
  end

type msymbolic_value = symbolic_value [@@deriving show]
(** "Meta"-symbolic value.

     See the explanations for [mvalue]

     TODO: we may want to create wrappers, to prevent mixing meta values
     and regular values.
 *)

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

    method visit_msymbolic_value : 'env -> msymbolic_value -> unit =
      fun _ _ -> ()
  end

(** Ancestor for [aproj] map visitor *)
class ['self] map_aproj_base =
  object (_self : 'self)
    inherit [_] map_typed_value
    method visit_rty : 'env -> rty -> rty = fun _ ty -> ty

    method visit_msymbolic_value : 'env -> msymbolic_value -> msymbolic_value =
      fun _ m -> m
  end

type aproj =
  | AProjLoans of symbolic_value * (msymbolic_value * aproj) list
      (** A projector of loans over a symbolic value.
      
          Note that the borrows of a symbolic value may be spread between
          different abstractions, meaning that the projector of loans might
          receive *several* (symbolic) given back values.
          
          This is the case in the following example:
          ```
          fn f<'a> (...) -> (&'a mut u32, &'a mut u32);
          fn g<'b, 'c>(p : (&'b mut u32, &'c mut u32));
          
          let p = f(...);
          g(move p);
          
          // Symbolic context after the call to g:
          // abs'a {'a} { [s@0 <: (&'a mut u32, &'a mut u32)] }
          //
          // abs'b {'b} { (s@0 <: (&'b mut u32, &'c mut u32)) }
          // abs'c {'c} { (s@0 <: (&'b mut u32, &'c mut u32)) }
          ```
          
          Upon evaluating the call to `f`, we introduce a symbolic value `s@0`
          and a projector of loans (projector loans from the region 'c).
          This projector will later receive two given back values: one for
          'a and one for 'b.
          
          We accumulate those values in the list of projections (note that
          the meta value stores the value which was given back).
          
          We can later end the projector of loans if `s@0` is not referenced
          anywhere in the context below a projector of borrows which intersects
          this projector of loans.
       *)
  | AProjBorrows of symbolic_value * rty
      (** Note that an AProjBorrows only operates on a value which is not below
          a shared loan: under a shared loan, we use [abstract_shared_borrow].
          
          Also note that once given to a borrow projection, a symbolic value
          can't get updated/expanded: this means that we don't need to save
          any meta-value here.
       *)
  | AEndedProjLoans of msymbolic_value * (msymbolic_value * aproj) list
      (** An ended projector of loans over a symbolic value.
      
          See the explanations for [AProjLoans]
          
          Note that we keep the original symbolic value as a meta-value.
       *)
  | AEndedProjBorrows of msymbolic_value
      (** The only purpose of [AEndedProjBorrows] is to store, for synthesis
          purposes, the symbolic value which was generated and given back upon
          ending the borrow.
       *)
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
      (** TODO: remove. We actually don't use that for the synthesis, but the
          meta-values.
       
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
  | AEndedMutLoan of {
      child : typed_avalue;
      given_back : typed_avalue;
      given_back_meta : mvalue;
    }
      (** An ended mutable loan in an abstraction.
          We need it because abstractions must keep track of the values
          we gave back to them, so that we can correctly instantiate
          backward functions.
          
          Rk.: *DO NOT* use [visit_AEndedMutLoan]. If we update the order of
          the arguments and you forget to swap them at the level of
          [visit_AEndedMutLoan], you will not notice it.          
      
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
       *)
  | AEndedSharedLoan of typed_value * typed_avalue
      (** Similar to [AEndedMutLoan] but in this case there are no avalues to
          give back. We keep the shared value because it now behaves as a
          "regular" value (which contains borrows we might want to end...).
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
  | AEndedIgnoredMutLoan of {
      child : typed_avalue;
      given_back : typed_avalue;
      given_back_meta : mvalue;
    }
      (** Similar to [AEndedMutLoan], for ignored loans.

           Rk.: *DO NOT* use [visit_AEndedIgnoredMutLoan].
           See the comment for [AEndedMutLoan].
       *)
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
    not independent of the parent avalues. For instance, a value
    `AMutBorrow (_, AMutBorrow (_, ...)` (ignoring the types) really is
    to be seen like a `mut_borrow ... (mut_borrow ...)`.
    
    TODO: be more precise about the ignored borrows (keep track of the borrow
    ids)?
*)
and aborrow_content =
  | AMutBorrow of mvalue * (BorrowId.id[@opaque]) * typed_avalue
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
          
          The meta-value stores the initial value on which the projector was
          applied, which reduced to this mut borrow. This meta-information
          is only used for the synthesis.
          TODO: do we really use it actually?
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
          
          TODO: the below explanations are obsolete

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
  | AEndedMutBorrow of msymbolic_value * typed_avalue
      (** The sole purpose of [AEndedMutBorrow] is to store the (symbolic) value
          that we gave back as a meta-value, to help with the synthesis.

          We also remember the child [avalue] because this structural information
          is useful for the synthesis (but not for the symbolic execution):
          in practice the child value should only contain ended borrows, ignored
          values, bottom values, etc.
       *)
  | AEndedSharedBorrow
      (** We don't really need [AEndedSharedBorrow]: we simply want to be
          precise, and not insert ⊥ when ending borrows.
       *)
  | AEndedIgnoredMutBorrow of {
      child : typed_avalue;
      given_back_loans_proj : typed_avalue;
      given_back_meta : msymbolic_value;
          (** [given_back_meta] is used to store the (symbolic) value we gave back
              upon ending the borrow.

              Rk.: *DO NOT* use [visit_AEndedIgnoredMutLoan].
              See the comment for [AEndedMutLoan].
          *)
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

(* TODO: the type of avalues doesn't make sense for loan avalues: they currently
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

(** The kind of an abstraction, which keeps track of its origin *)
type abs_kind =
  | FunCall  (** The abstraction was introduced because of a function call *)
  | SynthInput
      (** The abstraction keeps track of the input values of the function
          we are currently synthesizing. *)
  | SynthRet
      (** The abstraction "absorbed" the value returned by the function we
          are currently synthesizing *)
[@@deriving show]

type abs = {
  abs_id : (AbstractionId.id[@opaque]);
  call_id : (FunCallId.id[@opaque]);
      (** The identifier of the function call which introduced this
          abstraction. This is not used by the symbolic execution:
          this is only used for pretty-printing and debugging, in the
          symbolic AST, generated by the symbolic execution.
       *)
  back_id : (RegionGroupId.id[@opaque]);
      (** The region group id to which this abstraction is linked.
      
          In most situations, it gives the id of the backward function (hence
          the name), but it is a bit more subtle in the case of synth input
          and synth ret abstractions.

          This is not used by the symbolic execution: it is a utility for
          the symbolic AST, generated by the symbolic execution.
       *)
  kind : (abs_kind[@opaque]);
  can_end : (bool[@opaque]);
      (** Controls whether the region can be ended or not.
          
          This allows to "pin" some regions, and is useful when generating
          backward functions.
          
          For instance, if we have: `fn f<'a, 'b>(...) -> (&'a mut T, &'b mut T)`,
          when generating the backward function for 'a, we have to make sure we
          don't need to end the return region for 'b (if it is the case, it means
          the function doesn't borrow check).
       *)
  parents : (AbstractionId.Set.t[@opaque]);  (** The parent abstractions *)
  original_parents : (AbstractionId.id list[@opaque]);
      (** The original list of parents, ordered. This is used for synthesis. *)
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

(** A symbolic expansion
    
    A symbolic expansion doesn't represent a value, but rather an operation
    that we apply to values.
    
    TODO: this should rather be name "expanded_symbolic"
 *)
type symbolic_expansion =
  | SeConcrete of constant_value
  | SeAdt of (VariantId.id option * symbolic_value list)
  | SeMutRef of BorrowId.id * symbolic_value
  | SeSharedRef of BorrowId.Set.t * symbolic_value
