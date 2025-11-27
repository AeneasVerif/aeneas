open Identifiers
open Types
open Expressions
include Charon.Values

(* TODO(SH): I often write "abstract" (value, borrow content, etc.) while I should
 * write "abstraction" (because those values are not abstract, they simply are
 * inside abstractions) *)

module BorrowId = IdGen ()
module SharedBorrowId = IdGen ()
module SymbolicValueId = IdGen ()
module AbsId = IdGen ()
module FunCallId = IdGen ()
module LoopId = IdGen ()
module MetaId = IdGen ()

type symbolic_value_id = SymbolicValueId.id [@@deriving show, ord]
type symbolic_value_id_set = SymbolicValueId.Set.t [@@deriving show, ord]
type loop_id = LoopId.id [@@deriving show, ord]
type meta_id = MetaId.id [@@deriving show, ord]
type fun_call_id = FunCallId.id [@@deriving show, ord]
type borrow_id = BorrowId.id [@@deriving show, ord]
type borrow_id_set = BorrowId.Set.t [@@deriving show, ord]
type shared_borrow_id = SharedBorrowId.id [@@deriving show, ord]
type loan_id = BorrowId.id [@@deriving show, ord]
type loan_id_set = BorrowId.Set.t [@@deriving show, ord]

(** Ancestor for {!tvalue} iter visitor *)
class ['self] iter_tvalue_base =
  object (self : 'self)
    inherit [_] iter_ty

    method visit_symbolic_value_id : 'env -> symbolic_value_id -> unit =
      fun _ _ -> ()

    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
    method visit_borrow_id : 'env -> borrow_id -> unit = fun _ _ -> ()

    method visit_shared_borrow_id : 'env -> shared_borrow_id -> unit =
      fun _ _ -> ()

    method visit_loan_id : 'env -> loan_id -> unit = fun _ _ -> ()

    method visit_borrow_id_set : 'env -> borrow_id_set -> unit =
      fun env ids -> BorrowId.Set.iter (self#visit_borrow_id env) ids

    method visit_loan_id_set : 'env -> loan_id_set -> unit =
      fun env ids -> BorrowId.Set.iter (self#visit_loan_id env) ids
  end

(** Ancestor for {!tvalue} map visitor for *)
class ['self] map_tvalue_base =
  object (self : 'self)
    inherit [_] map_ty

    method visit_symbolic_value_id :
        'env -> symbolic_value_id -> symbolic_value_id =
      fun _ x -> x

    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
    method visit_borrow_id : 'env -> borrow_id -> borrow_id = fun _ id -> id

    method visit_shared_borrow_id : 'env -> shared_borrow_id -> shared_borrow_id
        =
      fun _ id -> id

    method visit_loan_id : 'env -> loan_id -> loan_id = fun _ id -> id

    method visit_borrow_id_set : 'env -> borrow_id_set -> borrow_id_set =
      fun env ids -> BorrowId.Set.map (self#visit_borrow_id env) ids

    method visit_loan_id_set : 'env -> loan_id_set -> loan_id_set =
      fun env ids -> BorrowId.Set.map (self#visit_loan_id env) ids
  end

(** A symbolic value *)
type symbolic_value = {
  sv_id : symbolic_value_id;
  sv_ty : ty;  (** This should be a type with regions *)
}

(** An untyped value, used in the environments - TODO: prefix the names with "V"
*)
and value =
  | VLiteral of literal  (** Non-symbolic primitive value *)
  | VAdt of adt_value  (** Enumerations and structures *)
  | VBottom  (** No value (uninitialized or moved value) *)
  | VBorrow of borrow_content  (** A borrowed value *)
  | VLoan of loan_content  (** A loaned value *)
  | VSymbolic of symbolic_value
      (** Borrow projector over a symbolic value.

          Note that contrary to the abstraction-values case, symbolic values
          appearing in regular values are interpreted as *borrow* projectors,
          they can never be *loan* projectors. *)

and adt_value = { variant_id : variant_id option; fields : tvalue list }

and borrow_content =
  | VSharedBorrow of borrow_id * shared_borrow_id
      (** A shared borrow. The [borrow_id] is the identifier appearing in the
          formalism and which links the borrow to its loan. The
          [shared_borrow_id] doesn't appear in the formalism and is here to
          uniquely identify the borrow, for convenience purposes. This is only
          an implementation detail and doesn't have any impact on the semantics.
      *)
  | VMutBorrow of borrow_id * tvalue  (** A mutably borrowed value. *)
  | VReservedMutBorrow of borrow_id * shared_borrow_id
      (** A reserved mut borrow.

          This is used to model
          {{:https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html}
           two-phase borrows}. When evaluating a two-phase mutable borrow we
          first introduce a reserved borrow which behaves like a shared borrow
          until the moment we actually *use* the borrow: at this point, we end
          all the other shared borrows (and reserved borrows - though there
          shouldn't be any other reserved borrows in practice) of this value and
          replace the reserved borrow with a mutable borrow (as well as the
          shared loan with a mutable loan).

          A simple use case of two-phase borrows:
          {[
            let mut v = Vec::new();
            v.push(v.len());
          ]}

          Without two-phase borrows, this gets desugared to (something similar
          to) the following MIR:
          {[
            v = Vec::new();
            v1 = &mut v;
            v2 = &v; // We need this borrow, but v has already been mutably borrowed!
            l = Vec::len(move v2); // We need v2 here, and v1 *below*
            Vec::push(move v1, move l);
          ]}

          With two-phase borrows we get this:
          {[
            v = Vec::new();
            v1 = &two-phase mut v; // v1 is a reserved borrow, and v is *shared*
            v2 = &v; // v is shared, so we can (immutably) borrow through v2
            l = Vec::len(move v2); // We use v2 here
            Vec::push(move v1, move l); // v1 gets promoted to a mutable borrow here
          ]} *)

and loan_content = VSharedLoan of loan_id * tvalue | VMutLoan of loan_id

(** "Regular" typed value (we map variables to typed values) *)
and tvalue = { value : value; ty : ty }
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_tvalue";
      variety = "iter";
      ancestors = [ "iter_tvalue_base" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    },
  visitors
    {
      name = "map_tvalue";
      variety = "map";
      ancestors = [ "map_tvalue_base" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    }]

(** "Meta"-value: information we store for the synthesis.

    Note that we never automatically visit the meta-values with the visitors:
    they really are meta information, and shouldn't be considered as part of the
    environment during a symbolic execution.

    TODO: we may want to create wrappers, to prevent accidently mixing meta
    values and regular values. *)
type mvalue = tvalue [@@deriving show, ord]

(** "Meta"-symbolic value.

    See the explanations for {!mvalue}

    TODO: we may want to create wrappers, to prevent mixing meta values and
    regular values. *)
type msymbolic_value = symbolic_value [@@deriving show, ord]

type msymbolic_value_id = symbolic_value_id [@@deriving show, ord]

(** "Meta" symbolic value consumed upon ending a loan *)
type mconsumed_symb = { sv_id : symbolic_value_id; proj_ty : ty }
[@@deriving show, ord]

(** "Meta" symbolic value given back upon ending a borrow *)
type mgiven_back_symb = { sv_id : symbolic_value_id; proj_ty : ty }
[@@deriving show, ord]

type abs_id = AbsId.id [@@deriving show, ord]
type abs_id_set = AbsId.Set.t [@@deriving show, ord]

(** Projection markers: those are used in the joins. For additional explanations
    see: https://arxiv.org/pdf/2404.02680#section.5 *)
type proj_marker = PNone | PLeft | PRight [@@deriving show, ord]

type ended_proj_borrow_meta = {
  consumed : msymbolic_value_id;
  given_back : msymbolic_value;
}
[@@deriving show, ord]

type aended_mut_borrow_meta = {
  bid : borrow_id;
  given_back : msymbolic_value;
      (** The value given back upon ending the borrow *)
}
[@@deriving show, ord]

type eended_mut_borrow_meta = {
  bid : borrow_id;
  given_back : msymbolic_value;
      (** The value given back upon ending the borrow *)
}
[@@deriving show, ord]

(** The kind of an abstraction, which keeps track of its origin *)
type abs_kind =
  | FunCall of (FunCallId.id * RegionGroupId.id)
      (** The abstraction was introduced because of a function call.

          It contains he identifier of the function call which introduced this
          abstraction, as well as the id of the backward function this
          abstraction stands for (backward functions are identified by the group
          of regions to which they are associated). This is not used by the
          symbolic execution: this is only used for pretty-printing and
          debugging in the symbolic AST, generated by the symbolic execution. *)
  | SynthInput of RegionGroupId.id
      (** The abstraction keeps track of the input values of the function we are
          currently synthesizing.

          We introduce one abstraction per (group of) region(s) in the function
          signature, the region group id identifies this group. Similarly to the
          [FunCall] case, this is not used by the symbolic execution. *)
  | SynthRet of RegionGroupId.id
      (** The abstraction "absorbed" the value returned by the function we are
          currently synthesizing

          See the explanations for [SynthInput]. *)
  | Loop of LoopId.id  (** The abstraction corresponds to a loop. *)
  | Identity
      (** An identity abstraction, which only consumes and provides shared
          borrows/loans.

          We introduce them to abstract the context a bit, for instance to
          compute fixed-points. *)
  | CopySymbolicValue
      (** See [InterpreterExpressions.copy_value]: a auxiliary region
          abstraction which we introduced because of a copy of a symbolic value
          containing borrows. *)
  | WithCont
      (** Introduced when simplifying the context before matching with a loop
          for instance. The abstraction should have a continuation which
          describes its computational behavior. *)
  | Join
      (** The abstraction was introduced after joining contexts, typically after
          an [if then else] or a [match] *)
[@@deriving show, ord]

module AbsBVarId = IdGen ()
module AbsFVarId = IdGen ()

(** A DeBruijn index identifying a group of bound variables *)
type abs_db_scope_id = int [@@deriving show, ord]

type abs_bvar_id = AbsBVarId.id [@@deriving show, ord]
type abs_fvar_id = AbsFVarId.id [@@deriving show, ord]

let ( abs_fvar_id_counter,
      marked_abs_fvar_ids,
      marked_abs_fvar_ids_insert_from_int,
      fresh_abs_fvar_id ) =
  AbsFVarId.fresh_marked_stateful_generator ()

(** The [Id] module for dummy variables in environments.

    Dummy variables are used to store values that we don't want to forget in the
    environment, because they contain borrows for instance, typically because
    they might be overwritten during an assignment. *)
module DummyVarId =
IdGen ()

type dummy_var_id = DummyVarId.id [@@deriving show, ord]

(** Ancestor for {!env} iter visitor *)
class ['self] iter_env_base =
  object (self : 'self)
    inherit [_] iter_tvalue
    method visit_fun_call_id : 'env -> fun_call_id -> unit = fun _ _ -> ()
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()
    method visit_mvalue : 'env -> mvalue -> unit = fun _ _ -> ()

    method visit_msymbolic_value : 'env -> msymbolic_value -> unit =
      fun _ _ -> ()

    method visit_msymbolic_value_id : 'env -> msymbolic_value_id -> unit =
      fun _ _ -> ()

    method visit_mconsumed_symb : 'env -> mconsumed_symb -> unit = fun _ _ -> ()

    method visit_mgiven_back_symb : 'env -> mgiven_back_symb -> unit =
      fun _ _ -> ()

    method visit_region_id_set : 'env -> region_id_set -> unit =
      fun env ids -> RegionId.Set.iter (self#visit_region_id env) ids

    method visit_abs_id : 'env -> abs_id -> unit = fun _ _ -> ()

    method visit_abs_id_set : 'env -> abs_id_set -> unit =
      fun env ids -> AbsId.Set.iter (self#visit_abs_id env) ids

    method visit_region_group_id : 'env -> region_group_id -> unit =
      fun _ _ -> ()

    method visit_proj_marker : 'env -> proj_marker -> unit = fun _ _ -> ()

    method visit_ended_proj_borrow_meta : 'env -> ended_proj_borrow_meta -> unit
        =
      fun _ _ -> ()

    method visit_aended_mut_borrow_meta : 'env -> aended_mut_borrow_meta -> unit
        =
      fun _ _ -> ()

    method visit_eended_mut_borrow_meta : 'env -> eended_mut_borrow_meta -> unit
        =
      fun _ _ -> ()

    method visit_abs_db_scope_id : 'env -> abs_db_scope_id -> unit =
      fun _ _ -> ()

    method visit_abs_bvar_id : 'env -> abs_bvar_id -> unit = fun _ _ -> ()
    method visit_abs_fvar_id : 'env -> abs_fvar_id -> unit = fun _ _ -> ()
    method visit_local_id : 'env -> local_id -> unit = fun _ _ -> ()
    method visit_dummy_var_id : 'env -> dummy_var_id -> unit = fun _ _ -> ()
    method visit_abs_kind : 'env -> abs_kind -> unit = fun _ _ -> ()
  end

(** Ancestor for {!env} map visitor *)
class ['self] map_env_base =
  object (self : 'self)
    inherit [_] map_tvalue
    method visit_fun_call_id : 'env -> fun_call_id -> fun_call_id = fun _ x -> x
    method visit_loop_id : 'env -> loop_id -> loop_id = fun _ x -> x
    method visit_mvalue : 'env -> mvalue -> mvalue = fun _ x -> x

    method visit_msymbolic_value : 'env -> msymbolic_value -> msymbolic_value =
      fun _ m -> m

    method visit_msymbolic_value_id :
        'env -> msymbolic_value_id -> msymbolic_value_id =
      fun _ m -> m

    method visit_mconsumed_symb : 'env -> mconsumed_symb -> mconsumed_symb =
      fun _ m -> m

    method visit_mgiven_back_symb : 'env -> mgiven_back_symb -> mgiven_back_symb
        =
      fun _ m -> m

    method visit_region_id_set : 'env -> region_id_set -> region_id_set =
      fun env ids -> RegionId.Set.map (self#visit_region_id env) ids

    method visit_abs_id : 'env -> abs_id -> abs_id = fun _ x -> x

    method visit_abs_id_set : 'env -> abs_id_set -> abs_id_set =
      fun env ids -> AbsId.Set.map (self#visit_abs_id env) ids

    method visit_region_group_id : 'env -> region_group_id -> region_group_id =
      fun _ x -> x

    method visit_proj_marker : 'env -> proj_marker -> proj_marker = fun _ x -> x

    method visit_ended_proj_borrow_meta :
        'env -> ended_proj_borrow_meta -> ended_proj_borrow_meta =
      fun _ x -> x

    method visit_aended_mut_borrow_meta :
        'env -> aended_mut_borrow_meta -> aended_mut_borrow_meta =
      fun _ x -> x

    method visit_eended_mut_borrow_meta :
        'env -> eended_mut_borrow_meta -> eended_mut_borrow_meta =
      fun _ x -> x

    method visit_abs_db_scope_id : 'env -> abs_db_scope_id -> abs_db_scope_id =
      fun _ x -> x

    method visit_abs_bvar_id : 'env -> abs_bvar_id -> abs_bvar_id = fun _ x -> x
    method visit_abs_fvar_id : 'env -> abs_fvar_id -> abs_fvar_id = fun _ x -> x
    method visit_local_id : 'env -> local_id -> local_id = fun _ x -> x

    method visit_dummy_var_id : 'env -> dummy_var_id -> dummy_var_id =
      fun _ x -> x

    method visit_abs_kind : 'env -> abs_kind -> abs_kind = fun _ x -> x
  end

(** When giving shared borrows to functions (i.e., inserting shared borrows
    inside abstractions) we need to reborrow the shared values. When doing so,
    we lookup the shared values and apply some special projections to the shared
    value (until we can't go further, i.e., we find symbolic values which may
    get expanded upon reading them later), which don't generate avalues but sets
    of borrow ids and symbolic values.

    Note that as shared values can't get modified it is ok to forget the
    structure of the values we projected, and only keep the set of borrows (and
    symbolic values).

    TODO: we may actually need to remember the structure, in order to know which
    borrows are inside which other borrows...

    TODO: remove once we simplify the handling of borrows. *)
type abstract_shared_borrow =
  | AsbBorrow of borrow_id * shared_borrow_id
  | AsbProjReborrows of symbolic_proj

(** A set of abstract shared borrows *)
and abstract_shared_borrows = abstract_shared_borrow list

(** Remark: the projection type inside the [symbolic_proj] is redundant with the
    type contained in the typed avalue it belongs to. We duplicate this type
    because in practice it is extremely convenient to also have them here.

    TODO: we also need to add the original type of the symbolic value. *)
and symbolic_proj = { sv_id : symbolic_value_id; proj_ty : ty }

and aproj =
  | AProjLoans of aproj_loans
  | AProjBorrows of aproj_borrows
  | AEndedProjLoans of aended_proj_loans
  | AEndedProjBorrows of aended_proj_borrows
  | AEmpty
      (** Nothing to project (because there are no borrows, etc.).

          Note that we can't replace [AEmpty] with [AIgnored] because [aproj] is
          recursive with itself through types like [aproj_loans]. *)

(** A projector of loans over a symbolic value.

    Whenever we call a function, we introduce a symbolic value for the returned
    value. We insert projectors of loans over this symbolic value in the
    abstractions introduced by this function call: those projectors allow to
    insert the proper loans in the various abstractions whenever symbolic
    borrows get expanded.

    The borrows of a symbolic value may be spread between different
    abstractions, meaning that *one* projector of loans might receive *several*
    (symbolic) given back values.

    This is the case in the following example:
    {[
      fn f<'a> (...) -> (&'a mut u32, &'a mut u32);
      fn g<'b, 'c>(p : (&'b mut u32, &'c mut u32));

      let p = f(...);
      g(move p);

      // Symbolic context after the call to g:
      // abs'a {'a} { proj_loans   [s@0 <: (&'a mut u32, &'a mut u32)] }
      //
      // abs'b {'b} { proj_borrows (s@0 <: (&'b mut u32, &'c mut u32)) }
      // abs'c {'c} { proj_borrows (s@0 <: (&'b mut u32, &'c mut u32)) }
    ]}

    Upon evaluating the call to [f], we introduce a symbolic value [s@0] and a
    projector of loans (projector loans from the region 'c). This projector will
    later receive two given back values: one for 'a and one for 'b.

    We accumulate those values in the list of projections (note that the meta
    value stores the value which was given back).

    We can later end the projector of loans if [s@0] is not referenced anywhere
    in the context below a projector of borrows which intersects this projector
    of loans. *)
and aproj_loans = {
  proj : symbolic_proj;
  consumed : (mconsumed_symb * aproj) list;
      (** The values we consumed because part of the loans in this loan
          projector were ended. For the reason why there is a list, see the
          explanations below. Note that because ending the loan may require
          ending several borrow projectors (and consuming their given back
          values) we accumulate the consumed values here, and turn the
          [AProjLoans] into an [AEndedProjLoans] only when there are no
          intersecting borrow projectors left in the environment. *)
  borrows : (mconsumed_symb * aproj) list;
      (** The additional borrow projectors we had to introduce because some
          ancestor region ended *)
}

(** Note that an AProjBorrows only operates on a value which is not below a
    shared loan: under a shared loan, we use {!abstract_shared_borrow}.

    Also note that once given to a borrow projection, a symbolic value can't get
    updated/expanded: this means that we don't need to save any meta-value here.

    TODO: the explanations below are wrong.

    Finally, we have the same problem as with loans, that is we may need to
    reproject loans coming from several abstractions. Consider for instance what
    happens if we end abs1 and abs2 below: the borrow projector inside of abs0
    will receive parts of their given back symbolic values:
    {[
      ...
      abs0 {'c} { proj_borrows (s@0 : (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      ...

      abs1 {'a} { proj_loans (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      abs2 {'b} { proj_loans (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      ...
    ]} *)
and aproj_borrows = {
  proj : symbolic_proj;
  loans : (mconsumed_symb * aproj) list;
      (** When an ancestor region ends, we may have to project the loans
          corresponding to its given back values. We store them here. *)
}

(** An ended projector of loans over a symbolic value.

    See the explanations for {!AProjLoans} *)
and aended_proj_loans = {
  proj : msymbolic_value_id;
      (** The id of the original symbolic value, that we preserve as a
          meta-value *)
  consumed : (mconsumed_symb * aproj) list;
      (** The values we consumed because part of the loans in this loan
          projector were ended (for the reason why there is a list, see the
          explanations below). *)
  borrows : (mconsumed_symb * aproj) list;
      (** The additional borrow projectors we had to introduce because some
          ancestor region ended *)
}

and aended_proj_borrows = {
  mvalues : ended_proj_borrow_meta;
      (** This stores, for synthesis purposes:
          - the symbolic value which was consumed upon creating the projection
          - the symbolic value which was generated and given back upon ending
            the borrows *)
  loans : (mconsumed_symb * aproj) list;
}

(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph: part of
    it is thus "abstracted" away. *)
and avalue =
  | AAdt of adt_avalue
  | ALoan of aloan_content
  | ABorrow of aborrow_content
  | ASymbolic of proj_marker * aproj
  | AIgnored of mvalue option
      (** A value which doesn't contain borrows, or which borrows we don't own
          and thus ignore.

          In the comments, we display it as [_].

          Note that we store the ignored value as a meta value. Also note that
          this value is not always present (when we introduce abstractions
          because of a join for instance). *)

and adt_avalue = {
  variant_id : (VariantId.id option[@opaque]);
  fields : tavalue list;
}

(** A loan content as stored in an abstraction.

    We use the children avalues for synthesis purposes: though not necessary to
    maintain the borrow graph, we maintain a structured representation of the
    avalues to synthesize values for the backward functions in the translation.

    Note that the children avalues are independent of the parent avalues. For
    instance, the child avalue contained in an {!AMutLoan} will likely contain
    other, independent loans. *)
and aloan_content =
  | AMutLoan of proj_marker * loan_id * tavalue
      (** A mutable loan owned by an abstraction.

          The avalue is the child avalue.

          Example: ========
          {[
            fn f<'a>(...) -> &'a mut &'a mut u32;

            let px = f(...);
          ]}

          We get (after some symbolic exansion):
          {[
            abs0 {
              a_mut_loan l0 (a_mut_loan l1 _)
            }
            px -> mut_borrow l0 (mut_borrow @s1)
          ]} *)
  | ASharedLoan of proj_marker * loan_id * tvalue * tavalue
      (** A shared loan owned by an abstraction.

          The avalue is the child avalue.

          Example: ========
          {[
            fn f<'a>(...) -> &'a u32;

            let px = f(...);
          ]}

          We get:
          {[
            abs0 { a_shared_loan {l0} @s0 _ }
            px -> shared_loan l0
          ]} *)
  | AEndedMutLoan of aended_mut_loan
      (** An ended mutable loan in an abstraction. We need it because
          abstractions must keep track of the values we gave back to them, so
          that we can correctly instantiate backward functions. *)
  | AEndedSharedLoan of tvalue * tavalue
      (** Similar to {!AEndedMutLoan} but in this case we don't consume given
          back values when the loan ends. We remember the shared value because
          it now behaves as a "regular" value (which might contain borrows we
          need to keep track of...). *)
  | AIgnoredMutLoan of loan_id option * tavalue
      (** An ignored mutable loan.

          We need to keep track of ignored mutable loans, because we may have to
          apply projections on the values given back to those loans (say you
          have a borrow of type [&'a mut &'b mut], in the abstraction 'b, the
          outer loan is ignored, however you need to keep track of it so that
          when ending the borrow corresponding to 'a you can correctly project
          on the inner given back value).

          Note that we need to do so only for borrows consumed by parent
          abstractions, hence the optional loan id.

          Example: ========
          {[
            fn f<'a,'b>(...) -> &'a mut &'b mut u32;
            let x = f(...);

            > abs'a { a_mut_loan l0 (a_ignored_mut_loan None _) _ }
            > abs'b { a_ignored_mut_loan (Some l0) (a_mut_loan l1 _) }
            > x -> mut_borrow l0 (mut_borrow l1 @s1)
          ]}

          If we end [l0]:
          {[
            abs'a { ... }
            abs'b {
              a_ended_ignored_mut_loan {
                child = a_mut_loan l1 _;
                given_back = a_mut_borrow l1 _;
                given_back_meta = mut_borrow l1 @s1
              }
            }
            x -> ⊥
          ]} *)
  | AEndedIgnoredMutLoan of aended_ignored_mut_loan
  | AIgnoredSharedLoan of tavalue
      (** An ignored shared loan.

          Example: ========
          {[
            fn f<'a,'b>(...) -> &'a &'b u32;
            let x = f(...);

            > abs'a { a_shared_loan {l0} (shared_borrow l1) (a_ignored_shared_loan _) }
            > abs'b { a_ignored_shared_loan (a_shared_loan {l1} @s1 _) }
            > x -> shared_borrow l0
          ]} *)

(** An ended mutable loan in an abstraction. We need it because abstractions
    must keep track of the values we gave back to them, so that we can correctly
    instantiate backward functions.

    [given_back]: stores the projected given back value (useful when there are
    nested borrows: ending a loan might consume borrows which need to be
    projected in the abstraction).

    [given_back_meta]: stores the (meta-)value which was consumed upon ending
    the loan. We use this for synthesis purposes.

    Rk.: *DO NOT* use [visit_AEndedMutLoan]. If we update the order of the
    arguments and you forget to swap them at the level of [visit_AEndedMutLoan],
    you will not notice it.

    Example 1: ==========
    {[
      abs0 { a_mut_loan l0 _ }
      x -> mut_borrow l0 (U32 3)
    ]}

    After ending [l0]:

    {[
      abs0 { a_ended_mut_loan { child = _; given_back = _; given_back_meta = U32 3; }
      x -> ⊥
    ]}

    Example 2 (nested borrows): ===========================
    {[
      abs0 { a_mut_loan l0 _ }
      ... // abstraction containing a_mut_loan l1
      x -> mut_borrow l0 (mut_borrow l1 (U32 3))
    ]}

    After ending [l0]:

    {[
      abs0 {
        a_ended_mut_loan {
          child = _;
          given_back = a_mut_borrow l1 _;
          given_back_meta = (mut_borrow l1 (U32 3));
        }
      }
      ...
      x -> ⊥
    ]} *)
and aended_mut_loan = {
  child : tavalue;
  given_back : tavalue;
  given_back_meta : mvalue;
}

(** Similar to {!AEndedMutLoan}, for ignored loans. See the comments for
    {!AIgnoredMutLoan}.

    Rk.: *DO NOT* use [visit_AEndedIgnoredMutLoan] (for the reason why, see the
    comments for {!AEndedMutLoan}). *)

and aended_ignored_mut_loan = {
  child : tavalue;
  given_back : tavalue;
  given_back_meta : mvalue;
}

(** Note that contrary to {!aloan_content}, here the children avalues are not
    independent of the parent avalues. For instance, a value
    [AMutBorrow (_, AMutBorrow (_, ...)] (ignoring the types) really is to be
    seen like a [mut_borrow ... (mut_borrow ...)] (i.e., it is a nested borrow).

    TODO: be more precise about the ignored borrows (keep track of the borrow
    ids)? *)
and aborrow_content =
  | AMutBorrow of proj_marker * borrow_id * tavalue
      (** A mutable borrow owned by an abstraction.

          Is used when an abstraction "consumes" borrows, when giving borrows as
          arguments to a function.

          Example: ========
          {[
            fn f<'a>(px : &'a mut u32);

            > x -> mut_loan l0
            > px -> mut_borrow l0 (U32 0)

            f(move px);

            > x -> mut_loan l0
            > px -> ⊥
            > abs0 { a_mut_borrow l0 (U32 0) _ }
          ]} *)
  | ASharedBorrow of proj_marker * borrow_id * shared_borrow_id
      (** A shared borrow owned by an abstraction.

          Example: ========
          {[
            fn f<'a>(px : &'a u32);

            > x -> shared_loan {l0} (U32 0)
            > px -> shared_borrow l0

            f(move px);

            > x -> shared_loan {l0} (U32 0)
            > px -> ⊥
            > abs0 { a_shared_borrow l0 _ }
          ]} *)
  | AIgnoredMutBorrow of borrow_id option * tavalue
      (** An ignored mutable borrow.

          We need to keep track of ignored mut borrows because when ending such
          borrows, we need to project the loans of the given back value to
          insert them in the proper abstractions.

          Note that we need to do so only for borrows consumed by parent
          abstractions (hence the optional borrow id).

          Rem.: we don't have an equivalent for shared borrows because if we
          ignore a shared borrow we don't need to keep track it (we directly use
          {!AProjSharedBorrow} to project the shared value).

          TODO: the explanations below are obsolete

          Example: ========
          {[
            fn f<'a,'b>(ppx : &'a mut &'b mut u32);

            > x -> mut_loan l0
            > px -> mut_loan l1
            > ppx -> mut_borrow l1 (mut_borrow l0 (U32 0))

            f(move ppx);

            > x -> mut_loan l0
            > px -> mut_loan l1
            > ppx -> ⊥
            > abs'a { a_mut_borrow l1 (a_ignored_mut_borrow None _) }
            > abs'b {parents={abs'a}} { a_ignored_mut_borrow (Some l1) (a_mut_borrow l0 _) }

            ... // abs'a ends

            > x -> mut_loan l0
            > px -> @s0
            > ppx -> ⊥
            > abs'b {
            >   a_ended_ignored_mut_borrow {
            >     child = a_mut_borrow l0 _;
            >     given_back = a_proj_loans (@s0 <: &'b mut u32) // <-- loan projector
            >   }
            > }

            ... // [@s0] gets expanded to [&mut l2 @s1]

            > x -> mut_loan l0
            > px -> &mut l2 @s1
            > ppx -> ⊥
            > abs'b {
            >   a_ended_ignored_mut_borrow {
            >     child = a_mut_borrow l0 _;
            >     given_back = a_mut_loan l2 _;
            >   }
            > }
          ]}

          Note that we could use [AIgnoredMutLoan] in the case the borrow id is
          not [None], which would allow us to simplify the rules (to not have
          rules to specifically handle the case of AIgnoredMutBorrow with Some
          borrow id) and also remove the AEndedIgnoredMutBorrow variant. For
          now, we prefer to be more precise that required. *)
  | AEndedMutBorrow of aended_mut_borrow_meta * tavalue
      (** The sole purpose of {!AEndedMutBorrow} is to store meta information
          for the synthesis, with in particular the (symbolic) value that was
          given back upon ending the borrow. *)
  | AEndedSharedBorrow
      (** We don't really need {!AEndedSharedBorrow}: we simply want to be
          precise, and not insert ⊥ when ending borrows. *)
  | AEndedIgnoredMutBorrow of aended_ignored_mut_borrow
  | AProjSharedBorrow of abstract_shared_borrows
      (** A projected shared borrow.

          When giving shared borrows as arguments to function calls, we
          introduce new borrows to keep track of the fact that the function
          might reborrow values inside. Note that as shared values are
          immutable, we don't really need to remember the structure of the
          shared values.

          Example: ======== Below, when calling [f], we need to introduce one
          shared re-borrow per *inner* borrow (the borrows for 'b and 'c but not
          'a) consumed by the function. Those reborrows are introduced by
          projecting over the shared value. For each one of those, we introduce
          an [abstract_shared_borrow] in the abstraction.
          {[
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
            > abs'a { a_shared_borrow {l2} }
            > abs'b { a_proj_shared_borrow {l3} } // l3 reborrows l1
            > abs'c { a_proj_shared_borrow {l4} } // l4 reborrows l0
          ]}

          Rem.: we introduce {!AProjSharedBorrow} only when we project a shared
          borrow *which is ignored* (i.e., the shared borrow doesn't belong to
          the current abstraction, in which case we still project the shared
          value). The reason is that if the shared borrow belongs to the
          abstraction, then by introducing a shared borrow inside the
          abstraction we make sure the whole value is shared (and thus
          immutable) for as long as the abstraction lives, meaning reborrowing
          subvalues is redundant. However, if the borrow doesn't belong to the
          abstraction, we need to project the shared values because it may
          contain some borrows which *do* belong to the current abstraction.

          TODO: maybe we should factorized [ASharedBorrow] and
          [AProjSharedBorrow]. *)

(** See the explanations for {!AIgnoredMutBorrow} *)
and aended_ignored_mut_borrow = {
  child : tavalue;
  given_back : tavalue;
  given_back_meta : msymbolic_value;
      (** [given_back_meta] is used to store the (symbolic) value we gave back
          upon ending the borrow.

          Rk.: *DO NOT* use [visit_AEndedIgnoredMutLoan]. See the comment for
          {!AEndedMutLoan}. *)
}

(** Rem.: the of evalues is not to be understood in the same manner as for
    values. To be more precise, shared aloans have the borrow type (i.e., a
    shared aloan has type [& (mut) T] instead of [T]). *)
and tavalue = {
  value : avalue;
  ty : ty;  (** This should be a type with regions *)
}

(** Remark: the projection type inside the [symbolic_proj] is redundant with the
    type contained in the typed evalue it belongs to. We duplicate this type
    because in practice it is extremely convenient to also have them here. *)
and esymbolic_proj = { sv_id : symbolic_value_id; proj_ty : ty }

and eproj =
  | EProjLoans of eproj_loans
  | EProjBorrows of eproj_borrows
  | EEndedProjLoans of eended_proj_loans
  | EEndedProjBorrows of eended_proj_borrows
  | EEmpty
      (** Nothing to project (because there are no borrows, etc.).

          Note that we can't replace [EEmpty] with [EIgnored] because [eproj] is
          recursive with itself through types like [eproj_loans]. *)

(** A projector of loans over a symbolic value.

    Whenever we call a function, we introduce a symbolic value for the returned
    value. We insert projectors of loans over this symbolic value in the
    abstractions introduced by this function call: those projectors allow to
    insert the proper loans in the various abstractions whenever symbolic
    borrows get expanded.

    The borrows of a symbolic value may be spread between different
    abstractions, meaning that *one* projector of loans might receive *several*
    (symbolic) given back values.

    This is the case in the following example:
    {[
      fn f<'a> (...) -> (&'a mut u32, &'a mut u32);
      fn g<'b, 'c>(p : (&'b mut u32, &'c mut u32));

      let p = f(...);
      g(move p);

      // Symbolic context after the call to g:
      // abs'a {'a} { proj_loans   [s@0 <: (&'a mut u32, &'a mut u32)] }
      //
      // abs'b {'b} { proj_borrows (s@0 <: (&'b mut u32, &'c mut u32)) }
      // abs'c {'c} { proj_borrows (s@0 <: (&'b mut u32, &'c mut u32)) }
    ]}

    Upon evaluating the call to [f], we introduce a symbolic value [s@0] and a
    projector of loans (projector loans from the region 'c). This projector will
    later receive two given back values: one for 'a and one for 'b.

    We accumulate those values in the list of projections (note that the meta
    value stores the value which was given back).

    We can later end the projector of loans if [s@0] is not referenced anywhere
    in the context below a projector of borrows which intersects this projector
    of loans. *)
and eproj_loans = {
  proj : esymbolic_proj;
  consumed : (mconsumed_symb * eproj) list;
      (** The values we consumed because part of the loans in this loan
          projector were ended. For the reason why there is a list, see the
          explanations below. Note that because ending the loan may require
          ending several borrow projectors (and consuming their given back
          values) we accumulate the consumed values here, and turn the
          [EprojLoans] into an [EEndedProjLoans] only when there are no
          intersecting borrow projectors left in the environment. *)
  borrows : (mconsumed_symb * eproj) list;
      (** The additional borrow projectors we had to introduce because some
          ancestor region ended *)
}

(** Note that an eproj_borrows only operates on a value which is not below a
    shared loan: under a shared loan, we use {!abstract_shared_borrow}.

    Also note that once given to a borrow projection, a symbolic value can't get
    updated/expanded: this means that we don't need to save any meta-value here.

    TODO: the explanations below are wrong.

    Finally, we have the same problem as with loans, that is we may need to
    reproject loans coming from several abstractions. Consider for instance what
    happens if we end abs1 and abs2 below: the borrow projector inside of abs0
    will receive parts of their given back symbolic values:
    {[
      ...
      abs0 {'c} { proj_borrows (s@0 : (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      ...

      abs1 {'a} { proj_loans (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      abs2 {'b} { proj_loans (&'a mut &'c mut u32, &'b mut &'c mut u32)) }
      ...
    ]} *)
and eproj_borrows = {
  proj : esymbolic_proj;
  loans : (mconsumed_symb * eproj) list;
      (** When an ancestor region ends, we may have to project the loans
          corresponding to its given back values. We store them here. *)
}

(** An ended projector of loans over a symbolic value.

    See the explanations for {!EprojLoans} *)
and eended_proj_loans = {
  proj : msymbolic_value_id;
      (** The id of the original symbolic value, that we preserve as a
          meta-value *)
  consumed : (mconsumed_symb * eproj) list;
      (** The values we consumed because part of the loans in this loan
          projector were ended (for the reason why there is a list, see the
          explanations below). *)
  borrows : (mconsumed_symb * eproj) list;
      (** The additional borrow projectors we had to introduce because some
          ancestor region ended *)
}

and eended_proj_borrows = {
  mvalues : ended_proj_borrow_meta;
      (** This stores, for synthesis purposes:
          - the symbolic value which was consumed upon creating the projection
          - the symbolic value which was generated and given back upon ending
            the borrows *)
  loans : (mconsumed_symb * eproj) list;
}

and abs_bvar = { scope : abs_db_scope_id; bvar_id : abs_bvar_id }

and abs_fun =
  | EOutputAbs of region_group_id
  | EInputAbs of region_group_id
  | EFunCall of abs_id
      (** The expression is the result of calling the backward function of a
          regular function.

          We remember the id of the corresponding region abstraction (we use
          this in the translation). *)
  | ELoop of abs_id * loop_id
      (** The expression is the result of calling the backward function of a
          loop.

          We also remember the id of the abstraction which introduced this call
          to the loop backward function. This is useful after joining region
          abstractions: we know which was the original region abstraction, which
          is helpful for the translation. *)
  | EJoin of abs_id
      (** Similar to [ELoop], but the abstraction was introduced when joining
          contexts after a branching *)

(** Abstraction values are used inside of abstractions to properly model
    borrowing relations introduced by function calls.

    When calling a function, we lose information about the borrow graph: part of
    it is thus "abstracted" away. *)
and evalue =
  | ELet of region_id_set * tepat * tevalue * tevalue
      (** Because let-bindings are used to bind expressions refering to
          different sets of regions, we need to precise the regions projected in
          the bound expression.

          Note that the set of regions applies to the projections inside the
          bound value and inside the binding *pattern*. *)
  | EJoinMarkers of tevalue * tevalue
      (** This expression is either the left expression (in case we project the
          left markers) or the right expression (in case we project the right
          markers). *)
  | EBVar of abs_bvar
  | EFVar of abs_fvar_id
  | EApp of abs_fun * tevalue list
  | EAdt of adt_evalue
  | EBottom (* TODO: remove once we change the way internal borrows are ended *)
  | ELoan of eloan_content
  | EBorrow of eborrow_content
  | ESymbolic of proj_marker * eproj
  | EValue of (env[@opaque]) * mvalue
      (** A concrete value, that we remember as a meta-value (together with the
          environment at the time we introduced this evalue - we need this to
          translate the shared borrows, because translating them requires
          looking up the corresponding loans) for the translation.

          We need this when we convert anonymous values to region abstractions.
          For instance, when converting [MB l 0] to a region abstraction, we
          introduce the following abstraction continuation:
          {[
            MB l : EValue 0
          ]}
          this means that when ending borrow [l] we should output exactly the
          value [0]. *)
  | EMutBorrowInput of tevalue
      (** This is the input of a mut loan.

          This happens when we convert a value like [MB l0 (ML l1 v, 0)] to a
          region abstraction: we need to remember that [(ML l1 v, 0)] will be
          the input of a mutable borrow, so we shouldn't filter any value when
          generating the pure translation.

          TODO: this is not very clean. *)
  | EIgnored
      (** A value which doesn't contain borrows, or which borrows we don't own
          and thus ignore.

          In the comments, we display it as [_]. *)

and epat =
  | POpen of abs_fvar_id
  | PBound
  | PAdt of variant_id option * tepat list
  | PIgnored

and tepat = { pat : epat; ty : ty  (** The type should have been normalized *) }

and adt_evalue = {
  variant_id : (VariantId.id option[@opaque]);
  fields : tevalue list;
}

(** A loan content as stored in an abstraction.

    We use the children evalues for synthesis purposes: though not necessary to
    maintain the borrow graph, we maintain a structured representation of the
    evalues to synthesize values for the backward functions in the translation.

    Note that the children evalues are independent of the parent evalues. For
    instance, the child evalue contained in an {!AMutLoan} will likely contain
    other, independent loans.

    Note that because shared loans do not consume anything we do not track them.
*)
and eloan_content =
  | EMutLoan of proj_marker * loan_id * tevalue
      (** A mutable loan owned by an abstraction.

          The evalue is the child evalue.

          Example: ========
          {[
            fn f<'a>(...) -> &'a mut &'a mut u32;

            let px = f(...);
          ]}

          We get (after some symbolic exansion):
          {[
            abs0 {
              a_mut_loan l0 (a_mut_loan l1 _)
            }
            px -> mut_borrow l0 (mut_borrow @s1)
          ]} *)
  | EEndedMutLoan of eended_mut_loan
      (** An ended mutable loan in an abstraction. We need it because
          abstractions must keep track of the values we gave back to them, so
          that we can correctly instantiate backward functions. *)
  | EIgnoredMutLoan of loan_id option * tevalue
      (** An ignored mutable loan.

          We need to keep track of ignored mutable loans, because we may have to
          apply projections on the values given back to those loans (say you
          have a borrow of type [&'a mut &'b mut], in the abstraction 'b, the
          outer loan is ignored, however you need to keep track of it so that
          when ending the borrow corresponding to 'a you can correctly project
          on the inner given back value). We also use this to

          Note that we need to do so only for borrows consumed by parent
          abstractions, hence the optional loan id.

          Example: ========
          {[
            fn f<'a,'b>(...) -> &'a mut &'b mut u32;
            let x = f(...);

            > abs'a { a_mut_loan l0 (a_ignored_mut_loan None _) _ }
            > abs'b { a_ignored_mut_loan (Some l0) (a_mut_loan l1 _) }
            > x -> mut_borrow l0 (mut_borrow l1 @s1)
          ]}

          If we end [l0]:
          {[
            abs'a { ... }
            abs'b {
              a_ended_ignored_mut_loan {
                child = a_mut_loan l1 _;
                given_back = a_mut_borrow l1 _;
                given_back_meta = mut_borrow l1 @s1
              }
            }
            x -> ⊥
          ]} *)
  | EEndedIgnoredMutLoan of eended_ignored_mut_loan

(** An ended mutable loan in an abstraction. We need it because abstractions
    must keep track of the values we gave back to them, so that we can correctly
    instantiate backward functions.

    [given_back]: stores the projected given back value (useful when there are
    nested borrows: ending a loan might consume borrows which need to be
    projected in the abstraction).

    [given_back_meta]: stores the (meta-)value which was consumed upon ending
    the loan. We use this for synthesis purposes.

    Rk.: *DO NOT* use [visit_EEndedMutLoan]. If we update the order of the
    arguments and you forget to swap them at the level of [visit_EEndedMutLoan],
    you will not notice it.

    Example 1: ==========
    {[
      abs0 { a_mut_loan l0 _ }
      x -> mut_borrow l0 (U32 3)
    ]}

    After ending [l0]:

    {[
      abs0 { a_ended_mut_loan { child = _; given_back = _; given_back_meta = U32 3; }
      x -> ⊥
    ]}

    Example 2 (nested borrows): ===========================
    {[
      abs0 { a_mut_loan l0 _ }
      ... // abstraction containing a_mut_loan l1
      x -> mut_borrow l0 (mut_borrow l1 (U32 3))
    ]}

    After ending [l0]:

    {[
      abs0 {
        a_ended_mut_loan {
          child = _;
          given_back = a_mut_borrow l1 _;
          given_back_meta = (mut_borrow l1 (U32 3));
        }
      }
      ...
      x -> ⊥
    ]} *)
and eended_mut_loan = {
  child : tevalue;
  given_back : tevalue;
  given_back_meta : mvalue;
}

(** Similar to {!EEndedMutLoan}, for ignored loans. See the comments for
    {!AIgnoredMutLoan}.

    Rk.: *DO NOT* use [visit_EEndedIgnoredMutLoan] (for the reason why, see the
    comments for {!EEndedMutLoan}). *)

and eended_ignored_mut_loan = {
  child : tevalue;
  given_back : tevalue;
  given_back_meta : mvalue;
}

(** Note that contrary to {!aloan_content}, here the children evalues are not
    independent of the parent evalues. For instance, a value
    [AMutBorrow (_, AMutBorrow (_, ...)] (ignoring the types) really is to be
    seen like a [mut_borrow ... (mut_borrow ...)] (i.e., it is a nested borrow).

    TODO: be more precise about the ignored borrows (keep track of the borrow
    ids)?

    Note that because shared borrows do not give back anything we do not track
    them. *)
and eborrow_content =
  | EMutBorrow of proj_marker * borrow_id * tevalue
      (** A mutable borrow owned by an abstraction.

          Is used when an abstraction "consumes" borrows, when giving borrows as
          arguments to a function.

          Example: ========
          {[
            fn f<'a>(px : &'a mut u32);

            > x -> mut_loan l0
            > px -> mut_borrow l0 (U32 0)

            f(move px);

            > x -> mut_loan l0
            > px -> ⊥
            > abs0 { a_mut_borrow l0 (U32 0) _ }
          ]}

          We remember the value consumed upon creating the mutable borrow. *)
  | EIgnoredMutBorrow of borrow_id option * tevalue
      (** An ignored mutable borrow.

          We need to keep track of ignored mut borrows because when ending such
          borrows, we need to project the loans of the given back value to
          insert them in the proper abstractions. We also use ignored mutable
          borrows in input expressions: see the explanations for [abs_cont]
          below. This is the reason why the borrow id is optional.

          Rem.: we don't have an equivalent for shared borrows because if we
          ignore a shared borrow we don't need to keep track it (we directly use
          {!EprojSharedBorrow} to project the shared value).

          TODO: the explanations below are obsolete

          Example: ========
          {[
            fn f<'a,'b>(ppx : &'a mut &'b mut u32);

            > x -> mut_loan l0
            > px -> mut_loan l1
            > ppx -> mut_borrow l1 (mut_borrow l0 (U32 0))

            f(move ppx);

            > x -> mut_loan l0
            > px -> mut_loan l1
            > ppx -> ⊥
            > abs'a { a_mut_borrow l1 (a_ignored_mut_borrow None _) }
            > abs'b {parents={abs'a}} { a_ignored_mut_borrow (Some l1) (a_mut_borrow l0 _) }

            ... // abs'a ends

            > x -> mut_loan l0
            > px -> @s0
            > ppx -> ⊥
            > abs'b {
            >   a_ended_ignored_mut_borrow {
            >     child = a_mut_borrow l0 _;
            >     given_back = a_proj_loans (@s0 <: &'b mut u32) // <-- loan projector
            >   }
            > }

            ... // [@s0] gets expanded to [&mut l2 @s1]

            > x -> mut_loan l0
            > px -> &mut l2 @s1
            > ppx -> ⊥
            > abs'b {
            >   a_ended_ignored_mut_borrow {
            >     child = a_mut_borrow l0 _;
            >     given_back = a_mut_loan l2 _;
            >   }
            > }
          ]}

          Note that we could use [AIgnoredMutLoan] in the case the borrow id is
          not [None], which would allow us to simplify the rules (to not have
          rules to specifically handle the case of AIgnoredMutBorrow with Some
          borrow id) and also remove the EEndedIgnoredMutBorrow variant. For
          now, we prefer to be more precise that required. *)
  | EEndedMutBorrow of eended_mut_borrow_meta * tevalue
      (** The sole purpose of {!EEndedMutBorrow} is to store meta information
          for the synthesis, with in particular the (symbolic) value that was
          given back upon ending the borrow. *)
  | EEndedIgnoredMutBorrow of eended_ignored_mut_borrow

(** See the explanations for {!AIgnoredMutBorrow} *)
and eended_ignored_mut_borrow = {
  child : tevalue;
  given_back : tevalue;
  given_back_meta : msymbolic_value;
      (** [given_back_meta] is used to store the (symbolic) value we gave back
          upon ending the borrow.

          Rk.: *DO NOT* use [visit_EEndedIgnoredMutLoan]. See the comment for
          {!EEndedMutLoan}. *)
}

(** Rem.: the of evalues is not to be understood in the same manner as for
    values. To be more precise, shared aloans have the borrow type (i.e., a
    shared aloan has type [& (mut) T] instead of [T]). *)
and tevalue = {
  value : evalue;
  ty : ty;  (** This should be a type with regions *)
}

(** The continuation representing the computation that has to be performed when
    ending a region abstraction (this continuation computes the values given
    back by the abstraction from the values it consumed).

    This is used by the translation, and is particularly useful to compute
    joins: when merging regions, we compose their continuations. *)
and abs_cont = {
  output : tevalue option;
      (** All abstraction continuations should have an output *but* the input
          abstractions introduced at initialization time for the purpose of
          doing the synthesis. Because of this, those abstractions should never
          be merged with other abstractions. *)
  input : tevalue option;
      (** TODO: update explanations (those are wrong).

          [output] gives the output borrows, while [input] is the computation
          which yields the value. If this computation is not present, it means
          that when ending a borrow we should give back the same value it holds.

          For instance, let's say we have a function
          [fn id<'a, T>(&'a mut T) -> &'a mut T]. Its evaluation gives:
          {[
            // x  -> ML l0
            // px -> MB l0 0
            py = id(move x);
            // x  -> ML l0
            // px -> ⊥
            // abs { MB l0, ML l1 }[[ MB l0: id_back (ML l1) ]]
            //                        ^^^^^  ^^^^^^^^^^^^^^^
            //                       output    input
            // py -> MB l1 s0
          ]}
          This environment means that when ending the region abstraction [abs],
          the value we give back upon ending [l0] is the backward function
          introduced by the call to [id] applied to the value consumed upon
          ending [ML L1].

          However, when we turn an anonymous value into a region abstraction we
          do not need to introduce an input:
          {[
            _ -> MB l0 v
              ~>
            abs { MB l0 }[[MB l0 v]]
          ]}
          This means that upon ending [l0] we get the value [v]. *)
}

(** Abstractions model the parts in the borrow graph where the borrowing
    relations have been abstracted because of a function call.

    In order to model the relations between the borrows, we use "abstraction
    values", which are a special kind of value. *)
and abs = {
  abs_id : abs_id;
  kind : abs_kind;
  can_end : bool;
      (** Controls whether the region can be ended or not.

          This allows to "pin" some regions, and is useful when generating
          backward functions.

          For instance, if we have:
          [fn f<'a, 'b>(...) -> (&'a mut T, &'b mut T)], when generating the
          backward function for 'a, we have to make sure we don't need to end
          the return region for 'b (if it is the case, it means the function
          doesn't borrow check). *)
  parents : abs_id_set;  (** The parent abstractions *)
  original_parents : abs_id list;
      (** The original list of parents, ordered. This is used for synthesis.
          TODO: remove? *)
  regions : abs_regions;
      (** TODO: actually we also (only?) need to put the regions at the level of
          the values themselves, otherwise some projections are not precise
          enough when merging region abstractions. *)
  avalues : tavalue list;  (** The values in this abstraction *)
  cont : abs_cont option;
      (** The continuation representing the abstraction in the translation.

          This continuation is optional: it is [none] when we are in the process
          of computing loop fixed points. *)
}

and abs_regions = {
  owned : region_id_set;  (** Regions owned by the abstraction *)
}

(** A binder used in an environment, to map a variable to a value *)
and real_var_binder = {
  index : local_id;  (** Unique variable identifier *)
  name : string option;  (** Possible name *)
}

(** A binder, for a "real" variable or a dummy variable *)
and var_binder = BVar of real_var_binder | BDummy of dummy_var_id

(** Environment value: mapping from variable to value, abstraction (only used in
    symbolic mode) or stack frame delimiter. *)
and env_elem =
  | EBinding of var_binder * tvalue
      (** Variable binding - the binder is None if the variable is a dummy
          variable (we use dummy variables to store temporaries while doing
          bookkeeping such as ending borrows for instance). *)
  | EAbs of abs
  | EFrame

and env = env_elem list
[@@deriving
  show,
  ord,
  visitors
    {
      name = "iter_env";
      variety = "iter";
      ancestors = [ "iter_env_base" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      monomorphic = [ "env" ] (* We need this to allows duplicate field names *);
    },
  visitors
    {
      name = "map_env";
      variety = "map";
      ancestors = [ "map_env_base" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
      monomorphic = [ "env" ] (* We need this to allows duplicate field names *);
    }]

class ['self] iter_tavalue =
  object (_self : 'self)
    inherit [_] iter_env
  end

class ['self] map_tavalue =
  object (_self : 'self)
    inherit [_] map_env
  end

class ['self] iter_tevalue =
  object (_self : 'self)
    inherit [_] iter_env
  end

class ['self] map_tevalue =
  object (_self : 'self)
    inherit [_] map_env
  end

class ['self] iter_abs =
  object (_self : 'self)
    inherit [_] iter_env
  end

class ['self] map_abs =
  object (_self : 'self)
    inherit [_] map_env
  end

(** A symbolic expansion

    A symbolic expansion doesn't represent a value, but rather an operation that
    we apply to values.

    TODO: this should rather be name "expanded_symbolic" *)
type symbolic_expansion =
  | SeLiteral of literal
  | SeAdt of (VariantId.id option * symbolic_value list)
  | SeMutRef of BorrowId.id * symbolic_value
  | SeSharedRef of BorrowId.id * symbolic_value
[@@deriving show]
