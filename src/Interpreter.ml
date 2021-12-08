module T = Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils

(* TODO: Change state-passing style to : st -> ... -> (st, v) *)
(* TODO: check that the value types are correct when evaluating *)
(* TODO: for debugging purposes, we might want to put use eval_ctx everywhere
   (rather than only env) *)

(* TODO: it would be good to find a "core", which implements the rules (like
   "end_borrow") and on top of which we build more complex functions which
   chose in which order to apply the rules, etc. This way we would make very
   explicit where we need to insert sanity checks, what the preconditions are,
   where invariants might be broken, etc.
*)

(* TODO: intensively test with PLT-redex *)

(** Some utilities *)

let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string

let ety_to_string = Print.EvalCtxCfimAst.ety_to_string

let typed_value_to_string = Print.EvalCtxCfimAst.typed_value_to_string

let place_to_string = Print.EvalCtxCfimAst.place_to_string

let operand_to_string = Print.EvalCtxCfimAst.operand_to_string

let statement_to_string ctx =
  Print.EvalCtxCfimAst.statement_to_string ctx "" "  "

(* TODO: move *)
let mk_var (index : V.VarId.id) (name : string option) (var_ty : T.ety) : A.var
    =
  { A.index; name; var_ty }

(** Small helper *)
let mk_place_from_var_id (var_id : V.VarId.id) : E.place =
  { var_id; projection = [] }

(** TODO: change the name *)
type eval_error = Panic

type 'a eval_result = ('a, eval_error) result

type exploration_kind = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  enter_abs : bool;
}
(** This record controls how some generic helper lookup/update
    functions behave, by restraining the kind of therms they can enter.
*)

exception Found
(** Utility exception

    When looking for something while exploring a term, it can be easier to
    just throw an exception to signal we found what we were looking for.
 *)

exception FoundBorrowContent of V.borrow_content
(** Utility exception *)

exception FoundLoanContent of V.loan_content
(** Utility exception *)

(** Check if a value contains a borrow *)
let borrows_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains inactivated mutable borrows *)
let inactivated_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_InactivatedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan *)
let loans_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Lookup a loan content.

    The loan is referred to by a borrow id.
 *)
let lookup_loan_opt (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env) :
    V.loan_content option =
  let obj =
    object
      inherit [_] C.iter_env_concrete as super

      method! visit_MutBorrow env bid mv =
        if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv else ()
      (** Control the diving into mutable borrows *)

      (* TODO
            method! visit_Loan env lc =
              match lc with
              | V.SharedLoan (bids, sv) ->
                  (* Check if this is the loan we are looking for, and control the dive *)
                  if V.BorrowId.Set.mem l bids then
                    raise (FoundLoanContent (V.SharedLoan (bids, sv)))
                  else if ek.enter_shared_loans then
                    super#visit_SharedLoan env bids sv
                  else ()
              | V.MutLoan bid ->
                  (* Check if this is the loan we are looking for *)
                  if bid = l then raise (FoundLoanContent (V.MutLoan bid))
                  else super#visit_MutLoan env bid
            (** We reimplement [visit_Loan] (rather than the more precise functions
                [visit_SharedLoan], etc.) on purpose: as we have an exhaustive match
                below, we are more resilient to definition updates (the compiler
                is our friend).
            *)
      *)
      method! visit_SharedLoan env bids sv =
        if V.BorrowId.Set.mem l bids then
          raise (FoundLoanContent (V.SharedLoan (bids, sv)))
        else if ek.enter_shared_loans then super#visit_SharedLoan env bids sv
        else ()
      (** Shared loan: checks if this is the loan we are looking for, and
          control the dive.    
      *)

      method! visit_MutLoan env bid =
        if bid = l then raise (FoundLoanContent (V.MutLoan bid))
        else super#visit_MutLoan env bid
      (** Mut loan: checks if this is the loan we are looking for
      *)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_env () env;
    None
  with FoundLoanContent lc -> Some lc

(** Lookup a loan content.

    The loan is referred to by a borrow id.
    Raises an exception if no loan was found.
 *)
let lookup_loan (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env) :
    V.loan_content =
  match lookup_loan_opt ek l env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let update_loan (ek : exploration_kind) (l : V.BorrowId.id)
    (nlc : V.loan_content) (env : C.env) : C.env =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let set_ref r =
    assert (not !r);
    r := true
  in

  let obj =
    object
      inherit [_] C.map_env_concrete as super

      method! visit_MutBorrow env bid mv =
        if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
        else V.MutBorrow (bid, mv)
      (** Control the diving into mutable borrows *)

      method! visit_SharedLoan env bids sv =
        if V.BorrowId.Set.mem l bids then (
          set_ref env;
          nlc)
        else if ek.enter_shared_loans then super#visit_SharedLoan env bids sv
        else V.SharedLoan (bids, sv)
      (** Shared loan: checks if this is the loan we are looking for, and
          control the dive.    
      *)

      method! visit_MutLoan env bid =
        if bid = l then (
          set_ref env;
          nlc)
        else super#visit_MutLoan env bid
      (** Mut loan: checks if this is the loan we are looking for
      *)
    end
  in

  let env = obj#visit_env r env in
  (* Check that we updated at least one loan *)
  assert !r;
  env

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow_opt (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env)
    : V.borrow_content option =
  let obj =
    object
      inherit [_] C.iter_env_concrete as super

      method! visit_MutBorrow env bid mv =
        if bid = l then raise (FoundBorrowContent (V.MutBorrow (bid, mv)))
        else if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
        else ()
      (** Check the borrow id and control the diving *)

      method! visit_SharedBorrow _env bid =
        if bid = l then raise (FoundBorrowContent (V.SharedBorrow bid)) else ()
      (** Check the borrow id *)

      method! visit_InactivatedMutBorrow _env bid =
        if bid = l then raise (FoundBorrowContent (V.InactivatedMutBorrow bid))
        else ()
      (** Check the borrow id *)

      method! visit_SharedLoan env bids sv =
        if ek.enter_shared_loans then super#visit_SharedLoan env bids sv else ()
      (** Control the diving *)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_env () env;
    None
  with FoundBorrowContent lc -> Some lc

(** Lookup a borrow content from a borrow id.

    Raise an exception if no loan was found
*)
let lookup_borrow (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env) :
    V.borrow_content =
  match lookup_borrow_opt ek l env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_borrow (ek : exploration_kind) (l : V.BorrowId.id)
    (nbc : V.borrow_content) (env : C.env) : C.env =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let set_ref r =
    assert (not !r);
    r := true
  in

  let obj =
    object
      inherit [_] C.map_env_concrete as super

      method! visit_MutBorrow env bid mv =
        if bid = l then (
          set_ref env;
          nbc)
        else if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
        else V.MutBorrow (bid, mv)
      (** Check the id and control diving *)

      method! visit_SharedBorrow env bid =
        if bid = l then (
          set_ref env;
          nbc)
        else super#visit_SharedBorrow env bid
      (** Check the id *)

      method! visit_InactivatedMutBorrow env bid =
        if bid = l then (
          set_ref env;
          nbc)
        else super#visit_InactivatedMutBorrow env bid
      (** Check the id *)

      method! visit_SharedLoan env bids sv =
        if ek.enter_shared_loans then super#visit_SharedLoan env bids sv
        else V.SharedLoan (bids, sv)
      (** Control the dive *)

      method! visit_MutLoan env bid =
        (* Nothing specific to do for mutable loans *)
        super#visit_MutLoan env bid
    end
  in

  let env = obj#visit_env r env in
  (* Check that we updated at least one borrow *)
  assert !r;
  env

(** The following type identifies the relative position of expressions (in
    particular borrows) in other expressions.
    
    For instance, it is used to control [end_borrow]: we usually only allow
    to end "outer" borrows, unless we perform a drop.
*)
type inner_outer = Inner | Outer

type borrow_ids = Borrows of V.BorrowId.Set.t | Borrow of V.BorrowId.id

(** Borrow lookup result *)
type borrow_lres =
  | NotFound
  | Outer of borrow_ids
  | FoundMut of V.typed_value
  | FoundShared
  | FoundInactivatedMut

let update_if_none opt x = match opt with None -> Some x | _ -> opt

(** Auxiliary function: see its usage in [end_borrow_get_borrow_in_value] *)
let update_outer_borrows (io : inner_outer) opt x =
  match io with
  | Inner ->
      (* If we can end inner borrows, we don't keep track of the outer borrows *)
      None
  | Outer -> update_if_none opt x

let unwrap_res_to_outer_or opt default =
  match opt with Some x -> Outer x | None -> default

(** Return the first loan we find in a value *)
let get_first_loan_in_value (v : V.typed_value) : V.loan_content option =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    None
  with FoundLoanContent lc -> Some lc

(** Check if a value contains ⊥ *)
let bottom_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_Bottom _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** See [end_borrow_get_borrow_in_env] *)
let rec end_borrow_get_borrow_in_value (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (outer_borrows : borrow_ids option) (v0 : V.typed_value)
    : V.typed_value * borrow_lres =
  (* (* We use a reference to check if we update a borrow, and that we don't
      * update more than one borrow. *)
     let r = ref false in
     let set_ref () =
       assert (not !r);
       r := true
     in

     (* The environment is used to keep track of the outer loans *)
     let obj =
       object
         inherit [_] C.map_env_concrete as super

         method! visit_MutLoan outer_borrows bid =
           super#visit_MutLoan outer_borrows bid
         (** Nothing particular to do *)

         method! visit_SharedLoan outer_borrows bids v =
           let outer_borrows = update_outer_borrows io outer_borrows (Borrows bids) in
           super#visit_SharedLoan outer_borrows bids v
         (** Update the outer borrows *)

         method! visit_borrow_content outer_borrows bc =
           match bc with
           | V.SharedBorrow l' ->
             if l = l' then (set_ref (); Bottom

         method! visit_MutBorrow outer_borrows bid mv = *)
  match v0.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> (v0, NotFound)
  | V.Adt adt ->
      (* Note that we allow assumed types (like boxes) to outlive their
       * inner borrows. Also note that when using the symbolic mode,
       * boxes will never be "opened" and will be manipulated solely
       * through functions like new, deref, etc. which will enforce that
       * we destroy boxes upon ending inner borrows *)
      let values, res =
        end_borrow_get_borrow_in_values config io l outer_borrows
          adt.field_values
      in
      ({ v0 with value = Adt { adt with field_values = values } }, res)
  | V.Loan (V.MutLoan _) -> (v0, NotFound)
  | V.Loan (V.SharedLoan (borrows, v)) ->
      (* Update the outer borrows, if necessary *)
      let outer_borrows =
        update_outer_borrows io outer_borrows (Borrows borrows)
      in
      let v', res =
        end_borrow_get_borrow_in_value config io l outer_borrows v
      in
      ({ value = V.Loan (V.SharedLoan (borrows, v')); ty = v0.ty }, res)
  | V.Borrow (SharedBorrow l') ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows FoundInactivatedMut )
      else (v0, NotFound)
  | V.Borrow (InactivatedMutBorrow l') ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows FoundInactivatedMut )
      else (v0, NotFound)
  | V.Borrow (V.MutBorrow (l', bv)) ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows (FoundMut bv) )
      else
        (* Update the outer borrows, if necessary *)
        let outer_borrows = update_outer_borrows io outer_borrows (Borrow l') in
        let bv', res =
          end_borrow_get_borrow_in_value config io l outer_borrows bv
        in
        ({ v0 with value = V.Borrow (V.MutBorrow (l', bv')) }, res)

and end_borrow_get_borrow_in_values (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (outer_borrows : borrow_ids option)
    (vl0 : V.typed_value list) : V.typed_value list * borrow_lres =
  match vl0 with
  | [] -> (vl0, NotFound)
  | v :: vl -> (
      let v', res =
        end_borrow_get_borrow_in_value config io l outer_borrows v
      in
      match res with
      | NotFound ->
          let vl', res =
            end_borrow_get_borrow_in_values config io l outer_borrows vl
          in
          (v' :: vl', res)
      | _ -> (v' :: vl, res))

(** Auxiliary function to end borrows: lookup a borrow in the environment,
    update it (by returning an updated environment where the borrow has been
    replaced by [Bottom])) if we can end the borrow (for instance, it is not
    an outer borrow...) or return the reason why we couldn't update the borrow.

    [end_borrow] then simply performs a loop: as long as we need to end (outer)
    borrows, we end them, and finally we end the borrow we wanted to end in the
    first place.
*)
let rec end_borrow_get_borrow_in_env (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (env0 : C.env) : C.env * borrow_lres =
  match env0 with
  | [] -> ([], NotFound)
  | C.Var (x, v) :: env -> (
      match end_borrow_get_borrow_in_value config io l None v with
      | v', NotFound ->
          let env, res = end_borrow_get_borrow_in_env config io l env in
          (Var (x, v') :: env, res)
      | v', res -> (Var (x, v') :: env, res))
  | C.Abs _ :: _ ->
      assert (config.mode = SymbolicMode);
      raise Unimplemented
  | C.Frame :: env -> end_borrow_get_borrow_in_env config io l env

(** See [give_back_value]. *)
let rec give_back_value_to_value config bid (v : V.typed_value)
    (destv : V.typed_value) : V.typed_value =
  match destv.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> destv
  | V.Adt av ->
      let field_values =
        List.map (give_back_value_to_value config bid v) av.field_values
      in
      { destv with value = Adt { av with field_values } }
  | V.Borrow bc ->
      (* We may need to insert the value inside a borrowed value *)
      let bc' =
        match bc with
        | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> bc
        | V.MutBorrow (bid', destv') ->
            MutBorrow (bid', give_back_value_to_value config bid v destv')
      in
      { destv with value = V.Borrow bc' }
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (_, _) -> destv
      | V.MutLoan bid' ->
          if bid' = bid then v
          else { destv with value = V.Loan (V.MutLoan bid') })

(** See [give_back_value]. *)
let give_back_value_to_abs (_config : C.config) _bid _v _abs : V.abs =
  (* TODO *)
  raise Unimplemented

(** See [give_back_shared]. *)
let rec give_back_shared_to_value (config : C.config) bid
    (destv : V.typed_value) : V.typed_value =
  match destv.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> destv
  | V.Adt av ->
      let field_values =
        List.map (give_back_shared_to_value config bid) av.field_values
      in
      { destv with value = Adt { av with field_values } }
  | V.Borrow bc ->
      (* We may need to insert the value inside a borrowed value *)
      let bc' =
        match bc with
        | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> bc
        | V.MutBorrow (bid', destv') ->
            MutBorrow (bid', give_back_shared_to_value config bid destv')
      in
      { destv with value = V.Borrow bc' }
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (bids, shared_value) ->
          if V.BorrowId.Set.mem bid bids then
            if V.BorrowId.Set.cardinal bids = 1 then shared_value
            else
              {
                destv with
                value =
                  V.Loan
                    (V.SharedLoan (V.BorrowId.Set.remove bid bids, shared_value));
              }
          else
            {
              destv with
              value =
                V.Loan
                  (V.SharedLoan
                     (bids, give_back_shared_to_value config bid shared_value));
            }
      | V.MutLoan _ -> destv)

(** See [give_back_shared]. *)
let give_back_shared_to_abs _config _bid _abs : V.abs =
  (* TODO *)
  raise Unimplemented

(** Auxiliary function to end borrows.
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function doesn't check that there is actually a loan somewhere
    to which we can give the value: if this has to be checked, the check must
    be independently done before.
 *)
let give_back_value (config : C.config) (bid : V.BorrowId.id)
    (v : V.typed_value) (env : C.env) : C.env =
  let give_back_value_to_env_value ev : C.env_value =
    match ev with
    | C.Var (vid, destv) ->
        C.Var (vid, give_back_value_to_value config bid v destv)
    | C.Abs abs ->
        assert (config.mode = SymbolicMode);
        C.Abs (give_back_value_to_abs config bid v abs)
    | C.Frame -> C.Frame
  in
  List.map give_back_value_to_env_value env

(** Auxiliary function to end borrows.
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.

    Note that this function doesn't check that there is actually a loan somewhere
    from which to remove the shared borrow id: if this has to be checked, the
    check must be independently done before.
 *)
let give_back_shared config (bid : V.BorrowId.id) (env : C.env) : C.env =
  let give_back_shared_to_env_value ev : C.env_value =
    match ev with
    | C.Var (vid, destv) ->
        C.Var (vid, give_back_shared_to_value config bid destv)
    | C.Abs abs ->
        assert (config.mode = SymbolicMode);
        C.Abs (give_back_shared_to_abs config bid abs)
    | C.Frame -> C.Frame
  in
  List.map give_back_shared_to_env_value env

(** When copying values, we duplicate the shared borrows. This is tantamount
    to reborrowing the shared value. The following function applies this change
    to an environment by inserting a new borrow id in the set of borrows tracked
    by a shared value, referenced by the [original_bid] argument.
 *)
let reborrow_shared (config : C.config) (original_bid : V.BorrowId.id)
    (new_bid : V.BorrowId.id) (ctx : C.eval_ctx) : C.eval_ctx =
  let rec reborrow_in_value (v : V.typed_value) : V.typed_value =
    match v.V.value with
    | V.Concrete _ | V.Bottom | V.Symbolic _ -> v
    | V.Adt av ->
        let fields = List.map reborrow_in_value av.field_values in
        { v with value = Adt { av with field_values = fields } }
    | V.Borrow bc -> (
        match bc with
        | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> v
        | V.MutBorrow (bid, bv) ->
            {
              v with
              value = V.Borrow (V.MutBorrow (bid, reborrow_in_value bv));
            })
    | V.Loan lc -> (
        match lc with
        | V.MutLoan _ -> v
        | V.SharedLoan (bids, sv) ->
            (* Shared loan: check if the borrow id we are looking for is in the
               set of borrow ids. If yes, insert the new borrow id, otherwise
               explore inside the shared value *)
            if V.BorrowId.Set.mem original_bid bids then
              let bids' = V.BorrowId.Set.add new_bid bids in
              { v with value = V.Loan (V.SharedLoan (bids', sv)) }
            else
              {
                v with
                value = V.Loan (V.SharedLoan (bids, reborrow_in_value sv));
              })
  in
  let reborrow_in_ev (ev : C.env_value) : C.env_value =
    match ev with
    | C.Var (vid, v) -> C.Var (vid, reborrow_in_value v)
    | C.Abs abs ->
        assert (config.mode = SymbolicMode);
        C.Abs abs
    | C.Frame -> C.Frame
  in
  { ctx with env = List.map reborrow_in_ev ctx.env }

(** End a borrow identified by its borrow id in an environment
    
    First lookup the borrow in the environment and replace it with [Bottom].
    Then, check that there is an associated loan in the environment. When moving
    values, before putting putting the value in its destination, we get an
    intermediate state where some values are "outside" the environment and thus
    inaccessible. As [give_back_value] just performs a map for instance, we
    need to check independently that there is indeed a loan ready to receive
    the value we give back (note that we also have other invariants like: there
    is exacly one mutable loan associated to a mutable borrow, etc. but they
    are more easily maintained). Note that in theory, we shouldn't never reach a
    problematic state as the one we describe above, because when we move a value
    we need to end all the loans inside before moving it. Still, it is a very
    useful sanity check.
    Finally, give the values back.

    Of course, we end outer borrows before updating the target borrow if it
    proves necessary: this is controled by the [io] parameter. If it is [Inner],
    we allow ending inner borrows (without ending the outer borrows first),
    otherwise we only allow ending outer borrows.
 *)
let rec end_borrow_in_env (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (env0 : C.env) : C.env =
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match end_borrow_get_borrow_in_env config io l env0 with
  (* It is possible that we can't find a borrow in symbolic mode (ending
   * an abstraction may end several borrows at once *)
  | env, NotFound ->
      assert (config.mode = SymbolicMode);
      env
  (* If we found outer borrows: end those borrows first *)
  | env, Outer outer_borrows ->
      let env =
        match outer_borrows with
        | Borrows bids -> end_borrows_in_env config io bids env
        | Borrow bid -> end_borrow_in_env config io bid env
      in
      (* Retry to end the borrow *)
      end_borrow_in_env config io l env
  (* If found mut: give the value back *)
  | env, FoundMut tv ->
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l env));
      give_back_value config l tv env
  (* If found shared or inactivated mut: remove the borrow id from the loan set of the shared value *)
  | env, (FoundShared | FoundInactivatedMut) ->
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l env));
      give_back_shared config l env

and end_borrows_in_env (config : C.config) (io : inner_outer)
    (lset : V.BorrowId.Set.t) (env0 : C.env) : C.env =
  V.BorrowId.Set.fold
    (fun id env -> end_borrow_in_env config io id env)
    lset env0

(** Same as [end_borrow_in_env], but operating on evaluation contexts *)
let end_borrow (config : C.config) (io : inner_outer) (l : V.BorrowId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
  L.log#ldebug
    (lazy
      ("end_borrow " ^ V.BorrowId.to_string l ^ ": context before:\n"
     ^ eval_ctx_to_string ctx));
  let env = end_borrow_in_env config io l ctx.env in
  let ctx = { ctx with env } in
  L.log#ldebug
    (lazy
      ("end_borrow " ^ V.BorrowId.to_string l ^ ": context after:\n"
     ^ eval_ctx_to_string ctx));
  ctx

(** Same as [end_borrows_in_env], but operating on evaluation contexts *)
let end_borrows (config : C.config) (io : inner_outer) (lset : V.BorrowId.Set.t)
    (ctx : C.eval_ctx) : C.eval_ctx =
  L.log#ldebug
    (lazy
      ("end_borrows "
      ^ V.BorrowId.set_to_string lset
      ^ ": context before:\n" ^ eval_ctx_to_string ctx));
  let env = end_borrows_in_env config io lset ctx.env in
  let ctx = { ctx with env } in
  L.log#ldebug
    (lazy
      ("end_borrows "
      ^ V.BorrowId.set_to_string lset
      ^ ": context after:\n" ^ eval_ctx_to_string ctx));
  ctx

let end_outer_borrow config = end_borrow config Outer

let end_outer_borrows config = end_borrows config Outer

let end_inner_borrow config = end_borrow config Inner

let end_inner_borrows config = end_borrows config Inner

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates the shared loan to a mutable loan (we then update
    the borrow with another helper). Of course, the shared loan must contain
    exactly one borrow id (the one we give as parameter), otherwise we can't
    promote it. Also, the shared value mustn't contain any loan.

    The returned value (previously shared) is checked:
    - it mustn't contain loans
    - it mustn't contain [Bottom]
    - it mustn't contain inactivated borrows
    TODO: this kind of checks should be put in an auxiliary helper, because
    they are redundant
 *)
let promote_shared_loan_to_mut_loan (l : V.BorrowId.id) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
  (* Lookup the shared loan *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx.env with
  | V.MutLoan _ -> failwith "Expected a shared loan, found a mut loan"
  | V.SharedLoan (bids, sv) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      assert (V.BorrowId.Set.mem l bids && V.BorrowId.Set.cardinal bids = 1);
      (* We need to check that there aren't any loans in the value:
           we should have gotten rid of those already, but it is better
           to do a sanity check. *)
      assert (not (loans_in_value sv));
      (* Also need to check there isn't [Bottom] (this is actually an invariant *)
      assert (not (bottom_in_value sv));
      (* Update the loan content *)
      let env = update_loan ek l (V.MutLoan l) ctx.env in
      let ctx = { ctx with env } in
      (* Return *)
      (ctx, sv)

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates a shared borrow to a mutable borrow.
 *)
let promote_inactivated_borrow_to_mut_borrow (l : V.BorrowId.id)
    (borrowed_value : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Lookup the inactivated borrow - note that we don't go inside borrows/loans:
     there can't be inactivated borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  match lookup_borrow ek l ctx.env with
  | V.SharedBorrow _ | V.MutBorrow (_, _) ->
      failwith "Expected an inactivated mutable borrow"
  | V.InactivatedMutBorrow _ ->
      (* Update it *)
      let env = update_borrow ek l (V.MutBorrow (l, borrowed_value)) ctx.env in
      { ctx with env }

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let rec activate_inactivated_mut_borrow (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx.env with
  | V.MutLoan _ -> failwith "Unreachable"
  | V.SharedLoan (bids, sv) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         inactivated borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let ctx =
            match lc with
            | V.SharedLoan (bids, _) -> end_outer_borrows config bids ctx
            | V.MutLoan bid -> end_outer_borrow config bid ctx
          in
          (* Recursive call *)
          activate_inactivated_mut_borrow config io l ctx
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          L.log#ldebug
            (lazy
              ("activate_inactivated_mut_borrow: resulting value:\n"
             ^ V.show_typed_value sv));
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value sv));
          assert (not (inactivated_in_value sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = V.BorrowId.Set.remove l bids in
          let ctx = end_borrows config io bids ctx in
          (* Promote the loan *)
          let ctx, borrowed_value = promote_shared_loan_to_mut_loan l ctx in
          (* Promote the borrow - the value should have been checked by
             [promote_shared_loan_to_mut_loan]
          *)
          promote_inactivated_borrow_to_mut_borrow l borrowed_value ctx)

(** Paths *)

(** When we fail reading from or writing to a path, it might be because we
    need to update the environment by ending borrows, expanding symbolic
    values, etc. The following type is used to convey this information.
    
    TODO: compare with borrow_lres?
*)
type path_fail_kind =
  | FailSharedLoan of V.BorrowId.Set.t
      (** Failure because we couldn't go inside a shared loan *)
  | FailMutLoan of V.BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | FailInactivatedMutBorrow of V.BorrowId.id
      (** Failure because we couldn't go inside an inactivated mutable borrow
          (which should get activated) *)
  | FailSymbolic of (E.projection_elem * V.symbolic_proj_comp)
      (** Failure because we need to enter a symbolic value (and thus need to expand it) *)
  (* TODO: Remove the parentheses *)
  | FailBottom of (int * E.projection_elem * T.ety)
      (** Failure because we need to enter an any value - we can expand Bottom
          values if they are left values. We return the number of elements which
          were remaining in the path when we reached the error - this allows to
          properly update the Bottom value, if needs be.
       *)
  | FailBorrow of V.borrow_content
      (** We got stuck because we couldn't enter a borrow *)

(** Result of evaluating a path (reading from a path/writing to a path)
    
    Note that when we fail, we return information used to update the
    environment, as well as the 
*)
type 'a path_access_result = ('a, path_fail_kind) result
(** The result of reading from/writing to a place *)

type updated_read_value = { read : V.typed_value; updated : V.typed_value }

type projection_access = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  lookup_shared_borrows : bool;
}

(** Generic function to access (read/write) the value at the end of a projection.

    We return the (eventually) updated value, the value we read at the end of
    the place and the (eventually) updated environment.
 *)
let rec access_projection (access : projection_access) (env : C.env)
    (* Function to (eventually) update the value we find *)
      (update : V.typed_value -> V.typed_value) (p : E.projection)
    (v : V.typed_value) : (C.env * updated_read_value) path_access_result =
  (* For looking up/updating shared loans *)
  let ek : exploration_kind =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match p with
  | [] ->
      let nv = update v in
      (* Type checking *)
      if nv.ty <> v.ty then (
        L.log#lerror
          (lazy
            ("Not the same type:\n- nv.ty: " ^ T.show_ety nv.ty ^ "\n- v.ty: "
           ^ T.show_ety v.ty));
        failwith
          "Assertion failed: new value doesn't have the same type as its \
           destination");
      Ok (env, { read = v; updated = nv })
  | pe :: p' -> (
      (* Match on the projection element and the value *)
      match (pe, v.V.value, v.V.ty) with
      (* Field projection - ADTs *)
      | ( Field (ProjAdt (def_id, opt_variant_id), field_id),
          V.Adt adt,
          T.Adt (T.AdtId def_id', _, _) ) -> (
          assert (def_id = def_id');
          (* Check that the projection is consistent with the current value *)
          (match (opt_variant_id, adt.variant_id) with
          | None, None -> ()
          | Some vid, Some vid' -> if vid <> vid' then failwith "Unreachable"
          | _ -> failwith "Unreachable");
          (* Actually project *)
          let fv = T.FieldId.nth adt.field_values field_id in
          match access_projection access env update p' fv with
          | Error err -> Error err
          | Ok (env, res) ->
              (* Update the field value *)
              let nvalues =
                T.FieldId.update_nth adt.field_values field_id res.updated
              in
              let nadt = V.Adt { adt with V.field_values = nvalues } in
              let updated = { v with value = nadt } in
              Ok (env, { res with updated }))
      (* Tuples *)
      | Field (ProjTuple arity, field_id), V.Adt adt, T.Adt (T.Tuple, _, _) -> (
          assert (arity = List.length adt.field_values);
          let fv = T.FieldId.nth adt.field_values field_id in
          (* Project *)
          match access_projection access env update p' fv with
          | Error err -> Error err
          | Ok (env, res) ->
              (* Update the field value *)
              let nvalues =
                T.FieldId.update_nth adt.field_values field_id res.updated
              in
              let ntuple = V.Adt { adt with field_values = nvalues } in
              let updated = { v with value = ntuple } in
              Ok (env, { res with updated })
          (* If we reach Bottom, it may mean we need to expand an uninitialized
           * enumeration value *))
      | Field (ProjAdt (_, _), _), V.Bottom, _ ->
          Error (FailBottom (1 + List.length p', pe, v.ty))
      | Field (ProjTuple _, _), V.Bottom, _ ->
          Error (FailBottom (1 + List.length p', pe, v.ty))
      (* Symbolic value: needs to be expanded *)
      | _, Symbolic sp, _ ->
          (* Expand the symbolic value *)
          Error (FailSymbolic (pe, sp))
      (* Box dereferencement *)
      | ( DerefBox,
          Adt { variant_id = None; field_values = [ bv ] },
          T.Adt (T.Assumed T.Box, _, _) ) -> (
          (* We allow moving inside of boxes. In practice, this kind of
           * manipulations should happen only inside unsage code, so
           * it shouldn't happen due to user code, and we leverage it
           * when implementing box dereferencement for the concrete
           * interpreter *)
          match access_projection access env update p' bv with
          | Error err -> Error err
          | Ok (env, res) ->
              let nv =
                {
                  v with
                  value =
                    V.Adt { variant_id = None; field_values = [ res.updated ] };
                }
              in
              Ok (env, { res with updated = nv }))
      (* Borrows *)
      | Deref, V.Borrow bc, _ -> (
          match bc with
          | V.SharedBorrow bid ->
              (* Lookup the loan content, and explore from there *)
              if access.lookup_shared_borrows then
                match lookup_loan ek bid env with
                | V.MutLoan _ -> failwith "Expected a shared loan"
                | V.SharedLoan (bids, sv) -> (
                    (* Explore the shared value *)
                    match access_projection access env update p' sv with
                    | Error err -> Error err
                    | Ok (env, res) ->
                        (* Update the shared loan with the new value returned
                           by [access_projection] *)
                        let env =
                          update_loan ek bid
                            (V.SharedLoan (bids, res.updated))
                            env
                        in
                        (* Return - note that we don't need to update the borrow itself *)
                        Ok (env, { res with updated = v }))
              else Error (FailBorrow bc)
          | V.InactivatedMutBorrow bid -> Error (FailInactivatedMutBorrow bid)
          | V.MutBorrow (bid, bv) ->
              if access.enter_mut_borrows then
                match access_projection access env update p' bv with
                | Error err -> Error err
                | Ok (env, res) ->
                    let nv =
                      {
                        v with
                        value = V.Borrow (V.MutBorrow (bid, res.updated));
                      }
                    in
                    Ok (env, { res with updated = nv })
              else Error (FailBorrow bc))
      | _, V.Loan lc, _ -> (
          match lc with
          | V.MutLoan bid -> Error (FailMutLoan bid)
          | V.SharedLoan (bids, sv) ->
              (* If we can enter shared loan, we ignore the loan. Pay attention
                 to the fact that we need to reexplore the *whole* place (i.e,
                 we mustn't ignore the current projection element *)
              if access.enter_shared_loans then
                match access_projection access env update (pe :: p') sv with
                | Error err -> Error err
                | Ok (env, res) ->
                    let nv =
                      {
                        v with
                        value = V.Loan (V.SharedLoan (bids, res.updated));
                      }
                    in
                    Ok (env, { res with updated = nv })
              else Error (FailSharedLoan bids))
      | (_, (V.Concrete _ | V.Adt _ | V.Bottom | V.Borrow _), _) as r ->
          let pe, v, ty = r in
          let pe = "- pe: " ^ E.show_projection_elem pe in
          let v = "- v:\n" ^ V.show_value v in
          let ty = "- ty:\n" ^ T.show_ety ty in
          L.log#serror ("Inconsistent projection:\n" ^ pe ^ "\n" ^ v ^ "\n" ^ ty);
          failwith "Inconsistent projection")

(** Generic function to access (read/write) the value at a given place.

    We return the value we read at the place and the (eventually) updated
    environment, if we managed to access the place, or the precise reason
    why we failed.
 *)
let access_place (access : projection_access)
    (* Function to (eventually) update the value we find *)
      (update : V.typed_value -> V.typed_value) (p : E.place) (env : C.env) :
    (C.env * V.typed_value) path_access_result =
  (* Lookup the variable's value *)
  let value = C.env_lookup_var_value env p.var_id in
  (* Apply the projection *)
  match access_projection access env update p.projection value with
  | Error err -> Error err
  | Ok (env, res) ->
      (* Update the value *)
      let env = C.env_update_var_value env p.var_id res.updated in
      (* Return *)
      Ok (env, res.read)

type access_kind =
  | Read  (** We can go inside borrows and loans *)
  | Write  (** Don't enter shared borrows or shared loans *)
  | Move  (** Don't enter borrows or loans *)

let access_kind_to_projection_access (access : access_kind) : projection_access
    =
  match access with
  | Read ->
      {
        enter_shared_loans = true;
        enter_mut_borrows = true;
        lookup_shared_borrows = true;
      }
  | Write ->
      {
        enter_shared_loans = false;
        enter_mut_borrows = true;
        lookup_shared_borrows = false;
      }
  | Move ->
      {
        enter_shared_loans = false;
        enter_mut_borrows = false;
        lookup_shared_borrows = false;
      }

(** Read the value at a given place *)
let read_place (config : C.config) (access : access_kind) (p : E.place)
    (ctx : C.eval_ctx) : V.typed_value path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function is the identity *)
  let update v = v in
  match access_place access update p ctx.env with
  | Error err -> Error err
  | Ok (env1, read_value) ->
      (* Note that we ignore the new environment: it should be the same as the
         original one.
      *)
      if config.check_invariants then
        if env1 <> ctx.env then (
          let msg =
            "Unexpected environment update:\nNew environment:\n"
            ^ C.show_env env1 ^ "\n\nOld environment:\n" ^ C.show_env ctx.env
          in
          L.log#serror msg;
          failwith "Unexpected environment update");
      Ok read_value

let read_place_unwrap (config : C.config) (access : access_kind) (p : E.place)
    (ctx : C.eval_ctx) : V.typed_value =
  match read_place config access p ctx with
  | Error _ -> failwith "Unreachable"
  | Ok v -> v

(** Update the value at a given place *)
let write_place (_config : C.config) (access : access_kind) (p : E.place)
    (nv : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function substitutes the value with the new value *)
  let update _ = nv in
  match access_place access update p ctx.env with
  | Error err -> Error err
  | Ok (env, _) ->
      (* We ignore the read value *)
      Ok { ctx with env }

let write_place_unwrap (config : C.config) (access : access_kind) (p : E.place)
    (nv : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx =
  match write_place config access p nv ctx with
  | Error _ -> failwith "Unreachable"
  | Ok ctx -> ctx

(** Compute an expanded ADT bottom value *)
let compute_expanded_bottom_adt_value (tyctx : T.type_def list)
    (def_id : T.TypeDefId.id) (opt_variant_id : T.VariantId.id option)
    (regions : T.erased_region list) (types : T.ety list) : V.typed_value =
  (* Lookup the definition and check if it is an enumeration - it
     should be an enumeration if and only if the projection element
     is a field projection with *some* variant id. Retrieve the list
     of fields at the same time. *)
  let def = T.TypeDefId.nth tyctx def_id in
  assert (List.length regions = List.length def.T.region_params);
  (* Compute the field types *)
  let field_types =
    Subst.type_def_get_instantiated_field_type def opt_variant_id types
  in
  (* Initialize the expanded value *)
  let fields =
    List.map
      (fun ty : V.typed_value -> ({ V.value = V.Bottom; ty } : V.typed_value))
      field_types
  in
  let av = V.Adt { variant_id = opt_variant_id; field_values = fields } in
  let ty = T.Adt (T.AdtId def_id, regions, types) in
  { V.value = av; V.ty }

(** Compute an expanded tuple bottom value *)
let compute_expanded_bottom_tuple_value (field_types : T.ety list) :
    V.typed_value =
  (* Generate the field values *)
  let fields =
    List.map (fun ty : V.typed_value -> { V.value = Bottom; ty }) field_types
  in
  let v = V.Adt { variant_id = None; field_values = fields } in
  let ty = T.Adt (T.Tuple, [], field_types) in
  { V.value = v; V.ty }

(** Auxiliary helper to expand [Bottom] values.

    During compilation, rustc desaggregates the ADT initializations. The
    consequence is that the following rust code:
    ```
    let x = Cons a b;
    ```

    Looks like this in MIR:
    ```
    (x as Cons).0 = a;
    (x as Cons).1 = b;
    set_discriminant(x, 0); // If `Cons` is the variant of index 0
    ```

    The consequence is that we may sometimes need to write fields to values
    which are currently [Bottom]. When doing this, we first expand the value
    to, say, [Cons Bottom Bottom] (note that field projection contains information
    about which variant we should project to, which is why we *can* set the
    variant index when writing one of its fields).
*)
let expand_bottom_value_from_projection (config : C.config)
    (access : access_kind) (p : E.place) (remaining_pes : int)
    (pe : E.projection_elem) (ty : T.ety) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Debugging *)
  L.log#ldebug
    (lazy
      ("expand_bottom_value_from_projection:\n" ^ "pe: "
     ^ E.show_projection_elem pe ^ "\n" ^ "ty: " ^ T.show_ety ty));
  (* Prepare the update: we need to take the proper prefix of the place
     during whose evaluation we got stuck *)
  let projection' =
    fst
      (Utilities.list_split_at p.projection
         (List.length p.projection - remaining_pes))
  in
  let p' = { p with projection = projection' } in
  (* Compute the expanded value.
     The type of the [Bottom] value should be a tuple or an ADT.
     Note that the projection element we got stuck at should be a
     field projection, and gives the variant id if the [Bottom] value
     is an enumeration value.
     Also, the expanded value should be the proper ADT variant or a tuple
     with the proper arity, with all the fields initialized to [Bottom]
  *)
  let nv =
    match (pe, ty) with
    (* "Regular" ADTs *)
    | ( Field (ProjAdt (def_id, opt_variant_id), _),
        T.Adt (T.AdtId def_id', regions, types) ) ->
        assert (def_id = def_id');
        compute_expanded_bottom_adt_value ctx.type_context def_id opt_variant_id
          regions types
    (* Tuples *)
    | Field (ProjTuple arity, _), T.Adt (T.Tuple, [], tys) ->
        assert (arity = List.length tys);
        (* Generate the field values *)
        compute_expanded_bottom_tuple_value tys
    | _ ->
        failwith
          ("Unreachable: " ^ E.show_projection_elem pe ^ ", " ^ T.show_ety ty)
  in
  (* Update the context by inserting the expanded value at the proper place *)
  match write_place config access p' nv ctx with
  | Ok ctx -> ctx
  | Error _ -> failwith "Unreachable"

(** Update the environment to be able to read a place.

    When reading a place, we may be stuck along the way because some value
    is borrowed, we reach a symbolic value, etc. In this situation [read_place]
    fails while returning precise information about the failure. This function
    uses this information to update the environment (by ending borrows,
    expanding symbolic values) until we manage to fully read the place.
 *)
let rec update_ctx_along_read_place (config : C.config) (access : access_kind)
    (p : E.place) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Attempt to read the place: if it fails, update the environment and retry *)
  match read_place config access p ctx with
  | Ok _ -> ctx
  | Error err ->
      let ctx =
        match err with
        | FailSharedLoan bids -> end_outer_borrows config bids ctx
        | FailMutLoan bid -> end_outer_borrow config bid ctx
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config Outer bid ctx
        | FailSymbolic (_pe, _sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (_, _, _) ->
            (* We can't expand [Bottom] values while reading them *)
            failwith "Found [Bottom] while reading a place"
        | FailBorrow _ -> failwith "Could not read a borrow"
      in
      update_ctx_along_read_place config access p ctx

(** Update the environment to be able to write to a place.

    See [update_env_alond_read_place].
*)
let rec update_ctx_along_write_place (config : C.config) (access : access_kind)
    (p : E.place) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Attempt to *read* (yes, "read": we check the access to the place, and
     write to it later) the place: if it fails, update the environment and retry *)
  match read_place config access p ctx with
  | Ok _ -> ctx
  | Error err ->
      let ctx =
        match err with
        | FailSharedLoan bids -> end_outer_borrows config bids ctx
        | FailMutLoan bid -> end_outer_borrow config bid ctx
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config Outer bid ctx
        | FailSymbolic (_pe, _sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (remaining_pes, pe, ty) ->
            (* Expand the [Bottom] value *)
            expand_bottom_value_from_projection config access p remaining_pes pe
              ty ctx
        | FailBorrow _ -> failwith "Could not write to a borrow"
      in
      update_ctx_along_write_place config access p ctx

exception UpdateCtx of C.eval_ctx
(** Small utility used to break control-flow *)

(** End the loans at a given place: read the value, if it contains a loan,
    end this loan, repeat.

    This is used when reading, borrowing, writing to a value. We typically
    first call [update_ctx_along_read_place] or [update_ctx_along_write_place]
    to get access to the value, then call this function to "prepare" the value:
    when moving values, we can't move a value which contains loans and thus need
    to end them, etc.
 *)
let rec end_loans_at_place (config : C.config) (access : access_kind)
    (p : E.place) (ctx : C.eval_ctx) : C.eval_ctx =
  (* First, retrieve the value *)
  match read_place config access p ctx with
  | Error _ -> failwith "Unreachable"
  | Ok v -> (
      (* Explore the value to check if we need to update the context.
         In particular, we need to end the proper loans in the value.
         Also, we fail if the value contains any [Bottom].

         We use exceptions to make it handy: whenever we update the
         context, we raise an exception wrapping the updated context.
      *)
      let rec inspect_update (v : V.typed_value) : unit =
        match v.V.value with
        | V.Concrete _ -> ()
        | V.Bottom -> ()
        | V.Symbolic _ ->
            (* Nothing to do for symbolic values - note that if the value needs
               to be copied, etc. we perform additional checks later *)
            ()
        | V.Adt adt -> List.iter inspect_update adt.field_values
        | V.Borrow bc -> (
            match bc with
            | V.SharedBorrow _ -> ()
            | V.MutBorrow (_, tv) -> inspect_update tv
            | V.InactivatedMutBorrow bid ->
                (* We need to activate inactivated borrows *)
                let ctx =
                  activate_inactivated_mut_borrow config Inner bid ctx
                in
                raise (UpdateCtx ctx))
        | V.Loan lc -> (
            match lc with
            | V.SharedLoan (bids, ty) -> (
                (* End the loans if we need a modification access, otherwise dive into
                   the shared value *)
                match access with
                | Read -> inspect_update ty
                | Write | Move ->
                    let ctx = end_outer_borrows config bids ctx in
                    raise (UpdateCtx ctx))
            | V.MutLoan bid ->
                (* We always need to end mutable borrows *)
                let ctx = end_outer_borrow config bid ctx in
                raise (UpdateCtx ctx))
      in
      (* Inspect the value and update the context while doing so.
         If the context gets updated: perform a recursive call (many things
         may have been updated in the context: we need to re-read the value
         at place [p] - and this value may actually not be accessible
         anymore...)
      *)
      try
        inspect_update v;
        (* No context update required: return the current context *)
        ctx
      with UpdateCtx ctx ->
        (* The context was updated: do a recursive call to reinspect the value *)
        end_loans_at_place config access p ctx)

(** Drop (end) all the loans and borrows at a given place, which should be
    seen as an l-value (we will write to it later, but need to drop the borrows
    before writing).

    We start by only dropping the borrows, then we end the loans. The reason
    is that some loan we find may be borrowed by another part of the subvalue.
    In order to correctly handle the "outer borrow" priority (we should end
    the outer borrows first) which is not really applied here (we are preparing
    the value for override: we can end the borrows inside, without ending the
    borrows we traversed to actually access the value) we first end the borrows
    we find in the place, to make sure all the "local" loans are taken care of.
    Then, if we find a loan, it means it is "externally" borrowed (the associated
    borrow is not in a subvalue of the place under inspection).
    Also note that whenever we end a loan, we might propagate back a value inside
    the place under inspection: we must re-end all the borrows we find there,
    before reconsidering loans.

    Repeat:
    - read the value at a given place
    - as long as we find a loan or a borrow, end it

    This is used to drop values (when we need to write to a place, we first
    drop the value there to properly propagate back values which are not/can't
    be borrowed anymore).
 *)
let rec drop_borrows_loans_at_lplace (config : C.config) (p : E.place)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* We do something similar to [end_loans_at_place].
     First, retrieve the value *)
  match read_place config Write p ctx with
  | Error _ -> failwith "Unreachable"
  | Ok v -> (
      (* Explore the value to check if we need to update the environment.

         Note that we can end the borrows which are inside the value (while the
         value itself might be inside a borrow/loan: we are thus ending inner
         borrows). Because a loan inside the value may be linked to a borrow
         somewhere else *also inside* the value (it's possible with adts),
         we first end all the borrows we find - by using [Inner] to allow
         ending inner borrows - then end all the loans we find. It is really
         important to do this in two steps: the borrow linked to a loan may
         be inside the value at place p, in which case this borrow may be
         an inner borrow that we *can* end, but it may also be outside this
         value, in which case we need to end all the outer borrows first...
         Also, whenever the environment is updated, we need to re-inspect
         the value at place p *in two steps* again (end borrows, then end loans).

         We use exceptions to make it handy.
      *)
      let rec inspect_update (end_loans : bool) (v : V.typed_value) : unit =
        match v.V.value with
        | V.Concrete _ -> ()
        | V.Bottom ->
            (* Note that we are going to *write* to the value: it is ok if this
               value contains [Bottom] - and actually we introduce some
               occurrences of [Bottom] by ending borrows *)
            ()
        | V.Symbolic _ ->
            (* Nothing to do for symbolic values - TODO: not sure *)
            raise Unimplemented
        | V.Adt adt -> List.iter (inspect_update end_loans) adt.field_values
        | V.Borrow bc -> (
            assert (not end_loans);

            (* Sanity check *)
            (* We need to end all borrows. Note that we ignore the outer borrows
               when ending the borrows we find here (we call [end_inner_borrow(s)]:
               the value at place p might be below a borrow/loan. Note however
               that the borrow we found here is an outer borrow, if we restrain
               ourselves at the value at place p.
            *)
            match bc with
            | V.SharedBorrow bid | V.MutBorrow (bid, _) ->
                L.log#ldebug
                  (lazy
                    ("drop_borrows_loans_at_lplace: dropping "
                   ^ V.BorrowId.to_string bid));
                raise (UpdateCtx (end_inner_borrow config bid ctx))
            | V.InactivatedMutBorrow bid ->
                L.log#ldebug
                  (lazy
                    ("drop_borrows_loans_at_lplace: activating "
                   ^ V.BorrowId.to_string bid));
                (* We need to activate inactivated borrows - later, we will
                 * actually end it *)
                let ctx =
                  activate_inactivated_mut_borrow config Inner bid ctx
                in
                raise (UpdateCtx ctx))
        | V.Loan lc ->
            if
              (* If we can, end the loans, otherwise ignore: keep for later *)
              end_loans
            then
              (* We need to end all loans. Note that as all the borrows inside
                 the value at place p should already have ended, the borrows
                 associated to the loans we find here should be borrows from
                 outside this value: we need to call [end_outer_borrow(s)]
                 (we can't ignore outer borrows this time).
              *)
              match lc with
              | V.SharedLoan (bids, _) ->
                  raise (UpdateCtx (end_outer_borrows config bids ctx))
              | V.MutLoan bid ->
                  raise (UpdateCtx (end_outer_borrow config bid ctx))
            else ()
      in
      (* Inspect the value and update the context while doing so.
         If the context gets updated: perform a recursive call (many things
         may have been updated in the context: first we need to retrieve the
         proper updated value - and this value may actually not be accessible
         anymore
      *)
      try
        (* Inspect the value: end the borrows only *)
        inspect_update false v;
        (* Inspect the value: end the loans *)
        inspect_update true v;
        (* No context update required: return the current context *)
        ctx
      with UpdateCtx ctx -> drop_borrows_loans_at_lplace config p ctx)

(** Copy a value, and return the resulting value.

    Note that copying values might update the context. For instance, when
    copying shared borrows, we need to insert new shared borrows in the context.
 *)
let rec copy_value (config : C.config) (ctx : C.eval_ctx) (v : V.typed_value) :
    C.eval_ctx * V.typed_value =
  match v.V.value with
  | V.Concrete _ -> (ctx, v)
  | V.Adt av ->
      (* Sanity check *)
      (match v.V.ty with
      | T.Adt (T.Assumed _, _, _) -> failwith "Can't copy an assumed value"
      | T.Adt ((T.AdtId _ | T.Tuple), _, _) -> () (* Ok *)
      | _ -> failwith "Unreachable");
      let ctx, fields =
        List.fold_left_map (copy_value config) ctx av.field_values
      in
      (ctx, { v with V.value = V.Adt { av with field_values = fields } })
  | V.Bottom -> failwith "Can't copy ⊥"
  | V.Borrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | SharedBorrow bid ->
          let ctx, bid' = C.fresh_borrow_id ctx in
          let ctx = reborrow_shared config bid bid' ctx in
          (ctx, { v with V.value = V.Borrow (SharedBorrow bid') })
      | MutBorrow (_, _) -> failwith "Can't copy a mutable borrow"
      | V.InactivatedMutBorrow _ ->
          failwith "Can't copy an inactivated mut borrow")
  | V.Loan lc -> (
      (* We can only copy shared loans *)
      match lc with
      | V.MutLoan _ -> failwith "Can't copy a mutable loan"
      | V.SharedLoan (_, sv) -> copy_value config ctx sv)
  | V.Symbolic _sp ->
      (* TODO: check that the value is copyable *)
      raise Unimplemented

(** Convert a constant operand value to a typed value *)
let constant_value_to_typed_value (ctx : C.eval_ctx) (ty : T.ety)
    (cv : E.operand_constant_value) : V.typed_value =
  (* Check the type while converting *)
  match (ty, cv) with
  (* Unit *)
  | T.Adt (T.Tuple, [], []), Unit -> mk_unit_value
  (* Adt with one variant and no fields *)
  | T.Adt (T.AdtId def_id, [], []), ConstantAdt def_id' ->
      assert (def_id = def_id');
      (* Check that the adt definition only has one variant with no fields,
         compute the variant id at the same time. *)
      let def = T.TypeDefId.nth ctx.type_context def_id in
      assert (List.length def.region_params = 0);
      assert (List.length def.type_params = 0);
      let variant_id =
        match def.kind with
        | Struct fields ->
            assert (List.length fields = 0);
            None
        | Enum variants ->
            assert (List.length variants = 1);
            let variant_id = T.VariantId.zero in
            let variant = T.VariantId.nth variants variant_id in
            assert (List.length variant.fields = 0);
            Some variant_id
      in
      let value = V.Adt { variant_id; field_values = [] } in
      { value; ty }
  (* Scalar, boolean... *)
  | T.Bool, ConstantValue (Bool v) -> { V.value = V.Concrete (Bool v); ty }
  | T.Char, ConstantValue (Char v) -> { V.value = V.Concrete (Char v); ty }
  | T.Str, ConstantValue (String v) -> { V.value = V.Concrete (String v); ty }
  | T.Integer int_ty, ConstantValue (V.Scalar v) ->
      (* Check the type and the ranges *)
      assert (int_ty == v.int_ty);
      assert (check_scalar_value_in_range v);
      { V.value = V.Concrete (V.Scalar v); ty }
  (* Remaining cases (invalid) - listing as much as we can on purpose
     (allows to catch errors at compilation if the definitions change) *)
  | _, Unit | _, ConstantAdt _ | _, ConstantValue _ ->
      failwith "Improperly typed constant value"

(** Small utility *)
let prepare_rplace (config : C.config) (access : access_kind) (p : E.place)
    (ctx : C.eval_ctx) : C.eval_ctx * V.typed_value =
  let ctx = update_ctx_along_read_place config access p ctx in
  let ctx = end_loans_at_place config access p ctx in
  let v = read_place_unwrap config access p ctx in
  (ctx, v)

(** Evaluate an operand. *)
let eval_operand (config : C.config) (ctx : C.eval_ctx) (op : E.operand) :
    C.eval_ctx * V.typed_value =
  (* Debug *)
  L.log#ldebug
    (lazy
      ("eval_operand:\n- ctx:\n" ^ eval_ctx_to_string ctx ^ "\n\n- op:\n"
     ^ operand_to_string ctx op ^ "\n"));
  (* Evaluate *)
  match op with
  | Expressions.Constant (ty, cv) ->
      let v = constant_value_to_typed_value ctx ty cv in
      (ctx, v)
  | Expressions.Copy p ->
      (* Access the value *)
      let access = Read in
      let ctx, v = prepare_rplace config access p ctx in
      (* Copy the value *)
      L.log#ldebug (lazy ("Value to copy:\n" ^ typed_value_to_string ctx v));
      assert (not (bottom_in_value v));
      copy_value config ctx v
  | Expressions.Move p -> (
      (* Access the value *)
      let access = Move in
      let ctx, v = prepare_rplace config access p ctx in
      (* Move the value *)
      L.log#ldebug (lazy ("Value to move:\n" ^ typed_value_to_string ctx v));
      assert (not (bottom_in_value v));
      let bottom : V.typed_value = { V.value = Bottom; ty = v.ty } in
      match write_place config access p bottom ctx with
      | Error _ -> failwith "Unreachable"
      | Ok ctx -> (ctx, v))

(** Evaluate several operands. *)
let eval_operands (config : C.config) (ctx : C.eval_ctx) (ops : E.operand list)
    : C.eval_ctx * V.typed_value list =
  List.fold_left_map (fun ctx op -> eval_operand config ctx op) ctx ops

let eval_two_operands (config : C.config) (ctx : C.eval_ctx) (op1 : E.operand)
    (op2 : E.operand) : C.eval_ctx * V.typed_value * V.typed_value =
  match eval_operands config ctx [ op1; op2 ] with
  | ctx, [ v1; v2 ] -> (ctx, v1, v2)
  | _ -> failwith "Unreachable"

let eval_unary_op (config : C.config) (ctx : C.eval_ctx) (unop : E.unop)
    (op : E.operand) : (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operand *)
  let ctx, v = eval_operand config ctx op in
  (* Apply the unop *)
  match (unop, v.V.value) with
  | E.Not, V.Concrete (Bool b) ->
      Ok (ctx, { v with V.value = V.Concrete (Bool (not b)) })
  | E.Neg, V.Concrete (V.Scalar sv) -> (
      let i = Z.neg sv.V.value in
      match mk_scalar sv.int_ty i with
      | Error _ -> Error Panic
      | Ok sv -> Ok (ctx, { v with V.value = V.Concrete (V.Scalar sv) }))
  | (E.Not | E.Neg), Symbolic _ -> raise Unimplemented (* TODO *)
  | _ -> failwith "Invalid value for unop"

let eval_binary_op (config : C.config) (ctx : C.eval_ctx) (binop : E.binop)
    (op1 : E.operand) (op2 : E.operand) :
    (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operands *)
  let ctx, v1, v2 = eval_two_operands config ctx op1 op2 in
  if
    (* Binary operations only apply on integer values, but when we check for
     * equality *)
    binop = Eq || binop = Ne
  then (
    (* Equality/inequality check is primitive only on primitive types *)
    assert (v1.ty = v2.ty);
    let b = v1 = v2 in
    Ok (ctx, { V.value = V.Concrete (Bool b); ty = T.Bool }))
  else
    match (v1.V.value, v2.V.value) with
    | V.Concrete (V.Scalar sv1), V.Concrete (V.Scalar sv2) -> (
        let res =
          (* There are binops which require the two operands to have the same
             type, and binops for which it is not the case.
             There are also binops which return booleans, and binops which
             return integers.
          *)
          match binop with
          | E.Lt | E.Le | E.Ge | E.Gt ->
              (* The two operands must have the same type and the result is a boolean *)
              assert (sv1.int_ty = sv2.int_ty);
              let b =
                match binop with
                | E.Lt -> Z.lt sv1.V.value sv2.V.value
                | E.Le -> Z.leq sv1.V.value sv2.V.value
                | E.Ge -> Z.geq sv1.V.value sv2.V.value
                | E.Gt -> Z.gt sv1.V.value sv2.V.value
                | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
                | E.BitOr | E.Shl | E.Shr | E.Ne | E.Eq ->
                    failwith "Unreachable"
              in
              Ok
                ({ V.value = V.Concrete (Bool b); ty = T.Bool } : V.typed_value)
          | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
          | E.BitOr -> (
              (* The two operands must have the same type and the result is an integer *)
              assert (sv1.int_ty = sv2.int_ty);
              let res =
                match binop with
                | E.Div ->
                    if sv2.V.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.div sv1.V.value sv2.V.value)
                | E.Rem ->
                    (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                    if sv2.V.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.rem sv1.V.value sv2.V.value)
                | E.Add -> mk_scalar sv1.int_ty (Z.add sv1.V.value sv2.V.value)
                | E.Sub -> mk_scalar sv1.int_ty (Z.sub sv1.V.value sv2.V.value)
                | E.Mul -> mk_scalar sv1.int_ty (Z.mul sv1.V.value sv2.V.value)
                | E.BitXor -> raise Unimplemented
                | E.BitAnd -> raise Unimplemented
                | E.BitOr -> raise Unimplemented
                | E.Lt | E.Le | E.Ge | E.Gt | E.Shl | E.Shr | E.Ne | E.Eq ->
                    failwith "Unreachable"
              in
              match res with
              | Error err -> Error err
              | Ok sv ->
                  Ok
                    {
                      V.value = V.Concrete (V.Scalar sv);
                      ty = Integer sv1.int_ty;
                    })
          | E.Shl | E.Shr -> raise Unimplemented
          | E.Ne | E.Eq -> failwith "Unreachable"
        in
        match res with Error _ -> Error Panic | Ok v -> Ok (ctx, v))
    | _ -> failwith "Invalid inputs for binop"

(** Evaluate an rvalue in a given context: return the updated context and
    the computed value
*)
let eval_rvalue (config : C.config) (ctx : C.eval_ctx) (rvalue : E.rvalue) :
    (C.eval_ctx * V.typed_value) eval_result =
  match rvalue with
  | E.Use op -> Ok (eval_operand config ctx op)
  | E.Ref (p, bkind) -> (
      match bkind with
      | E.Shared | E.TwoPhaseMut ->
          (* Access the value *)
          let access = if bkind = E.Shared then Read else Write in
          let ctx, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - simply a shared borrow with a fresh id *)
          let ctx, bid = C.fresh_borrow_id ctx in
          (* Note that the reference is *mutable* if we do a two-phase borrow *)
          let rv_ty =
            T.Ref (T.Erased, v.ty, if bkind = E.Shared then Shared else Mut)
          in
          let bc =
            if bkind = E.Shared then V.SharedBorrow bid
            else V.InactivatedMutBorrow bid
          in
          let rv : V.typed_value = { V.value = V.Borrow bc; ty = rv_ty } in
          (* Compute the value with which to replace the value at place p *)
          let nv =
            match v.V.value with
            | V.Loan (V.SharedLoan (bids, sv)) ->
                (* Shared loan: insert the new borrow id *)
                let bids1 = V.BorrowId.Set.add bid bids in
                { v with V.value = V.Loan (V.SharedLoan (bids1, sv)) }
            | _ ->
                (* Not a shared loan: add a wrapper *)
                let v' =
                  V.Loan (V.SharedLoan (V.BorrowId.Set.singleton bid, v))
                in
                { v with V.value = v' }
          in
          (* Update the value in the context *)
          let ctx = write_place_unwrap config access p nv ctx in
          (* Return *)
          Ok (ctx, rv)
      | E.Mut ->
          (* Access the value *)
          let access = Write in
          let ctx, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
          let ctx, bid = C.fresh_borrow_id ctx in
          let rv_ty = T.Ref (T.Erased, v.ty, Mut) in
          let rv : V.typed_value =
            { V.value = V.Borrow (V.MutBorrow (bid, v)); ty = rv_ty }
          in
          (* Compute the value with which to replace the value at place p *)
          let nv = { v with V.value = V.Loan (V.MutLoan bid) } in
          (* Update the value in the context *)
          let ctx = write_place_unwrap config access p nv ctx in
          (* Return *)
          Ok (ctx, rv))
  | E.UnaryOp (unop, op) -> eval_unary_op config ctx unop op
  | E.BinaryOp (binop, op1, op2) -> eval_binary_op config ctx binop op1 op2
  | E.Discriminant p -> (
      (* Note that discriminant values have type `isize` *)
      (* Access the value *)
      let access = Read in
      let ctx, v = prepare_rplace config access p ctx in
      match v.V.value with
      | Adt av -> (
          match av.variant_id with
          | None ->
              failwith
                "Invalid input for `discriminant`: structure instead of enum"
          | Some variant_id -> (
              let id = Z.of_int (T.VariantId.to_int variant_id) in
              match mk_scalar Isize id with
              | Error _ ->
                  failwith "Disciminant id out of range"
                  (* Should really never happen *)
              | Ok sv ->
                  Ok
                    ( ctx,
                      { V.value = V.Concrete (V.Scalar sv); ty = Integer Isize }
                    )))
      | _ -> failwith "Invalid input for `discriminant`")
  | E.Aggregate (aggregate_kind, ops) -> (
      (* Evaluate the operands *)
      let ctx, values = eval_operands config ctx ops in
      (* Match on the aggregate kind *)
      match aggregate_kind with
      | E.AggregatedTuple ->
          let tys = List.map (fun (v : V.typed_value) -> v.V.ty) values in
          let v = V.Adt { variant_id = None; field_values = values } in
          let ty = T.Adt (T.Tuple, [], tys) in
          Ok (ctx, { V.value = v; ty })
      | E.AggregatedAdt (def_id, opt_variant_id, regions, types) ->
          (* Sanity checks *)
          let type_def = C.ctx_lookup_type_def ctx def_id in
          assert (List.length type_def.region_params = List.length regions);
          let expected_field_types =
            Subst.ctx_adt_get_instantiated_field_types ctx def_id opt_variant_id
              types
          in
          assert (
            expected_field_types
            = List.map (fun (v : V.typed_value) -> v.V.ty) values);
          (* Construct the value *)
          let av : V.adt_value =
            { V.variant_id = opt_variant_id; V.field_values = values }
          in
          let aty = T.Adt (T.AdtId def_id, regions, types) in
          Ok (ctx, { V.value = Adt av; ty = aty }))

(** Result of evaluating a statement - TODO: add prefix *)
type statement_eval_res = Unit | Break of int | Continue of int | Return

(** Small utility.
    
    Prepare a place which is to be used as the destination of an assignment:
    update the environment along the paths, end the borrows and loans at
    this place, etc.

    Return the updated context and the (updated) value at the end of the
    place. This value should not contain any loan or borrow (and we check
    it is the case). Note that it is very likely to contain [Bottom] values.
 *)
let prepare_lplace (config : C.config) (p : E.place) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
  (* TODO *)
  let access = Write in
  let ctx = update_ctx_along_write_place config access p ctx in
  (* End the borrows and loans, starting with the borrows *)
  let ctx = drop_borrows_loans_at_lplace config p ctx in
  (* Read the value and check it *)
  let v = read_place_unwrap config access p ctx in
  (* Sanity checks *)
  assert (not (loans_in_value v));
  assert (not (borrows_in_value v));
  (* Return *)
  (ctx, v)

(** Read the value at a given place.
    As long as it is a loan, end the loan.
    This function doesn't perform a recursive exploration:
    it won't dive into the value to end all the inner
    loans (contrary to [drop_borrows_loans_at_lplace] for
    instance).
 *)
let rec end_loan_exactly_at_place (config : C.config) (access : access_kind)
    (p : E.place) (ctx : C.eval_ctx) : C.eval_ctx =
  let v = read_place_unwrap config access p ctx in
  match v.V.value with
  | V.Loan (V.SharedLoan (bids, _)) ->
      let ctx = end_borrows config Outer bids ctx in
      end_loan_exactly_at_place config access p ctx
  | V.Loan (V.MutLoan bid) ->
      let ctx = end_borrow config Outer bid ctx in
      end_loan_exactly_at_place config access p ctx
  | _ -> ctx

(** Updates the discriminant of a value at a given place.

    There are two situations:
    - either the discriminant is already the proper one (in which case we
      don't do anything)
    - or it is not the proper one (because the variant is not the proper
      one, or the value is actually [Bottom] - this happens when
      initializing ADT values), in which case we replace the value with
      a variant with all its fields set to [Bottom].
      For instance, something like: `Cons Bottom Bottom`.
 *)
let set_discriminant (config : C.config) (ctx : C.eval_ctx) (p : E.place)
    (variant_id : T.VariantId.id) :
    (C.eval_ctx * statement_eval_res) eval_result =
  (* Access the value *)
  let access = Write in
  let ctx = update_ctx_along_read_place config access p ctx in
  let ctx = end_loan_exactly_at_place config access p ctx in
  let v = read_place_unwrap config access p ctx in
  (* Update the value *)
  match (v.V.ty, v.V.value) with
  | T.Adt (T.AdtId def_id, regions, types), V.Adt av -> (
      (* There are two situations:
         - either the discriminant is already the proper one (in which case we
           don't do anything)
         - or it is not the proper one, in which case we replace the value with
           a variant with all its fields set to [Bottom]
      *)
      match av.variant_id with
      | None -> failwith "Found a struct value while expected an enum"
      | Some variant_id' ->
          if variant_id' = variant_id then (* Nothing to do *)
            Ok (ctx, Unit)
          else
            (* Replace the value *)
            let bottom_v =
              compute_expanded_bottom_adt_value ctx.type_context def_id
                (Some variant_id) regions types
            in
            let ctx = write_place_unwrap config access p bottom_v ctx in
            Ok (ctx, Unit))
  | T.Adt (T.AdtId def_id, regions, types), V.Bottom ->
      let bottom_v =
        compute_expanded_bottom_adt_value ctx.type_context def_id
          (Some variant_id) regions types
      in
      let ctx = write_place_unwrap config access p bottom_v ctx in
      Ok (ctx, Unit)
  | _, V.Symbolic _ ->
      assert (config.mode = SymbolicMode);
      (* TODO *) raise Unimplemented
  | _, (V.Adt _ | V.Bottom) -> failwith "Inconsistent state"
  | _, (V.Concrete _ | V.Borrow _ | V.Loan _) -> failwith "Unexpected value"

(** Push a frame delimiter in the context's environment *)
let ctx_push_frame (ctx : C.eval_ctx) : C.eval_ctx =
  { ctx with env = Frame :: ctx.env }

(** Drop a value at a given place *)
let drop_value (config : C.config) (ctx : C.eval_ctx) (p : E.place) : C.eval_ctx
    =
  L.log#ldebug (lazy ("drop_value: place: " ^ place_to_string ctx p));
  (* Prepare the place (by ending the loans, then the borrows) *)
  let ctx, v = prepare_lplace config p ctx in
  (* Replace the value with [Bottom] *)
  let nv = { v with value = V.Bottom } in
  let ctx = write_place_unwrap config Write p nv ctx in
  ctx

(** Small helper: compute the type of the return value for a specific
    instantiation of a non-local function.
 *)
let get_non_local_function_return_type (fid : A.assumed_fun_id)
    (region_params : T.erased_region list) (type_params : T.ety list) : T.ety =
  match (fid, region_params, type_params) with
  | A.BoxNew, [], [ bty ] -> T.Adt (T.Assumed T.Box, [], [ bty ])
  | A.BoxDeref, [], [ bty ] -> T.Ref (T.Erased, bty, T.Shared)
  | A.BoxDerefMut, [], [ bty ] -> T.Ref (T.Erased, bty, T.Mut)
  | A.BoxFree, [], [ _ ] -> mk_unit_ty
  | _ -> failwith "Inconsistent state"

(** Pop the current frame.
    
    Drop all the local variables but the return variable, move the return
    value out of the return variable, remove all the local variables (but not the
    abstractions!) from the context, remove the [Frame] indicator delimiting the
    current frame and return the return value and the updated context.
 *)
let ctx_pop_frame (config : C.config) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
  (* Debug *)
  L.log#ldebug (lazy ("ctx_pop_frame:\n" ^ eval_ctx_to_string ctx));
  (* Eval *)
  let ret_vid = V.VarId.zero in
  (* List the local variables, but the return variable *)
  let rec list_locals env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs _ :: env -> list_locals env
    | C.Var (var, _) :: env ->
        let locals = list_locals env in
        if var.index <> ret_vid then var.index :: locals else locals
    | C.Frame :: _ -> []
  in
  let locals = list_locals ctx.env in
  (* Debug *)
  L.log#ldebug
    (lazy
      ("ctx_pop_frame: locals to drop: ["
      ^ String.concat "," (List.map V.VarId.to_string locals)
      ^ "]"));
  (* Drop the local variables *)
  let ctx =
    List.fold_left
      (fun ctx lid -> drop_value config ctx (mk_place_from_var_id lid))
      ctx locals
  in
  (* Debug *)
  L.log#ldebug
    (lazy
      ("ctx_pop_frame: after dropping local variables:\n"
     ^ eval_ctx_to_string ctx));
  (* Move the return value out of the return variable *)
  let ctx, ret_value =
    eval_operand config ctx (E.Move (mk_place_from_var_id ret_vid))
  in
  (* Pop the frame *)
  let rec pop env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs abs :: env -> C.Abs abs :: pop env
    | C.Var (_, _) :: env -> pop env
    | C.Frame :: env -> env
  in
  let env = pop ctx.env in
  let ctx = { ctx with env } in
  (ctx, ret_value)

(** Assign a value to a given place *)
let assign_to_place (config : C.config) (ctx : C.eval_ctx) (v : V.typed_value)
    (p : E.place) : C.eval_ctx =
  (* Prepare the destination *)
  let ctx, _ = prepare_lplace config p ctx in
  (* Update the destination *)
  let ctx = write_place_unwrap config Write p v ctx in
  ctx

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_new (config : C.config) (region_params : T.erased_region list)
    (type_params : T.ety list) (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  (* Check and retrieve the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ ) ->
      (* Required type checking *)
      assert (input_value.V.ty = boxed_ty);

      (* Move the input value *)
      let ctx, moved_input_value =
        eval_operand config ctx
          (E.Move (mk_place_from_var_id input_var.C.index))
      in

      (* Create the box value *)
      let box_ty = T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) in
      let box_v =
        V.Adt { variant_id = None; field_values = [ moved_input_value ] }
      in
      let box_v = mk_typed_value box_ty box_v in

      (* Move this value to the return variable *)
      let dest = mk_place_from_var_id V.VarId.zero in
      let ctx = assign_to_place config ctx box_v dest in

      (* Return *)
      Ok ctx
  | _ -> failwith "Inconsistent state"

(** Deconstruct a type of the form `Box<T>` to retrieve the `T` inside *)
let ty_get_box (box_ty : T.ety) : T.ety =
  match box_ty with
  | T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) -> boxed_ty
  | _ -> failwith "Not a boxed type"

(** Deconstruct a type of the form `&T` or `&mut T` to retrieve the `T` (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : T.ety) : T.erased_region * T.ety * T.ref_kind =
  match ty with
  | T.Ref (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> failwith "Not a ref type"

(** Auxiliary function which factorizes code to evaluate `std::Deref::deref`
    and `std::DerefMut::deref_mut` - see [eval_non_local_function_call] *)
let eval_box_deref_mut_or_shared (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (is_mut : bool) (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  (* Check the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ ) -> (
      (* Required type checking. We must have:
         - input_value.ty == & (mut) Box<ty>
         - boxed_ty == ty
         for some ty
      *)
      (let _, input_ty, ref_kind = ty_get_ref input_value.V.ty in
       assert (match ref_kind with T.Shared -> not is_mut | T.Mut -> is_mut);
       let input_ty = ty_get_box input_ty in
       assert (input_ty = boxed_ty));

      (* Borrow the boxed value *)
      let p =
        { E.var_id = input_var.C.index; projection = [ E.Deref; E.DerefBox ] }
      in
      let borrow_kind = if is_mut then E.Mut else E.Shared in
      let rv = E.Ref (p, borrow_kind) in
      match eval_rvalue config ctx rv with
      | Error err -> Error err
      | Ok (ctx, borrowed_value) ->
          (* Move the borrowed value to its destination *)
          let destp = mk_place_from_var_id V.VarId.zero in
          let ctx = assign_to_place config ctx borrowed_value destp in
          Ok ctx)
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref (config : C.config) (region_params : T.erased_region list)
    (type_params : T.ety list) (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  let is_mut = false in
  eval_box_deref_mut_or_shared config region_params type_params is_mut ctx

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_mut (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  let is_mut = true in
  eval_box_deref_mut_or_shared config region_params type_params is_mut ctx

(** Auxiliary function - see [eval_non_local_function_call].

    `Box::free` is not handled the same way as the other assumed functions:
    - in the regular case, whenever we need to evaluate an assumed function,
      we evaluate the operands, push a frame, call a dedicated function
      to correctly update the variables in the frame (and mimic the execution
      of a body) and finally pop the frame
    - in the case of `Box::free`: the value given to this function is often
      of the form `Box(⊥)` because we can move the value out of the
      box before freeing the box. It makes it invalid to see box_free as a
      "regular" function: it is not valid to call a function with arguments
      which contain `⊥`. For this reason, we execute `Box::free` as drop_value,
      but this is a bit annoying with regards to the semantics...

    Followingly this function doesn't behave like the others: it does not expect
    a stack frame to have been pushed, but rather simply behaves like [drop_value].
    It thus updates the box value (by calling [drop_value]) and updates
    the destination (by setting it to `()`).
*)
let eval_box_free (config : C.config) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place)
    (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  match (region_params, type_params, args) with
  | [], [ boxed_ty ], [ E.Move input_box_place ] ->
      (* Required type checking *)
      let input_box = read_place_unwrap config Write input_box_place ctx in
      (let input_ty = ty_get_box input_box.V.ty in
       assert (input_ty = boxed_ty));

      (* Drop the value *)
      let ctx = drop_value config ctx input_box_place in

      (* Update the destination by setting it to `()` *)
      let ctx = assign_to_place config ctx mk_unit_value dest in

      (* Return *)
      Ok ctx
  | _ -> failwith "Inconsistent state"

(** Evaluate a non-local (i.e, assumed) function call such as `Box::deref`
    (auxiliary helper for [eval_statement]) *)
let eval_non_local_function_call (config : C.config) (ctx : C.eval_ctx)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result =
  (* Debug *)
  L.log#ldebug
    (lazy
      (let type_params =
         "["
         ^ String.concat ", " (List.map (ety_to_string ctx) type_params)
         ^ "]"
       in
       let args =
         "[" ^ String.concat ", " (List.map (operand_to_string ctx) args) ^ "]"
       in
       let dest = place_to_string ctx dest in
       "eval_non_local_function_call:\n- fid:" ^ A.show_assumed_fun_id fid
       ^ "\n- type_params: " ^ type_params ^ "\n- args: " ^ args ^ "\n- dest: "
       ^ dest));

  (* There are two cases (and this is extremely annoying):
     - the function is not box_free
     - the function is box_free
     See [eval_box_free]
  *)
  match fid with
  | A.BoxFree ->
      (* Degenerate case: box_free *)
      eval_box_free config region_params type_params args dest ctx
  | _ -> (
      (* "Normal" case: not box_free *)
      (* Evaluate the operands *)
      let ctx, args_vl = eval_operands config ctx args in

      (* Push the stack frame: we initialize the frame with the return variable,
         and one variable per input argument *)
      let ctx = ctx_push_frame ctx in

      (* Create and push the return variable *)
      let ret_vid = V.VarId.zero in
      let ret_ty =
        get_non_local_function_return_type fid region_params type_params
      in
      let ret_var = mk_var ret_vid (Some "@return") ret_ty in
      let ctx = C.ctx_push_uninitialized_var ctx ret_var in

      (* Create and push the input variables *)
      let input_vars =
        V.VarId.mapi_from1
          (fun id (v : V.typed_value) -> (mk_var id None v.V.ty, v))
          args_vl
      in
      let ctx = C.ctx_push_vars ctx input_vars in

      (* "Execute" the function body. As the functions are assumed, here we call
         custom functions to perform the proper manipulations: we don't have
         access to a body. *)
      let res =
        match fid with
        | A.BoxNew -> eval_box_new config region_params type_params ctx
        | A.BoxDeref -> eval_box_deref config region_params type_params ctx
        | A.BoxDerefMut ->
            eval_box_deref_mut config region_params type_params ctx
        | A.BoxFree -> failwith "Unreachable"
        (* should have been treated above *)
      in

      (* Check if the function body evaluated correctly *)
      match res with
      | Error err -> Error err
      | Ok ctx ->
          (* Pop the stack frame and retrieve the return value *)
          let ctx, ret_value = ctx_pop_frame config ctx in

          (* Move the return value to its destination *)
          let ctx = assign_to_place config ctx ret_value dest in

          (* Return *)
          Ok ctx)

(** Evaluate a statement *)
let rec eval_statement (config : C.config) (ctx : C.eval_ctx) (st : A.statement)
    : (C.eval_ctx * statement_eval_res) eval_result =
  (* Debugging *)
  L.log#ldebug
    (lazy
      ("\n" ^ eval_ctx_to_string ctx ^ "\nAbout to evaluate statement: "
     ^ statement_to_string ctx st ^ "\n"));
  (* Evaluate *)
  match st with
  | A.Assign (p, rvalue) -> (
      (* Evaluate the rvalue *)
      match eval_rvalue config ctx rvalue with
      | Error err -> Error err
      | Ok (ctx, rvalue) ->
          (* Assign *)
          let ctx = assign_to_place config ctx rvalue p in
          Ok (ctx, Unit))
  | A.FakeRead p ->
      let ctx, _ = prepare_rplace config Read p ctx in
      Ok (ctx, Unit)
  | A.SetDiscriminant (p, variant_id) ->
      set_discriminant config ctx p variant_id
  | A.Drop p -> Ok (drop_value config ctx p, Unit)
  | A.Assert assertion -> (
      let ctx, v = eval_operand config ctx assertion.cond in
      assert (v.ty = T.Bool);
      match v.value with
      | Concrete (Bool b) ->
          if b = assertion.expected then Ok (ctx, Unit) else Error Panic
      | _ -> failwith "Expected a boolean")
  | A.Call call -> eval_function_call config ctx call
  | A.Panic -> Error Panic
  | A.Return -> Ok (ctx, Return)
  | A.Break i -> Ok (ctx, Break i)
  | A.Continue i -> Ok (ctx, Continue i)
  | A.Nop -> Ok (ctx, Unit)
  | A.Sequence (st1, st2) -> (
      (* Evaluate the first statement *)
      match eval_statement config ctx st1 with
      | Error err -> Error err
      | Ok (ctx, Unit) ->
          (* Evaluate the second statement *)
          eval_statement config ctx st2
      (* Control-flow break: transmit. We enumerate the cases on purpose *)
      | Ok (ctx, Break i) -> Ok (ctx, Break i)
      | Ok (ctx, Continue i) -> Ok (ctx, Continue i)
      | Ok (ctx, Return) -> Ok (ctx, Return))
  | A.Loop loop_body ->
      (* Evaluate a loop body

         We need a specific function for the [Continue] case: in case we continue,
         we might have to reevaluate the current loop body with the new context
         (and repeat this an indefinite number of times).
      *)
      let rec eval_loop_body (ctx : C.eval_ctx) :
          (C.eval_ctx * statement_eval_res) eval_result =
        (* Evaluate the loop body *)
        match eval_statement config ctx loop_body with
        | Error err -> Error err
        | Ok (ctx, Unit) ->
            (* We finished evaluating the statement in a "normal" manner *)
            Ok (ctx, Unit)
        (* Control-flow breaks *)
        | Ok (ctx, Break i) ->
            (* Decrease the break index *)
            if i = 0 then Ok (ctx, Unit) else Ok (ctx, Break (i - 1))
        | Ok (ctx, Continue i) ->
            (* Decrease the continue index *)
            if i = 0 then
              (* We stop there. When we continue, we go back to the beginning
                 of the loop: we must thus reevaluate the loop body (and
                 recheck the result to know whether we must reevaluate again,
                 etc. *)
              eval_loop_body ctx
            else (* We don't stop there: transmit *)
              Ok (ctx, Continue (i - 1))
        | Ok (ctx, Return) -> Ok (ctx, Return)
      in
      (* Apply *)
      eval_loop_body ctx
  | A.Switch (op, tgts) -> (
      (* Evaluate the operand *)
      let ctx, op_v = eval_operand config ctx op in
      match tgts with
      | A.If (st1, st2) -> (
          match op_v.value with
          | V.Concrete (V.Bool b) ->
              if b then eval_statement config ctx st1
              else eval_statement config ctx st2
          | _ -> failwith "Inconsistent state")
      | A.SwitchInt (int_ty, tgts, otherwise) -> (
          match op_v.value with
          | V.Concrete (V.Scalar sv) -> (
              assert (sv.V.int_ty = int_ty);
              match List.find_opt (fun (sv', _) -> sv = sv') tgts with
              | None -> eval_statement config ctx otherwise
              | Some (_, tgt) -> eval_statement config ctx tgt)
          | _ -> failwith "Inconsistent state"))

(** Evaluate a function call (auxiliary helper for [eval_statement]) *)
and eval_function_call (config : C.config) (ctx : C.eval_ctx) (call : A.call) :
    (C.eval_ctx * statement_eval_res) eval_result =
  (* There are two cases *
     - this is a local function, in which case we execute its body
     - this is a non-local function, in which case there is a special treatment
  *)
  let res =
    match call.func with
    | A.Local fid ->
        eval_local_function_call config ctx fid call.region_params
          call.type_params call.args call.dest
    | A.Assumed fid ->
        eval_non_local_function_call config ctx fid call.region_params
          call.type_params call.args call.dest
  in
  match res with Error err -> Error err | Ok ctx -> Ok (ctx, Unit)

(** Evaluate a local (i.e, not assumed) function call (auxiliary helper for
    [eval_statement]) *)
and eval_local_function_call (config : C.config) (ctx : C.eval_ctx)
    (fid : A.FunDefId.id) (_region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result =
  (* Retrieve the (correctly instantiated) body *)
  let def = C.ctx_lookup_fun_def ctx fid in
  match config.mode with
  | ConcreteMode -> (
      let tsubst =
        Subst.make_type_subst
          (List.map (fun v -> v.T.index) def.A.signature.type_params)
          type_params
      in
      let locals, body = Subst.fun_def_substitute_in_body tsubst def in

      (* Evaluate the input operands *)
      let ctx, args = eval_operands config ctx args in
      assert (List.length args = def.A.arg_count);

      (* Push a frame delimiter *)
      let ctx = ctx_push_frame ctx in

      (* Compute the initial values for the local variables *)
      (* 1. Push the return value *)
      let ret_var, locals =
        match locals with
        | ret_ty :: locals -> (ret_ty, locals)
        | _ -> failwith "Unreachable"
      in
      let ctx = C.ctx_push_var ctx ret_var (C.mk_bottom ret_var.var_ty) in

      (* 2. Push the input values *)
      let input_locals, locals =
        Utilities.list_split_at locals def.A.arg_count
      in
      let inputs = List.combine input_locals args in
      (* Note that this function checks that the variables and their values
         have the same type (this is important) *)
      let ctx = C.ctx_push_vars ctx inputs in

      (* 3. Push the remaining local variables (initialized as [Bottom]) *)
      let ctx = C.ctx_push_uninitialized_vars ctx locals in

      (* Execute the function body *)
      match eval_function_body config ctx body with
      | Error Panic -> Error Panic
      | Ok ctx ->
          (* Pop the stack frame and retrieve the return value *)
          let ctx, ret_value = ctx_pop_frame config ctx in

          (* Move the return value to its destination *)
          let ctx = assign_to_place config ctx ret_value dest in

          (* Return *)
          Ok ctx)
  | SymbolicMode -> raise Unimplemented

(** Evaluate a statement seen as a function body (auxiliary helper for
    [eval_statement]) *)
and eval_function_body (config : C.config) (ctx : C.eval_ctx)
    (body : A.statement) : (C.eval_ctx, eval_error) result =
  match eval_statement config ctx body with
  | Error err -> Error err
  | Ok (ctx, res) -> (
      match res with
      | Unit | Break _ | Continue _ -> failwith "Inconsistent state"
      | Return -> Ok ctx)

module Test = struct
  (** Test a unit function (taking no arguments) by evaluating it in an empty
    environment
 *)
  let test_unit_function (type_defs : T.type_def list)
      (fun_defs : A.fun_def list) (fid : A.FunDefId.id) : unit eval_result =
    (* Retrieve the function declaration *)
    let fdef = A.FunDefId.nth fun_defs fid in

    (* Debug *)
    L.log#ldebug
      (lazy ("test_unit_function: " ^ Print.Types.name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (List.length fdef.A.signature.region_params = 0);
    assert (List.length fdef.A.signature.type_params = 0);
    assert (fdef.A.arg_count = 0);

    (* Create the evaluation context *)
    let ctx =
      {
        C.type_context = type_defs;
        C.fun_context = fun_defs;
        C.type_vars = [];
        C.env = [];
        C.symbolic_counter = V.SymbolicValueId.generator_zero;
        C.borrow_counter = V.BorrowId.generator_zero;
      }
    in

    (* Put the (uninitialized) local variables *)
    let ctx = C.ctx_push_uninitialized_vars ctx fdef.A.locals in

    (* Evaluate the function *)
    let config = { C.mode = C.ConcreteMode; C.check_invariants = true } in
    match eval_function_body config ctx fdef.A.body with
    | Error err -> Error err
    | Ok _ -> Ok ()

  (** Small helper: return true if the function is a unit function (no parameters,
    no arguments) - TODO: move *)
  let fun_def_is_unit (def : A.fun_def) : bool =
    def.A.arg_count = 0
    && List.length def.A.signature.region_params = 0
    && List.length def.A.signature.type_params = 0
    && List.length def.A.signature.inputs = 0

  (** Test all the unit functions in a list of function definitions *)
  let test_all_unit_functions (type_defs : T.type_def list)
      (fun_defs : A.fun_def list) : unit =
    let test_fun (def : A.fun_def) : unit =
      if fun_def_is_unit def then
        match test_unit_function type_defs fun_defs def.A.def_id with
        | Error _ -> failwith "Unit test failed"
        | Ok _ -> ()
      else ()
    in
    List.iter test_fun fun_defs
end
