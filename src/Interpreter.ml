open Types
open Values
open Scalars
open Expressions
open CfimAst
open Print.Values
open Errors
open Contexts

(* TODO: Change state-passing style to : st -> ... -> (st, v) *)
(* TODO: check that the value types are correct when evaluating *)

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

(** Apply a predicate to all the borrows in a value *)
let rec check_borrows_in_value (check : borrow_content -> bool)
    (v : typed_value) : bool =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> true
  | Adt av -> FieldId.for_all (check_borrows_in_value check) av.field_values
  | Tuple values -> FieldId.for_all (check_borrows_in_value check) values
  | Assumed (Box bv) -> check_borrows_in_value check bv
  | Borrow bc -> (
      check bc
      &&
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> true
      | MutBorrow (_, mv) -> check_borrows_in_value check mv)
  | Loan lc -> (
      match lc with
      | SharedLoan (_, sv) -> check_borrows_in_value check sv
      | MutLoan _ -> true)

(** Apply a predicate to all the loans in a value *)
let rec check_loans_in_value (check : loan_content -> bool) (v : typed_value) :
    bool =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> true
  | Adt av -> FieldId.for_all (check_loans_in_value check) av.field_values
  | Tuple values -> FieldId.for_all (check_loans_in_value check) values
  | Assumed (Box bv) -> check_loans_in_value check bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> true
      | MutBorrow (_, mv) -> check_loans_in_value check mv)
  | Loan lc -> (
      check lc
      &&
      match lc with
      | SharedLoan (_, sv) -> check_loans_in_value check sv
      | MutLoan _ -> true)

(** Lookup a loan content in a value *)
let rec lookup_loan_in_value (ek : exploration_kind) (l : BorrowId.id)
    (v : typed_value) : loan_content option =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> None
  | Adt av ->
      let values = FieldId.vector_to_list av.field_values in
      List.find_map (lookup_loan_in_value ek l) values
  | Tuple values ->
      let values = FieldId.vector_to_list values in
      List.find_map (lookup_loan_in_value ek l) values
  | Assumed (Box bv) -> lookup_loan_in_value ek l bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> None
      | MutBorrow (_, mv) ->
          if ek.enter_mut_borrows then lookup_loan_in_value ek l mv else None)
  | Loan lc -> (
      match lc with
      | SharedLoan (bids, sv) ->
          if BorrowId.Set.mem l bids then Some lc
          else if ek.enter_shared_loans then lookup_loan_in_value ek l sv
          else None
      | MutLoan bid -> if bid = l then Some (MutLoan bid) else None)

(** Lookup a loan content.

    The loan is referred to by a borrow id.
 *)
let lookup_loan (ek : exploration_kind) (l : BorrowId.id) (env : env) :
    loan_content =
  let lookup_loan_in_env_value (ev : env_value) : loan_content option =
    match ev with
    | Var (_, v) -> lookup_loan_in_value ek l v
    | Abs _ -> raise Unimplemented
    (* TODO *)
  in
  match List.find_map lookup_loan_in_env_value env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a loan content in a value.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let rec update_loan_in_value (ek : exploration_kind) (l : BorrowId.id)
    (nlc : loan_content) (v : typed_value) : typed_value =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> v
  | Adt av ->
      let values =
        FieldId.map (update_loan_in_value ek l nlc) av.field_values
      in
      let av = { av with field_values = values } in
      { v with value = Adt av }
  | Tuple values ->
      let values = FieldId.map (update_loan_in_value ek l nlc) values in
      { v with value = Tuple values }
  | Assumed (Box bv) ->
      { v with value = Assumed (Box (update_loan_in_value ek l nlc bv)) }
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> v
      | MutBorrow (bid, mv) ->
          if ek.enter_mut_borrows then
            let v' =
              Borrow (MutBorrow (bid, update_loan_in_value ek l nlc mv))
            in
            { v with value = v' }
          else v)
  | Loan lc -> (
      match lc with
      | SharedLoan (bids, sv) ->
          if BorrowId.Set.mem l bids then { v with value = Loan nlc }
          else if ek.enter_shared_loans then
            let v' =
              Loan (SharedLoan (bids, update_loan_in_value ek l nlc sv))
            in
            { v with value = v' }
          else v
      | MutLoan bid -> if bid = l then { v with value = Loan nlc } else v)

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_loan (ek : exploration_kind) (l : BorrowId.id) (nlc : loan_content)
    (env : env) : env =
  let update_loan_in_env_value (ev : env_value) : env_value =
    match ev with
    | Var (vid, v) -> Var (vid, update_loan_in_value ek l nlc v)
    | Abs abs -> raise Unimplemented
    (* TODO *)
  in
  List.map update_loan_in_env_value env

(** Lookup a borrow content in a value *)
let rec lookup_borrow_in_value (ek : exploration_kind) (l : BorrowId.id)
    (v : typed_value) : borrow_content option =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> None
  | Adt av ->
      let values = FieldId.vector_to_list av.field_values in
      List.find_map (lookup_borrow_in_value ek l) values
  | Tuple values ->
      let values = FieldId.vector_to_list values in
      List.find_map (lookup_borrow_in_value ek l) values
  | Assumed (Box bv) -> lookup_borrow_in_value ek l bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow bid -> if l = bid then Some bc else None
      | InactivatedMutBorrow bid -> if l = bid then Some bc else None
      | MutBorrow (bid, mv) ->
          if bid = l then Some bc
          else if ek.enter_mut_borrows then lookup_borrow_in_value ek l mv
          else None)
  | Loan lc -> (
      match lc with
      | SharedLoan (_, sv) ->
          if ek.enter_shared_loans then lookup_borrow_in_value ek l sv else None
      | MutLoan bid -> None)

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow (ek : exploration_kind) (l : BorrowId.id) (env : env) :
    borrow_content =
  let lookup_borrow_in_env_value (ev : env_value) =
    match ev with
    | Var (_, v) -> lookup_borrow_in_value ek l v
    | Abs _ -> raise Unimplemented
    (* TODO *)
  in
  match List.find_map lookup_borrow_in_env_value env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a borrow content in a value.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let rec update_borrow_in_value (ek : exploration_kind) (l : BorrowId.id)
    (nbc : borrow_content) (v : typed_value) : typed_value =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> v
  | Adt av ->
      let values =
        FieldId.map (update_borrow_in_value ek l nbc) av.field_values
      in
      let av = { av with field_values = values } in
      { v with value = Adt av }
  | Tuple values ->
      let values = FieldId.map (update_borrow_in_value ek l nbc) values in
      { v with value = Tuple values }
  | Assumed (Box bv) ->
      { v with value = Assumed (Box (update_borrow_in_value ek l nbc bv)) }
  | Borrow bc -> (
      match bc with
      | SharedBorrow bid | InactivatedMutBorrow bid ->
          if bid = l then { v with value = Borrow nbc } else v
      | MutBorrow (bid, mv) ->
          if bid = l then { v with value = Borrow nbc }
          else if ek.enter_mut_borrows then
            let v' =
              Borrow (MutBorrow (bid, update_borrow_in_value ek l nbc mv))
            in
            { v with value = v' }
          else v)
  | Loan lc -> (
      match lc with
      | SharedLoan (bids, sv) ->
          if ek.enter_shared_loans then
            let v' =
              Loan (SharedLoan (bids, update_borrow_in_value ek l nbc sv))
            in
            { v with value = v' }
          else v
      | MutLoan _ -> v)

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_borrow (ek : exploration_kind) (l : BorrowId.id)
    (nbc : borrow_content) (env : env) : env =
  let update_borrow_in_env_value (ev : env_value) : env_value =
    match ev with
    | Var (vid, v) -> Var (vid, update_borrow_in_value ek l nbc v)
    | Abs abs -> raise Unimplemented
    (* TODO *)
  in
  List.map update_borrow_in_env_value env

(** The following type identifies the relative position of expressions (in
    particular borrows) in other expressions.
    
    For instance, it is used to control [end_borrow]: we usually only allow
    to end "outer" borrows, unless we perform a drop.
*)
type inner_outer = Inner | Outer

type borrow_ids = Borrows of BorrowId.Set.t | Borrow of BorrowId.id

(** Borrow lookup result *)
type borrow_lres =
  | NotFound
  | Outer of borrow_ids
  | FoundMut of typed_value
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

(** Check if a value contains loans *)
let rec loans_in_value (v : typed_value) : bool =
  match v.value with
  | Concrete _ -> false
  | Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      List.exists loans_in_value fields
  | Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      List.exists loans_in_value fields
  | Assumed (Box bv) -> loans_in_value bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> false
      | MutBorrow (_, bv) -> loans_in_value bv)
  | Loan lc -> true

(** Return the first loan we find in a value *)
let rec get_first_loan_in_value (v : typed_value) : loan_content option =
  match v.value with
  | Concrete _ -> None
  | Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      get_first_loan_in_values fields
  | Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      get_first_loan_in_values fields
  | Assumed (Box bv) -> get_first_loan_in_value bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> None
      | MutBorrow (_, bv) -> get_first_loan_in_value bv)
  | Loan lc -> Some lc

and get_first_loan_in_values (vl : typed_value list) : loan_content option =
  match vl with
  | [] -> None
  | v :: vl' -> (
      match get_first_loan_in_value v with
      | Some lc -> Some lc
      | None -> get_first_loan_in_values vl)

(** Check if a value contains ⊥ *)
let rec bottom_in_value (v : typed_value) : bool =
  match v.value with
  | Concrete _ -> false
  | Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      List.exists bottom_in_value fields
  | Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      List.exists bottom_in_value fields
  | Assumed (Box bv) -> bottom_in_value bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> false
      | MutBorrow (_, bv) -> bottom_in_value bv)
  | Loan lc -> (
      match lc with
      | SharedLoan (_, sv) -> bottom_in_value sv
      | MutLoan _ -> false)

(** See [end_borrow_get_borrow_in_env] *)
let rec end_borrow_get_borrow_in_value config io l outer_borrows v0 :
    typed_value * borrow_lres =
  match v0.value with
  | Concrete _ | Bottom | Symbolic _ -> (v0, NotFound)
  | Assumed (Box bv) ->
      let bv', res =
        end_borrow_get_borrow_in_value config io l outer_borrows bv
      in
      (* Note that we allow boxes to outlive the inner borrows.
       * Also note that when using the symbolic mode, boxes will never
       * be "opened" and will be manipulated solely through functions
       * like new, deref, etc. which will enforce that we destroy
       * boxes upon ending inner borrows *)
      ({ v0 with value = Assumed (Box bv') }, res)
  | Adt adt ->
      let values = FieldId.vector_to_list adt.field_values in
      let values', res =
        end_borrow_get_borrow_in_values config io l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      ({ v0 with value = Adt { adt with field_values = values' } }, res)
  | Tuple values ->
      let values = FieldId.vector_to_list values in
      let values', res =
        end_borrow_get_borrow_in_values config io l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      ({ v0 with value = Tuple values' }, res)
  | Loan (MutLoan _) -> (v0, NotFound)
  | Loan (SharedLoan (borrows, v)) ->
      (* Update the outer borrows, if necessary *)
      let outer_borrows =
        update_outer_borrows io outer_borrows (Borrows borrows)
      in
      let v', res =
        end_borrow_get_borrow_in_value config io l outer_borrows v
      in
      ({ value = Loan (SharedLoan (borrows, v')); ty = v0.ty }, res)
  | Borrow (SharedBorrow l') ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows FoundInactivatedMut )
      else (v0, NotFound)
  | Borrow (InactivatedMutBorrow l') ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows FoundInactivatedMut )
      else (v0, NotFound)
  | Borrow (MutBorrow (l', bv)) ->
      if l = l' then
        ( { v0 with value = Bottom },
          unwrap_res_to_outer_or outer_borrows (FoundMut bv) )
      else
        (* Update the outer borrows, if necessary *)
        let outer_borrows = update_outer_borrows io outer_borrows (Borrow l') in
        let bv', res =
          end_borrow_get_borrow_in_value config io l outer_borrows bv
        in
        ({ v0 with value = Borrow (MutBorrow (l', bv')) }, res)

and end_borrow_get_borrow_in_values config io l outer_borrows vl0 :
    typed_value list * borrow_lres =
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
let rec end_borrow_get_borrow_in_env (config : config) (io : inner_outer) l env0
    : env * borrow_lres =
  match env0 with
  | [] -> ([], NotFound)
  | Var (x, v) :: env -> (
      match end_borrow_get_borrow_in_value config io l None v with
      | v', NotFound ->
          let env', res = end_borrow_get_borrow_in_env config io l env in
          (Var (x, v') :: env', res)
      | v', res -> (Var (x, v') :: env, res))
  | Abs _ :: _ ->
      assert (config.mode = SymbolicMode);
      raise Unimplemented

(** See [give_back_value]. *)
let rec give_back_value_to_value config bid (v : typed_value)
    (destv : typed_value) : typed_value =
  match destv.value with
  | Concrete _ | Bottom | Symbolic _ -> destv
  | Adt av ->
      let field_values =
        List.map
          (give_back_value_to_value config bid v)
          (FieldId.vector_to_list av.field_values)
      in
      let field_values = FieldId.vector_of_list field_values in
      { destv with value = Adt { av with field_values } }
  | Tuple values ->
      let values =
        List.map
          (give_back_value_to_value config bid v)
          (FieldId.vector_to_list values)
      in
      let values = FieldId.vector_of_list values in
      { destv with value = Tuple values }
  | Assumed (Box destv') ->
      {
        destv with
        value = Assumed (Box (give_back_value_to_value config bid v destv'));
      }
  | Borrow bc ->
      (* We may need to insert the value inside a borrowed value *)
      let bc' =
        match bc with
        | SharedBorrow _ | InactivatedMutBorrow _ -> bc
        | MutBorrow (bid', destv') ->
            MutBorrow (bid', give_back_value_to_value config bid v destv')
      in
      { destv with value = Borrow bc' }
  | Loan lc -> (
      match lc with
      | SharedLoan (_, _) -> destv
      | MutLoan bid' ->
          if bid' = bid then v else { destv with value = Loan (MutLoan bid') })

(** See [give_back_value]. *)
let give_back_value_to_abs (_config : config) _bid _v _abs : abs =
  (* TODO *)
  raise Unimplemented

(** See [give_back_shared]. *)
let rec give_back_shared_to_value (config : config) bid (destv : typed_value) :
    typed_value =
  match destv.value with
  | Concrete _ | Bottom | Symbolic _ -> destv
  | Adt av ->
      let field_values =
        List.map
          (give_back_shared_to_value config bid)
          (FieldId.vector_to_list av.field_values)
      in
      let field_values = FieldId.vector_of_list field_values in
      { destv with value = Adt { av with field_values } }
  | Tuple values ->
      let values =
        List.map
          (give_back_shared_to_value config bid)
          (FieldId.vector_to_list values)
      in
      let values = FieldId.vector_of_list values in
      { destv with value = Tuple values }
  | Assumed (Box destv') ->
      {
        destv with
        value = Assumed (Box (give_back_shared_to_value config bid destv'));
      }
  | Borrow bc ->
      (* We may need to insert the value inside a borrowed value *)
      let bc' =
        match bc with
        | SharedBorrow _ | InactivatedMutBorrow _ -> bc
        | MutBorrow (bid', destv') ->
            MutBorrow (bid', give_back_shared_to_value config bid destv')
      in
      { destv with value = Borrow bc' }
  | Loan lc -> (
      match lc with
      | SharedLoan (bids, shared_value) ->
          if BorrowId.Set.mem bid bids then
            if BorrowId.Set.cardinal bids = 1 then shared_value
            else
              {
                destv with
                value =
                  Loan (SharedLoan (BorrowId.Set.remove bid bids, shared_value));
              }
          else
            {
              destv with
              value =
                Loan
                  (SharedLoan
                     (bids, give_back_shared_to_value config bid shared_value));
            }
      | MutLoan _ -> destv)

(** See [give_back_shared]. *)
let give_back_shared_to_abs _config _bid _abs : abs =
  (* TODO *)
  raise Unimplemented

(** Auxiliary function to end borrows.
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.
 *)
let give_back_value (config : config) (bid : BorrowId.id) (v : typed_value)
    (env : env) : env =
  let give_back_value_to_env_value ev : env_value =
    match ev with
    | Var (vid, destv) -> Var (vid, give_back_value_to_value config bid v destv)
    | Abs abs ->
        assert (config.mode = SymbolicMode);
        Abs (give_back_value_to_abs config bid v abs)
  in
  List.map give_back_value_to_env_value env

(** Auxiliary function to end borrows.
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.
 *)
let give_back_shared config (bid : BorrowId.id) (env : env) : env =
  let give_back_shared_to_env_value ev : env_value =
    match ev with
    | Var (vid, destv) -> Var (vid, give_back_shared_to_value config bid destv)
    | Abs abs ->
        assert (config.mode = SymbolicMode);
        Abs (give_back_shared_to_abs config bid abs)
  in
  List.map give_back_shared_to_env_value env

(** When copying values, we duplicate the shared borrows. This is tantamount
    to reborrowing the shared value. The following function applies this change
    to an environment by inserting a new borrow id in the set of borrows tracked
    by a shared value, referenced by the [original_bid] argument.
 *)
let reborrow_shared (config : config) (original_bid : BorrowId.id)
    (new_bid : BorrowId.id) (env : env) : env =
  let rec reborrow_in_value (v : typed_value) : typed_value =
    match v.value with
    | Concrete _ | Bottom | Symbolic _ -> v
    | Adt av ->
        let fields = FieldId.vector_to_list av.field_values in
        let fields = List.map reborrow_in_value fields in
        let fields = FieldId.vector_of_list fields in
        { v with value = Adt { av with field_values = fields } }
    | Tuple fields ->
        let fields = FieldId.vector_to_list fields in
        let fields = List.map reborrow_in_value fields in
        let fields = FieldId.vector_of_list fields in
        { v with value = Tuple fields }
    | Assumed (Box bv) ->
        { v with value = Assumed (Box (reborrow_in_value bv)) }
    | Borrow bc -> (
        match bc with
        | SharedBorrow _ | InactivatedMutBorrow _ -> v
        | MutBorrow (bid, bv) ->
            { v with value = Borrow (MutBorrow (bid, reborrow_in_value bv)) })
    | Loan lc -> (
        match lc with
        | MutLoan _ -> v
        | SharedLoan (bids, sv) ->
            (* Shared loan: check if the borrow id we are looking for is in the
               set of borrow ids. If yes, insert the new borrow id, otherwise
               explore inside the shared value *)
            if BorrowId.Set.mem original_bid bids then
              let bids' = BorrowId.Set.add new_bid bids in
              { v with value = Loan (SharedLoan (bids', sv)) }
            else
              { v with value = Loan (SharedLoan (bids, reborrow_in_value sv)) })
  in
  let reborrow_in_ev (ev : env_value) : env_value =
    match ev with
    | Var (vid, v) -> Var (vid, reborrow_in_value v)
    | Abs abs ->
        assert (config.mode = SymbolicMode);
        Abs abs
  in
  List.map reborrow_in_ev env

(** End a borrow identified by its borrow id
    
    First lookup the borrow in the environment and replace it with [Bottom],
    then update the loan. Ends outer borrows before updating the borrow if
    it is necessary.
 *)
let rec end_borrow (config : config) (io : inner_outer) (l : BorrowId.id)
    (env0 : env) : env =
  match end_borrow_get_borrow_in_env config io l env0 with
  (* It is possible that we can't find a borrow in symbolic mode (ending
   * an abstraction may end several borrows at once *)
  | env, NotFound ->
      assert (config.mode = SymbolicMode);
      env
  (* If we found outer borrows: end those borrows first *)
  | env, Outer outer_borrows ->
      let env' =
        match outer_borrows with
        | Borrows bids -> end_borrows config io bids env
        | Borrow bid -> end_borrow config io bid env
      in
      (* Retry to end the borrow *)
      end_borrow config io l env'
  (* If found mut: give the value back *)
  | env, FoundMut tv -> give_back_value config l tv env
  (* If found shared or inactivated mut: remove the borrow id from the loan set of the shared value *)
  | env, (FoundShared | FoundInactivatedMut) -> give_back_shared config l env

and end_borrows (config : config) (io : inner_outer) (lset : BorrowId.Set.t)
    (env0 : env) : env =
  BorrowId.Set.fold (fun id env -> end_borrow config io id env) lset env0

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
let promote_shared_loan_to_mut_loan (l : BorrowId.id) (env : env) :
    env * typed_value =
  (* Lookup the shared loan *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l env with
  | MutLoan _ -> failwith "Expected a shared loan, found a mut loan"
  | SharedLoan (bids, sv) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      assert (BorrowId.Set.mem l bids && BorrowId.Set.cardinal bids = 1);
      (* We need to check that there aren't any loans in the value:
           we should have gotten rid of those already, but it is better
           to do a sanity check. *)
      assert (not (loans_in_value sv));
      (* Also need to check there isn't [Bottom] (this is actually an invariant *)
      assert (not (bottom_in_value sv));
      (* Update the loan content *)
      let env1 = update_loan ek l (MutLoan l) env in
      (* Return *)
      (env1, sv)

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates a shared borrow to a mutable borrow.
 *)
let promote_inactivated_borrow_to_mut_borrow (l : BorrowId.id)
    (borrowed_value : typed_value) (env : env) : env =
  (* Lookup the inactivated borrow - note that we don't go inside borrows/loans:
     there can't be inactivated borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  match lookup_borrow ek l env with
  | SharedBorrow _ | MutBorrow (_, _) ->
      failwith "Expected an inactivated mutable borrow"
  | InactivatedMutBorrow _ ->
      (* Update it *)
      update_borrow ek l (MutBorrow (l, borrowed_value)) env

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let rec activate_inactivated_mut_borrow (config : config) (io : inner_outer)
    (l : BorrowId.id) (env : env) : env =
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l env with
  | MutLoan _ -> failwith "Unreachable"
  | SharedLoan (bids, sv) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         inactivated borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let env' =
            match lc with
            | SharedLoan (bids, _) -> end_outer_borrows config bids env
            | MutLoan bid -> end_outer_borrow config bid env
          in
          (* Recursive call *)
          activate_inactivated_mut_borrow config io l env'
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value sv));
          let check_not_inactivated bc =
            match bc with InactivatedMutBorrow _ -> false | _ -> true
          in
          assert (not (check_borrows_in_value check_not_inactivated sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = BorrowId.Set.remove l bids in
          let env1 = end_borrows config io bids env in
          (* Promote the loan *)
          let env2, borrowed_value = promote_shared_loan_to_mut_loan l env1 in
          (* Promote the borrow - the value should have been checked by
             [promote_shared_loan_to_mut_loan]
          *)
          promote_inactivated_borrow_to_mut_borrow l borrowed_value env2)

(** Paths *)

(** When we fail reading from or writing to a path, it might be because we
    need to update the environment by ending borrows, expanding symbolic
    values, etc. The following type is used to convey this information. *)
type path_fail_kind =
  | FailSharedLoan of BorrowId.Set.t
      (** Failure because we couldn't go inside a shared loan *)
  | FailMutLoan of BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | FailInactivatedMutBorrow of BorrowId.id
      (** Failure because we couldn't go inside an inactivated mutable borrow
          (which should get activated) *)
  | FailSymbolic of (projection_elem * symbolic_proj_comp)
      (** Failure because we need to enter a symbolic value (and thus need to expand it) *)
  | FailBottom of (int * projection_elem * ety)
      (** Failure because we need to enter an any value - we can expand Bottom
          values if they are left values. We return the number of elements which
          were remaining in the path when we reached the error - this allows to
          properly update the Bottom value, if needs be.
       *)
  | FailBorrow of borrow_content
      (** We got stuck because we couldn't enter a borrow *)

(** Result of evaluating a path (reading from a path/writing to a path)
    
    Note that when we fail, we return information used to update the
    environment, as well as the 
*)
type 'a path_access_result = ('a, path_fail_kind) result
(** The result of reading from/writing to a place *)

(*(** Return the shared value referenced by a borrow id *)
let lookup_shared_value_from_borrow_id (bid : BorrowId.id) (env : env) :
    typed_value =
  let rec lookup_in_value (v : typed_value) : typed_value option =
    match v.value with
    | Concrete _ | Bottom | Symbolic _ -> None
    | Adt av ->
        let values = FieldId.vector_to_list av.field_values in
        lookup_in_values values
    | Tuple values ->
        let values = FieldId.vector_to_list values in
        lookup_in_values values
    | Borrow bc -> (
        match bc with
        | SharedBorrow _ | InactivatedMutBorrow _ -> None
        | MutBorrow (_, bv) -> lookup_in_value bv)
    | Loan lc -> (
        match lc with
        | SharedLoan (bids, sv) ->
            if BorrowId.Set.mem bid bids then Some v else lookup_in_value sv
        | MutLoan _ -> None)
    | Assumed (Box bv) -> lookup_in_value bv
  and lookup_in_values (vl : typed_value list) : typed_value option =
    List.find_map lookup_in_value vl
  in
  let lookup_in_env_value (ev : env_value) : typed_value option =
    match ev with
    | Var (_, v) -> lookup_in_value v
    | Abs _ -> raise Unimplemented
  in
  match List.find_map lookup_in_env_value env with
  | None -> failwith "Unreachable"
  | Some v -> v*)

type updated_read_value = { read : typed_value; updated : typed_value }

type projection_access = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  lookup_shared_borrows : bool;
}

(** Generic function to access (read/write) the value at the end of a projection.

    We return the (eventually) updated value, the value we read at the end of
    the place and the (eventually) updated environment.
 *)
let rec access_projection (access : projection_access) (env : env)
    (* Function to (eventually) update the value we find *)
      (update : typed_value -> typed_value) (p : projection) (v : typed_value) :
    (env * updated_read_value) path_access_result =
  (* For looking up/updating shared loans *)
  let ek : exploration_kind =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match p with
  | [] ->
      let nv = update v in
      (* Type checking *)
      assert (nv.ty = v.ty);
      Ok (env, { read = v; updated = nv })
  | pe :: p' -> (
      (* Match on the projection element and the value *)
      match (pe, v.value) with
      (* Field projection *)
      | Field (ProjAdt (_def_id, opt_variant_id), field_id), Adt adt -> (
          (* Check that the projection is consistent with the current value *)
          (match (opt_variant_id, adt.variant_id) with
          | None, None -> ()
          | Some vid, Some vid' -> if vid <> vid' then failwith "Unreachable"
          | _ -> failwith "Unreachable");
          (* Actually project *)
          let fv = FieldId.nth adt.field_values field_id in
          match access_projection access env update p fv with
          | Error err -> Error err
          | Ok (env1, res) ->
              (* Update the field value *)
              let nvalues =
                FieldId.update_nth adt.field_values field_id res.updated
              in
              let nadt = Adt { adt with field_values = nvalues } in
              let updated = { v with value = nadt } in
              Ok (env1, { res with updated }))
      (* Tuples *)
      | Field (ProjTuple arity, field_id), Tuple values -> (
          assert (arity = FieldId.length values);
          let fv = FieldId.nth values field_id in
          (* Project *)
          match access_projection access env update p fv with
          | Error err -> Error err
          | Ok (env1, res) ->
              (* Update the field value *)
              let nvalues = FieldId.update_nth values field_id res.updated in
              let ntuple = Tuple nvalues in
              let updated = { v with value = ntuple } in
              Ok (env1, { res with updated })
          (* If we reach Bottom, it may mean we need to expand an uninitialized
           * enumeration value *))
      | Field (ProjAdt (_, Some _variant_id), _), Bottom ->
          Error (FailBottom (1 + List.length p', pe, v.ty))
      (* Symbolic value: needs to be expanded *)
      | _, Symbolic sp ->
          (* Expand the symbolic value *)
          Error (FailSymbolic (pe, sp))
      (* Box dereferencement *)
      | DerefBox, Assumed (Box bv) -> (
          (* We allow moving inside of boxes *)
          match access_projection access env update p' bv with
          | Error err -> Error err
          | Ok (env1, res) ->
              let nv = { v with value = Assumed (Box res.updated) } in
              Ok (env1, { res with updated = nv }))
      (* Borrows *)
      | Deref, Borrow bc -> (
          match bc with
          | SharedBorrow bid ->
              (* Lookup the loan content, and explore from there *)
              if access.lookup_shared_borrows then
                match lookup_loan ek bid env with
                | MutLoan _ -> failwith "Expected a shared loan"
                | SharedLoan (bids, sv) -> (
                    (* Explore the shared value *)
                    match access_projection access env update p' sv with
                    | Error err -> Error err
                    | Ok (env1, res) ->
                        (* Update the shared loan with the new value returned
                           by [access_projection] *)
                        let env2 =
                          update_loan ek bid
                            (SharedLoan (bids, res.updated))
                            env1
                        in
                        (* Return - note that we don't need to update the borrow itself *)
                        Ok (env2, { res with updated = v }))
              else Error (FailBorrow bc)
          | InactivatedMutBorrow bid -> Error (FailInactivatedMutBorrow bid)
          | MutBorrow (bid, bv) ->
              if access.enter_mut_borrows then
                match access_projection access env update p' bv with
                | Error err -> Error err
                | Ok (env1, res) ->
                    let nv =
                      { v with value = Borrow (MutBorrow (bid, res.updated)) }
                    in
                    Ok (env1, { res with updated = nv })
              else Error (FailBorrow bc))
      | _, Loan lc -> (
          match lc with
          | MutLoan bid -> Error (FailMutLoan bid)
          | SharedLoan (bids, sv) ->
              (* If we can enter shared loan, we ignore the loan. Pay attention
                 to the fact that we need to reexplore the *whole* place (i.e,
                 we mustn't ignore the current projection element *)
              if access.enter_shared_loans then
                match access_projection access env update (pe :: p') sv with
                | Error err -> Error err
                | Ok (env1, res) ->
                    let nv =
                      { v with value = Loan (SharedLoan (bids, res.updated)) }
                    in
                    Ok (env1, { res with updated = nv })
              else Error (FailSharedLoan bids)))

(** Generic function to access (read/write) the value at a given place.

    We return the value we read at the place and the (eventually) updated
    environment, if we managed to access the place, or the precise reason
    why we failed.
 *)
let access_place (access : projection_access)
    (* Function to (eventually) update the value we find *)
      (update : typed_value -> typed_value) (p : place) (env : env) :
    (env * typed_value) path_access_result =
  (* Lookup the variable's value *)
  let value = env_lookup_var_value env p.var_id in
  (* Apply the projection *)
  match access_projection access env update p.projection value with
  | Error err -> Error err
  | Ok (env1, res) ->
      (* Update the value *)
      let env2 = env_update_var_value env p.var_id res.updated in
      (* Return *)
      Ok (env2, res.read)

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
let read_place (config : config) (access : access_kind) (p : place) (env : env)
    : typed_value path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function is the identity *)
  let update v = v in
  match access_place access update p env with
  | Error err -> Error err
  | Ok (env1, read_value) ->
      (* Note that we ignore the new environment: it should be the same as the
         original one.
      *)
      if config.check_invariants then assert (env1 = env);
      Ok read_value

let read_place_unwrap (config : config) (access : access_kind) (p : place)
    (env : env) : typed_value =
  match read_place config access p env with
  | Error _ -> failwith "Unreachable"
  | Ok v -> v

(** Update the value at a given place *)
let write_place (_config : config) (access : access_kind) (p : place)
    (nv : typed_value) (env : env) : env path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function substitutes the value with the new value *)
  let update _ = nv in
  match access_place access update p env with
  | Error err -> Error err
  | Ok (env1, _) ->
      (* We ignore the read value *)
      Ok env1

let write_place_unwrap (config : config) (access : access_kind) (p : place)
    (nv : typed_value) (env : env) : env =
  match write_place config access p nv env with
  | Error _ -> failwith "Unreachable"
  | Ok env -> env

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
let expand_bottom_value (config : config) (access : access_kind)
    (tyctx : type_def TypeDefId.vector) (p : place) (remaining_pes : int)
    (pe : projection_elem) (ty : ety) (env : env) : env =
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
    | ( Field (ProjAdt (def_id, opt_variant_id), _),
        Types.Adt (def_id', regions, types) ) ->
        (* Lookup the definition and check if it is an enumeration - it
           should be an enumeration if and only if the projection element
           is a field projection with *some* variant id. Retrieve the list
           of fields at the same time. *)
        assert (def_id = def_id');
        let def = TypeDefId.nth tyctx def_id in
        let fields =
          match (def.kind, opt_variant_id) with
          | Struct fields, None -> fields
          | Enum variants, Some variant_id ->
              (* Retrieve the proper variant *)
              let variant = VariantId.nth variants variant_id in
              variant.fields
        in
        (* Initialize the expanded value *)
        let fields = FieldId.vector_to_list fields in
        let fields =
          List.map
            (fun f -> { value = Bottom; ty = erase_regions f.field_ty })
            fields
        in
        let fields = FieldId.vector_of_list fields in
        Values.Adt
          {
            def_id;
            variant_id = opt_variant_id;
            regions;
            types;
            field_values = fields;
          }
    | Field (ProjTuple arity, _), Types.Tuple tys ->
        assert (arity = List.length tys);
        (* Generate the field values *)
        let fields = List.map (fun ty -> { value = Bottom; ty }) tys in
        let fields = FieldId.vector_of_list fields in
        Values.Tuple fields
    | _ -> failwith "Unreachable"
  in
  let nv = { value = nv; ty } in
  (* Update the environment by inserting the expanded value at the proper place *)
  match write_place config access p' nv env with
  | Ok env -> env
  | Error _ -> failwith "Unreachable"

(** Update the environment to be able to read a place.

    When reading a place, we may be stuck along the way because some value
    is borrowed, we reach a symbolic value, etc. In this situation [read_place]
    fails while returning precise information about the failure. This function
    uses this information to update the environment (by ending borrows,
    expanding symbolic values) until we manage to fully read the place.
 *)
let rec update_env_along_read_place (config : config) (access : access_kind)
    (p : place) (env : env) : env =
  (* Attempt to read the place: if it fails, update the environment and retry *)
  match read_place config access p env with
  | Ok _ -> env
  | Error err ->
      let env' =
        match err with
        | FailSharedLoan bids -> end_outer_borrows config bids env
        | FailMutLoan bid -> end_outer_borrow config bid env
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config Outer bid env
        | FailSymbolic (pe, sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (remaining_pes, pe, ty) ->
            (* We can't expand [Bottom] values while reading them *)
            failwith "Found [Bottom] while reading a place"
        | FailBorrow _ -> failwith "Could not read a borrow"
      in
      update_env_along_read_place config access p env'

(** Update the environment to be able to write to a place.

    See [update_env_alond_read_place].
*)
let rec update_env_along_write_place (config : config) (access : access_kind)
    (tyctx : type_def TypeDefId.vector) (p : place) (nv : typed_value)
    (env : env) : env =
  (* Attempt to write the place: if it fails, update the environment and retry *)
  match write_place config access p nv env with
  | Ok v -> env
  | Error err ->
      let env' =
        match err with
        | FailSharedLoan bids -> end_outer_borrows config bids env
        | FailMutLoan bid -> end_outer_borrow config bid env
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config Outer bid env
        | FailSymbolic (pe, sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (remaining_pes, pe, ty) ->
            (* Expand the [Bottom] value *)
            expand_bottom_value config access tyctx p remaining_pes pe ty env
        | FailBorrow _ -> failwith "Could not write to a borrow"
      in
      update_env_along_write_place config access tyctx p nv env'

exception UpdateEnv of env
(** Small utility used to break control-flow *)

(** Collect the borrows at a given place (by ending borrows when we find some
    loans).

    This is used when reading, borrowing, writing to a value. We typically
    first call [update_env_along_read_place] or [update_env_along_write_place]
    to get access to the value, then call this function to "prepare" the value.
 *)
let rec collect_borrows_at_place (config : config) (access : access_kind)
    (p : place) (env : env) : env =
  (* First, retrieve the value *)
  match read_place config access p env with
  | Error _ -> failwith "Unreachable"
  | Ok v -> (
      (* Explore the value to check if we need to update the environment.
         In particular, we need to end the proper loans in the value.
         Also, we fail if the value contains any [Bottom].

         We use exceptions to make it handy.
      *)
      let rec inspect_update v : unit =
        match v.value with
        | Concrete _ -> ()
        | Bottom ->
            failwith "Unreachable"
            (* note that we don't really need to fail here *)
        | Symbolic _ ->
            (* Nothing to do for symbolic values - note that if the value needs
               to be copied, etc. we perform additional checks later *)
            ()
        | Adt adt -> FieldId.iter inspect_update adt.field_values
        | Tuple values -> FieldId.iter inspect_update values
        | Assumed (Box v) -> inspect_update v
        | Borrow bc -> (
            match bc with
            | SharedBorrow _ -> ()
            | MutBorrow (_, tv) -> inspect_update tv
            | InactivatedMutBorrow bid ->
                (* We need to activate inactivated borrows *)
                let env' =
                  activate_inactivated_mut_borrow config Inner bid env
                in
                raise (UpdateEnv env'))
        | Loan lc -> (
            match lc with
            | SharedLoan (bids, ty) -> (
                (* End the loans if we need a modification access, otherwise dive into
                   the shared value *)
                match access with
                | Read -> inspect_update ty
                | Write | Move ->
                    let env' = end_outer_borrows config bids env in
                    raise (UpdateEnv env'))
            | MutLoan bid ->
                (* We always need to end mutable borrows *)
                let env' = end_outer_borrow config bid env in
                raise (UpdateEnv env'))
      in
      (* Inspect the value and update the environment while doing so.
         If the environment gets updated: perform a recursive call (many things
         may have been updated in the environment: first we need to retrieve the
         proper updated value - and this value may actually not be accessible
         anymore
      *)
      try
        inspect_update v;
        (* No environment update required: return the current environment *)
        env
      with UpdateEnv env' -> collect_borrows_at_place config access p env')

(** Drop (end) all the borrows at a given place.

    Repeat:
    - read the value at a given place
    - as long as we find a loans or a borrow, end it

    This is used to drop values (when we need to write to a place, we first
    drop the value there to properly propagate back values which are not/can't
    be borrowed anymore).
 *)
let rec drop_borrows_at_place (config : config) (p : place) (env : env) : env =
  (* We do something similar to [collect_borrows_at_place].
     First, retrieve the value *)
  match read_place config Write p env with
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
      let rec inspect_update (end_loans : bool) v : unit =
        match v.value with
        | Concrete _ -> ()
        | Bottom ->
            (* Note that we are going to *write* to the value: it is ok if this
               value contains [Bottom] - and actually we introduce some
               occurrences of [Bottom] by ending borrows *)
            ()
        | Symbolic _ ->
            (* Nothing to do for symbolic values - TODO: not sure *)
            raise Unimplemented
        | Adt adt -> FieldId.iter (inspect_update end_loans) adt.field_values
        | Tuple values -> FieldId.iter (inspect_update end_loans) values
        | Assumed (Box v) -> inspect_update end_loans v
        | Borrow bc -> (
            assert (not end_loans);
            (* Sanity check *)
            (* We need to end all borrows. Note that we ignore the outer borrows
               when ending the borrows we find here (we call [end_inner_borrow(s)]:
               the value at place p might be below a borrow/loan. Note however
               that the borrow we found here is an outer borrow, if we restrain
               ourselves at the value at place p.
            *)
            match bc with
            | SharedBorrow bid | MutBorrow (bid, _) ->
                raise (UpdateEnv (end_inner_borrow config bid env))
            | InactivatedMutBorrow bid ->
                (* We need to activate inactivated borrows - later, we will
                 * actually end it *)
                let env' =
                  activate_inactivated_mut_borrow config Inner bid env
                in
                raise (UpdateEnv env'))
        | Loan lc ->
            if (* If we can, end the loans, otherwise ignore *)
               end_loans then
              (* We need to end all loans. Note that as all the borrows inside
                 the value at place p should already have ended, the borrows
                 associated to the loans we find here should be borrows from
                 outside this value: we need to call [end_outer_borrow(s)]
                 (we can't ignore outer borrows this time).
              *)
              match lc with
              | SharedLoan (bids, _) ->
                  raise (UpdateEnv (end_outer_borrows config bids env))
              | MutLoan bid ->
                  raise (UpdateEnv (end_outer_borrow config bid env))
            else ()
      in
      (* Inspect the value and update the environment while doing so.
         If the environment gets updated: perform a recursive call (many things
         may have been updated in the environment: first we need to retrieve the
         proper updated value - and this value may actually not be accessible
         anymore
      *)
      try
        (* Inspect the value: end the borrows only *)
        inspect_update false v;
        (* Inspect the value: end the loans *)
        inspect_update true v;
        (* No environment update required: return the current environment *)
        env
      with UpdateEnv env' -> drop_borrows_at_place config p env')

(** Copy a value, and return the resulting value.

    Note that copying values might update the context. For instance, when
    copying shared borrows, we need to insert new shared borrows in the context.
 *)
let rec copy_value (config : config) (ctx : eval_ctx) (v : typed_value) :
    eval_ctx * typed_value =
  match v.value with
  | Values.Concrete _ -> (ctx, v)
  | Values.Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      let ctx', fields = List.fold_left_map (copy_value config) ctx fields in
      let fields = FieldId.vector_of_list fields in
      (ctx', { v with value = Values.Adt { av with field_values = fields } })
  | Values.Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      let ctx', fields = List.fold_left_map (copy_value config) ctx fields in
      let fields = FieldId.vector_of_list fields in
      (ctx', { v with value = Values.Tuple fields })
  | Values.Bottom -> failwith "Can't copy ⊥"
  | Values.Assumed av -> failwith "Can't copy an assumed value"
  | Values.Borrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | SharedBorrow bid ->
          let ctx', bid' = fresh_borrow_id ctx in
          let env'' = reborrow_shared config bid bid' ctx'.env in
          let ctx'' = { ctx' with env = env'' } in
          (ctx'', { v with value = Values.Borrow (SharedBorrow bid') })
      | MutBorrow (_, _) -> failwith "Can't copy a mutable borrow"
      | InactivatedMutBorrow _ ->
          failwith "Can't copy an inactivated mut borrow")
  | Values.Loan lc -> (
      (* We can only copy shared loans *)
      match lc with
      | MutLoan _ -> failwith "Can't copy a mutable loan"
      | SharedLoan (_, sv) -> copy_value config ctx sv)
  | Values.Symbolic _sp ->
      (* TODO: check that the value is copyable *)
      raise Unimplemented

(** Convert a constant operand value to a typed value *)
let constant_value_to_typed_value (ctx : eval_ctx) (ty : ety)
    (cv : operand_constant_value) : typed_value =
  (* Check the type while converting *)
  match (ty, cv) with
  (* Unit *)
  | Types.Tuple [], Unit -> { value = Tuple (FieldId.vector_of_list []); ty }
  (* Adt with one variant and no fields *)
  | Types.Adt (def_id, [], []), ConstantAdt def_id' ->
      assert (def_id = def_id');
      (* Check that the adt definition only has one variant with no fields,
         compute the variant id at the same time. *)
      let def = TypeDefId.nth ctx.type_context def_id in
      assert (RegionVarId.length def.region_params = 0);
      assert (TypeVarId.length def.type_params = 0);
      let variant_id =
        match def.kind with
        | Struct fields ->
            assert (FieldId.length fields = 0);
            None
        | Enum variants ->
            assert (VariantId.length variants = 1);
            let variant_id = VariantId.zero in
            let variant = VariantId.nth variants variant_id in
            assert (FieldId.length variant.fields = 0);
            Some variant_id
      in
      let value =
        Adt
          {
            def_id;
            variant_id;
            regions = [];
            types = [];
            field_values = FieldId.vector_of_list [];
          }
      in
      { value; ty }
  (* Scalar, boolean... *)
  | Types.Bool, ConstantValue (Bool v) -> { value = Concrete (Bool v); ty }
  | Types.Char, ConstantValue (Char v) -> { value = Concrete (Char v); ty }
  | Types.Str, ConstantValue (String v) -> { value = Concrete (String v); ty }
  | Types.Integer int_ty, ConstantValue (Scalar v) ->
      (* Check the type and the ranges *)
      assert (int_ty == v.int_ty);
      assert (check_scalar_value_in_range v);
      { value = Concrete (Scalar v); ty }
  (* Remaining cases (invalid) - listing as much as we can on purpose
     (allows to catch errors at compilation if the definitions change) *)
  | _, Unit | _, ConstantAdt _ | _, ConstantValue _ ->
      failwith "Improperly typed constant value"

(** Small utility *)
let prepare_rplace (config : config) (access : access_kind) (p : place)
    (ctx : eval_ctx) : eval_ctx * typed_value =
  let env1 = update_env_along_read_place config access p ctx.env in
  let env2 = collect_borrows_at_place config access p env1 in
  let v = read_place_unwrap config access p env2 in
  let ctx2 = { ctx with env = env2 } in
  (ctx2, v)

let eval_operand (config : config) (ctx : eval_ctx) (op : operand) :
    eval_ctx * typed_value =
  match op with
  | Expressions.Constant (ty, cv) ->
      let v = constant_value_to_typed_value ctx ty cv in
      (ctx, v)
  | Expressions.Copy p ->
      (* Access the value *)
      let access = Read in
      let ctx2, v = prepare_rplace config access p ctx in
      (* Copy the value *)
      assert (not (bottom_in_value v));
      copy_value config ctx2 v
  | Expressions.Move p -> (
      (* Access the value *)
      let access = Move in
      let ctx2, v = prepare_rplace config access p ctx in
      (* Move the value *)
      assert (not (bottom_in_value v));
      let bottom = { value = Bottom; ty = v.ty } in
      match write_place config access p bottom ctx2.env with
      | Error _ -> failwith "Unreachable"
      | Ok env3 ->
          let ctx3 = { ctx2 with env = env3 } in
          (ctx3, v))

let eval_unary_op (config : config) (ctx : eval_ctx) (unop : unop)
    (op : operand) : (eval_ctx * typed_value) eval_result =
  (* Evaluate the operand *)
  let access = Read in
  let ctx1, v = eval_operand config ctx op in
  (* Apply the unop *)
  match (unop, v.value) with
  | Not, Concrete (Bool b) ->
      Ok (ctx1, { v with value = Concrete (Bool (not b)) })
  | Neg, Concrete (Scalar sv) -> (
      let i = Z.neg sv.value in
      match mk_scalar sv.int_ty i with
      | Error _ -> Error Panic
      | Ok sv -> Ok (ctx1, { v with value = Concrete (Scalar sv) }))
  | (Not | Neg), Symbolic _ -> raise Unimplemented (* TODO *)
  | _ -> failwith "Invalid value for unop"

let eval_binary_op (config : config) (ctx : eval_ctx) (binop : binop)
    (op1 : operand) (op2 : operand) : (eval_ctx * typed_value) eval_result =
  (* Evaluate the operands *)
  let access = Read in
  let ctx1, v1 = eval_operand config ctx op1 in
  let ctx2, v2 = eval_operand config ctx1 op2 in
  (* Binary operations only apply on integer values, but when we check for
   * equality *)
  if binop = Eq || binop = Ne then (
    (* Equality/inequality check is primitive only on primitive types *)
    assert (v1.ty = v2.ty);
    let b = v1 = v2 in
    Ok (ctx2, { value = Concrete (Bool b); ty = Types.Bool }))
  else
    match (v1.value, v2.value) with
    | Concrete (Scalar sv1), Concrete (Scalar sv2) -> (
        let res =
          (* There are binops which require the two operands to have the same
             type, and binops for which it is not the case.
             There are also binops which return booleans, and binops which
             return integers.
          *)
          match binop with
          | Lt | Le | Ge | Gt ->
              (* The two operands must have the same type and the result is a boolean *)
              assert (sv1.int_ty = sv2.int_ty);
              let b =
                match binop with
                | Lt -> Z.lt sv1.value sv1.value
                | Le -> Z.leq sv1.value sv1.value
                | Ge -> Z.geq sv1.value sv1.value
                | Gt -> Z.gt sv1.value sv1.value
                | Div | Rem | Add | Sub | Mul | BitXor | BitAnd | BitOr | Shl
                | Shr | Ne | Eq ->
                    failwith "Unreachable"
              in
              Ok { value = Concrete (Bool b); ty = Types.Bool }
          | Div | Rem | Add | Sub | Mul | BitXor | BitAnd | BitOr -> (
              (* The two operands must have the same type and the result is an integer *)
              assert (sv1.int_ty = sv2.int_ty);
              let res =
                match binop with
                | Div ->
                    if sv2.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.div sv1.value sv2.value)
                | Rem ->
                    (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                    if sv2.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.rem sv1.value sv2.value)
                | Add -> mk_scalar sv1.int_ty (Z.add sv1.value sv2.value)
                | Sub -> mk_scalar sv1.int_ty (Z.sub sv1.value sv2.value)
                | Mul -> mk_scalar sv1.int_ty (Z.mul sv1.value sv2.value)
                | BitXor -> raise Unimplemented
                | BitAnd -> raise Unimplemented
                | BitOr -> raise Unimplemented
                | Lt | Le | Ge | Gt | Shl | Shr | Ne | Eq ->
                    failwith "Unreachable"
              in
              match res with
              | Error err -> Error err
              | Ok sv ->
                  Ok { value = Concrete (Scalar sv); ty = Integer sv1.int_ty })
          | Shl | Shr -> raise Unimplemented
          | Ne | Eq -> failwith "Unreachable"
        in
        match res with Error _ -> Error Panic | Ok v -> Ok (ctx2, v))
    | _ -> failwith "Invalid inputs for binop"

let eval_rvalue (config : config) (ctx : eval_ctx) (rvalue : rvalue) :
    (eval_ctx * typed_value) eval_result =
  match rvalue with
  | Use op -> Ok (eval_operand config ctx op)
  | Ref (p, bkind) -> (
      match bkind with
      | Expressions.Shared | Expressions.TwoPhaseMut ->
          (* Access the value *)
          let access = if bkind = Expressions.Shared then Read else Write in
          let ctx2, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - simply a shared borrow with a fresh id *)
          let ctx3, bid = fresh_borrow_id ctx2 in
          let rv_ty = Types.Ref (Erased, v.ty, Shared) in
          let bc =
            if bkind = Expressions.Shared then SharedBorrow bid
            else InactivatedMutBorrow bid
          in
          let rv = { value = Borrow bc; ty = rv_ty } in
          (* Compute the value with which to replace the value at place p *)
          let nv =
            match v.value with
            | Loan (SharedLoan (bids, sv)) ->
                (* Shared loan: insert the new borrow id *)
                let bids1 = BorrowId.Set.add bid bids in
                { v with value = Loan (SharedLoan (bids1, sv)) }
            | _ ->
                (* Not a shared loan: add a wrapper *)
                let v' = Loan (SharedLoan (BorrowId.Set.singleton bid, v)) in
                { v with value = v' }
          in
          (* Update the value in the environment *)
          let env4 = write_place_unwrap config access p nv ctx3.env in
          (* Return *)
          Ok ({ ctx3 with env = env4 }, rv)
      | Expressions.Mut ->
          (* Access the value *)
          let access = Write in
          let ctx2, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
          let ctx3, bid = fresh_borrow_id ctx2 in
          let rv_ty = Types.Ref (Erased, v.ty, Mut) in
          let rv = { value = Borrow (MutBorrow (bid, v)); ty = rv_ty } in
          (* Compute the value with which to replace the value at place p *)
          let nv = { v with value = Loan (MutLoan bid) } in
          (* Update the value in the environment *)
          let env4 = write_place_unwrap config access p nv ctx3.env in
          (* Return *)
          Ok ({ ctx3 with env = env4 }, rv))
  | UnaryOp (unop, op) -> eval_unary_op config ctx unop op
  | BinaryOp (binop, op1, op2) -> eval_binary_op config ctx binop op1 op2
  | Discriminant p -> (
      (* Note that discriminant values have type `isize` *)
      (* Access the value *)
      let access = Read in
      let ctx1, v = prepare_rplace config access p ctx in
      match v.value with
      | Adt av -> (
          match av.variant_id with
          | None ->
              failwith
                "Invalid input for `discriminant`: structure instead of enum"
          | Some variant_id -> (
              let id = Z.of_int (VariantId.to_int variant_id) in
              match mk_scalar Isize id with
              | Error _ ->
                  failwith "Disciminant id out of range"
                  (* Should really never happen *)
              | Ok sv ->
                  Ok (ctx1, { value = Concrete (Scalar sv); ty = Integer Isize })
              ))
      | _ -> failwith "Invalid input for `discriminant`")
  | Aggregate (aggregate_kind, ops) -> raise Unimplemented
