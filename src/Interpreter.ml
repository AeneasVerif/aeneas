open Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module A = CfimAst

(* TODO: Change state-passing style to : st -> ... -> (st, v) *)
(* TODO: check that the value types are correct when evaluating *)
(* TODO: module Type = T, etc. *)

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
let rec check_borrows_in_value (check : V.borrow_content -> bool)
    (v : V.typed_value) : bool =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> true
  | V.Adt av -> FieldId.for_all (check_borrows_in_value check) av.field_values
  | V.Tuple values -> FieldId.for_all (check_borrows_in_value check) values
  | V.Assumed (Box bv) -> check_borrows_in_value check bv
  | V.Borrow bc -> (
      check bc
      &&
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> true
      | V.MutBorrow (_, mv) -> check_borrows_in_value check mv)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (_, sv) -> check_borrows_in_value check sv
      | V.MutLoan _ -> true)

(** Apply a predicate to all the loans in a value *)
let rec check_loans_in_value (check : V.loan_content -> bool)
    (v : V.typed_value) : bool =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> true
  | V.Adt av -> FieldId.for_all (check_loans_in_value check) av.field_values
  | V.Tuple values -> FieldId.for_all (check_loans_in_value check) values
  | V.Assumed (Box bv) -> check_loans_in_value check bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> true
      | V.MutBorrow (_, mv) -> check_loans_in_value check mv)
  | V.Loan lc -> (
      check lc
      &&
      match lc with
      | V.SharedLoan (_, sv) -> check_loans_in_value check sv
      | V.MutLoan _ -> true)

(** Lookup a loan content in a value *)
let rec lookup_loan_in_value (ek : exploration_kind) (l : V.BorrowId.id)
    (v : V.typed_value) : V.loan_content option =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> None
  | V.Adt av ->
      let values = FieldId.vector_to_list av.field_values in
      List.find_map (lookup_loan_in_value ek l) values
  | V.Tuple values ->
      let values = FieldId.vector_to_list values in
      List.find_map (lookup_loan_in_value ek l) values
  | V.Assumed (Box bv) -> lookup_loan_in_value ek l bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> None
      | V.MutBorrow (_, mv) ->
          if ek.enter_mut_borrows then lookup_loan_in_value ek l mv else None)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (bids, sv) ->
          if V.BorrowId.Set.mem l bids then Some lc
          else if ek.enter_shared_loans then lookup_loan_in_value ek l sv
          else None
      | V.MutLoan bid -> if bid = l then Some (V.MutLoan bid) else None)

(** Lookup a loan content.

    The loan is referred to by a borrow id.
 *)
let lookup_loan (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env) :
    V.loan_content =
  let lookup_loan_in_env_value (ev : C.env_value) : V.loan_content option =
    match ev with
    | C.Var (_, v) -> lookup_loan_in_value ek l v
    | C.Abs _ -> raise Unimplemented
    (* TODO *)
  in
  match List.find_map lookup_loan_in_env_value env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a loan content in a value.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let rec update_loan_in_value (ek : exploration_kind) (l : V.BorrowId.id)
    (nlc : V.loan_content) (v : V.typed_value) : V.typed_value =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> v
  | V.Adt av ->
      let values =
        FieldId.map (update_loan_in_value ek l nlc) av.field_values
      in
      let av = { av with field_values = values } in
      { v with value = Adt av }
  | V.Tuple values ->
      let values = FieldId.map (update_loan_in_value ek l nlc) values in
      { v with value = Tuple values }
  | V.Assumed (Box bv) ->
      { v with value = Assumed (Box (update_loan_in_value ek l nlc bv)) }
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> v
      | V.MutBorrow (bid, mv) ->
          if ek.enter_mut_borrows then
            let v' =
              V.Borrow (V.MutBorrow (bid, update_loan_in_value ek l nlc mv))
            in
            { v with value = v' }
          else v)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (bids, sv) ->
          if V.BorrowId.Set.mem l bids then { v with value = V.Loan nlc }
          else if ek.enter_shared_loans then
            let v' =
              V.Loan (V.SharedLoan (bids, update_loan_in_value ek l nlc sv))
            in
            { v with value = v' }
          else v
      | V.MutLoan bid -> if bid = l then { v with value = V.Loan nlc } else v)

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_loan (ek : exploration_kind) (l : V.BorrowId.id)
    (nlc : V.loan_content) (env : C.env) : C.env =
  let update_loan_in_env_value (ev : C.env_value) : C.env_value =
    match ev with
    | C.Var (vid, v) -> Var (vid, update_loan_in_value ek l nlc v)
    | C.Abs _ -> raise Unimplemented
    (* TODO *)
  in
  List.map update_loan_in_env_value env

(** Lookup a borrow content in a value *)
let rec lookup_borrow_in_value (ek : exploration_kind) (l : V.BorrowId.id)
    (v : V.typed_value) : V.borrow_content option =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> None
  | V.Adt av ->
      let values = FieldId.vector_to_list av.field_values in
      List.find_map (lookup_borrow_in_value ek l) values
  | V.Tuple values ->
      let values = FieldId.vector_to_list values in
      List.find_map (lookup_borrow_in_value ek l) values
  | V.Assumed (Box bv) -> lookup_borrow_in_value ek l bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow bid -> if l = bid then Some bc else None
      | V.InactivatedMutBorrow bid -> if l = bid then Some bc else None
      | V.MutBorrow (bid, mv) ->
          if bid = l then Some bc
          else if ek.enter_mut_borrows then lookup_borrow_in_value ek l mv
          else None)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (_, sv) ->
          if ek.enter_shared_loans then lookup_borrow_in_value ek l sv else None
      | V.MutLoan _ -> None)

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow (ek : exploration_kind) (l : V.BorrowId.id) (env : C.env) :
    V.borrow_content =
  let lookup_borrow_in_env_value (ev : C.env_value) =
    match ev with
    | C.Var (_, v) -> lookup_borrow_in_value ek l v
    | C.Abs _ -> raise Unimplemented
    (* TODO *)
  in
  match List.find_map lookup_borrow_in_env_value env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a borrow content in a value.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let rec update_borrow_in_value (ek : exploration_kind) (l : V.BorrowId.id)
    (nbc : V.borrow_content) (v : V.typed_value) : V.typed_value =
  match v.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> v
  | V.Adt av ->
      let values =
        FieldId.map (update_borrow_in_value ek l nbc) av.field_values
      in
      let av = { av with field_values = values } in
      { v with value = Adt av }
  | V.Tuple values ->
      let values = FieldId.map (update_borrow_in_value ek l nbc) values in
      { v with value = Tuple values }
  | V.Assumed (Box bv) ->
      { v with value = Assumed (Box (update_borrow_in_value ek l nbc bv)) }
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow bid | V.InactivatedMutBorrow bid ->
          if bid = l then { v with value = V.Borrow nbc } else v
      | V.MutBorrow (bid, mv) ->
          if bid = l then { v with value = V.Borrow nbc }
          else if ek.enter_mut_borrows then
            let v' =
              V.Borrow (V.MutBorrow (bid, update_borrow_in_value ek l nbc mv))
            in
            { v with value = v' }
          else v)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (bids, sv) ->
          if ek.enter_shared_loans then
            let v' =
              V.Loan (V.SharedLoan (bids, update_borrow_in_value ek l nbc sv))
            in
            { v with value = v' }
          else v
      | V.MutLoan _ -> v)

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_borrow (ek : exploration_kind) (l : V.BorrowId.id)
    (nbc : V.borrow_content) (env : C.env) : C.env =
  let update_borrow_in_env_value (ev : C.env_value) : C.env_value =
    match ev with
    | C.Var (vid, v) -> Var (vid, update_borrow_in_value ek l nbc v)
    | C.Abs _ -> raise Unimplemented
    (* TODO *)
  in
  List.map update_borrow_in_env_value env

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

(** Check if a value contains loans *)
let rec loans_in_value (v : V.typed_value) : bool =
  match v.V.value with
  | V.Concrete _ -> false
  | V.Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      List.exists loans_in_value fields
  | V.Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      List.exists loans_in_value fields
  | V.Assumed (Box bv) -> loans_in_value bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> false
      | V.MutBorrow (_, bv) -> loans_in_value bv)
  | V.Loan _ -> true
  | V.Bottom | V.Symbolic _ -> false

(** Return the first loan we find in a value *)
let rec get_first_loan_in_value (v : V.typed_value) : V.loan_content option =
  match v.V.value with
  | V.Concrete _ -> None
  | V.Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      get_first_loan_in_values fields
  | V.Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      get_first_loan_in_values fields
  | V.Assumed (Box bv) -> get_first_loan_in_value bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> None
      | V.MutBorrow (_, bv) -> get_first_loan_in_value bv)
  | V.Loan lc -> Some lc
  | V.Bottom | V.Symbolic _ -> None

and get_first_loan_in_values (vl : V.typed_value list) : V.loan_content option =
  match vl with
  | [] -> None
  | v :: vl' -> (
      match get_first_loan_in_value v with
      | Some lc -> Some lc
      | None -> get_first_loan_in_values vl')

(** Check if a value contains ⊥ *)
let rec bottom_in_value (v : V.typed_value) : bool =
  match v.V.value with
  | V.Concrete _ -> false
  | V.Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      List.exists bottom_in_value fields
  | V.Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      List.exists bottom_in_value fields
  | V.Assumed (Box bv) -> bottom_in_value bv
  | V.Borrow bc -> (
      match bc with
      | V.SharedBorrow _ | V.InactivatedMutBorrow _ -> false
      | V.MutBorrow (_, bv) -> bottom_in_value bv)
  | V.Loan lc -> (
      match lc with
      | V.SharedLoan (_, sv) -> bottom_in_value sv
      | V.MutLoan _ -> false)
  | V.Bottom -> true
  | V.Symbolic _ ->
      (* This depends on the regions which have ended *)
      raise Unimplemented

(** See [end_borrow_get_borrow_in_env] *)
let rec end_borrow_get_borrow_in_value config io l outer_borrows v0 :
    V.typed_value * borrow_lres =
  match v0.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> (v0, NotFound)
  | V.Assumed (Box bv) ->
      let bv', res =
        end_borrow_get_borrow_in_value config io l outer_borrows bv
      in
      (* Note that we allow boxes to outlive the inner borrows.
       * Also note that when using the symbolic mode, boxes will never
       * be "opened" and will be manipulated solely through functions
       * like new, deref, etc. which will enforce that we destroy
       * boxes upon ending inner borrows *)
      ({ v0 with value = Assumed (Box bv') }, res)
  | V.Adt adt ->
      let values = FieldId.vector_to_list adt.field_values in
      let values', res =
        end_borrow_get_borrow_in_values config io l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      ({ v0 with value = Adt { adt with field_values = values' } }, res)
  | V.Tuple values ->
      let values = FieldId.vector_to_list values in
      let values', res =
        end_borrow_get_borrow_in_values config io l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      ({ v0 with value = Tuple values' }, res)
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

and end_borrow_get_borrow_in_values config io l outer_borrows vl0 :
    V.typed_value list * borrow_lres =
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
let rec end_borrow_get_borrow_in_env (config : C.config) (io : inner_outer) l
    env0 : C.env * borrow_lres =
  match env0 with
  | [] -> ([], NotFound)
  | C.Var (x, v) :: env -> (
      match end_borrow_get_borrow_in_value config io l None v with
      | v', NotFound ->
          let env', res = end_borrow_get_borrow_in_env config io l env in
          (Var (x, v') :: env', res)
      | v', res -> (Var (x, v') :: env, res))
  | C.Abs _ :: _ ->
      assert (config.mode = SymbolicMode);
      raise Unimplemented

(** See [give_back_value]. *)
let rec give_back_value_to_value config bid (v : V.typed_value)
    (destv : V.typed_value) : V.typed_value =
  match destv.V.value with
  | V.Concrete _ | V.Bottom | V.Symbolic _ -> destv
  | V.Adt av ->
      let field_values =
        List.map
          (give_back_value_to_value config bid v)
          (FieldId.vector_to_list av.field_values)
      in
      let field_values = FieldId.vector_of_list field_values in
      { destv with value = Adt { av with field_values } }
  | V.Tuple values ->
      let values =
        List.map
          (give_back_value_to_value config bid v)
          (FieldId.vector_to_list values)
      in
      let values = FieldId.vector_of_list values in
      { destv with value = Tuple values }
  | V.Assumed (Box destv') ->
      {
        destv with
        value = Assumed (Box (give_back_value_to_value config bid v destv'));
      }
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
        List.map
          (give_back_shared_to_value config bid)
          (FieldId.vector_to_list av.field_values)
      in
      let field_values = FieldId.vector_of_list field_values in
      { destv with value = Adt { av with field_values } }
  | V.Tuple values ->
      let values =
        List.map
          (give_back_shared_to_value config bid)
          (FieldId.vector_to_list values)
      in
      let values = FieldId.vector_of_list values in
      { destv with value = Tuple values }
  | V.Assumed (Box destv') ->
      {
        destv with
        value = Assumed (Box (give_back_shared_to_value config bid destv'));
      }
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
  in
  List.map give_back_value_to_env_value env

(** Auxiliary function to end borrows.
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.
 *)
let give_back_shared config (bid : V.BorrowId.id) (env : C.env) : C.env =
  let give_back_shared_to_env_value ev : C.env_value =
    match ev with
    | C.Var (vid, destv) ->
        C.Var (vid, give_back_shared_to_value config bid destv)
    | C.Abs abs ->
        assert (config.mode = SymbolicMode);
        C.Abs (give_back_shared_to_abs config bid abs)
  in
  List.map give_back_shared_to_env_value env

(** When copying values, we duplicate the shared borrows. This is tantamount
    to reborrowing the shared value. The following function applies this change
    to an environment by inserting a new borrow id in the set of borrows tracked
    by a shared value, referenced by the [original_bid] argument.
 *)
let reborrow_shared (config : C.config) (original_bid : V.BorrowId.id)
    (new_bid : V.BorrowId.id) (env : C.env) : C.env =
  let rec reborrow_in_value (v : V.typed_value) : V.typed_value =
    match v.V.value with
    | V.Concrete _ | V.Bottom | V.Symbolic _ -> v
    | V.Adt av ->
        let fields = FieldId.vector_to_list av.field_values in
        let fields = List.map reborrow_in_value fields in
        let fields = FieldId.vector_of_list fields in
        { v with value = Adt { av with field_values = fields } }
    | V.Tuple fields ->
        let fields = FieldId.vector_to_list fields in
        let fields = List.map reborrow_in_value fields in
        let fields = FieldId.vector_of_list fields in
        { v with value = Tuple fields }
    | V.Assumed (Box bv) ->
        { v with value = Assumed (Box (reborrow_in_value bv)) }
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
  in
  List.map reborrow_in_ev env

(** End a borrow identified by its borrow id
    
    First lookup the borrow in the environment and replace it with [Bottom],
    then update the loan. Ends outer borrows before updating the borrow if
    it is necessary.
 *)
let rec end_borrow (config : C.config) (io : inner_outer) (l : V.BorrowId.id)
    (env0 : C.env) : C.env =
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

and end_borrows (config : C.config) (io : inner_outer) (lset : V.BorrowId.Set.t)
    (env0 : C.env) : C.env =
  V.BorrowId.Set.fold (fun id env -> end_borrow config io id env) lset env0

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
let promote_shared_loan_to_mut_loan (l : V.BorrowId.id) (env : C.env) :
    C.env * V.typed_value =
  (* Lookup the shared loan *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l env with
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
      let env1 = update_loan ek l (V.MutLoan l) env in
      (* Return *)
      (env1, sv)

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates a shared borrow to a mutable borrow.
 *)
let promote_inactivated_borrow_to_mut_borrow (l : V.BorrowId.id)
    (borrowed_value : V.typed_value) (env : C.env) : C.env =
  (* Lookup the inactivated borrow - note that we don't go inside borrows/loans:
     there can't be inactivated borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  match lookup_borrow ek l env with
  | V.SharedBorrow _ | V.MutBorrow (_, _) ->
      failwith "Expected an inactivated mutable borrow"
  | V.InactivatedMutBorrow _ ->
      (* Update it *)
      update_borrow ek l (V.MutBorrow (l, borrowed_value)) env

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let rec activate_inactivated_mut_borrow (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (env : C.env) : C.env =
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l env with
  | V.MutLoan _ -> failwith "Unreachable"
  | V.SharedLoan (bids, sv) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         inactivated borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let env' =
            match lc with
            | V.SharedLoan (bids, _) -> end_outer_borrows config bids env
            | V.MutLoan bid -> end_outer_borrow config bid env
          in
          (* Recursive call *)
          activate_inactivated_mut_borrow config io l env'
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value sv));
          let check_not_inactivated bc =
            match bc with V.InactivatedMutBorrow _ -> false | _ -> true
          in
          assert (not (check_borrows_in_value check_not_inactivated sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = V.BorrowId.Set.remove l bids in
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
  | FailSharedLoan of V.BorrowId.Set.t
      (** Failure because we couldn't go inside a shared loan *)
  | FailMutLoan of V.BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | FailInactivatedMutBorrow of V.BorrowId.id
      (** Failure because we couldn't go inside an inactivated mutable borrow
          (which should get activated) *)
  | FailSymbolic of (E.projection_elem * V.symbolic_proj_comp)
      (** Failure because we need to enter a symbolic value (and thus need to expand it) *)
  | FailBottom of (int * E.projection_elem * ety)
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
      assert (nv.ty = v.ty);
      Ok (env, { read = v; updated = nv })
  | pe :: p' -> (
      (* Match on the projection element and the value *)
      match (pe, v.V.value) with
      (* Field projection *)
      | Field (ProjAdt (_def_id, opt_variant_id), field_id), V.Adt adt -> (
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
              let nadt = V.Adt { adt with V.field_values = nvalues } in
              let updated = { v with value = nadt } in
              Ok (env1, { res with updated }))
      (* Tuples *)
      | Field (ProjTuple arity, field_id), V.Tuple values -> (
          assert (arity = FieldId.length values);
          let fv = FieldId.nth values field_id in
          (* Project *)
          match access_projection access env update p fv with
          | Error err -> Error err
          | Ok (env1, res) ->
              (* Update the field value *)
              let nvalues = FieldId.update_nth values field_id res.updated in
              let ntuple = V.Tuple nvalues in
              let updated = { v with value = ntuple } in
              Ok (env1, { res with updated })
          (* If we reach Bottom, it may mean we need to expand an uninitialized
           * enumeration value *))
      | Field (ProjAdt (_, Some _variant_id), _), V.Bottom ->
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
              let nv = { v with value = V.Assumed (V.Box res.updated) } in
              Ok (env1, { res with updated = nv }))
      (* Borrows *)
      | Deref, V.Borrow bc -> (
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
                    | Ok (env1, res) ->
                        (* Update the shared loan with the new value returned
                           by [access_projection] *)
                        let env2 =
                          update_loan ek bid
                            (V.SharedLoan (bids, res.updated))
                            env1
                        in
                        (* Return - note that we don't need to update the borrow itself *)
                        Ok (env2, { res with updated = v }))
              else Error (FailBorrow bc)
          | V.InactivatedMutBorrow bid -> Error (FailInactivatedMutBorrow bid)
          | V.MutBorrow (bid, bv) ->
              if access.enter_mut_borrows then
                match access_projection access env update p' bv with
                | Error err -> Error err
                | Ok (env1, res) ->
                    let nv =
                      {
                        v with
                        value = V.Borrow (V.MutBorrow (bid, res.updated));
                      }
                    in
                    Ok (env1, { res with updated = nv })
              else Error (FailBorrow bc))
      | _, V.Loan lc -> (
          match lc with
          | V.MutLoan bid -> Error (FailMutLoan bid)
          | V.SharedLoan (bids, sv) ->
              (* If we can enter shared loan, we ignore the loan. Pay attention
                 to the fact that we need to reexplore the *whole* place (i.e,
                 we mustn't ignore the current projection element *)
              if access.enter_shared_loans then
                match access_projection access env update (pe :: p') sv with
                | Error err -> Error err
                | Ok (env1, res) ->
                    let nv =
                      {
                        v with
                        value = V.Loan (V.SharedLoan (bids, res.updated));
                      }
                    in
                    Ok (env1, { res with updated = nv })
              else Error (FailSharedLoan bids))
      | ( _,
          ( V.Concrete _ | V.Adt _ | V.Tuple _ | V.Bottom | V.Assumed _
          | V.Borrow _ ) ) ->
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
  | Ok (env1, res) ->
      (* Update the value *)
      let env2 = C.env_update_var_value env1 p.var_id res.updated in
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
let read_place (config : C.config) (access : access_kind) (p : E.place)
    (env : C.env) : V.typed_value path_access_result =
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

let read_place_unwrap (config : C.config) (access : access_kind) (p : E.place)
    (env : C.env) : V.typed_value =
  match read_place config access p env with
  | Error _ -> failwith "Unreachable"
  | Ok v -> v

(** Update the value at a given place *)
let write_place (_config : C.config) (access : access_kind) (p : E.place)
    (nv : V.typed_value) (env : C.env) : C.env path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function substitutes the value with the new value *)
  let update _ = nv in
  match access_place access update p env with
  | Error err -> Error err
  | Ok (env1, _) ->
      (* We ignore the read value *)
      Ok env1

let write_place_unwrap (config : C.config) (access : access_kind) (p : E.place)
    (nv : V.typed_value) (env : C.env) : C.env =
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
let expand_bottom_value (config : C.config) (access : access_kind)
    (tyctx : type_def TypeDefId.vector) (p : E.place) (remaining_pes : int)
    (pe : E.projection_elem) (ty : ety) (env : C.env) : C.env =
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
          | _ -> failwith "Unreachable"
        in
        (* Initialize the expanded value *)
        let fields = FieldId.vector_to_list fields in
        let fields =
          List.map
            (fun f -> { V.value = Bottom; ty = erase_regions f.field_ty })
            fields
        in
        let fields = FieldId.vector_of_list fields in
        V.Adt
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
        let fields = List.map (fun ty -> { V.value = Bottom; ty }) tys in
        let fields = FieldId.vector_of_list fields in
        V.Tuple fields
    | _ -> failwith "Unreachable"
  in
  let nv = { V.value = nv; ty } in
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
let rec update_env_along_read_place (config : C.config) (access : access_kind)
    (p : E.place) (env : C.env) : C.env =
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
        | FailSymbolic (_pe, _sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (_, _, _) ->
            (* We can't expand [Bottom] values while reading them *)
            failwith "Found [Bottom] while reading a place"
        | FailBorrow _ -> failwith "Could not read a borrow"
      in
      update_env_along_read_place config access p env'

(** Update the environment to be able to write to a place.

    See [update_env_alond_read_place].
*)
let rec update_env_along_write_place (config : C.config) (access : access_kind)
    (tyctx : type_def TypeDefId.vector) (p : E.place) (nv : V.typed_value)
    (env : C.env) : C.env =
  (* Attempt to write the place: if it fails, update the environment and retry *)
  match write_place config access p nv env with
  | Ok env' -> env'
  | Error err ->
      let env' =
        match err with
        | FailSharedLoan bids -> end_outer_borrows config bids env
        | FailMutLoan bid -> end_outer_borrow config bid env
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config Outer bid env
        | FailSymbolic (_pe, _sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (remaining_pes, pe, ty) ->
            (* Expand the [Bottom] value *)
            expand_bottom_value config access tyctx p remaining_pes pe ty env
        | FailBorrow _ -> failwith "Could not write to a borrow"
      in
      update_env_along_write_place config access tyctx p nv env'

exception UpdateEnv of C.env
(** Small utility used to break control-flow *)

(** Collect the borrows at a given place (by ending borrows when we find some
    loans).

    This is used when reading, borrowing, writing to a value. We typically
    first call [update_env_along_read_place] or [update_env_along_write_place]
    to get access to the value, then call this function to "prepare" the value.
 *)
let rec collect_borrows_at_place (config : C.config) (access : access_kind)
    (p : E.place) (env : C.env) : C.env =
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
        match v.V.value with
        | V.Concrete _ -> ()
        | V.Bottom ->
            failwith "Unreachable"
            (* note that we don't really need to fail here *)
        | V.Symbolic _ ->
            (* Nothing to do for symbolic values - note that if the value needs
               to be copied, etc. we perform additional checks later *)
            ()
        | V.Adt adt -> FieldId.iter inspect_update adt.field_values
        | V.Tuple values -> FieldId.iter inspect_update values
        | V.Assumed (Box v) -> inspect_update v
        | V.Borrow bc -> (
            match bc with
            | V.SharedBorrow _ -> ()
            | V.MutBorrow (_, tv) -> inspect_update tv
            | V.InactivatedMutBorrow bid ->
                (* We need to activate inactivated borrows *)
                let env' =
                  activate_inactivated_mut_borrow config Inner bid env
                in
                raise (UpdateEnv env'))
        | V.Loan lc -> (
            match lc with
            | V.SharedLoan (bids, ty) -> (
                (* End the loans if we need a modification access, otherwise dive into
                   the shared value *)
                match access with
                | Read -> inspect_update ty
                | Write | Move ->
                    let env' = end_outer_borrows config bids env in
                    raise (UpdateEnv env'))
            | V.MutLoan bid ->
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
let rec drop_borrows_at_place (config : C.config) (p : E.place) (env : C.env) :
    C.env =
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
        | V.Adt adt -> FieldId.iter (inspect_update end_loans) adt.field_values
        | V.Tuple values -> FieldId.iter (inspect_update end_loans) values
        | V.Assumed (Box v) -> inspect_update end_loans v
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
                raise (UpdateEnv (end_inner_borrow config bid env))
            | V.InactivatedMutBorrow bid ->
                (* We need to activate inactivated borrows - later, we will
                 * actually end it *)
                let env' =
                  activate_inactivated_mut_borrow config Inner bid env
                in
                raise (UpdateEnv env'))
        | V.Loan lc ->
            if (* If we can, end the loans, otherwise ignore *)
               end_loans then
              (* We need to end all loans. Note that as all the borrows inside
                 the value at place p should already have ended, the borrows
                 associated to the loans we find here should be borrows from
                 outside this value: we need to call [end_outer_borrow(s)]
                 (we can't ignore outer borrows this time).
              *)
              match lc with
              | V.SharedLoan (bids, _) ->
                  raise (UpdateEnv (end_outer_borrows config bids env))
              | V.MutLoan bid ->
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
let rec copy_value (config : C.config) (ctx : C.eval_ctx) (v : V.typed_value) :
    C.eval_ctx * V.typed_value =
  match v.V.value with
  | V.Concrete _ -> (ctx, v)
  | V.Adt av ->
      let fields = FieldId.vector_to_list av.field_values in
      let ctx', fields = List.fold_left_map (copy_value config) ctx fields in
      let fields = FieldId.vector_of_list fields in
      (ctx', { v with V.value = V.Adt { av with field_values = fields } })
  | V.Tuple fields ->
      let fields = FieldId.vector_to_list fields in
      let ctx', fields = List.fold_left_map (copy_value config) ctx fields in
      let fields = FieldId.vector_of_list fields in
      (ctx', { v with V.value = V.Tuple fields })
  | V.Bottom -> failwith "Can't copy ⊥"
  | V.Assumed _ -> failwith "Can't copy an assumed value"
  | V.Borrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | SharedBorrow bid ->
          let ctx', bid' = C.fresh_borrow_id ctx in
          let env'' = reborrow_shared config bid bid' ctx'.env in
          let ctx'' = { ctx' with env = env'' } in
          (ctx'', { v with V.value = V.Borrow (SharedBorrow bid') })
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
let constant_value_to_typed_value (ctx : C.eval_ctx) (ty : ety)
    (cv : E.operand_constant_value) : V.typed_value =
  (* Check the type while converting *)
  match (ty, cv) with
  (* Unit *)
  | Types.Tuple [], Unit ->
      { V.value = V.Tuple (FieldId.vector_of_list []); ty }
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
        V.Adt
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
  | Types.Bool, ConstantValue (Bool v) -> { V.value = V.Concrete (Bool v); ty }
  | Types.Char, ConstantValue (Char v) -> { V.value = V.Concrete (Char v); ty }
  | Types.Str, ConstantValue (String v) ->
      { V.value = V.Concrete (String v); ty }
  | Types.Integer int_ty, ConstantValue (V.Scalar v) ->
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
  let env1 = update_env_along_read_place config access p ctx.env in
  let env2 = collect_borrows_at_place config access p env1 in
  let v = read_place_unwrap config access p env2 in
  let ctx2 = { ctx with env = env2 } in
  (ctx2, v)

(** When we need to evaluate several operands (for a function call for instance),
    we need to prepare *all* the values by ending borrows, etc. *then* update them
    (by moving them, borrowing them, etc.).

    The reason is that borrows in some of the values we access may reference
    some of the other values: we may not be able to update the borrows if those
    values have, say, been moved (and are not present in the environment anymore).

    For this reason, we split [eval_operand] into two functions:
    - [eval_operand_prepare]
    - [eval_operand_apply]
    which are then used in [eval_operand] and [eval_operands].
 *)
let eval_operand_prepare (config : C.config) (ctx : C.eval_ctx) (op : E.operand)
    : C.eval_ctx =
  match op with
  | Expressions.Constant (_, _) -> ctx (* nothing to do *)
  | Expressions.Copy p ->
      let access = Read in
      fst (prepare_rplace config access p ctx)
  | Expressions.Move p ->
      let access = Move in
      fst (prepare_rplace config access p ctx)

(** See [eval_operand_prepare] (which should have been called before) *)
let eval_operand_apply (config : C.config) (ctx : C.eval_ctx) (op : E.operand) :
    C.eval_ctx * V.typed_value =
  match op with
  | Expressions.Constant (ty, cv) ->
      let v = constant_value_to_typed_value ctx ty cv in
      (ctx, v)
  | Expressions.Copy p ->
      (* Access the value *)
      let access = Read in
      let v = read_place_unwrap config access p ctx.env in
      (* Copy the value *)
      assert (not (bottom_in_value v));
      copy_value config ctx v
  | Expressions.Move p -> (
      (* Access the value *)
      let access = Move in
      let v = read_place_unwrap config access p ctx.env in
      (* Move the value *)
      assert (not (bottom_in_value v));
      let bottom = { V.value = Bottom; ty = v.ty } in
      match write_place config access p bottom ctx.env with
      | Error _ -> failwith "Unreachable"
      | Ok env1 ->
          let ctx1 = { ctx with env = env1 } in
          (ctx1, v))

(** Evaluate an operand.

    WARNING: it is ok to use this function only if we have exactly one
    operand to evaluate. If there are several, use [eval_operands].
    Otherwise, we may break invariants (if some values refer to other
    values via borrows).
 *)
let eval_operand (config : C.config) (ctx : C.eval_ctx) (op : E.operand) :
    C.eval_ctx * V.typed_value =
  let ctx1 = eval_operand_prepare config ctx op in
  eval_operand_apply config ctx1 op

(** Evaluate several operands.

 *)
let eval_operands (config : C.config) (ctx : C.eval_ctx) (ops : E.operand list)
    : C.eval_ctx * V.typed_value list =
  (* First prepare the values to end/activate the borrows *)
  let ctx1 =
    List.fold_left (fun ctx op -> eval_operand_prepare config ctx op) ctx ops
  in
  (* Then actually apply the operands to move, borrow, copy... *)
  List.fold_left_map (fun ctx op -> eval_operand_apply config ctx op) ctx1 ops

let eval_two_operands (config : C.config) (ctx : C.eval_ctx) (op1 : E.operand)
    (op2 : E.operand) : C.eval_ctx * V.typed_value * V.typed_value =
  match eval_operands config ctx [ op1; op2 ] with
  | ctx', [ v1; v2 ] -> (ctx', v1, v2)
  | _ -> failwith "Unreachable"

let eval_unary_op (config : C.config) (ctx : C.eval_ctx) (unop : E.unop)
    (op : E.operand) : (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operand *)
  let ctx1, v = eval_operand config ctx op in
  (* Apply the unop *)
  match (unop, v.V.value) with
  | E.Not, V.Concrete (Bool b) ->
      Ok (ctx1, { v with V.value = V.Concrete (Bool (not b)) })
  | E.Neg, V.Concrete (V.Scalar sv) -> (
      let i = Z.neg sv.V.value in
      match mk_scalar sv.int_ty i with
      | Error _ -> Error Panic
      | Ok sv -> Ok (ctx1, { v with V.value = V.Concrete (V.Scalar sv) }))
  | (E.Not | E.Neg), Symbolic _ -> raise Unimplemented (* TODO *)
  | _ -> failwith "Invalid value for unop"

let eval_binary_op (config : C.config) (ctx : C.eval_ctx) (binop : E.binop)
    (op1 : E.operand) (op2 : E.operand) :
    (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operands *)
  let ctx2, v1, v2 = eval_two_operands config ctx op1 op2 in
  if
    (* Binary operations only apply on integer values, but when we check for
     * equality *)
    binop = Eq || binop = Ne
  then (
    (* Equality/inequality check is primitive only on primitive types *)
    assert (v1.ty = v2.ty);
    let b = v1 = v2 in
    Ok (ctx2, { V.value = V.Concrete (Bool b); ty = Types.Bool }))
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
                | E.Lt -> Z.lt sv1.V.value sv1.V.value
                | E.Le -> Z.leq sv1.V.value sv1.V.value
                | E.Ge -> Z.geq sv1.V.value sv1.V.value
                | E.Gt -> Z.gt sv1.V.value sv1.V.value
                | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
                | E.BitOr | E.Shl | E.Shr | E.Ne | E.Eq ->
                    failwith "Unreachable"
              in
              Ok { V.value = V.Concrete (Bool b); ty = Types.Bool }
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
        match res with Error _ -> Error Panic | Ok v -> Ok (ctx2, v))
    | _ -> failwith "Invalid inputs for binop"

(** Evaluate an rvalue in a given context: return the updated context and
    the computed value *)
let eval_rvalue (config : C.config) (ctx : C.eval_ctx) (rvalue : E.rvalue) :
    (C.eval_ctx * V.typed_value) eval_result =
  match rvalue with
  | E.Use op -> Ok (eval_operand config ctx op)
  | E.Ref (p, bkind) -> (
      match bkind with
      | E.Shared | E.TwoPhaseMut ->
          (* Access the value *)
          let access = if bkind = E.Shared then Read else Write in
          let ctx2, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - simply a shared borrow with a fresh id *)
          let ctx3, bid = C.fresh_borrow_id ctx2 in
          let rv_ty = Types.Ref (Erased, v.ty, Shared) in
          let bc =
            if bkind = E.Shared then V.SharedBorrow bid
            else V.InactivatedMutBorrow bid
          in
          let rv = { V.value = V.Borrow bc; ty = rv_ty } in
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
          (* Update the value in the environment *)
          let env4 = write_place_unwrap config access p nv ctx3.env in
          (* Return *)
          Ok ({ ctx3 with env = env4 }, rv)
      | E.Mut ->
          (* Access the value *)
          let access = Write in
          let ctx2, v = prepare_rplace config access p ctx in
          (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
          let ctx3, bid = C.fresh_borrow_id ctx2 in
          let rv_ty = Types.Ref (Erased, v.ty, Mut) in
          let rv = { V.value = V.Borrow (V.MutBorrow (bid, v)); ty = rv_ty } in
          (* Compute the value with which to replace the value at place p *)
          let nv = { v with V.value = V.Loan (V.MutLoan bid) } in
          (* Update the value in the environment *)
          let env4 = write_place_unwrap config access p nv ctx3.env in
          (* Return *)
          Ok ({ ctx3 with env = env4 }, rv))
  | E.UnaryOp (unop, op) -> eval_unary_op config ctx unop op
  | E.BinaryOp (binop, op1, op2) -> eval_binary_op config ctx binop op1 op2
  | E.Discriminant p -> (
      (* Note that discriminant values have type `isize` *)
      (* Access the value *)
      let access = Read in
      let ctx1, v = prepare_rplace config access p ctx in
      match v.V.value with
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
                  Ok
                    ( ctx1,
                      { V.value = V.Concrete (V.Scalar sv); ty = Integer Isize }
                    )))
      | _ -> failwith "Invalid input for `discriminant`")
  | E.Aggregate (aggregate_kind, ops) -> (
      (* Evaluate the operands *)
      let ctx1, values = eval_operands config ctx ops in
      let values = FieldId.vector_of_list values in
      (* Match on the aggregate kind *)
      match aggregate_kind with
      | E.AggregatedTuple ->
          let tys =
            List.map (fun v -> v.V.ty) (FieldId.vector_to_list values)
          in
          Ok (ctx1, { V.value = Tuple values; ty = Types.Tuple tys })
      | E.AggregatedAdt (def_id, opt_variant_id, regions, types) ->
          (* Sanity checks *)
          let type_def = C.ctx_lookup_type_def ctx def_id in
          assert (
            RegionVarId.length type_def.region_params = List.length regions);
          let expected_field_types =
            Subst.ctx_adt_get_instantiated_field_types ctx1 def_id
              opt_variant_id types
          in
          assert (expected_field_types = FieldId.map (fun v -> v.V.ty) values);
          (* Construct the value *)
          let av =
            {
              V.def_id;
              V.variant_id = opt_variant_id;
              V.regions;
              V.types;
              V.field_values = values;
            }
          in
          let aty = Types.Adt (def_id, regions, types) in
          Ok (ctx1, { V.value = Adt av; ty = aty }))

(** Result of evaluating a statement *)
type statement_eval_res = Unit | Break of int | Continue of int | Panic

let rec eval_statement (ctx : C.eval_ctx) (st : A.statement) :
    C.eval_ctx * statement_eval_res =
  match st with
  | A.Assign (p, rvalue) -> raise Unimplemented
  | A.FakeRead p -> raise Unimplemented
  | A.SetDiscriminant (p, variant_id) -> raise Unimplemented
  | A.Drop p -> raise Unimplemented
  | A.Assert assertion -> raise Unimplemented
  | A.Call call -> raise Unimplemented
  | A.Panic -> raise Unimplemented
  | A.Return -> raise Unimplemented
  | A.Break i -> raise Unimplemented
  | A.Continue i -> raise Unimplemented
  | A.Nop -> (ctx, Unit)
