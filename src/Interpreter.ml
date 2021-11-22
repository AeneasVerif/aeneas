open Types
open Values
open Print.Values
open Errors

type env_value = Var of string * typed_value | Abs of abs

type env = env_value list

let env_value_to_string (fmt : value_formatter) (ev : env_value) : string =
  match ev with
  | Var (vname, tv) -> vname ^ " -> " ^ typed_value_to_string fmt tv
  | Abs abs -> abs_to_string fmt abs

let env_to_string (fmt : value_formatter) (env : env) : string =
  "{\n"
  ^ String.concat ";\n"
      (List.map (fun ev -> "  " ^ env_value_to_string fmt ev) env)
  ^ "\n}"

type 'a result = Stuck | Panic | Res of 'a

type interpreter_mode = ConcreteMode | SymbolicMode

type config = { mode : interpreter_mode; check_invariants : bool }

type outer_borrows = Borrows of BorrowId.Set.t | Borrow of BorrowId.id

(** Borrow lookup result *)
type borrow_lres =
  | NotFound
  | Outer of outer_borrows
  | FoundMut of typed_value
  | FoundShared
  | FoundInactivatedMut

let update_if_none opt x = match opt with None -> Some x | _ -> opt

let unwrap_res_to_outer_or opt default =
  match opt with Some x -> Outer x | None -> default

let rec end_borrow_get_borrow_in_value config l outer_borrows v0 :
    borrow_lres * typed_value =
  match v0.value with
  | Concrete _ | Bottom | Symbolic _ -> (NotFound, v0)
  | Assumed (Box bv) ->
      let res, bv' = end_borrow_get_borrow_in_value config l outer_borrows bv in
      (* Note that we allow boxes to outlive the inner borrows.
       * Also note that when using the symbolic mode, boxes will never
       * be "opened" and will be manipulated solely through functions
       * like new, deref, etc. which will enforce that we destroy
       * boxes upon ending inner borrows *)
      (res, { v0 with value = Assumed (Box bv') })
  | Adt adt ->
      let values = FieldId.vector_to_list adt.field_values in
      let res, values' =
        end_borrow_get_borrow_in_values config l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      (res, { v0 with value = Adt { adt with field_values = values' } })
  | Tuple values ->
      let values = FieldId.vector_to_list values in
      let res, values' =
        end_borrow_get_borrow_in_values config l outer_borrows values
      in
      let values' = FieldId.vector_of_list values' in
      (res, { v0 with value = Tuple values' })
  | Loan (MutLoan _) -> (NotFound, v0)
  | Loan (SharedLoan (borrows, v)) ->
      let outer_borrows = update_if_none outer_borrows (Borrows borrows) in
      let res, v' = end_borrow_get_borrow_in_value config l outer_borrows v in
      (res, { value = Loan (SharedLoan (borrows, v')); ty = v0.ty })
  | Borrow (SharedBorrow l') ->
      if l = l' then
        ( unwrap_res_to_outer_or outer_borrows FoundInactivatedMut,
          { v0 with value = Bottom } )
      else (NotFound, v0)
  | Borrow (InactivatedMutBorrow l') ->
      if l = l' then
        ( unwrap_res_to_outer_or outer_borrows FoundInactivatedMut,
          { v0 with value = Bottom } )
      else (NotFound, v0)
  | Borrow (MutBorrow (l', bv)) ->
      if l = l' then
        ( unwrap_res_to_outer_or outer_borrows (FoundMut bv),
          { v0 with value = Bottom } )
      else
        let outer_borrows = update_if_none outer_borrows (Borrow l') in
        let res, bv' =
          end_borrow_get_borrow_in_value config l outer_borrows bv
        in
        (res, { v0 with value = Borrow (MutBorrow (l', bv')) })

and end_borrow_get_borrow_in_values config l outer_borrows vl0 :
    borrow_lres * typed_value list =
  match vl0 with
  | [] -> (NotFound, vl0)
  | v :: vl -> (
      let res, v' = end_borrow_get_borrow_in_value config l outer_borrows v in
      match res with
      | NotFound ->
          let res, vl' =
            end_borrow_get_borrow_in_values config l outer_borrows vl
          in
          (res, v' :: vl')
      | _ -> (res, v' :: vl))

let rec end_borrow_get_borrow_in_env (config : config) l env0 :
    borrow_lres * env =
  match env0 with
  | [] -> (NotFound, [])
  | Var (x, v) :: env -> (
      match end_borrow_get_borrow_in_value config l None v with
      | NotFound, v' ->
          let res, env' = end_borrow_get_borrow_in_env config l env in
          (res, Var (x, v') :: env')
      | res, v' -> (res, Var (x, v') :: env))
  | Abs _ :: _ -> (
      match config.mode with
      | ConcreteMode ->
          (* There can't be abstractions if we run in concrete mode *)
          unreachable __LOC__
      | SymbolicMode ->
          (* TODO *)
          unimplemented __LOC__)

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

let give_back_value_to_abs (_config : config) _bid _v _abs : abs =
  (* TODO *)
  unimplemented __LOC__

let give_back_value_to_env_value config bid v ev : env_value =
  match ev with
  | Var (vname, destv) ->
      Var (vname, give_back_value_to_value config bid v destv)
  | Abs abs -> (
      match config.mode with
      | ConcreteMode -> unreachable __LOC__
      | SymbolicMode -> Abs (give_back_value_to_abs config bid v abs))

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

let give_back_shared_to_abs _config _bid _abs : abs =
  (* TODO *)
  unimplemented __LOC__

let give_back_shared_to_env_value (config : config) bid ev : env_value =
  match ev with
  | Var (vname, destv) -> Var (vname, give_back_shared_to_value config bid destv)
  | Abs abs -> (
      match config.mode with
      | ConcreteMode -> unreachable __LOC__
      | SymbolicMode -> Abs (give_back_shared_to_abs config bid abs))

let give_back_value (config : config) (bid : BorrowId.id) (v : typed_value)
    (env0 : env) : env =
  List.map (give_back_value_to_env_value config bid v) env0

let give_back_shared config (bid : BorrowId.id) (env0 : env) : env =
  List.map (give_back_shared_to_env_value config bid) env0

let rec end_borrow (config : config) (l : BorrowId.id) (env0 : env) : env =
  match end_borrow_get_borrow_in_env config l env0 with
  (* It is possible that we can't find a borrow in symbolic mode (ending
   * an abstraction may end several borrows at once *)
  | NotFound, env -> (
      match config.mode with
      | ConcreteMode -> unreachable __LOC__
      | SymbolicMode -> env)
  (* If we found outer borrows: end those borrows first *)
  | Outer outer_borrows, env ->
      let env' =
        match outer_borrows with
        | Borrows bids ->
            BorrowId.Set.fold (fun id env -> end_borrow config id env) bids env
        | Borrow bid -> end_borrow config bid env
      in
      end_borrow config l env'
  (* If found mut: give the value back *)
  | FoundMut tv, env -> give_back_value config l tv env
  (* If found shared: remove the borrow id from the loan set of the shared value *)
  | FoundShared, env -> give_back_shared config l env
  | FoundInactivatedMut, _env ->
      (* We found an inactivated mut: activate it *)
      unimplemented __LOC__
