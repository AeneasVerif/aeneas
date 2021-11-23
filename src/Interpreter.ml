open Types
open Values
open Expressions
open Print.Values
open Errors

type env_value = Var of VarId.id * typed_value | Abs of abs

type env = env_value list

let env_value_to_string (fmt : value_formatter) (ev : env_value) : string =
  match ev with
  | Var (vid, tv) ->
      var_id_to_string vid ^ " -> " ^ typed_value_to_string fmt tv
  | Abs abs -> abs_to_string fmt abs

let env_to_string (fmt : value_formatter) (env : env) : string =
  "{\n"
  ^ String.concat ";\n"
      (List.map (fun ev -> "  " ^ env_value_to_string fmt ev) env)
  ^ "\n}"

type 'a eval_result = Stuck | Panic | Res of 'a

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
  | Abs _ :: _ ->
      assert (config.mode = SymbolicMode);
      raise Unimplemented

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
  raise Unimplemented

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
  raise Unimplemented

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

let give_back_shared config (bid : BorrowId.id) (env : env) : env =
  let give_back_shared_to_env_value ev : env_value =
    match ev with
    | Var (vid, destv) -> Var (vid, give_back_shared_to_value config bid destv)
    | Abs abs ->
        assert (config.mode = SymbolicMode);
        Abs (give_back_shared_to_abs config bid abs)
  in
  List.map give_back_shared_to_env_value env

(** End a borrow identified by its borrow id
    
    First lookup the borrow in the environment and replace it with [Bottom],
    then update the loan. Ends outer borrows before updating the borrow if
    it is necessary.
 *)
let rec end_borrow (config : config) (l : BorrowId.id) (env0 : env) : env =
  match end_borrow_get_borrow_in_env config l env0 with
  (* It is possible that we can't find a borrow in symbolic mode (ending
   * an abstraction may end several borrows at once *)
  | NotFound, env ->
      assert (config.mode = SymbolicMode);
      env
  (* If we found outer borrows: end those borrows first *)
  | Outer outer_borrows, env ->
      let env' =
        match outer_borrows with
        | Borrows bids -> end_borrows config bids env
        | Borrow bid -> end_borrow config bid env
      in
      end_borrow config l env'
  (* If found mut: give the value back *)
  | FoundMut tv, env -> give_back_value config l tv env
  (* If found shared or inactivated mut: remove the borrow id from the loan set of the shared value *)
  | (FoundShared | FoundInactivatedMut), env -> give_back_shared config l env

and end_borrows (config : config) (lset : BorrowId.Set.t) (env0 : env) : env =
  BorrowId.Set.fold (fun id env -> end_borrow config id env) lset env0

let rec lookup_loan_in_value (config : config) (l : BorrowId.id)
    (v : typed_value) : loan_content option =
  match v.value with
  | Concrete _ | Bottom | Symbolic _ -> None
  | Adt av ->
      let values = FieldId.vector_to_list av.field_values in
      List.find_map (lookup_loan_in_value config l) values
  | Tuple values ->
      let values = FieldId.vector_to_list values in
      List.find_map (lookup_loan_in_value config l) values
  | Assumed (Box bv) -> lookup_loan_in_value config l bv
  | Borrow bc -> (
      match bc with
      | SharedBorrow _ | InactivatedMutBorrow _ -> None
      | MutBorrow (_, mv) -> lookup_loan_in_value config l mv)
  | Loan lc -> (
      match lc with
      | SharedLoan (bids, sv) ->
          if BorrowId.Set.mem l bids then Some lc
          else lookup_loan_in_value config l sv
      | MutLoan _ -> None)

(** Lookup a loan - note that we never lookup loans in abstractions *)
let lookup_loan_in_env_value (config : config) (l : BorrowId.id)
    (ev : env_value) : loan_content option =
  match ev with
  | Var (_, v) -> lookup_loan_in_value config l v
  | Abs _ ->
      assert (config.mode = SymbolicMode);
      None

(** Lookup a loan content from a borrow id.
    Note that we never lookup loans in the abstractions.
 *)
let lookup_loan_from_borrow_id (config : config) (l : BorrowId.id) (env : env) :
    loan_content =
  match List.find_map (lookup_loan_in_env_value config l) env with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** If a shared value is borrowed exactly once, we can promote this shared loan
    to a mutable loan. The function returns the borrowed value and the updated
    environment.
 *)
let promote_shared_loan_to_mut_loan (config : config) (l : BorrowId.id)
    (env0 : env) : typed_value * env =
  (* Promote inside a value: return the borrowed value and the updated value.
   * The return value is an option: we return None if we didn't update anything. *)
  let rec promote_in_value (v : typed_value) :
      (typed_value * typed_value) option =
    match v.value with
    | Concrete _ | Bottom | Symbolic _ -> None
    | Adt av -> (
        let values = FieldId.vector_to_list av.field_values in
        match promote_in_values values with
        | None -> None
        | Some (borrowed, values') ->
            let av =
              { av with field_values = FieldId.vector_of_list values' }
            in
            Some (borrowed, { v with value = Adt av }))
    | Tuple values -> (
        let values = FieldId.vector_to_list values in
        match promote_in_values values with
        | None -> None
        | Some (borrowed, values') ->
            let values' = FieldId.vector_of_list values' in
            Some (borrowed, { v with value = Tuple values' }))
    | Borrow _ ->
        (* We can't promote inside a borrow *)
        None
    | Loan lc -> (
        match lc with
        | SharedLoan (bids, tv) ->
            (* Note that we can't promote *inside* shared values *)
            if BorrowId.Set.mem l bids && BorrowId.Set.cardinal bids = 1 then
              Some (tv, { v with value = Loan (MutLoan l) })
            else None
        | MutLoan _ -> None)
    | Assumed (Box bv) -> (
        match promote_in_value bv with
        | None -> None
        | Some (borrowed, bv') ->
            Some (borrowed, { v with value = Assumed (Box bv') }))
  (* Promote inside a list of values: return the borrowed value (if we promoted one)
   * and the list of updated values *)
  and promote_in_values (vl : typed_value list) :
      (typed_value * typed_value list) option =
    match vl with
    | [] -> None
    | v :: vl' -> (
        match promote_in_value v with
        | None -> (
            match promote_in_values vl' with
            | None -> None
            | Some (borrowed, vl'') -> Some (borrowed, v :: vl''))
        | Some (borrowed, nv) -> Some (borrowed, nv :: vl'))
  in
  (* Promote in the environment *)
  let rec promote_in_env (env0 : env) : typed_value * env =
    match env0 with
    | [] -> failwith "Unreachable"
    | Var (vid, v) :: env -> (
        match promote_in_value v with
        | None ->
            let borrowed, env' = promote_in_env env in
            (borrowed, Var (vid, v) :: env')
        | Some (borrowed, new_v) -> (borrowed, Var (vid, new_v) :: env))
    | Abs abs :: env ->
        (* We don't promote inside abstractions *)
        assert (config.mode = SymbolicMode);
        let borrowed, env' = promote_in_env env in
        (borrowed, Abs abs :: env')
  in
  (* Apply *)
  promote_in_env env0

let promote_inactivated_borrow_to_mut_borrow (config : config) (l : BorrowId.id)
    (borrowed_value : typed_value) (env0 : env) : env =
  let rec promote_in_value (v : typed_value) : typed_value =
    match v.value with
    | Concrete _ | Bottom | Symbolic _ -> v
    | Adt av ->
        let values = FieldId.vector_to_list av.field_values in
        let values = List.map promote_in_value values in
        let values = FieldId.vector_of_list values in
        { v with value = Adt { av with field_values = values } }
    | Tuple values ->
        let values = FieldId.vector_to_list values in
        let values = List.map promote_in_value values in
        let values = FieldId.vector_of_list values in
        { v with value = Tuple values }
    | Assumed (Box av) -> { v with value = Assumed (Box (promote_in_value av)) }
    | Borrow bc -> (
        (* We shouldn't need to promote inside borrowed values: here we just need
         * to check if the borrow is the inactivated mutable borrow we are looking
         * for *)
        match bc with
        | SharedBorrow _ | MutBorrow (_, _) -> v
        | InactivatedMutBorrow bid -> if bid == l then borrowed_value else v)
    | Loan _ ->
        (* We shouldn't need to promote inside loans *)
        v
  in
  let promote_in_env_value (ev : env_value) : env_value =
    match ev with
    | Var (name, v) -> Var (name, promote_in_value v)
    | Abs abs ->
        assert (config.mode = SymbolicMode);
        Abs abs
  in
  List.map promote_in_env_value env0

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let activate_inactivated_mut_borrow (config : config) (l : BorrowId.id)
    (env : env) : env =
  match lookup_loan_from_borrow_id config l env with
  | MutLoan _ -> failwith "Unreachable"
  | SharedLoan (bids, _) ->
      (* End the borrows which borrow from the value, at the exception of the borrow
       * we want to promote *)
      let bids = BorrowId.Set.remove l bids in
      let env' = end_borrows config bids env in
      (* Promote the loan *)
      let borrowed_value, env'' =
        promote_shared_loan_to_mut_loan config l env'
      in
      (* Promote the borrow *)
      promote_inactivated_borrow_to_mut_borrow config l borrowed_value env''

(** Paths *)

type path_access = Read | Write

(** When we fail reading from or writing to a path, it might be because we
 ** need to update the environment by ending borrows, expanding symbolic
 ** values, etc. *)
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

(** Result of evaluating a path (reading from a path/writing to a path)
    
    Note that when we fail, we return information used to update the
    environment, as well as the 
*)
type 'a path_access_result = ('a, path_fail_kind) result
(** The result of reading from/writing to a place *)

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
  | Some v -> v

(** Read the value at the end of a projection *)
let rec read_projection (config : config) (access : path_access) (env : env)
    (p : projection) (v : typed_value) : typed_value path_access_result =
  match p with
  | [] -> Ok v
  | pe :: p' -> (
      (* The projection is non-empty: we need to enter all the loans we find,
       * if we are allowed to do so *)
      let rec enter_loans (v : typed_value) : typed_value path_access_result =
        match v.value with
        | Loan lc -> (
            match (access, lc) with
            (* We can enter shared loans only if we are in "read" mode *)
            | Read, SharedLoan (_, sv) -> enter_loans sv
            | Write, SharedLoan (bids, _) -> Error (FailSharedLoan bids)
            (* We always have to end mutable loans *)
            | _, MutLoan bid -> Error (FailMutLoan bid))
        | _ -> Ok v
      in
      (* Enter inside the loans and match on the resulting value *)
      match enter_loans v with
      | Ok v -> (
          (* Match on the projection element and the value *)
          match (pe, v.value) with
          (* Field projection *)
          | Field (ProjAdt (_def_id, opt_variant_id), field_id), Adt adt ->
              (* Check that the projection is consistent with the current value *)
              (match (opt_variant_id, adt.variant_id) with
              | None, None -> ()
              | Some vid, Some vid' ->
                  if vid <> vid' then failwith "Unreachable"
              | _ -> failwith "Unreachable");
              (* Actually project *)
              let fv = FieldId.nth adt.field_values field_id in
              read_projection config access env p fv
          (* Tuples *)
          | Field (ProjTuple _, field_id), Tuple values ->
              let fv = FieldId.nth values field_id in
              read_projection config access env p fv
          (* We can expand [Bottom] values only while *writing* to places *)
          | _, Bottom -> failwith "Unreachable"
          (* Symbolic value: needs to be expanded *)
          | _, Symbolic sp ->
              assert (config.mode = SymbolicMode);
              (* Expand the symbolic value *)
              Error (FailSymbolic (pe, sp))
          (* Box dereferencement *)
          | DerefBox, Assumed (Box bv) ->
              read_projection config access env p' bv
          (* Borrow dereferencement *)
          | Deref, Borrow bc -> (
              match (access, bc) with
              | Read, SharedBorrow bid ->
                  let sv = lookup_shared_value_from_borrow_id bid env in
                  read_projection config access env p' sv
              | Write, SharedBorrow _ -> failwith "Unreachable"
              | _, MutBorrow (_, bv) -> read_projection config access env p' bv
              (* We need to activate inactivated mutable borrows *)
              | _, InactivatedMutBorrow bid ->
                  Error (FailInactivatedMutBorrow bid))
          (* Remaining cases: error. We enumerate all the value variants
           * on purpose, to make sure we statically catch errors if we
           * modify the [value] definition. *)
          | _, (Concrete _ | Adt _ | Tuple _ | Assumed _ | Borrow _ | Loan _) ->
              failwith "Unreachable")
      (* Entering loans failed *)
      | res -> res)

(** Read the value at the end of a place *)
let read_place (config : config) (access : path_access) (p : place) (env0 : env)
    : typed_value path_access_result =
  let rec read_in_env env : typed_value path_access_result =
    match env with
    | [] -> failwith "Unreachable"
    | Var (vid, v) :: env' ->
        if vid = p.var_id then read_projection config access env0 p.projection v
        else read_in_env env'
    | Abs _ :: env' -> read_in_env env'
  in
  read_in_env env0

(** Update the value at the end of a projection *)
let rec write_projection (config : config) (new_value : typed_value)
    (p : projection) (v : typed_value) : typed_value path_access_result =
  match p with
  | [] -> Ok v
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
          (* Update the field value *)
          match write_projection config new_value p fv with
          | Error err -> Error err
          | Ok nfv ->
              (* Reinsert the field value *)
              let nvalues = FieldId.update_nth adt.field_values field_id nfv in
              let nadt = Adt { adt with field_values = nvalues } in
              Ok { v with value = nadt })
      (* Tuples *)
      | Field (ProjTuple _, field_id), Tuple values -> (
          (* Project *)
          let fv = FieldId.nth values field_id in
          (* Update the field value *)
          match write_projection config new_value p fv with
          | Error err -> Error err
          | Ok nfv ->
              (* Reinsert the field value *)
              let nvalues = FieldId.update_nth values field_id nfv in
              let ntuple = Tuple nvalues in
              Ok { v with value = ntuple })
      (* If we reach Bottom, it may mean we need to expand an uninitialized
       * enumeration value *)
      | Field (ProjAdt (_, Some _variant_id), _), Bottom ->
          Error (FailBottom (1 + List.length p', pe, v.ty))
      (* Symbolic value: needs to be expanded *)
      | _, Symbolic sp ->
          assert (config.mode = SymbolicMode);
          (* Expand the symbolic value *)
          Error (FailSymbolic (pe, sp))
      (* Box dereferencement *)
      | DerefBox, Assumed (Box bv) -> (
          (* Update the boxed value *)
          match write_projection config new_value p' bv with
          | Error err -> Error err
          | Ok nbv -> Ok { v with value = Assumed (Box nbv) })
      (* Borrow dereferencement *)
      | Deref, Borrow bc -> (
          match bc with
          | SharedBorrow _ ->
              (* We can't update inside shared borrows *)
              failwith "Unreachable"
          | MutBorrow (bid, bv) -> (
              match write_projection config new_value p' bv with
              | Error err -> Error err
              | Ok nbv -> Ok { v with value = Borrow (MutBorrow (bid, nbv)) })
          (* We need to activate inactivated mutable borrows *)
          | InactivatedMutBorrow bid -> Error (FailInactivatedMutBorrow bid))
      (* We can never enter loans *)
      | _, Loan (SharedLoan (bids, _)) -> Error (FailSharedLoan bids)
      (* We also always have to end mutable loans *)
      | _, Loan (MutLoan bid) -> Error (FailMutLoan bid)
      (* Remaining cases: error. We enumerate all the value variants
       * on purpose, to make sure we statically catch errors if we
       * modify the [value] definition. *)
      | _, (Concrete _ | Adt _ | Tuple _ | Bottom | Assumed _ | Borrow _) ->
          failwith "Unreachable")

(** Update the value at the end of a place *)
let write_place (config : config) (nv : typed_value) (p : place) (env0 : env) :
    env path_access_result =
  let rec write_in_env env : env path_access_result =
    match env with
    | [] -> failwith "Unreachable"
    | Var (vid, v) :: env' -> (
        if vid = p.var_id then
          match write_projection config nv p.projection v with
          | Ok nv -> Ok (Var (vid, nv) :: env')
          | Error res -> Error res
        else
          match write_in_env env' with
          | Ok env'' -> Ok (Var (vid, v) :: env'')
          | res -> res)
    | Abs abs :: env' -> (
        match write_in_env env' with
        | Ok env'' -> Ok (Abs abs :: env'')
        | res -> res)
  in
  write_in_env env0

(** Auxiliary function to expand [Bottom] values

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
(*let expand_bottom_value (config : config) (tyctx : type_def TypeDefId.vector)
    (p : place) (env : env) (remaining_pes : int) (pe : projection_elem)
    (ty : ety) : env =
  let *)

(** Update the environment to be able to read a place.

    When reading a place, we may be stuck along the way because some value
    is borrowed, we reach a symbolic value, etc. In this situation [read_place]
    fails while returning precise information about the failure. This function
    uses this information to update the environment (by ending borrows,
    expanding symbolic values) until we manage to fully read the place.
 *)
let rec update_env_along_read_place (config : config) (access : path_access)
    (p : place) (env : env) : typed_value * env =
  (* Attempt to read the place: if it fails, update the environment and retry *)
  match read_place config access p env with
  | Ok v -> (v, env)
  | Error err ->
      let env' =
        match err with
        | FailSharedLoan bids -> end_borrows config bids env
        | FailMutLoan bid -> end_borrow config bid env
        | FailInactivatedMutBorrow bid ->
            activate_inactivated_mut_borrow config bid env
        | FailSymbolic (pe, sp) ->
            (* Expand the symbolic value *)
            raise Unimplemented
        | FailBottom (remaining_pes, pe, ty) ->
            (* We can't expand [Bottom] values while reading them *)
            failwith "Unreachable"
      in
      update_env_along_read_place config access p env'
