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
  | Var (vid, destv) -> Var (vid, give_back_value_to_value config bid v destv)
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
  | Var (vid, destv) -> Var (vid, give_back_shared_to_value config bid destv)
  | Abs abs -> (
      match config.mode with
      | ConcreteMode -> unreachable __LOC__
      | SymbolicMode -> Abs (give_back_shared_to_abs config bid abs))

let give_back_value (config : config) (bid : BorrowId.id) (v : typed_value)
    (env : env) : env =
  List.map (give_back_value_to_env_value config bid v) env

let give_back_shared config (bid : BorrowId.id) (env : env) : env =
  List.map (give_back_shared_to_env_value config bid) env

(** End a borrow identified by its borrow id
    
    First lookup the borrow in the environment and replace it with [Bottom],
    then update the loan. Ends outer borrows before updating the borrow if
    it is necessary.
 *)
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
  | Abs _ -> (
      match config.mode with
      | ConcreteMode -> unreachable __LOC__
      | SymbolicMode -> None)

(** Lookup a loan content from a borrow id.
    Note that we never lookup loans in the abstractions.
 *)
let lookup_loan_from_borrow_id (config : config) (l : BorrowId.id) (env : env) :
    loan_content =
  match List.find_map (lookup_loan_in_env_value config l) env with
  | None -> unreachable __LOC__
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
    | [] -> unreachable __LOC__
    | Var (vid, v) :: env -> (
        match promote_in_value v with
        | None ->
            let borrowed, env' = promote_in_env env in
            (borrowed, Var (vid, v) :: env')
        | Some (borrowed, new_v) -> (borrowed, Var (vid, new_v) :: env))
    | Abs abs :: env ->
        (* We don't promote inside abstractions *)
        if config.mode = ConcreteMode then unreachable __LOC__
        else
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
        if config.mode = ConcreteMode then unreachable __LOC__ else Abs abs
  in
  List.map promote_in_env_value env0

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let activate_inactivated_mut_borrow (config : config) (l : BorrowId.id)
    (env : env) : env =
  match lookup_loan_from_borrow_id config l env with
  | MutLoan _ -> unreachable __LOC__
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

(** The result of reading from/writing to a place *)
type 'a path_access_result =
  | Success of 'a  (** Success *)
  | SharedLoan of BorrowId.Set.t
      (** Failure because we couldn't go inside a shared loan *)
  | MutLoan of BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | InactivatedMutBorrow of BorrowId.id
      (** Failure because we couldn't go inside an inactivated mutable borrow
          (which should get activated) *)
  | Failed
      (** Failure for another reason (ex.: couldn't go inside a shared borrow... *)

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
    | Abs _ -> unimplemented __LOC__
  in
  match List.find_map lookup_in_env_value env with
  | None -> unreachable __LOC__
  | Some v -> v

(** Read the value at the end of a projection *)
let rec read_projection (config : config) (access : path_access) (env : env)
    (p : projection) (v : typed_value) : typed_value path_access_result =
  match p with
  | [] -> Success v
  | pe :: p' -> (
      match (pe, v.value) with
      | _, Concrete _ | _, Bottom -> Failed
      | _, Symbolic _ -> (
          match config.mode with
          | ConcreteMode -> unreachable __LOC__
          | SymbolicMode ->
              (* Expand the symbolic value *)
              (* TODO *)
              unimplemented __LOC__)
      | DerefBox, Assumed (Box bv) -> read_projection config access env p' bv
      | Deref, Borrow bc -> (
          match (access, bc) with
          | Read, SharedBorrow bid ->
              let sv = lookup_shared_value_from_borrow_id bid env in
              read_projection config access env p' sv
          | Write, SharedBorrow _ -> Failed
          | _, MutBorrow (_, bv) -> read_projection config access env p' bv
          | _, InactivatedMutBorrow bid -> InactivatedMutBorrow bid)
      | _, Loan lc -> (
          match (access, lc) with
          | Read, SharedLoan (_, sv) ->
              read_projection config access env (pe :: p') sv
          | Write, SharedLoan (bids, _) -> SharedLoan bids
          | _, MutLoan bid -> MutLoan bid)
      | _ -> unreachable __LOC__)

(** Read the value at the end of a place *)
let read_place (config : config) (access : path_access) (p : place) (env0 : env)
    : typed_value path_access_result =
  let rec read_in_env env : typed_value path_access_result =
    match env with
    | [] -> unreachable __LOC__
    | Var (vid, v) :: env' ->
        if vid = p.var_id then read_projection config access env0 p.projection v
        else read_in_env env'
    | Abs _ :: env' -> read_in_env env'
  in
  read_in_env env0
