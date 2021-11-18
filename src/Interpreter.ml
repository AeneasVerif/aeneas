open Types
open Values

type env_value = Var of string * typed_value | Abs of abs

type env = env_value list

type 'a result = Stuck | Panic | Res of 'a

type interpreter_mode = ConcreteMode | SymbolicMode

type config = { mode : interpreter_mode; check_invariants : bool }

type outer_borrows = Borrows of BorrowId.Set.t | Borrow of BorrowId.id

(** Borrow lookup result *)
type borrow_lres =
  | Outer of outer_borrows
  | FoundMut of typed_value
  | FoundShared
  | NotFound

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
        ( unwrap_res_to_outer_or outer_borrows FoundShared,
          { v0 with value = Bottom } )
      else (NotFound, v0)
  | Borrow (InactivatedMutBorrow l') ->
      if l = l' then
        ( unwrap_res_to_outer_or outer_borrows FoundShared,
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

(*let rec end_borrow_get_borrow_in_env config l env : borrow_lres * env =
  match env with
  | [] -> NotFound
  | Var (x, v) :: env' -> (
      match end_borrow_get_borrow_in_value config None l v with
      | NotFound, v' ->
          let res, env'' = end_borrow_get_borrow_in_env config l env' in
          (res, Var (x, v') :: env'')
      | res, v' -> (res, Var (x, v') :: env'))
  | Abs _ :: _ -> unimplemented __LOC__*)

(*let rec end_borrow config (env0 : env) (env : env) (l : BorrowId.id) =
  match env with
  | [] -> []
  | Var (x, v) :: env' -> unimplemented __LOC__
  | Abs _ :: _ -> (
      match config.mode with
      | Concrete -> unreachable __LOC__
      | Symbolic -> unimplemented __LOC__)*)
