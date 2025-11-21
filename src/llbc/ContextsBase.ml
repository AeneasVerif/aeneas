open Types
open Values
module L = Logging

(** The local logger *)
let log = L.contexts_log

(*
(** Some global counters.

    Note that those counters were initially stored in {!eval_ctx} values, but it
    proved better to make them global and stateful:
    - when branching (and thus executing on several paths with different
      contexts) it is better to really have unique ids everywhere (and not have
      fresh ids shared by several contexts even though introduced after the
      branching) because at some point we might need to merge the different
      contexts
    - also, it is a lot more convenient to not store those counters in contexts
      objects

    ============= **WARNING**: ============= Pay attention when playing with
    closures, as you may not always generate fresh identifiers without noticing
    it, especially when using type abbreviations. For instance, consider the
    following:
    {[
      type fun_type = unit -> ...
      fn f x : fun_type =
        let id = fresh_id () in
        ...
        fun () -> ...

      let g = f x in   // <-- the fresh identifier gets generated here
      let x1 = g () in // <-- no fresh generation here
      let x2 = g () in
      ...
    ]}

    This is why, in such cases, we often introduce all the inputs, even when
    they are not used (which happens!).
    {[
      fn f x : fun_type =
       fun .. ->
        let id = fresh_id () in
        ...
    ]}

    Note that in practice, we never reuse closures, except when evaluating a
    branching in the execution (which is fine, because the branches evaluate
    independentely of each other). Still, it is always a good idea to be
    defensive.

    However, the same problem arises with logging.

    Also, a more defensive way would be to not use global references, and store
    the counters in the evaluation context. This is actually what was originally
    done, before we updated the code to use global counters because it proved
    more convenient (and even before updating the code of the interpreter to use
    CPS). *)
let ( symbolic_value_id_counter,
      marked_symbolic_value_ids,
      marked_symbolic_value_ids_insert_from_int,
      fresh_symbolic_value_id ) =
  SymbolicValueId.fresh_marked_stateful_generator ()

let ( borrow_id_counter,
      marked_borrow_ids,
      marked_borrow_ids_insert_from_int,
      fresh_borrow_id ) =
  BorrowId.fresh_marked_stateful_generator ()

let ( shared_borrow_id_counter,
      marked_shared_borrow_ids,
      marked_shared_borrow_ids_insert_from_int,
      fresh_shared_borrow_id ) =
  SharedBorrowId.fresh_marked_stateful_generator ()

let ( region_id_counter,
      marked_region_ids,
      marked_region_ids_insert_from_int,
      fresh_region_id ) =
  RegionId.fresh_marked_stateful_generator ()

let abs_id_counter, marked_abs_ids, marked_abs_ids_insert_from_int, fresh_abs_id
    =
  AbsId.fresh_marked_stateful_generator ()

let ( abs_fvar_id_counter,
      marked_abs_fvar_ids,
      marked_abs_fvar_ids_insert_from_int,
      fresh_abs_fvar_id ) =
  AbsFVarId.fresh_marked_stateful_generator ()

let loop_id_counter, fresh_loop_id = LoopId.fresh_stateful_generator ()

let fun_call_id_counter, fresh_fun_call_id =
  FunCallId.fresh_stateful_generator ()

let dummy_var_id_counter, fresh_dummy_var_id =
  DummyVarId.fresh_stateful_generator ()

(** We don't need to reset the global counters, but it is good to do it from
    time to time, for instance every time we start evaluating/ synthesizing a
    function.

    The reasons are manifold:
    - it might prevent the counters from overflowing (although this seems
      extremely unlikely - as a side node: we have overflow checks to make sure
      the synthesis doesn't get impacted by potential overflows)
    - most importantly, it allows to always manipulate small values, which is
      always a lot more readable when debugging *)
let reset_global_counters () =
  (* This one comes from Values.ml *)
  abs_fvar_id_counter := AbsFVarId.generator_zero;
  (* *)
  symbolic_value_id_counter := SymbolicValueId.generator_zero;
  borrow_id_counter := BorrowId.generator_zero;
  shared_borrow_id_counter := SharedBorrowId.generator_zero;
  region_id_counter := RegionId.generator_zero;
  abs_id_counter := AbsId.generator_zero;
  loop_id_counter := LoopId.generator_zero;
  let _ =
    (* We want the loop id to start at 1 *)
    fresh_loop_id ()
  in
  fun_call_id_counter := FunCallId.generator_zero;
  dummy_var_id_counter := DummyVarId.generator_zero
    *)

type marked_ids = {
  symbolic_value_ids : SymbolicValueId.Set.t;
  fun_call_ids : FunCallId.Set.t;
  dummy_var_ids : DummyVarId.Set.t;
  borrow_ids : BorrowId.Set.t;
  shared_borrow_ids : SharedBorrowId.Set.t;
  abs_ids : AbsId.Set.t;
  region_ids : RegionId.Set.t;
  abs_fvar_ids : AbsFVarId.Set.t;
  pure_fvar_ids : Pure.FVarId.Set.t;
  loop_ids : LoopId.Set.t;
  meta_ids : MetaId.Set.t;
}

let empty_marked_ids : marked_ids =
  {
    symbolic_value_ids = SymbolicValueId.Set.empty;
    fun_call_ids = FunCallId.Set.empty;
    dummy_var_ids = DummyVarId.Set.empty;
    borrow_ids = BorrowId.Set.empty;
    shared_borrow_ids = SharedBorrowId.Set.empty;
    abs_ids = AbsId.Set.empty;
    region_ids = RegionId.Set.empty;
    abs_fvar_ids = AbsFVarId.Set.empty;
    pure_fvar_ids = Pure.FVarId.Set.empty;
    loop_ids = LoopId.Set.empty;
    meta_ids = MetaId.Set.empty;
  }
