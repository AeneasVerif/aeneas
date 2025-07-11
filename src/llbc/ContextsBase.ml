open Types
open Expressions
open Values
open Identifiers
module L = Logging

(** The local logger *)
let log = L.contexts_log

(** The [Id] module for dummy variables.

    Dummy variables are used to store values that we don't want to forget in the
    environment, because they contain borrows for instance, typically because
    they might be overwritten during an assignment. *)
module DummyVarId =
IdGen ()

type dummy_var_id = DummyVarId.id [@@deriving show, ord]

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

let ( region_id_counter,
      marked_region_ids,
      marked_region_ids_insert_from_int,
      fresh_region_id ) =
  RegionId.fresh_marked_stateful_generator ()

let ( abstraction_id_counter,
      marked_abstraction_ids,
      marked_abstraction_ids_insert_from_int,
      fresh_abstraction_id ) =
  AbstractionId.fresh_marked_stateful_generator ()

let loop_id_counter, fresh_loop_id = LoopId.fresh_stateful_generator ()

let fun_call_id_counter, fresh_fun_call_id =
  FunCallId.fresh_stateful_generator ()

let dummy_var_id_counter, fresh_dummy_var_id =
  DummyVarId.fresh_stateful_generator ()

(** We shouldn't need to reset the global counters, but it might be good to do
    it from time to time, for instance every time we start evaluating/
    synthesizing a function.

    The reasons are manifold:
    - it might prevent the counters from overflowing (although this seems
      extremely unlikely - as a side node: we have overflow checks to make sure
      the synthesis doesn't get impacted by potential overflows)
    - most importantly, it allows to always manipulate low values, which is
      always a lot more readable when debugging *)
let reset_global_counters () =
  symbolic_value_id_counter := SymbolicValueId.generator_zero;
  borrow_id_counter := BorrowId.generator_zero;
  region_id_counter := RegionId.generator_zero;
  abstraction_id_counter := AbstractionId.generator_zero;
  loop_id_counter := LoopId.generator_zero;
  (* We want the loop id to start at 1 *)
  let _ = fresh_loop_id () in
  fun_call_id_counter := FunCallId.generator_zero;
  dummy_var_id_counter := DummyVarId.generator_zero

(** Ancestor for {!type:env} iter visitor *)
class ['self] iter_env_base =
  object (_self : 'self)
    inherit [_] iter_abs
    method visit_local_id : 'env -> local_id -> unit = fun _ _ -> ()
    method visit_dummy_var_id : 'env -> dummy_var_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!type:env} map visitor *)
class ['self] map_env_base =
  object (_self : 'self)
    inherit [_] map_abs
    method visit_local_id : 'env -> local_id -> local_id = fun _ x -> x

    method visit_dummy_var_id : 'env -> dummy_var_id -> dummy_var_id =
      fun _ x -> x
  end

(** A binder used in an environment, to map a variable to a value *)
type real_var_binder = {
  index : local_id;  (** Unique variable identifier *)
  name : string option;  (** Possible name *)
}

(** A binder, for a "real" variable or a dummy variable *)
and var_binder = BVar of real_var_binder | BDummy of dummy_var_id

(** Environment value: mapping from variable to value, abstraction (only used in
    symbolic mode) or stack frame delimiter. *)
and env_elem =
  | EBinding of var_binder * typed_value
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
    },
  visitors
    {
      name = "map_env";
      variety = "map";
      ancestors = [ "map_env_base" ];
      nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
      concrete = true;
    }]
