open Types
open Values
open LlbcAst
module V = Values
open ValuesUtils
module M = Modules

(** Some global counters.
 *
 * Note that those counters were initially stored in [eval_ctx] values,
 * but it proved better to make them global and stateful:
 * - when branching (and thus executing on several paths with different
 *   contexts) it is better to really have unique ids everywhere (and
 *   not have fresh ids shared by several contexts even though introduced
 *   after the branching) because at some point we might need to merge the
 *   different contexts
 * - also, it is a lot more convenient to not store those counters in contexts
 *   objects
 *
 * =============
 * **WARNING**:
 * =============
 * Pay attention when playing with closures, as you may not always generate
 * fresh identifiers without noticing it, especially when using type abbreviations.
 * For instance, consider the following:
 * ```
 * type fun_type = unit -> ...
 * fn f x : fun_type =
 *   let id = fresh_id () in
 *   ...
 *
 * let g = f x in   // <-- the fresh identifier gets generated here
 * let x1 = g () in // <-- no fresh generation here
 * let x2 = g () in
 * ...
 * ```
 *
 * This is why, in such cases, we often introduce all the inputs, even
 * when they are not used (which happens!).
 * ```
 * fn f x : fun_type =
 *  fun .. ->
 *   let id = fresh_id () in
 *   ...
 * ```
 *
 * Note that in practice, we never reuse closures, except when evaluating
 * a branching in the execution (which is fine, because the branches evaluate
 * independentely of each other). Still, it is always a good idea to be
 * defensive.
 *
 * However, the same problem arises with logging. 
 *
 * Also, a more defensive way would be to not use global references, and
 * store the counters in the evaluation context. This is actually what was
 * originally done, before we updated the code to use global counters because
 * it proved more convenient (and even before updating the code of the
 * interpreter to use CPS).
 *)

let symbolic_value_id_counter, fresh_symbolic_value_id =
  SymbolicValueId.fresh_stateful_generator ()

let borrow_id_counter, fresh_borrow_id = BorrowId.fresh_stateful_generator ()

let region_id_counter, fresh_region_id = RegionId.fresh_stateful_generator ()

let abstraction_id_counter, fresh_abstraction_id =
  AbstractionId.fresh_stateful_generator ()

let fun_call_id_counter, fresh_fun_call_id =
  FunCallId.fresh_stateful_generator ()

(** We shouldn't need to reset the global counters, but it might be good to
    do it from time to time, for instance every time we start evaluating/
    synthesizing a function.
    
    The reasons are manifold:
    - it might prevent the counters from overflowing (although this seems
      extremely unlikely - as a side node: we have overflow checks to make
      sure the synthesis doesn't get impacted by potential overflows)
    - most importantly, it allows to always manipulate low values, which
      is always a lot more readable when debugging
 *)
let reset_global_counters () =
  symbolic_value_id_counter := SymbolicValueId.generator_zero;
  borrow_id_counter := BorrowId.generator_zero;
  region_id_counter := RegionId.generator_zero;
  abstraction_id_counter := AbstractionId.generator_zero;
  fun_call_id_counter := FunCallId.generator_zero

type binder = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;  (** Possible name *)
}
[@@deriving show]
(** A binder used in an environment, to map a variable to a value *)

(** Environment value: mapping from variable to value, abstraction (only
    used in symbolic mode) or stack frame delimiter.
    
    TODO: rename Var (-> Binding?)
 *)
type env_elem =
  | Var of (binder option[@opaque]) * typed_value
      (** Variable binding - the binder is None if the variable is a dummy variable
          (we use dummy variables to store temporaries while doing bookkeeping such
           as ending borrows for instance). *)
  | Abs of abs
  | Frame
[@@deriving
  show,
    visitors
      {
        name = "iter_env_elem";
        variety = "iter";
        ancestors = [ "iter_abs" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_env_elem";
        variety = "map";
        ancestors = [ "map_abs" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]

type env = env_elem list
[@@deriving
  show,
    visitors
      {
        name = "iter_env";
        variety = "iter";
        ancestors = [ "iter_env_elem" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      },
    visitors
      {
        name = "map_env";
        variety = "map";
        ancestors = [ "map_env_elem" ];
        nude = true (* Don't inherit [VisitorsRuntime.iter] *);
        concrete = true;
      }]

type interpreter_mode = ConcreteMode | SymbolicMode [@@deriving show]

type config = {
  mode : interpreter_mode;
      (** Concrete mode (interpreter) or symbolic mode (for synthesis) **)
  check_invariants : bool;
      (** Check that invariants are maintained whenever we execute a statement *)
  greedy_expand_symbolics_with_borrows : bool;
      (** Expand all symbolic values containing borrows upon introduction - allows
          to use restrict ourselves to a simpler model for the projectors over
          symbolic values.
          The interpreter fails if doing this requires to do a branching (because
          we need to expand an enumeration with strictly more than one variant)
          or if we need to expand a recursive type (because this leads to looping).
       *)
  allow_bottom_below_borrow : bool;
      (** Experimental.
  
          We sometimes want to temporarily break the invariant that there is no
          bottom value below a borrow. If this value is true, we don't check
          the invariant, and the rule becomes: we can't end a borrow *if* it contains
          a bottom value. The consequence is that it becomes ok to temporarily
          have bottom below a borrow, if we put something else inside before ending
          the borrow.
          
          For instance, when evaluating an assignment, we move the value which
          will be overwritten then do some administrative tasks with the borrows,
          then move the rvalue to its destination. We currently want to be able
          to check the invariants every time we end a borrow/an abstraction,
          meaning at intermediate steps of the assignment where the invariants
          might actually be broken.
       *)
  return_unit_end_abs_with_no_loans : bool;
      (** If a function doesn't return any borrows, we can immediately call
          its backward functions. If this option is on, whenever we call a
          function *and* this function returns unit, we immediately end all the
          abstractions which are introduced and don't contain loans. This can be
          useful to make the code cleaner (the backward function is introduced
          where the function call happened) and make sure all forward functions
          with no return value are followed by a backward function.
       *)
}
[@@deriving show]

type partial_config = {
  check_invariants : bool;
  greedy_expand_symbolics_with_borrows : bool;
  allow_bottom_below_borrow : bool;
  return_unit_end_abs_with_no_loans : bool;
}
(** See [config] *)

let config_of_partial (mode : interpreter_mode) (config : partial_config) :
    config =
  {
    mode;
    check_invariants = config.check_invariants;
    greedy_expand_symbolics_with_borrows =
      config.greedy_expand_symbolics_with_borrows;
    allow_bottom_below_borrow = config.allow_bottom_below_borrow;
    return_unit_end_abs_with_no_loans = config.return_unit_end_abs_with_no_loans;
  }

type type_context = {
  type_decls_groups : M.type_declaration_group TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
  type_infos : TypesAnalysis.type_infos;
}
[@@deriving show]

type fun_context = {
  fun_decls : fun_decl FunDeclId.Map.t;
}
[@@deriving show]

type global_context = {
  global_decls : global_decl GlobalDeclId.Map.t;
}
[@@deriving show]

type eval_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  global_context : global_context;
  type_vars : type_var list;
  env : env;
  ended_regions : RegionId.Set.t;
}
[@@deriving show]
(** Evaluation context *)

let lookup_type_var (ctx : eval_ctx) (vid : TypeVarId.id) : type_var =
  TypeVarId.nth ctx.type_vars vid

let opt_binder_has_vid (bv : binder option) (vid : VarId.id) : bool =
  match bv with Some bv -> bv.index = vid | None -> false

let ctx_lookup_binder (ctx : eval_ctx) (vid : VarId.id) : binder =
  (* TOOD: we might want to stop at the end of the frame *)
  let rec lookup env =
    match env with
    | [] ->
        raise (Invalid_argument ("Variable not found: " ^ VarId.to_string vid))
    | Var (var, _) :: env' ->
        if opt_binder_has_vid var vid then Option.get var else lookup env'
    | (Abs _ | Frame) :: env' -> lookup env'
  in
  lookup ctx.env

(** TODO: make this more efficient with maps *)
let ctx_lookup_type_decl (ctx : eval_ctx) (tid : TypeDeclId.id) : type_decl =
  TypeDeclId.Map.find tid ctx.type_context.type_decls

(** TODO: make this more efficient with maps *)
let ctx_lookup_fun_decl (ctx : eval_ctx) (fid : FunDeclId.id) : fun_decl =
  FunDeclId.Map.find fid ctx.fun_context.fun_decls

(** TODO: make this more efficient with maps *)
let ctx_lookup_global_decl (ctx : eval_ctx) (gid : GlobalDeclId.id) : global_decl =
  GlobalDeclId.Map.find gid ctx.global_context.global_decls

(** Retrieve a variable's value in an environment *)
let env_lookup_var_value (env : env) (vid : VarId.id) : typed_value =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec lookup env =
    match env with
    | [] -> failwith "Unexpected"
    | Var (var, v) :: env' ->
        if opt_binder_has_vid var vid then v else lookup env'
    | Abs _ :: env' -> lookup env'
    | Frame :: _ -> failwith "End of frame"
  in
  lookup env

(** Retrieve a variable's value in an evaluation context *)
let ctx_lookup_var_value (ctx : eval_ctx) (vid : VarId.id) : typed_value =
  env_lookup_var_value ctx.env vid

(** Update a variable's value in an environment

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let env_update_var_value (env : env) (vid : VarId.id) (nv : typed_value) : env =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec update env =
    match env with
    | [] -> failwith "Unexpected"
    | Var (var, v) :: env' ->
        if opt_binder_has_vid var vid then Var (var, nv) :: env'
        else Var (var, v) :: update env'
    | Abs abs :: env' -> Abs abs :: update env'
    | Frame :: _ -> failwith "End of frame"
  in
  update env

let var_to_binder (var : var) : binder = { index = var.index; name = var.name }

(** Update a variable's value in an evaluation context.

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let ctx_update_var_value (ctx : eval_ctx) (vid : VarId.id) (nv : typed_value) :
    eval_ctx =
  { ctx with env = env_update_var_value ctx.env vid nv }

(** Push a variable in the context's environment.

    Checks that the pushed variable and its value have the same type (this
    is important).
*)
let ctx_push_var (ctx : eval_ctx) (var : var) (v : typed_value) : eval_ctx =
  assert (var.var_ty = v.ty);
  let bv = var_to_binder var in
  { ctx with env = Var (Some bv, v) :: ctx.env }

(** Push a list of variables.

    Checks that the pushed variables and their values have the same type (this
    is important).
*)
let ctx_push_vars (ctx : eval_ctx) (vars : (var * typed_value) list) : eval_ctx
    =
  assert (
    List.for_all
      (fun (var, (value : typed_value)) -> var.var_ty = value.ty)
      vars);
  let vars =
    List.map (fun (var, value) -> Var (Some (var_to_binder var), value)) vars
  in
  let vars = List.rev vars in
  { ctx with env = List.append vars ctx.env }

(** Push a dummy variable in the context's environment. *)
let ctx_push_dummy_var (ctx : eval_ctx) (v : typed_value) : eval_ctx =
  { ctx with env = Var (None, v) :: ctx.env }

(** Pop the first dummy variable from a context's environment. *)
let ctx_pop_dummy_var (ctx : eval_ctx) : eval_ctx * typed_value =
  let rec pop_var (env : env) : env * typed_value =
    match env with
    | [] -> failwith "Could not find a dummy variable"
    | Var (None, v) :: env -> (env, v)
    | ee :: env ->
        let env, v = pop_var env in
        (ee :: env, v)
  in
  let env, v = pop_var ctx.env in
  ({ ctx with env }, v)

(** Read the first dummy variable in a context's environment. *)
let ctx_read_first_dummy_var (ctx : eval_ctx) : typed_value =
  let rec read_var (env : env) : typed_value =
    match env with
    | [] -> failwith "Could not find a dummy variable"
    | Var (None, v) :: _env -> v
    | _ :: env -> read_var env
  in
  read_var ctx.env

(** Push an uninitialized variable (which thus maps to [Bottom]) *)
let ctx_push_uninitialized_var (ctx : eval_ctx) (var : var) : eval_ctx =
  ctx_push_var ctx var (mk_bottom var.var_ty)

(** Push a list of uninitialized variables (which thus map to [Bottom]) *)
let ctx_push_uninitialized_vars (ctx : eval_ctx) (vars : var list) : eval_ctx =
  let vars = List.map (fun v -> (v, mk_bottom v.var_ty)) vars in
  ctx_push_vars ctx vars

let env_lookup_abs (env : env) (abs_id : V.AbstractionId.id) : V.abs =
  let rec lookup env =
    match env with
    | [] -> failwith "Unexpected"
    | Var (_, _) :: env' -> lookup env'
    | Abs abs :: env' -> if abs.abs_id = abs_id then abs else lookup env'
    | Frame :: env' -> lookup env'
  in
  lookup env

let ctx_lookup_abs (ctx : eval_ctx) (abs_id : V.AbstractionId.id) : V.abs =
  env_lookup_abs ctx.env abs_id

let ctx_type_decl_is_rec (ctx : eval_ctx) (id : TypeDeclId.id) : bool =
  let decl_group = TypeDeclId.Map.find id ctx.type_context.type_decls_groups in
  match decl_group with M.Rec _ -> true | M.NonRec _ -> false

(** Visitor to iterate over the values in the *current* frame *)
class ['self] iter_frame =
  object (self : 'self)
    inherit [_] V.iter_abs

    method visit_Var : 'acc -> binder option -> typed_value -> unit =
      fun acc _vid v -> self#visit_typed_value acc v

    method visit_Abs : 'acc -> abs -> unit =
      fun acc abs -> self#visit_abs acc abs

    method visit_env_elem : 'acc -> env_elem -> unit =
      fun acc em ->
        match em with
        | Var (vid, v) -> self#visit_Var acc vid v
        | Abs abs -> self#visit_Abs acc abs
        | Frame -> failwith "Unreachable"

    method visit_env : 'acc -> env -> unit =
      fun acc env ->
        match env with
        | [] -> ()
        | Frame :: _ -> (* We stop here *) ()
        | em :: env ->
            self#visit_env_elem acc em;
            self#visit_env acc env
  end

(** Visitor to map over the values in the *current* frame *)
class ['self] map_frame_concrete =
  object (self : 'self)
    inherit [_] V.map_abs

    method visit_Var : 'acc -> binder option -> typed_value -> env_elem =
      fun acc vid v ->
        let v = self#visit_typed_value acc v in
        Var (vid, v)

    method visit_Abs : 'acc -> abs -> env_elem =
      fun acc abs -> Abs (self#visit_abs acc abs)

    method visit_env_elem : 'acc -> env_elem -> env_elem =
      fun acc em ->
        match em with
        | Var (vid, v) -> self#visit_Var acc vid v
        | Abs abs -> self#visit_Abs acc abs
        | Frame -> failwith "Unreachable"

    method visit_env : 'acc -> env -> env =
      fun acc env ->
        match env with
        | [] -> []
        | Frame :: env -> (* We stop here *) Frame :: env
        | em :: env ->
            let em = self#visit_env_elem acc em in
            let env = self#visit_env acc env in
            em :: env
  end

(** Visitor to iterate over the values in a context *)
class ['self] iter_eval_ctx =
  object (_self : 'self)
    inherit [_] iter_env as super

    method visit_eval_ctx : 'acc -> eval_ctx -> unit =
      fun acc ctx -> super#visit_env acc ctx.env
  end

(** Visitor to map the values in a context *)
class ['self] map_eval_ctx =
  object (_self : 'self)
    inherit [_] map_env as super

    method visit_eval_ctx : 'acc -> eval_ctx -> eval_ctx =
      fun acc ctx ->
        let env = super#visit_env acc ctx.env in
        { ctx with env }
  end
