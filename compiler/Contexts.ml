open Types
open Expressions
open Values
open LlbcAst
module V = Values
open ValuesUtils
open Identifiers

(** The [Id] module for dummy variables.

    Dummy variables are used to store values that we don't want to forget
    in the environment, because they contain borrows for instance, typically
    because they might be overwritten during an assignment.
  *)
module DummyVarId =
IdGen ()

type dummy_var_id = DummyVarId.id [@@deriving show, ord]

(** Some global counters.

  Note that those counters were initially stored in {!eval_ctx} values,
  but it proved better to make them global and stateful:
  - when branching (and thus executing on several paths with different
    contexts) it is better to really have unique ids everywhere (and
    not have fresh ids shared by several contexts even though introduced
    after the branching) because at some point we might need to merge the
    different contexts
  - also, it is a lot more convenient to not store those counters in contexts
    objects

  =============
  **WARNING**:
  =============
  Pay attention when playing with closures, as you may not always generate
  fresh identifiers without noticing it, especially when using type abbreviations.
  For instance, consider the following:
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

  This is why, in such cases, we often introduce all the inputs, even
  when they are not used (which happens!).
  {[
    fn f x : fun_type =
     fun .. ->
      let id = fresh_id () in
      ...
  ]}

  Note that in practice, we never reuse closures, except when evaluating
  a branching in the execution (which is fine, because the branches evaluate
  independentely of each other). Still, it is always a good idea to be
  defensive.

  However, the same problem arises with logging. 

  Also, a more defensive way would be to not use global references, and
  store the counters in the evaluation context. This is actually what was
  originally done, before we updated the code to use global counters because
  it proved more convenient (and even before updating the code of the
  interpreter to use CPS).
 *)

let symbolic_value_id_counter, fresh_symbolic_value_id =
  SymbolicValueId.fresh_stateful_generator ()

let borrow_id_counter, fresh_borrow_id = BorrowId.fresh_stateful_generator ()
let region_id_counter, fresh_region_id = RegionId.fresh_stateful_generator ()

let abstraction_id_counter, fresh_abstraction_id =
  AbstractionId.fresh_stateful_generator ()

let loop_id_counter, fresh_loop_id = LoopId.fresh_stateful_generator ()

let fun_call_id_counter, fresh_fun_call_id =
  FunCallId.fresh_stateful_generator ()

let dummy_var_id_counter, fresh_dummy_var_id =
  DummyVarId.fresh_stateful_generator ()

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
  loop_id_counter := LoopId.generator_zero;
  fun_call_id_counter := FunCallId.generator_zero;
  dummy_var_id_counter := DummyVarId.generator_zero

(** Ancestor for {!var_binder} iter visitor *)
class ['self] iter_var_binder_base =
  object (_self : 'self)
    inherit [_] iter_abs
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_dummy_var_id : 'env -> dummy_var_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!var_binder} map visitor *)
class ['self] map_var_binder_base =
  object (_self : 'self)
    inherit [_] map_abs
    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x

    method visit_dummy_var_id : 'env -> dummy_var_id -> dummy_var_id =
      fun _ x -> x
  end

(** A binder used in an environment, to map a variable to a value *)
type var_binder = {
  index : var_id;  (** Unique variable identifier *)
  name : string option;  (** Possible name *)
}
[@@deriving
  show,
    visitors
      {
        name = "iter_var_binder";
        variety = "iter";
        ancestors = [ "iter_var_binder_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_var_binder";
        variety = "map";
        ancestors = [ "map_var_binder_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** A binder, for a "real" variable or a dummy variable *)
type binder = VarBinder of var_binder | DummyBinder of dummy_var_id
[@@deriving
  show,
    visitors
      {
        name = "iter_binder";
        variety = "iter";
        ancestors = [ "iter_var_binder" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_binder";
        variety = "map";
        ancestors = [ "map_var_binder" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor for {!env_elem} iter visitor *)
class ['self] iter_env_elem_base =
  object (_self : 'self)
    inherit [_] iter_binder
  end

(** Ancestor for {!env_elem} map visitor *)
class ['self] map_env_elem_base =
  object (_self : 'self)
    inherit [_] map_binder
  end

(** Environment value: mapping from variable to value, abstraction (only
    used in symbolic mode) or stack frame delimiter.
    
    TODO: rename Var (-> Binding?)
 *)
type env_elem =
  | Var of binder * typed_value
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
        ancestors = [ "iter_env_elem_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_env_elem";
        variety = "map";
        ancestors = [ "map_env_elem_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
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
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_env";
        variety = "map";
        ancestors = [ "map_env_elem" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type interpreter_mode = ConcreteMode | SymbolicMode [@@deriving show]

type config = {
  mode : interpreter_mode;
      (** Concrete mode (interpreter) or symbolic mode (for synthesis) **)
}
[@@deriving show]

let mk_config (mode : interpreter_mode) : config = { mode }

type type_context = {
  type_decls_groups : type_declaration_group TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
  type_infos : TypesAnalysis.type_infos;
}
[@@deriving show]

type fun_context = { fun_decls : fun_decl FunDeclId.Map.t } [@@deriving show]

type global_context = { global_decls : global_decl GlobalDeclId.Map.t }
[@@deriving show]

type trait_decls_context = { trait_decls : trait_decl TraitDeclId.Map.t }
[@@deriving show]

type trait_impls_context = { trait_impls : trait_impl TraitImplId.Map.t }
[@@deriving show]

type decls_ctx = {
  type_ctx : type_context;
  fun_ctx : fun_context;
  global_ctx : global_context;
  trait_decls_ctx : trait_decls_context;
  trait_impls_ctx : trait_impls_context;
}
[@@deriving show]

(** A reference to a trait associated type *)
type 'r trait_type_ref = { trait_ref : 'r trait_ref; type_name : string }
[@@deriving show, ord]

type etrait_type_ref = erased_region trait_type_ref [@@deriving show, ord]

type rtrait_type_ref = Types.RegionId.id Types.region trait_type_ref
[@@deriving show, ord]

(* TODO: correctly use the functors so as not to have a duplication below *)
module ETraitTypeRefOrd = struct
  type t = etrait_type_ref

  let compare = compare_etrait_type_ref
  let to_string = show_etrait_type_ref
  let pp_t = pp_etrait_type_ref
  let show_t = show_etrait_type_ref
end

module RTraitTypeRefOrd = struct
  type t = rtrait_type_ref

  let compare = compare_rtrait_type_ref
  let to_string = show_rtrait_type_ref
  let pp_t = pp_rtrait_type_ref
  let show_t = show_rtrait_type_ref
end

module ETraitTypeRefMap = Collections.MakeMap (ETraitTypeRefOrd)
module RTraitTypeRefMap = Collections.MakeMap (RTraitTypeRefOrd)

(** Evaluation context *)
type eval_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  global_context : global_context;
  trait_decls_context : trait_decls_context;
  trait_impls_context : trait_impls_context;
  region_groups : RegionGroupId.id list;
  type_vars : type_var list;
  const_generic_vars : const_generic_var list;
  const_generic_vars_map : typed_value Types.ConstGenericVarId.Map.t;
      (** The map from const generic vars to their values. Those values
          can be symbolic values or concrete values (in the latter case:
          if we run in interpreter mode) *)
  norm_trait_etypes : ety ETraitTypeRefMap.t;
      (** The normalized trait types (a map from trait types to their representatives).
          Note that this doesn't support account higher-order types. *)
  norm_trait_rtypes : rty RTraitTypeRefMap.t;
      (** We need this because we manipulate two kinds of types.
          Note that we actually forbid regions from appearing both in the trait
          references and in the constraints given to the associated types,
          meaning that we don't have to worry about mismatches due to changes
          in region ids.

          TODO: how not to duplicate?
       *)
  env : env;
  ended_regions : RegionId.Set.t;
}
[@@deriving show]

let lookup_type_var_opt (ctx : eval_ctx) (vid : TypeVarId.id) : type_var option
    =
  if TypeVarId.to_int vid < List.length ctx.type_vars then
    Some (TypeVarId.nth ctx.type_vars vid)
  else None

let lookup_type_var (ctx : eval_ctx) (vid : TypeVarId.id) : type_var =
  TypeVarId.nth ctx.type_vars vid

let lookup_const_generic_var_opt (ctx : eval_ctx) (vid : ConstGenericVarId.id) :
    const_generic_var option =
  if ConstGenericVarId.to_int vid < List.length ctx.const_generic_vars then
    Some (ConstGenericVarId.nth ctx.const_generic_vars vid)
  else None

let lookup_const_generic_var (ctx : eval_ctx) (vid : ConstGenericVarId.id) :
    const_generic_var =
  ConstGenericVarId.nth ctx.const_generic_vars vid

(** Lookup a variable in the current frame *)
let env_lookup_var (env : env) (vid : VarId.id) : var_binder * typed_value =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec lookup env =
    match env with
    | [] ->
        raise (Invalid_argument ("Variable not found: " ^ VarId.to_string vid))
    | Var (VarBinder var, v) :: env' ->
        if var.index = vid then (var, v) else lookup env'
    | (Var (DummyBinder _, _) | Abs _) :: env' -> lookup env'
    | Frame :: _ -> raise (Failure "End of frame")
  in
  lookup env

let ctx_lookup_var_binder (ctx : eval_ctx) (vid : VarId.id) : var_binder =
  fst (env_lookup_var ctx.env vid)

let ctx_lookup_type_decl (ctx : eval_ctx) (tid : TypeDeclId.id) : type_decl =
  TypeDeclId.Map.find tid ctx.type_context.type_decls

let ctx_lookup_fun_decl (ctx : eval_ctx) (fid : FunDeclId.id) : fun_decl =
  FunDeclId.Map.find fid ctx.fun_context.fun_decls

let ctx_lookup_global_decl (ctx : eval_ctx) (gid : GlobalDeclId.id) :
    global_decl =
  GlobalDeclId.Map.find gid ctx.global_context.global_decls

let ctx_lookup_trait_decl (ctx : eval_ctx) (id : TraitDeclId.id) : trait_decl =
  TraitDeclId.Map.find id ctx.trait_decls_context.trait_decls

let ctx_lookup_trait_impl (ctx : eval_ctx) (id : TraitImplId.id) : trait_impl =
  TraitImplId.Map.find id ctx.trait_impls_context.trait_impls

(** Retrieve a variable's value in the current frame *)
let env_lookup_var_value (env : env) (vid : VarId.id) : typed_value =
  snd (env_lookup_var env vid)

(** Retrieve a variable's value in an evaluation context *)
let ctx_lookup_var_value (ctx : eval_ctx) (vid : VarId.id) : typed_value =
  env_lookup_var_value ctx.env vid

(** Retrieve a const generic value in an evaluation context *)
let ctx_lookup_const_generic_value (ctx : eval_ctx) (vid : ConstGenericVarId.id)
    : typed_value =
  Types.ConstGenericVarId.Map.find vid ctx.const_generic_vars_map

(** Update a variable's value in the current frame.

    This is a helper function: it can break invariants and doesn't perform
    any check.
*)
let env_update_var_value (env : env) (vid : VarId.id) (nv : typed_value) : env =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec update env =
    match env with
    | [] -> raise (Failure "Unexpected")
    | Var ((VarBinder b as var), v) :: env' ->
        if b.index = vid then Var (var, nv) :: env'
        else Var (var, v) :: update env'
    | ((Var (DummyBinder _, _) | Abs _) as ee) :: env' -> ee :: update env'
    | Frame :: _ -> raise (Failure "End of frame")
  in
  update env

let var_to_binder (var : var) : var_binder =
  { index = var.index; name = var.name }

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
  { ctx with env = Var (VarBinder bv, v) :: ctx.env }

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
    List.map
      (fun (var, value) -> Var (VarBinder (var_to_binder var), value))
      vars
  in
  let vars = List.rev vars in
  { ctx with env = List.append vars ctx.env }

(** Push a dummy variable in the context's environment. *)
let ctx_push_dummy_var (ctx : eval_ctx) (vid : DummyVarId.id) (v : typed_value)
    : eval_ctx =
  { ctx with env = Var (DummyBinder vid, v) :: ctx.env }

(** Remove a dummy variable from a context's environment. *)
let ctx_remove_dummy_var (ctx : eval_ctx) (vid : DummyVarId.id) :
    eval_ctx * typed_value =
  let rec remove_var (env : env) : env * typed_value =
    match env with
    | [] -> raise (Failure "Could not lookup a dummy variable")
    | Var (DummyBinder vid', v) :: env when vid' = vid -> (env, v)
    | ee :: env ->
        let env, v = remove_var env in
        (ee :: env, v)
  in
  let env, v = remove_var ctx.env in
  ({ ctx with env }, v)

(** Lookup a dummy variable in a context's environment. *)
let ctx_lookup_dummy_var (ctx : eval_ctx) (vid : DummyVarId.id) : typed_value =
  let rec lookup_var (env : env) : typed_value =
    match env with
    | [] -> raise (Failure "Could not lookup a dummy variable")
    | Var (DummyBinder vid', v) :: _env when vid' = vid -> v
    | _ :: env -> lookup_var env
  in
  lookup_var ctx.env

(** Push an uninitialized variable (which thus maps to {!constructor:Values.value.Bottom}) *)
let ctx_push_uninitialized_var (ctx : eval_ctx) (var : var) : eval_ctx =
  ctx_push_var ctx var (mk_bottom var.var_ty)

(** Push a list of uninitialized variables (which thus map to {!constructor:Values.value.Bottom}) *)
let ctx_push_uninitialized_vars (ctx : eval_ctx) (vars : var list) : eval_ctx =
  let vars = List.map (fun v -> (v, mk_bottom v.var_ty)) vars in
  ctx_push_vars ctx vars

let env_find_abs (env : env) (pred : V.abs -> bool) : V.abs option =
  let rec lookup env =
    match env with
    | [] -> None
    | Var (_, _) :: env' -> lookup env'
    | Abs abs :: env' -> if pred abs then Some abs else lookup env'
    | Frame :: env' -> lookup env'
  in
  lookup env

let env_lookup_abs (env : env) (abs_id : V.AbstractionId.id) : V.abs =
  Option.get (env_find_abs env (fun abs -> abs.abs_id = abs_id))

(** Remove an abstraction from the context, as well as all the references to
    this abstraction (for instance, remove the abs id from all the parent sets
    of all the other abstractions).
 *)
let env_remove_abs (env : env) (abs_id : V.AbstractionId.id) :
    env * V.abs option =
  let rec remove (env : env) : env * V.abs option =
    match env with
    | [] -> raise (Failure "Unreachable")
    | Frame :: _ -> (env, None)
    | Var (bv, v) :: env ->
        let env, abs_opt = remove env in
        (Var (bv, v) :: env, abs_opt)
    | Abs abs :: env ->
        if abs.abs_id = abs_id then (env, Some abs)
        else
          let env, abs_opt = remove env in
          (* Update the parents set *)
          let parents = V.AbstractionId.Set.remove abs_id abs.parents in
          (Abs { abs with V.parents } :: env, abs_opt)
  in
  remove env

(** Substitue an abstraction in an environment.

    Note that we substitute an abstraction (identified by its id) with a different
    abstraction which **doesn't necessarily have the same id**. Because of this,
    we also substitute the abstraction id wherever it is used (i.e., in the
    parent sets of the other abstractions).
 *)
let env_subst_abs (env : env) (abs_id : V.AbstractionId.id) (nabs : V.abs) :
    env * V.abs option =
  let rec update (env : env) : env * V.abs option =
    match env with
    | [] -> raise (Failure "Unreachable")
    | Frame :: _ -> (* We're done *) (env, None)
    | Var (bv, v) :: env ->
        let env, opt_abs = update env in
        (Var (bv, v) :: env, opt_abs)
    | Abs abs :: env ->
        if abs.abs_id = abs_id then (Abs nabs :: env, Some abs)
        else
          let env, opt_abs = update env in
          (* Update the parents set *)
          let parents = abs.parents in
          let parents =
            if V.AbstractionId.Set.mem abs_id parents then
              let parents = V.AbstractionId.Set.remove abs_id parents in
              V.AbstractionId.Set.add nabs.abs_id parents
            else parents
          in
          (Abs { abs with V.parents } :: env, opt_abs)
  in
  update env

let ctx_lookup_abs (ctx : eval_ctx) (abs_id : V.AbstractionId.id) : V.abs =
  env_lookup_abs ctx.env abs_id

let ctx_find_abs (ctx : eval_ctx) (p : V.abs -> bool) : V.abs option =
  env_find_abs ctx.env p

(** See the comments for {!env_remove_abs} *)
let ctx_remove_abs (ctx : eval_ctx) (abs_id : V.AbstractionId.id) :
    eval_ctx * V.abs option =
  let env, abs = env_remove_abs ctx.env abs_id in
  ({ ctx with env }, abs)

(** See the comments for {!env_subst_abs} *)
let ctx_subst_abs (ctx : eval_ctx) (abs_id : V.AbstractionId.id) (nabs : V.abs)
    : eval_ctx * V.abs option =
  let env, abs_opt = env_subst_abs ctx.env abs_id nabs in
  ({ ctx with env }, abs_opt)

let ctx_set_abs_can_end (ctx : eval_ctx) (abs_id : V.AbstractionId.id)
    (can_end : bool) : eval_ctx =
  let abs = ctx_lookup_abs ctx abs_id in
  let abs = { abs with can_end } in
  fst (ctx_subst_abs ctx abs_id abs)

let ctx_type_decl_is_rec (ctx : eval_ctx) (id : TypeDeclId.id) : bool =
  let decl_group = TypeDeclId.Map.find id ctx.type_context.type_decls_groups in
  match decl_group with Rec _ -> true | NonRec _ -> false

(** Visitor to iterate over the values in the *current* frame *)
class ['self] iter_frame =
  object (self : 'self)
    inherit [_] iter_env

    method! visit_env : 'acc -> env -> unit =
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
    inherit [_] map_env

    method! visit_env : 'acc -> env -> env =
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

let env_iter_abs (f : V.abs -> unit) (env : env) : unit =
  List.iter
    (fun (ee : env_elem) ->
      match ee with Var _ | Frame -> () | Abs abs -> f abs)
    env

let env_map_abs (f : V.abs -> V.abs) (env : env) : env =
  List.map
    (fun (ee : env_elem) ->
      match ee with Var _ | Frame -> ee | Abs abs -> Abs (f abs))
    env

let env_filter_abs (f : V.abs -> bool) (env : env) : env =
  List.filter
    (fun (ee : env_elem) ->
      match ee with Var _ | Frame -> true | Abs abs -> f abs)
    env
