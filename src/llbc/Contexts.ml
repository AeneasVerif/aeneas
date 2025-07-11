open Types
open Expressions
open Values
open LlbcAst
open LlbcAstUtils
open ValuesUtils
open Errors
include ContextsBase

module OrderedBinder : Collections.OrderedType with type t = var_binder = struct
  type t = var_binder

  let compare x y = compare_var_binder x y
  let to_string x = show_var_binder x
  let pp_t fmt x = Format.pp_print_string fmt (show_var_binder x)
  let show_t x = show_var_binder x
end

module BinderMap = Collections.MakeMap (OrderedBinder)

type interpreter_mode = ConcreteMode | SymbolicMode [@@deriving show]

type config = {
  mode : interpreter_mode;
      (** Concrete mode (interpreter) or symbolic mode (for synthesis) **)
}
[@@deriving show]

let mk_config (mode : interpreter_mode) : config = { mode }

type type_ctx = {
  type_decls_groups : type_declaration_group TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
      (* Copy of the declarations in the crate *)
  type_infos : TypesAnalysis.type_infos;
}
[@@deriving show]

type fun_ctx = {
  fun_decls : fun_decl FunDeclId.Map.t;
      (* Copy of the declarations in the crate *)
  fun_infos : FunsAnalysis.fun_info FunDeclId.Map.t;
  regions_hierarchies : region_var_groups FunIdMap.t;
}
[@@deriving show]

type decls_ctx = { crate : crate; type_ctx : type_ctx; fun_ctx : fun_ctx }
[@@deriving show]

(** A reference to a trait associated type *)
type trait_type_ref = { trait_ref : trait_ref; type_name : string }
[@@deriving show, ord]

(* TODO: correctly use the functors so as not to have a duplication below *)
module TraitTypeRefOrd = struct
  type t = trait_type_ref

  let compare = compare_trait_type_ref
  let to_string = show_trait_type_ref
  let pp_t = pp_trait_type_ref
  let show_t = show_trait_type_ref
end

module TraitTypeRefMap = Collections.MakeMap (TraitTypeRefOrd)

(** Evaluation context *)
type eval_ctx = {
  crate : crate;
  type_ctx : type_ctx;
  fun_ctx : fun_ctx;
  region_groups : RegionGroupId.id list;
  type_vars : type_var list;
  const_generic_vars : const_generic_var list;
  const_generic_vars_map : typed_value Types.ConstGenericVarId.Map.t;
      (** The map from const generic vars to their values. Those values can be
          symbolic values or concrete values (in the latter case: if we run in
          interpreter mode).

          TODO: this is actually not used in symbolic mode, where we directly
          introduce fresh symbolic values. *)
  norm_trait_types : ty TraitTypeRefMap.t;
      (** The normalized trait types (a map from trait types to their
          representatives). Note that this doesn't take into account
          higher-order type constraints (of the shape `for<'a> ...`). *)
  env : env;
  ended_regions : RegionId.Set.t;
}
[@@deriving show]

let lookup_type_var_opt (ctx : eval_ctx) (vid : TypeVarId.id) : type_var option
    =
  TypeVarId.nth_opt ctx.type_vars vid

let lookup_type_var (ctx : eval_ctx) (vid : TypeVarId.id) : type_var =
  TypeVarId.nth ctx.type_vars vid

let lookup_const_generic_var_opt (ctx : eval_ctx) (vid : ConstGenericVarId.id) :
    const_generic_var option =
  ConstGenericVarId.nth_opt ctx.const_generic_vars vid

let lookup_const_generic_var (ctx : eval_ctx) (vid : ConstGenericVarId.id) :
    const_generic_var =
  ConstGenericVarId.nth ctx.const_generic_vars vid

(** Lookup a variable in the current frame *)
let env_lookup_var (span : Meta.span) (env : env) (vid : LocalId.id) :
    real_var_binder * typed_value =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec lookup env =
    match env with
    | [] ->
        raise
          (Invalid_argument ("Variable not found: " ^ LocalId.to_string vid))
    | EBinding (BVar var, v) :: env' ->
        if var.index = vid then (var, v) else lookup env'
    | (EBinding (BDummy _, _) | EAbs _) :: env' -> lookup env'
    | EFrame :: _ -> craise __FILE__ __LINE__ span "End of frame"
  in
  lookup env

let ctx_lookup_real_var_binder (span : Meta.span) (ctx : eval_ctx)
    (vid : LocalId.id) : real_var_binder =
  fst (env_lookup_var span ctx.env vid)

let ctx_lookup_type_decl (span : Meta.span) (ctx : eval_ctx)
    (tid : TypeDeclId.id) : type_decl =
  silent_unwrap_opt_span __FILE__ __LINE__ (Some span)
    (TypeDeclId.Map.find_opt tid ctx.crate.type_decls)

let ctx_lookup_fun_decl (span : Meta.span) (ctx : eval_ctx) (fid : FunDeclId.id)
    : fun_decl =
  silent_unwrap_opt_span __FILE__ __LINE__ (Some span)
    (FunDeclId.Map.find_opt fid ctx.crate.fun_decls)

let ctx_lookup_global_decl (span : Meta.span) (ctx : eval_ctx)
    (gid : GlobalDeclId.id) : global_decl =
  silent_unwrap_opt_span __FILE__ __LINE__ (Some span)
    (GlobalDeclId.Map.find_opt gid ctx.crate.global_decls)

let ctx_lookup_trait_decl (span : Meta.span) (ctx : eval_ctx)
    (id : TraitDeclId.id) : trait_decl =
  silent_unwrap_opt_span __FILE__ __LINE__ (Some span)
    (TraitDeclId.Map.find_opt id ctx.crate.trait_decls)

let ctx_lookup_trait_impl (span : Meta.span) (ctx : eval_ctx)
    (id : TraitImplId.id) : trait_impl =
  silent_unwrap_opt_span __FILE__ __LINE__ (Some span)
    (TraitImplId.Map.find_opt id ctx.crate.trait_impls)

(** Retrieve a variable's value in the current frame *)
let env_lookup_var_value (span : Meta.span) (env : env) (vid : LocalId.id) :
    typed_value =
  snd (env_lookup_var span env vid)

let ctx_lookup_var_value (span : Meta.span) (ctx : eval_ctx) (vid : LocalId.id)
    : typed_value =
  env_lookup_var_value span ctx.env vid

(** Retrieve a const generic value in an evaluation context *)
let ctx_lookup_const_generic_value (ctx : eval_ctx) (vid : ConstGenericVarId.id)
    : typed_value =
  Types.ConstGenericVarId.Map.find vid ctx.const_generic_vars_map

(** Update a variable's value in the current frame.

    This is a helper function: it can break invariants and doesn't perform any
    check. *)
let env_update_var_value (span : Meta.span) (env : env) (vid : LocalId.id)
    (nv : typed_value) : env =
  (* We take care to stop at the end of current frame: different variables
     in different frames can have the same id!
  *)
  let rec update env =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Unexpected"
    | EBinding ((BVar b as var), v) :: env' ->
        if b.index = vid then EBinding (var, nv) :: env'
        else EBinding (var, v) :: update env'
    | ((EBinding (BDummy _, _) | EAbs _) as ee) :: env' -> ee :: update env'
    | EFrame :: _ -> craise __FILE__ __LINE__ span "End of frame"
  in
  update env

let var_to_binder (var : local) : real_var_binder =
  { index = var.index; name = var.name }

(** Update a variable's value in an evaluation context.

    This is a helper function: it can break invariants and doesn't perform any
    check. *)
let ctx_update_var_value (span : Meta.span) (ctx : eval_ctx) (vid : LocalId.id)
    (nv : typed_value) : eval_ctx =
  { ctx with env = env_update_var_value span ctx.env vid nv }

(** Push a variable in the context's environment.

    Checks that the pushed variable and its value have the same type (this is
    important). *)
let ctx_push_var (span : Meta.span) (ctx : eval_ctx) (var : local)
    (v : typed_value) : eval_ctx =
  cassert __FILE__ __LINE__
    (TypesUtils.ty_is_ety var.var_ty && var.var_ty = v.ty)
    span "The pushed variables and their values do not have the same type";
  let bv = var_to_binder var in
  { ctx with env = EBinding (BVar bv, v) :: ctx.env }

(** Push a list of variables.

    Checks that the pushed variables and their values have the same type (this
    is important). *)
let ctx_push_vars (span : Meta.span) (ctx : eval_ctx)
    (vars : (local * typed_value) list) : eval_ctx =
  log#ltrace
    (lazy
      ("push_vars:\n"
      ^ String.concat "\n"
          (List.map
             (fun (var, value) ->
               (* We can unfortunately not use Print because it depends on Contexts... *)
               show_var var ^ " -> " ^ show_typed_value value)
             vars)));
  cassert __FILE__ __LINE__
    (List.for_all
       (fun (var, (value : typed_value)) ->
         TypesUtils.ty_is_ety var.var_ty && var.var_ty = value.ty)
       vars)
    span "The pushed variables and their values do not have the same type";
  let vars =
    List.map
      (fun (var, value) -> EBinding (BVar (var_to_binder var), value))
      vars
  in
  let vars = List.rev vars in
  { ctx with env = List.append vars ctx.env }

(** Push a dummy variable in the context's environment. *)
let ctx_push_dummy_var (ctx : eval_ctx) (vid : DummyVarId.id) (v : typed_value)
    : eval_ctx =
  { ctx with env = EBinding (BDummy vid, v) :: ctx.env }

let ctx_push_fresh_dummy_var (ctx : eval_ctx) (v : typed_value) : eval_ctx =
  ctx_push_dummy_var ctx (fresh_dummy_var_id ()) v

let ctx_push_fresh_dummy_vars (ctx : eval_ctx) (vl : typed_value list) :
    eval_ctx =
  List.fold_left (fun ctx v -> ctx_push_fresh_dummy_var ctx v) ctx vl

(** Remove a dummy variable from a context's environment. *)
let ctx_remove_dummy_var span (ctx : eval_ctx) (vid : DummyVarId.id) :
    eval_ctx * typed_value =
  let rec remove_var (env : env) : env * typed_value =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Could not lookup a dummy variable"
    | EBinding (BDummy vid', v) :: env when vid' = vid -> (env, v)
    | ee :: env ->
        let env, v = remove_var env in
        (ee :: env, v)
  in
  let env, v = remove_var ctx.env in
  ({ ctx with env }, v)

(** Lookup a dummy variable in a context's environment. *)
let ctx_lookup_dummy_var (span : Meta.span) (ctx : eval_ctx)
    (vid : DummyVarId.id) : typed_value =
  let rec lookup_var (env : env) : typed_value =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Could not lookup a dummy variable"
    | EBinding (BDummy vid', v) :: _env when vid' = vid -> v
    | _ :: env -> lookup_var env
  in
  lookup_var ctx.env

let erase_regions (ty : ty) : ty =
  let v =
    object
      inherit [_] map_ty
      method! visit_region _ _ = RErased
    end
  in
  v#visit_ty () ty

(** Push an uninitialized variable (which thus maps to
    {!constructor:Values.value.VBottom}) *)
let ctx_push_uninitialized_var (span : Meta.span) (ctx : eval_ctx) (var : local)
    : eval_ctx =
  ctx_push_var span ctx var (mk_bottom span (erase_regions var.var_ty))

(** Push a list of uninitialized variables (which thus map to
    {!constructor:Values.value.VBottom}) *)
let ctx_push_uninitialized_vars (span : Meta.span) (ctx : eval_ctx)
    (vars : local list) : eval_ctx =
  let vars =
    List.map (fun v -> (v, mk_bottom span (erase_regions v.var_ty))) vars
  in
  ctx_push_vars span ctx vars

let env_find_abs (env : env) (pred : abs -> bool) : abs option =
  let rec lookup env =
    match env with
    | [] -> None
    | EBinding (_, _) :: env' -> lookup env'
    | EAbs abs :: env' -> if pred abs then Some abs else lookup env'
    | EFrame :: env' -> lookup env'
  in
  lookup env

let env_lookup_abs_opt (env : env) (abs_id : AbstractionId.id) : abs option =
  env_find_abs env (fun abs -> abs.abs_id = abs_id)

(** Remove an abstraction from the context, as well as all the references to
    this abstraction (for instance, remove the abs id from all the parent sets
    of all the other abstractions). *)
let env_remove_abs (span : Meta.span) (env : env) (abs_id : AbstractionId.id) :
    env * abs option =
  let rec remove (env : env) : env * abs option =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Unreachable"
    | EFrame :: _ -> (env, None)
    | EBinding (bv, v) :: env ->
        let env, abs_opt = remove env in
        (EBinding (bv, v) :: env, abs_opt)
    | EAbs abs :: env ->
        if abs.abs_id = abs_id then (env, Some abs)
        else
          let env, abs_opt = remove env in
          (* Update the parents set *)
          let parents = AbstractionId.Set.remove abs_id abs.parents in
          (EAbs { abs with parents } :: env, abs_opt)
  in
  remove env

(** Substitue an abstraction in an environment.

    Note that we substitute an abstraction (identified by its id) with a
    different abstraction which **doesn't necessarily have the same id**.
    Because of this, we also substitute the abstraction id wherever it is used
    (i.e., in the parent sets of the other abstractions). *)
let env_subst_abs (span : Meta.span) (env : env) (abs_id : AbstractionId.id)
    (nabs : abs) : env * abs option =
  let rec update (env : env) : env * abs option =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Unreachable"
    | EFrame :: _ -> (* We're done *) (env, None)
    | EBinding (bv, v) :: env ->
        let env, opt_abs = update env in
        (EBinding (bv, v) :: env, opt_abs)
    | EAbs abs :: env ->
        if abs.abs_id = abs_id then (EAbs nabs :: env, Some abs)
        else
          let env, opt_abs = update env in
          (* Update the parents set *)
          let parents = abs.parents in
          let parents =
            if AbstractionId.Set.mem abs_id parents then
              let parents = AbstractionId.Set.remove abs_id parents in
              AbstractionId.Set.add nabs.abs_id parents
            else parents
          in
          (EAbs { abs with parents } :: env, opt_abs)
  in
  update env

let ctx_lookup_abs_opt (ctx : eval_ctx) (abs_id : AbstractionId.id) : abs option
    =
  env_lookup_abs_opt ctx.env abs_id

let ctx_lookup_abs (ctx : eval_ctx) (abs_id : AbstractionId.id) : abs =
  Option.get (ctx_lookup_abs_opt ctx abs_id)

let ctx_find_abs (ctx : eval_ctx) (p : abs -> bool) : abs option =
  env_find_abs ctx.env p

(** See the comments for {!env_remove_abs} *)
let ctx_remove_abs (span : Meta.span) (ctx : eval_ctx)
    (abs_id : AbstractionId.id) : eval_ctx * abs option =
  let env, abs = env_remove_abs span ctx.env abs_id in
  ({ ctx with env }, abs)

(** See the comments for {!env_subst_abs} *)
let ctx_subst_abs (span : Meta.span) (ctx : eval_ctx)
    (abs_id : AbstractionId.id) (nabs : abs) : eval_ctx * abs option =
  let env, abs_opt = env_subst_abs span ctx.env abs_id nabs in
  ({ ctx with env }, abs_opt)

let ctx_set_abs_can_end (span : Meta.span) (ctx : eval_ctx)
    (abs_id : AbstractionId.id) (can_end : bool) : eval_ctx =
  let abs = ctx_lookup_abs ctx abs_id in
  let abs = { abs with can_end } in
  fst (ctx_subst_abs span ctx abs_id abs)

let ctx_type_decl_is_rec (ctx : eval_ctx) (id : TypeDeclId.id) : bool =
  let decl_group = TypeDeclId.Map.find id ctx.type_ctx.type_decls_groups in
  match decl_group with
  | RecGroup _ -> true
  | NonRecGroup _ -> false

(** Visitor to iterate over the values in the *current* frame *)
class ['self] iter_frame =
  object (self : 'self)
    inherit [_] iter_env

    method! visit_env : 'acc -> env -> unit =
      fun acc env ->
        match env with
        | [] -> ()
        | EFrame :: _ -> (* We stop here *) ()
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
        | EFrame :: env -> (* We stop here *) EFrame :: env
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

let env_iter_abs (f : abs -> unit) (env : env) : unit =
  List.iter
    (fun (ee : env_elem) ->
      match ee with
      | EBinding _ | EFrame -> ()
      | EAbs abs -> f abs)
    env

let env_map_abs (f : abs -> abs) (env : env) : env =
  List.map
    (fun (ee : env_elem) ->
      match ee with
      | EBinding _ | EFrame -> ee
      | EAbs abs -> EAbs (f abs))
    env

let env_filter_abs (f : abs -> bool) (env : env) : env =
  List.filter
    (fun (ee : env_elem) ->
      match ee with
      | EBinding _ | EFrame -> true
      | EAbs abs -> f abs)
    env

(** Return the types of the properly instantiated ADT's variant, provided a
    context.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead. *)
let ctx_type_get_instantiated_variants_fields_types (span : Meta.span)
    (ctx : eval_ctx) (def_id : TypeDeclId.id) (generics : generic_args) :
    (VariantId.id option * ty list) list =
  let def = ctx_lookup_type_decl span ctx def_id in
  Substitute.type_decl_get_instantiated_variants_fields_types def generics

(** Return the types of the properly instantiated ADT's variant, provided a
    context.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead. *)
let ctx_type_get_instantiated_field_types (span : Meta.span) (ctx : eval_ctx)
    (def_id : TypeDeclId.id) (opt_variant_id : VariantId.id option)
    (generics : generic_args) : ty list =
  let def = ctx_lookup_type_decl span ctx def_id in
  Substitute.type_decl_get_instantiated_field_types def opt_variant_id generics

(** Return the types of the properly instantiated ADT value (note that here, ADT
    is understood in its broad meaning: ADT, builtin value or tuple).

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead. *)
let ctx_adt_get_instantiated_field_types (span : Meta.span) (ctx : eval_ctx)
    (id : type_id) (variant_id : variant_id option) (generics : generic_args) :
    ty list =
  match id with
  | TAdtId id ->
      (* Retrieve the types of the fields *)
      ctx_type_get_instantiated_field_types span ctx id variant_id generics
  | TTuple ->
      cassert __FILE__ __LINE__ (variant_id = None) span
        "Tuples don't have variants";
      cassert __FILE__ __LINE__ (generics.regions = []) span
        "Tuples don't have region parameters";
      generics.types
  | TBuiltin aty -> (
      match aty with
      | TBox ->
          cassert __FILE__ __LINE__ (variant_id = None) span
            "Boxes don't have variants";
          sanity_check __FILE__ __LINE__ (generics.regions = []) span;
          sanity_check __FILE__ __LINE__ (List.length generics.types = 1) span;
          sanity_check __FILE__ __LINE__ (generics.const_generics = []) span;
          generics.types
      | TArray | TSlice | TStr ->
          (* Those types don't have fields *)
          craise __FILE__ __LINE__ span "Unreachable")
