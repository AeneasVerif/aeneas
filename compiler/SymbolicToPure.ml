open Utils
open LlbcAstUtils
open Pure
open PureUtils
open InterpreterUtils
open FunsAnalysis
open TypesAnalysis
module T = Types
module V = Values
module C = Contexts
module A = LlbcAst
module S = SymbolicAst
module PP = PrintPure

(** The local logger *)
let log = Logging.symbolic_to_pure_log

type type_context = {
  llbc_type_decls : T.type_decl TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
      (** We use this for type-checking (for sanity checks) when translating
          values and functions.
          This map is empty when we translate the types, then contains all
          the translated types when we translate the functions.
       *)
  type_infos : type_infos;
  recursive_decls : T.TypeDeclId.Set.t;
}
[@@deriving show]

type fun_sig_named_outputs = {
  sg : fun_sig;  (** A function signature *)
  output_names : string option list;
      (** In case the signature is for a backward function, we may provides names
          for the outputs. The reason is that the outputs of backward functions
          come from (in case there are no nested borrows) borrows present in the
          inputs of the original rust function. In this situation, we can use the
          names of those inputs to name the outputs. Those names are very useful
          to generate beautiful codes (we may need to introduce temporary variables
          in the bodies of the backward functions to store the returned values, in
          which case we use those names).
       *)
}
[@@deriving show]

type fun_context = {
  llbc_fun_decls : A.fun_decl A.FunDeclId.Map.t;
  fun_sigs : fun_sig_named_outputs RegularFunIdNotLoopMap.t;  (** *)
  fun_infos : fun_info A.FunDeclId.Map.t;
  regions_hierarchies : T.region_var_groups FunIdMap.t;
}
[@@deriving show]

type global_context = { llbc_global_decls : A.global_decl A.GlobalDeclId.Map.t }
[@@deriving show]

type trait_decls_context = A.trait_decl A.TraitDeclId.Map.t [@@deriving show]
type trait_impls_context = A.trait_impl A.TraitImplId.Map.t [@@deriving show]

(** Whenever we translate a function call or an ended abstraction, we
    store the related information (this is useful when translating ended
    children abstractions).
 *)
type call_info = {
  forward : S.call;
  forward_inputs : texpression list;
      (** Remember the list of inputs given to the forward function.

          Those inputs include the fuel and the state, if pertinent.
       *)
  backwards : (V.abs * texpression list) T.RegionGroupId.Map.t;
      (** A map from region group id (i.e., backward function id) to
          pairs (abstraction, additional arguments received by the backward function)
       
          TODO: remove? it is also in the bs_ctx ("abstractions" field)
       *)
}
[@@deriving show]

(** Contains information about a loop we entered.

    Note that a path in a translated function body can have at most one call to
    a loop, because the loop function takes care of the end of the execution
    (and always happen at the end of the function). To be more precise, if we
    translate a function body which contains a loop, one of the leaves will be a
    call to the loop translation. The same happens for loop bodies.

    For instance, if in Rust we have:
    {[
      fn get(...) {
        let x = f(...);

        loop {
          ...
        }
      }
    ]}

    Then in the translation we have:
    {[
      let get_fwd ... =
        let x = f_fwd ... in
        (* We end the function by calling the loop translation *)
        get_fwd_loop ...
    ]}

    The various input and output fields are for this unique loop call, if
    there is one.
 *)
type loop_info = {
  loop_id : LoopId.id;
  input_vars : var list;
  input_svl : V.symbolic_value list;
  generics : generic_args;
  forward_inputs : texpression list option;
      (** The forward inputs are initialized at [None] *)
  forward_output_no_state_no_result : var option;
      (** The forward outputs are initialized at [None] *)
}
[@@deriving show]

(** Body synthesis context *)
type bs_ctx = {
  type_context : type_context;
  fun_context : fun_context;
  global_context : global_context;
  trait_decls_ctx : trait_decls_context;
  trait_impls_ctx : trait_impls_context;
  fun_decl : A.fun_decl;
  bid : T.RegionGroupId.id option;  (** TODO: rename *)
  sg : fun_sig;
      (** The function signature - useful in particular to translate [Panic] *)
  fwd_sg : fun_sig;  (** The signature of the forward function *)
  sv_to_var : var V.SymbolicValueId.Map.t;
      (** Whenever we encounter a new symbolic value (introduced because of
          a symbolic expansion or upon ending an abstraction, for instance)
          we introduce a new variable (with a let-binding).
       *)
  var_counter : VarId.generator;
  state_var : VarId.id;
      (** The current state variable, in case the function is stateful *)
  back_state_var : VarId.id;
      (** The additional input state variable received by a stateful backward function.
          When generating stateful functions, we generate code of the following
          form:

          {[
            (st1, y)  <-- f_fwd x st0; // st0 is the state upon calling f_fwd
            ... // the state may be updated
            (st3, x') <-- f_back x st0 y' st2; // st2 is the state upon calling f_back
          ]}

          When translating a backward function, we need at some point to update
          [state_var] with [back_state_var], to account for the fact that the
          state may have been updated by the caller between the call to the
          forward function and the call to the backward function.
       *)
  fuel0 : VarId.id;
      (** The original fuel taken as input by the function (if we use fuel) *)
  fuel : VarId.id;
      (** The fuel to use for the recursive calls (if we use fuel) *)
  forward_inputs : var list;
      (** The input parameters for the forward function corresponding to the
          translated Rust inputs (no fuel, no state).
       *)
  backward_inputs : var list T.RegionGroupId.Map.t;
      (** The additional input parameters for the backward functions coming
          from the borrows consumed upon ending the lifetime (as a consequence
          those don't include the backward state, if there is one).
       *)
  backward_outputs : var list T.RegionGroupId.Map.t;
      (** The variables that the backward functions will output, corresponding
          to the borrows they give back (don't include the backward state)
       *)
  loop_backward_outputs : var list T.RegionGroupId.Map.t option;
      (** Same as {!backward_outputs}, but for loops (if we entered a loop).

          [None] if we are not inside a loop, [Some] otherwise (and whatever
          the kind of function we are translating: it will be [Some] even
          though we are synthesizing a forward function).

          TODO: move to {!loop_info}
       *)
  calls : call_info V.FunCallId.Map.t;
      (** The function calls we encountered so far *)
  abstractions : (V.abs * texpression list) V.AbstractionId.Map.t;
      (** The ended abstractions we encountered so far, with their additional input arguments  *)
  loop_ids_map : LoopId.id V.LoopId.Map.t;  (** Ids to use for the loops *)
  loops : loop_info LoopId.Map.t;
      (** The loops we encountered so far.

          We are using a map to be general - in practice we will fail if we encounter
          more than one loop on a single path.
       *)
  loop_id : LoopId.id option;
      (** [Some] if we reached a loop (we are synthesizing a function, and reached a loop, or are
          synthesizing the loop body itself)
       *)
  inside_loop : bool;
      (** In case {!loop_id} is [Some]:
          - if [true]: we are synthesizing a loop body
          - if [false]: we reached a loop and are synthesizing the end of the function (after the loop body)

          Note that when a function contains a loop, we group the function symbolic AST and the loop symbolic
          AST in a single function.
       *)
}
[@@deriving show]

(* TODO: move *)
let bs_ctx_to_fmt_env (ctx : bs_ctx) : Print.fmt_env =
  let type_decls = ctx.type_context.llbc_type_decls in
  let fun_decls = ctx.fun_context.llbc_fun_decls in
  let global_decls = ctx.global_context.llbc_global_decls in
  let trait_decls = ctx.trait_decls_ctx in
  let trait_impls = ctx.trait_impls_ctx in
  let { regions; types; const_generics; trait_clauses } : T.generic_params =
    ctx.fun_decl.signature.generics
  in
  let preds = ctx.fun_decl.signature.preds in
  {
    type_decls;
    fun_decls;
    global_decls;
    trait_decls;
    trait_impls;
    regions = [ regions ];
    types;
    const_generics;
    trait_clauses;
    preds;
    locals = [];
  }

let bs_ctx_to_pure_fmt_env (ctx : bs_ctx) : PrintPure.fmt_env =
  let type_decls = ctx.type_context.llbc_type_decls in
  let fun_decls = ctx.fun_context.llbc_fun_decls in
  let global_decls = ctx.global_context.llbc_global_decls in
  let trait_decls = ctx.trait_decls_ctx in
  let trait_impls = ctx.trait_impls_ctx in
  let generics = ctx.sg.generics in
  {
    type_decls;
    fun_decls;
    global_decls;
    trait_decls;
    trait_impls;
    generics;
    locals = [];
  }

let ctx_generic_args_to_string (ctx : bs_ctx) (args : T.generic_args) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.generic_args_to_string env args

let name_to_string (ctx : bs_ctx) =
  Print.Types.name_to_string (bs_ctx_to_fmt_env ctx)

let symbolic_value_to_string (ctx : bs_ctx) (sv : V.symbolic_value) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.symbolic_value_to_string env sv

let typed_value_to_string (ctx : bs_ctx) (v : V.typed_value) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.typed_value_to_string env v

let pure_ty_to_string (ctx : bs_ctx) (ty : ty) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.ty_to_string env false ty

let ty_to_string (ctx : bs_ctx) (ty : T.ty) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.ty_to_string env ty

let type_decl_to_string (ctx : bs_ctx) (def : T.type_decl) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.type_decl_to_string env def

let pure_type_decl_to_string (ctx : bs_ctx) (def : type_decl) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.type_decl_to_string env def

let texpression_to_string (ctx : bs_ctx) (e : texpression) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.texpression_to_string env false "" "  " e

let fun_id_to_string (ctx : bs_ctx) (id : A.fun_id) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Expressions.fun_id_to_string env id

let fun_sig_to_string (ctx : bs_ctx) (sg : fun_sig) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_sig_to_string env sg

let fun_decl_to_string (ctx : bs_ctx) (def : Pure.fun_decl) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_decl_to_string env def

let typed_pattern_to_string (ctx : bs_ctx) (p : Pure.typed_pattern) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.typed_pattern_to_string env p

(* TODO: move *)
let abs_to_string (ctx : bs_ctx) (abs : V.abs) : string =
  let env = bs_ctx_to_fmt_env ctx in
  let verbose = false in
  let indent = "" in
  let indent_incr = "  " in
  Print.Values.abs_to_string env verbose indent indent_incr abs

let get_instantiated_fun_sig (fun_id : A.fun_id)
    (back_id : T.RegionGroupId.id option) (generics : generic_args)
    (ctx : bs_ctx) : inst_fun_sig =
  (* Lookup the non-instantiated function signature *)
  let sg =
    (RegularFunIdNotLoopMap.find (fun_id, back_id) ctx.fun_context.fun_sigs).sg
  in
  (* Create the substitution *)
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics sg.generics generics tr_self in
  (* Apply *)
  fun_sig_substitute subst sg

let bs_ctx_lookup_llbc_type_decl (id : TypeDeclId.id) (ctx : bs_ctx) :
    T.type_decl =
  TypeDeclId.Map.find id ctx.type_context.llbc_type_decls

let bs_ctx_lookup_llbc_fun_decl (id : A.FunDeclId.id) (ctx : bs_ctx) :
    A.fun_decl =
  A.FunDeclId.Map.find id ctx.fun_context.llbc_fun_decls

(* TODO: move *)
let bs_ctx_lookup_local_function_sig (def_id : A.FunDeclId.id)
    (back_id : T.RegionGroupId.id option) (ctx : bs_ctx) : fun_sig =
  let id = (E.FRegular def_id, back_id) in
  (RegularFunIdNotLoopMap.find id ctx.fun_context.fun_sigs).sg

(* Some generic translation functions (we need to translate different "flavours"
   of types: forward types, backward types, etc.) *)
let rec translate_generic_args (translate_ty : T.ty -> ty)
    (generics : T.generic_args) : generic_args =
  (* We ignore the regions: if they didn't cause trouble for the symbolic execution,
     then everything's fine *)
  let types = List.map translate_ty generics.types in
  let const_generics = generics.const_generics in
  let trait_refs =
    List.map (translate_trait_ref translate_ty) generics.trait_refs
  in
  { types; const_generics; trait_refs }

and translate_trait_ref (translate_ty : T.ty -> ty) (tr : T.trait_ref) :
    trait_ref =
  let trait_id = translate_trait_instance_id translate_ty tr.trait_id in
  let generics = translate_generic_args translate_ty tr.generics in
  let trait_decl_ref =
    translate_trait_decl_ref translate_ty tr.trait_decl_ref
  in
  { trait_id; generics; trait_decl_ref }

and translate_trait_decl_ref (translate_ty : T.ty -> ty) (tr : T.trait_decl_ref)
    : trait_decl_ref =
  let decl_generics = translate_generic_args translate_ty tr.decl_generics in
  { trait_decl_id = tr.trait_decl_id; decl_generics }

and translate_trait_instance_id (translate_ty : T.ty -> ty)
    (id : T.trait_instance_id) : trait_instance_id =
  let translate_trait_instance_id = translate_trait_instance_id translate_ty in
  match id with
  | T.Self -> Self
  | TraitImpl id -> TraitImpl id
  | BuiltinOrAuto _ ->
      (* We should have eliminated those in the prepasses *)
      raise (Failure "Unreachable")
  | Clause id -> Clause id
  | ParentClause (inst_id, decl_id, clause_id) ->
      let inst_id = translate_trait_instance_id inst_id in
      ParentClause (inst_id, decl_id, clause_id)
  | ItemClause (inst_id, decl_id, item_name, clause_id) ->
      let inst_id = translate_trait_instance_id inst_id in
      ItemClause (inst_id, decl_id, item_name, clause_id)
  | TraitRef tr -> TraitRef (translate_trait_ref translate_ty tr)
  | FnPointer _ | Closure _ -> raise (Failure "Closures are not supported yet")
  | UnknownTrait s -> raise (Failure ("Unknown trait found: " ^ s))

(** Translate a signature type - TODO: factor out the different translation functions *)
let rec translate_sty (ty : T.ty) : ty =
  let translate = translate_sty in
  match ty with
  | T.TAdt (type_id, generics) -> (
      let generics = translate_sgeneric_args generics in
      match type_id with
      | T.TAdtId adt_id -> TAdt (TAdtId adt_id, generics)
      | T.TTuple ->
          assert (generics.const_generics = []);
          mk_simpl_tuple_ty generics.types
      | T.TAssumed aty -> (
          match aty with
          | T.TBox -> (
              (* Eliminate the boxes *)
              match generics.types with
              | [ ty ] -> ty
              | _ ->
                  raise
                    (Failure
                       "Box/vec/option type with incorrect number of arguments")
              )
          | T.TArray -> TAdt (TAssumed TArray, generics)
          | T.TSlice -> TAdt (TAssumed TSlice, generics)
          | T.TStr -> TAdt (TAssumed TStr, generics)))
  | TVar vid -> TVar vid
  | TLiteral ty -> TLiteral ty
  | TNever -> raise (Failure "Unreachable")
  | TRef (_, rty, _) -> translate rty
  | TRawPtr (ty, rkind) ->
      let mut = match rkind with RMut -> Mut | RShared -> Const in
      let ty = translate ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TAssumed (TRawPtr mut), generics)
  | TTraitType (trait_ref, generics, type_name) ->
      let trait_ref = translate_strait_ref trait_ref in
      let generics = translate_sgeneric_args generics in
      TTraitType (trait_ref, generics, type_name)
  | TArrow _ -> raise (Failure "TODO")

and translate_sgeneric_args (generics : T.generic_args) : generic_args =
  translate_generic_args translate_sty generics

and translate_strait_ref (tr : T.trait_ref) : trait_ref =
  translate_trait_ref translate_sty tr

and translate_strait_instance_id (id : T.trait_instance_id) : trait_instance_id
    =
  translate_trait_instance_id translate_sty id

let translate_trait_clause (clause : T.trait_clause) : trait_clause =
  let { T.clause_id; meta = _; trait_id; clause_generics } = clause in
  let generics = translate_sgeneric_args clause_generics in
  { clause_id; trait_id; generics }

let translate_strait_type_constraint (ttc : T.trait_type_constraint) :
    trait_type_constraint =
  let { T.trait_ref; generics; type_name; ty } = ttc in
  let trait_ref = translate_strait_ref trait_ref in
  let generics = translate_sgeneric_args generics in
  let ty = translate_sty ty in
  { trait_ref; generics; type_name; ty }

let translate_predicates (preds : T.predicates) : predicates =
  let trait_type_constraints =
    List.map translate_strait_type_constraint preds.trait_type_constraints
  in
  { trait_type_constraints }

let translate_generic_params (generics : T.generic_params) : generic_params =
  let { T.regions = _; types; const_generics; trait_clauses } = generics in
  let trait_clauses = List.map translate_trait_clause trait_clauses in
  { types; const_generics; trait_clauses }

let translate_field (f : T.field) : field =
  let field_name = f.field_name in
  let field_ty = translate_sty f.field_ty in
  { field_name; field_ty }

let translate_fields (fl : T.field list) : field list =
  List.map translate_field fl

let translate_variant (v : T.variant) : variant =
  let variant_name = v.variant_name in
  let fields = translate_fields v.fields in
  { variant_name; fields }

let translate_variants (vl : T.variant list) : variant list =
  List.map translate_variant vl

(** Translate a type def kind from LLBC *)
let translate_type_decl_kind (kind : T.type_decl_kind) : type_decl_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields fields)
  | T.Enum variants -> Enum (translate_variants variants)
  | T.Opaque -> Opaque

(** Translate a type definition from LLBC

    Remark: this is not symbolic to pure but LLBC to pure. Still,
    I don't see the point of moving this definition for now.
 *)
let translate_type_decl (ctx : Contexts.decls_ctx) (def : T.type_decl) :
    type_decl =
  log#ldebug
    (lazy
      (let ctx = Print.Contexts.decls_ctx_to_fmt_env ctx in
       "translate_type_decl:\n\n"
       ^ Print.Types.type_decl_to_string ctx def
       ^ "\n"));
  let env = Print.Contexts.decls_ctx_to_fmt_env ctx in
  let def_id = def.T.def_id in
  let llbc_name = def.name in
  let name = Print.Types.name_to_string env def.name in
  let { T.regions; types; const_generics; trait_clauses } = def.generics in
  (* Can't translate types with regions for now *)
  assert (regions = []);
  let trait_clauses = List.map translate_trait_clause trait_clauses in
  let generics = { types; const_generics; trait_clauses } in
  let kind = translate_type_decl_kind def.T.kind in
  let preds = translate_predicates def.preds in
  let is_local = def.is_local in
  let meta = def.meta in
  {
    def_id;
    is_local;
    llbc_name;
    name;
    meta;
    generics;
    llbc_generics = def.generics;
    kind;
    preds;
  }

let translate_type_id (id : T.type_id) : type_id =
  match id with
  | TAdtId adt_id -> TAdtId adt_id
  | TAssumed aty ->
      let aty =
        match aty with
        | T.TArray -> TArray
        | T.TSlice -> TSlice
        | T.TStr -> TStr
        | T.TBox ->
            (* Boxes have to be eliminated: this type id shouldn't
               be translated *)
            raise (Failure "Unreachable")
      in
      TAssumed aty
  | TTuple -> TTuple

(** Translate a type, seen as an input/output of a forward function
    (preserve all borrows, etc.).

    Remark: it doesn't matter whether the types has regions or erased regions
    (both cases happen, actually).

    TODO: factor out the various translation functions.
*)
let rec translate_fwd_ty (type_infos : type_infos) (ty : T.ty) : ty =
  let translate = translate_fwd_ty type_infos in
  match ty with
  | T.TAdt (type_id, generics) -> (
      let t_generics = translate_fwd_generic_args type_infos generics in
      (* Eliminate boxes and simplify tuples *)
      match type_id with
      | TAdtId _ | TAssumed (TArray | TSlice | TStr) ->
          let type_id = translate_type_id type_id in
          TAdt (type_id, t_generics)
      | TTuple ->
          (* Note that if there is exactly one type, [mk_simpl_tuple_ty] is the
             identity *)
          mk_simpl_tuple_ty t_generics.types
      | TAssumed TBox -> (
          (* We eliminate boxes *)
          (* No general parametricity for now *)
          assert (
            not
              (List.exists
                 (TypesUtils.ty_has_borrows type_infos)
                 generics.types));
          match t_generics.types with
          | [ bty ] -> bty
          | _ ->
              raise
                (Failure
                   "Unreachable: box/vec/option receives exactly one type \
                    parameter")))
  | TVar vid -> TVar vid
  | TNever -> raise (Failure "Unreachable")
  | TLiteral lty -> TLiteral lty
  | TRef (_, rty, _) -> translate rty
  | TRawPtr (ty, rkind) ->
      let mut = match rkind with RMut -> Mut | RShared -> Const in
      let ty = translate ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TAssumed (TRawPtr mut), generics)
  | TTraitType (trait_ref, generics, type_name) ->
      let trait_ref = translate_fwd_trait_ref type_infos trait_ref in
      let generics = translate_fwd_generic_args type_infos generics in
      TTraitType (trait_ref, generics, type_name)
  | TArrow _ -> raise (Failure "TODO")

and translate_fwd_generic_args (type_infos : type_infos)
    (generics : T.generic_args) : generic_args =
  translate_generic_args (translate_fwd_ty type_infos) generics

and translate_fwd_trait_ref (type_infos : type_infos) (tr : T.trait_ref) :
    trait_ref =
  translate_trait_ref (translate_fwd_ty type_infos) tr

and translate_fwd_trait_instance_id (type_infos : type_infos)
    (id : T.trait_instance_id) : trait_instance_id =
  translate_trait_instance_id (translate_fwd_ty type_infos) id

(** Simply calls [translate_fwd_ty] *)
let ctx_translate_fwd_ty (ctx : bs_ctx) (ty : T.ty) : ty =
  let type_infos = ctx.type_context.type_infos in
  translate_fwd_ty type_infos ty

(** Simply calls [translate_fwd_generic_args] *)
let ctx_translate_fwd_generic_args (ctx : bs_ctx) (generics : T.generic_args) :
    generic_args =
  let type_infos = ctx.type_context.type_infos in
  translate_fwd_generic_args type_infos generics

(** Translate a type, when some regions may have ended.
    
    We return an option, because the translated type may be empty.
    
    [inside_mut]: are we inside a mutable borrow?
 *)
let rec translate_back_ty (type_infos : type_infos)
    (keep_region : T.region -> bool) (inside_mut : bool) (ty : T.ty) : ty option
    =
  let translate = translate_back_ty type_infos keep_region inside_mut in
  (* A small helper for "leave" types *)
  let wrap ty = if inside_mut then Some ty else None in
  match ty with
  | T.TAdt (type_id, generics) -> (
      match type_id with
      | TAdtId _ | TAssumed (TArray | TSlice | TStr) ->
          let type_id = translate_type_id type_id in
          if inside_mut then
            (* We do not want to filter anything, so we translate the generics
               as "forward" types *)
            let generics = translate_fwd_generic_args type_infos generics in
            Some (TAdt (type_id, generics))
          else
            (* If not inside a mutable reference: check if at least one
               of the generics contains a mutable reference (i.e., is not
               translated to `None`. If yes, keep the whole type, and
               translate all the generics as "forward" types (the backward
               function will extract the proper information from the ADT value)
            *)
            let types = List.filter_map translate generics.types in
            if types <> [] then
              let generics = translate_fwd_generic_args type_infos generics in
              Some (TAdt (type_id, generics))
            else None
      | TAssumed TBox -> (
          (* Don't accept ADTs (which are not tuples) with borrows for now *)
          assert (not (TypesUtils.ty_has_borrows type_infos ty));
          (* Eliminate the box *)
          match generics.types with
          | [ bty ] -> translate bty
          | _ ->
              raise
                (Failure "Unreachable: boxes receive exactly one type parameter")
          )
      | TTuple -> (
          (* Tuples can contain borrows (which we eliminate) *)
          let tys_t = List.filter_map translate generics.types in
          match tys_t with
          | [] -> None
          | _ ->
              (* Note that if there is exactly one type, [mk_simpl_tuple_ty]
               * is the identity *)
              Some (mk_simpl_tuple_ty tys_t)))
  | TVar vid -> wrap (TVar vid)
  | TNever -> raise (Failure "Unreachable")
  | TLiteral lty -> wrap (TLiteral lty)
  | TRef (r, rty, rkind) -> (
      match rkind with
      | RShared ->
          (* Ignore shared references, unless we are below a mutable borrow *)
          if inside_mut then translate rty else None
      | RMut ->
          (* Dive in, remembering the fact that we are inside a mutable borrow *)
          let inside_mut = true in
          if keep_region r then
            translate_back_ty type_infos keep_region inside_mut rty
          else None)
  | TRawPtr _ ->
      (* TODO: not sure what to do here *)
      None
  | TTraitType (trait_ref, generics, type_name) ->
      assert (generics.regions = []);
      (* Translate the trait ref and the generics as "forward" generics -
         we do not want to filter any type *)
      let trait_ref = translate_fwd_trait_ref type_infos trait_ref in
      let generics = translate_fwd_generic_args type_infos generics in
      Some (TTraitType (trait_ref, generics, type_name))
  | TArrow _ -> raise (Failure "TODO")

(** Simply calls [translate_back_ty] *)
let ctx_translate_back_ty (ctx : bs_ctx) (keep_region : 'r -> bool)
    (inside_mut : bool) (ty : T.ty) : ty option =
  let type_infos = ctx.type_context.type_infos in
  translate_back_ty type_infos keep_region inside_mut ty

let mk_type_check_ctx (ctx : bs_ctx) : PureTypeCheck.tc_ctx =
  let const_generics =
    T.ConstGenericVarId.Map.of_list
      (List.map
         (fun (cg : T.const_generic_var) ->
           (cg.index, ctx_translate_fwd_ty ctx (T.TLiteral cg.ty)))
         ctx.sg.generics.const_generics)
  in
  let env = VarId.Map.empty in
  {
    PureTypeCheck.type_decls = ctx.type_context.type_decls;
    global_decls = ctx.global_context.llbc_global_decls;
    env;
    const_generics;
  }

let type_check_pattern (ctx : bs_ctx) (v : typed_pattern) : unit =
  let ctx = mk_type_check_ctx ctx in
  let _ = PureTypeCheck.check_typed_pattern ctx v in
  ()

let type_check_texpression (ctx : bs_ctx) (e : texpression) : unit =
  if !Config.type_check_pure_code then
    let ctx = mk_type_check_ctx ctx in
    PureTypeCheck.check_texpression ctx e

let translate_fun_id_or_trait_method_ref (ctx : bs_ctx)
    (id : A.fun_id_or_trait_method_ref) : fun_id_or_trait_method_ref =
  match id with
  | FunId fun_id -> FunId fun_id
  | TraitMethod (trait_ref, method_name, fun_decl_id) ->
      let type_infos = ctx.type_context.type_infos in
      let trait_ref = translate_fwd_trait_ref type_infos trait_ref in
      TraitMethod (trait_ref, method_name, fun_decl_id)

let bs_ctx_register_forward_call (call_id : V.FunCallId.id) (forward : S.call)
    (args : texpression list) (ctx : bs_ctx) : bs_ctx =
  let calls = ctx.calls in
  assert (not (V.FunCallId.Map.mem call_id calls));
  let info =
    { forward; forward_inputs = args; backwards = T.RegionGroupId.Map.empty }
  in
  let calls = V.FunCallId.Map.add call_id info calls in
  { ctx with calls }

(** [back_args]: the *additional* list of inputs received by the backward function *)
let bs_ctx_register_backward_call (abs : V.abs) (call_id : V.FunCallId.id)
    (back_id : T.RegionGroupId.id) (back_args : texpression list) (ctx : bs_ctx)
    : bs_ctx * fun_or_op_id =
  (* Insert the abstraction in the call informations *)
  let info = V.FunCallId.Map.find call_id ctx.calls in
  assert (not (T.RegionGroupId.Map.mem back_id info.backwards));
  let backwards =
    T.RegionGroupId.Map.add back_id (abs, back_args) info.backwards
  in
  let info = { info with backwards } in
  let calls = V.FunCallId.Map.add call_id info ctx.calls in
  (* Insert the abstraction in the abstractions map *)
  let abstractions = ctx.abstractions in
  assert (not (V.AbstractionId.Map.mem abs.abs_id abstractions));
  let abstractions =
    V.AbstractionId.Map.add abs.abs_id (abs, back_args) abstractions
  in
  (* Retrieve the fun_id *)
  let fun_id =
    match info.forward.call_id with
    | S.Fun (fid, _) ->
        let fid = translate_fun_id_or_trait_method_ref ctx fid in
        Fun (FromLlbc (fid, None, Some back_id))
    | S.Unop _ | S.Binop _ -> raise (Failure "Unreachable")
  in
  (* Update the context and return *)
  ({ ctx with calls; abstractions }, fun_id)

(** List the ancestors of an abstraction *)
let list_ancestor_abstractions_ids (ctx : bs_ctx) (abs : V.abs)
    (call_id : V.FunCallId.id) : V.AbstractionId.id list =
  (* We could do something more "elegant" without references, but it is
   * so much simpler to use references... *)
  let abs_set = ref V.AbstractionId.Set.empty in
  let rec gather (abs_id : V.AbstractionId.id) : unit =
    if V.AbstractionId.Set.mem abs_id !abs_set then ()
    else (
      abs_set := V.AbstractionId.Set.add abs_id !abs_set;
      let abs, _ = V.AbstractionId.Map.find abs_id ctx.abstractions in
      List.iter gather abs.original_parents)
  in
  List.iter gather abs.original_parents;
  let ids = !abs_set in
  (* List the ancestors, in the proper order *)
  let call_info = V.FunCallId.Map.find call_id ctx.calls in
  List.filter
    (fun id -> V.AbstractionId.Set.mem id ids)
    call_info.forward.abstractions

(** List the ancestor abstractions of an abstraction introduced because of
    a function call *)
let list_ancestor_abstractions (ctx : bs_ctx) (abs : V.abs)
    (call_id : V.FunCallId.id) : (V.abs * texpression list) list =
  let abs_ids = list_ancestor_abstractions_ids ctx abs call_id in
  List.map (fun id -> V.AbstractionId.Map.find id ctx.abstractions) abs_ids

(** Small utility.

    Does the function *decrease* the fuel? [true] if recursive.
 *)
let function_decreases_fuel (info : fun_effect_info) : bool =
  !Config.use_fuel && info.is_rec

(** Small utility.

    Does the function *use* the fuel? [true] if can diverge.
 *)
let function_uses_fuel (info : fun_effect_info) : bool =
  !Config.use_fuel && info.can_diverge

(** Small utility *)
let mk_fuel_input_ty_as_list (info : fun_effect_info) : ty list =
  if function_uses_fuel info then [ mk_fuel_ty ] else []

(** Small utility *)
let mk_fuel_input_as_list (ctx : bs_ctx) (info : fun_effect_info) :
    texpression list =
  if function_uses_fuel info then [ mk_fuel_texpression ctx.fuel ] else []

(** Small utility. *)
let get_fun_effect_info (fun_infos : fun_info A.FunDeclId.Map.t)
    (fun_id : A.fun_id_or_trait_method_ref) (lid : V.LoopId.id option)
    (gid : T.RegionGroupId.id option) : fun_effect_info =
  match fun_id with
  | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
      let info = A.FunDeclId.Map.find fid fun_infos in
      let stateful_group = info.stateful in
      let stateful =
        stateful_group && ((not !Config.backward_no_state_update) || gid = None)
      in
      {
        can_fail = info.can_fail;
        stateful_group;
        stateful;
        can_diverge = info.can_diverge;
        is_rec = info.is_rec || Option.is_some lid;
      }
  | FunId (FAssumed aid) ->
      assert (lid = None);
      {
        can_fail = Assumed.assumed_fun_can_fail aid;
        stateful_group = false;
        stateful = false;
        can_diverge = false;
        is_rec = false;
      }

(** Translate a function signature.

    Note that the function also takes a list of names for the inputs, and
    computes, for every output for the backward functions, a corresponding
    name (outputs for backward functions come from borrows in the inputs
    of the forward function) which we use as hints to generate pretty names
    in the extracted code.
 *)
let translate_fun_sig (decls_ctx : C.decls_ctx) (fun_id : A.fun_id)
    (sg : A.fun_sig) (input_names : string option list)
    (bid : T.RegionGroupId.id option) : fun_sig_named_outputs =
  let fun_infos = decls_ctx.fun_ctx.fun_infos in
  let type_infos = decls_ctx.type_ctx.type_infos in
  (* Retrieve the list of parent backward functions *)
  let regions_hierarchy =
    FunIdMap.find fun_id decls_ctx.fun_ctx.regions_hierarchies
  in
  let gid, parents =
    match bid with
    | None -> (None, T.RegionGroupId.Set.empty)
    | Some bid ->
        let parents = list_ancestor_region_groups regions_hierarchy bid in
        (Some bid, parents)
  in
  (* Is the function stateful, and can it fail? *)
  let lid = None in
  let effect_info = get_fun_effect_info fun_infos (FunId fun_id) lid bid in
  (* We need an evaluation context to normalize the types (to normalize the
     associated types, etc. - for instance it may happen that the types
     refer to the types associated to a trait ref, but where the trait ref
     is a known impl). *)
  (* Create the context *)
  let ctx =
    let region_groups =
      List.map (fun (g : T.region_var_group) -> g.id) regions_hierarchy
    in
    let ctx =
      InterpreterUtils.initialize_eval_context decls_ctx region_groups
        sg.generics.types sg.generics.const_generics
    in
    (* Compute the normalization map for the *sty* types and add it to the context *)
    AssociatedTypes.ctx_add_norm_trait_types_from_preds ctx
      sg.preds.trait_type_constraints
  in

  (* Normalize the signature *)
  let sg =
    let ({ A.inputs; output; _ } : A.fun_sig) = sg in
    let norm = AssociatedTypes.ctx_normalize_ty ctx in
    let inputs = List.map norm inputs in
    let output = norm output in
    { sg with A.inputs; output }
  in

  (* List the inputs for:
   * - the fuel
   * - the forward function
   * - the parent backward functions, in proper order
   * - the current backward function (if it is a backward function)
   *)
  let fuel = mk_fuel_input_ty_as_list effect_info in
  let fwd_inputs = List.map (translate_fwd_ty type_infos) sg.inputs in
  (* For the backward functions: for now we don't supported nested borrows,
   * so just check that there aren't parent regions *)
  assert (T.RegionGroupId.Set.is_empty parents);
  (* Small helper to translate types for backward functions *)
  let translate_back_ty_for_gid (gid : T.RegionGroupId.id) (ty : T.ty) :
      ty option =
    let rg = T.RegionGroupId.nth regions_hierarchy gid in
    (* Turn *all* the outer bound regions into free regions *)
    let _, rid_subst, r_subst =
      Substitute.fresh_regions_with_substs_from_vars ~fail_if_not_found:true
        sg.generics.regions
    in
    let subst = { Substitute.empty_subst with r_subst } in
    let ty = Substitute.ty_substitute subst ty in
    (* Compute the set of regions belonging to this group *)
    let gr_regions =
      T.RegionId.Set.of_list
        (List.map (fun rid -> Option.get (rid_subst rid)) rg.regions)
    in
    let keep_region r =
      match r with
      | T.RStatic -> raise Unimplemented
      | RErased -> raise (Failure "Unexpected erased region")
      | RBVar _ -> raise (Failure "Unexpected bound region")
      | RFVar rid -> T.RegionId.Set.mem rid gr_regions
    in
    let inside_mut = false in
    translate_back_ty type_infos keep_region inside_mut ty
  in
  (* Compute the additinal inputs for the current function, if it is a backward
   * function *)
  let back_inputs =
    match gid with
    | None -> []
    | Some gid ->
        (* For now, we don't allow nested borrows, so the additional inputs to the
           backward function can only come from borrows that were returned like
           in (for the backward function we introduce for 'a):
           {[
             fn f<'a>(...) -> &'a mut u32;
           ]}
           Upon ending the abstraction for 'a, we need to get back the borrow
           the function returned.
        *)
        List.filter_map (translate_back_ty_for_gid gid) [ sg.output ]
  in
  (* If the function is stateful, the inputs are:
     - forward:  [fwd_ty0, ..., fwd_tyn, state]
     - backward:
       - if {!Config.backward_no_state_update}: [fwd_ty0, ..., fwd_tyn, state, back_ty, state]
       - otherwise: [fwd_ty0, ..., fwd_tyn, state, back_ty]

       The backward takes the same state as input as the forward function,
       together with the state at the point where it gets called, if it is
       stateful.

       See the comments for {!Config.backward_no_state_update}
  *)
  let fwd_state_ty =
    (* For the forward state, we check if the *whole group* is stateful.
       See {!effect_info}. *)
    if effect_info.stateful_group then [ mk_state_ty ] else []
  in
  let back_state_ty =
    (* For the backward state, we check if the function is a backward function,
       and it is stateful *)
    if effect_info.stateful && Option.is_some gid then [ mk_state_ty ] else []
  in

  (* Concatenate the inputs, in the following order:
   * - forward inputs
   * - forward state input
   * - backward inputs
   * - backward state input
   *)
  let inputs =
    List.concat [ fuel; fwd_inputs; fwd_state_ty; back_inputs; back_state_ty ]
  in
  (* Outputs *)
  let output_names, doutputs =
    match gid with
    | None ->
        (* This is a forward function: there is one (unnamed) output *)
        ([ None ], [ translate_fwd_ty type_infos sg.output ])
    | Some gid ->
        (* This is a backward function: there might be several outputs.
           The outputs are the borrows inside the regions of the abstractions
           and which are present in the input values. For instance, see:
           {[
             fn f<'a>(x : &'a mut u32) -> ...;
           ]}
           Upon ending the abstraction for 'a, we give back the borrow which
           was consumed through the [x] parameter.
        *)
        let outputs =
          List.map
            (fun (name, input_ty) ->
              (name, translate_back_ty_for_gid gid input_ty))
            (List.combine input_names sg.inputs)
        in
        (* Filter *)
        let outputs =
          List.filter (fun (_, opt_ty) -> Option.is_some opt_ty) outputs
        in
        let outputs =
          List.map (fun (name, opt_ty) -> (name, Option.get opt_ty)) outputs
        in
        List.split outputs
  in
  (* Create the return type *)
  let output =
    (* Group the outputs together *)
    let output = mk_simpl_tuple_ty doutputs in
    (* Add the output state *)
    let output =
      if effect_info.stateful then mk_simpl_tuple_ty [ mk_state_ty; output ]
      else output
    in
    (* Wrap in a result type *)
    if effect_info.can_fail then mk_result_ty output else output
  in
  (* Generic parameters *)
  let generics = translate_generic_params sg.generics in
  (* Return *)
  let has_fuel = fuel <> [] in
  let num_fwd_inputs_no_state = List.length fwd_inputs in
  let num_fwd_inputs_with_fuel_no_state =
    (* We use the fact that [fuel] has length 1 if we use some fuel, 0 otherwise *)
    List.length fuel + num_fwd_inputs_no_state
  in
  let num_back_inputs_no_state =
    if bid = None then None else Some (List.length back_inputs)
  in
  let info =
    {
      has_fuel;
      num_fwd_inputs_with_fuel_no_state;
      num_fwd_inputs_with_fuel_with_state =
        (* We use the fact that [fwd_state_ty] has length 1 if there is a state,
           and 0 otherwise *)
        num_fwd_inputs_with_fuel_no_state + List.length fwd_state_ty;
      num_back_inputs_no_state;
      num_back_inputs_with_state =
        (* Length of [back_state_ty]: similar trick as for [fwd_state_ty] *)
        Option.map
          (fun n -> n + List.length back_state_ty)
          num_back_inputs_no_state;
      effect_info;
    }
  in
  let preds = translate_predicates sg.preds in
  let sg =
    {
      generics;
      llbc_generics = sg.generics;
      preds;
      inputs;
      output;
      doutputs;
      info;
    }
  in
  { sg; output_names }

let bs_ctx_fresh_state_var (ctx : bs_ctx) : bs_ctx * typed_pattern =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let state_var =
    { id; basename = Some ConstStrings.state_basename; ty = mk_state_ty }
  in
  let state_pat = mk_typed_pattern_from_var state_var None in
  (* Update the context *)
  let ctx = { ctx with var_counter; state_var = id } in
  (* Return *)
  (ctx, state_pat)

(** WARNING: do not call this function directly.
    Call [fresh_named_var_for_symbolic_value] instead. *)
let fresh_var_llbc_ty (basename : string option) (ty : T.ty) (ctx : bs_ctx) :
    bs_ctx * var =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let ty = ctx_translate_fwd_ty ctx ty in
  let var = { id; basename; ty } in
  (* Update the context *)
  let ctx = { ctx with var_counter } in
  (* Return *)
  (ctx, var)

let fresh_named_var_for_symbolic_value (basename : string option)
    (sv : V.symbolic_value) (ctx : bs_ctx) : bs_ctx * var =
  (* Generate the fresh variable *)
  let ctx, var = fresh_var_llbc_ty basename sv.sv_ty ctx in
  (* Insert in the map *)
  let sv_to_var = V.SymbolicValueId.Map.add_strict sv.sv_id var ctx.sv_to_var in
  (* Update the context *)
  let ctx = { ctx with sv_to_var } in
  (* Return *)
  (ctx, var)

let fresh_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) :
    bs_ctx * var =
  fresh_named_var_for_symbolic_value None sv ctx

let fresh_vars_for_symbolic_values (svl : V.symbolic_value list) (ctx : bs_ctx)
    : bs_ctx * var list =
  List.fold_left_map (fun ctx sv -> fresh_var_for_symbolic_value sv ctx) ctx svl

let fresh_named_vars_for_symbolic_values
    (svl : (string option * V.symbolic_value) list) (ctx : bs_ctx) :
    bs_ctx * var list =
  List.fold_left_map
    (fun ctx (name, sv) -> fresh_named_var_for_symbolic_value name sv ctx)
    ctx svl

(** This generates a fresh variable **which is not to be linked to any symbolic value** *)
let fresh_var (basename : string option) (ty : ty) (ctx : bs_ctx) : bs_ctx * var
    =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh ctx.var_counter in
  let var = { id; basename; ty } in
  (* Update the context *)
  let ctx = { ctx with var_counter } in
  (* Return *)
  (ctx, var)

let fresh_vars (vars : (string option * ty) list) (ctx : bs_ctx) :
    bs_ctx * var list =
  List.fold_left_map (fun ctx (name, ty) -> fresh_var name ty ctx) ctx vars

let lookup_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) : var =
  match V.SymbolicValueId.Map.find_opt sv.sv_id ctx.sv_to_var with
  | Some v -> v
  | None ->
      raise
        (Failure
           ("Could not find var for symbolic value: "
           ^ V.SymbolicValueId.to_string sv.sv_id))

(** Peel boxes as long as the value is of the form [Box<T>] *)
let rec unbox_typed_value (v : V.typed_value) : V.typed_value =
  match (v.value, v.ty) with
  | V.VAdt av, T.TAdt (T.TAssumed T.TBox, _) -> (
      match av.field_values with
      | [ bv ] -> unbox_typed_value bv
      | _ -> raise (Failure "Unreachable"))
  | _ -> v

(** Translate a symbolic value *)
let symbolic_value_to_texpression (ctx : bs_ctx) (sv : V.symbolic_value) :
    texpression =
  (* Translate the type *)
  let var = lookup_var_for_symbolic_value sv ctx in
  mk_texpression_from_var var

(** Translate a typed value.

    It is used, for instance, on values used as inputs for function calls.

    **IMPORTANT**: this function makes the assumption that the typed value
    doesn't contain ⊥. This means in particular that symbolic values don't
    contain ended regions.
    
    TODO: we might want to remember in the symbolic AST the set of ended
    regions, at the points where we need it, for sanity checks (though the
    sanity checks in the symbolic interpreter should be enough).
    The points where we need this set so far:
    - function call
    - end abstraction
    - return
 *)
let rec typed_value_to_texpression (ctx : bs_ctx) (ectx : C.eval_ctx)
    (v : V.typed_value) : texpression =
  (* We need to ignore boxes *)
  let v = unbox_typed_value v in
  let translate = typed_value_to_texpression ctx ectx in
  (* Translate the type *)
  let ty = ctx_translate_fwd_ty ctx v.ty in
  (* Translate the value *)
  let value =
    match v.value with
    | VLiteral cv -> { e = Const cv; ty }
    | VAdt av -> (
        let variant_id = av.variant_id in
        let field_values = List.map translate av.field_values in
        (* Eliminate the tuple wrapper if it is a tuple with exactly one field *)
        match v.ty with
        | TAdt (TTuple, _) ->
            assert (variant_id = None);
            mk_simpl_tuple_texpression field_values
        | _ ->
            (* Retrieve the type and the translated generics from the translated
               type (simpler this way) *)
            let adt_id, generics = ty_as_adt ty in
            (* Create the constructor *)
            let qualif_id = AdtCons { adt_id; variant_id = av.variant_id } in
            let qualif = { id = qualif_id; generics } in
            let cons_e = Qualif qualif in
            let field_tys =
              List.map (fun (v : texpression) -> v.ty) field_values
            in
            let cons_ty = mk_arrows field_tys ty in
            let cons = { e = cons_e; ty = cons_ty } in
            (* Apply the constructor *)
            mk_apps cons field_values)
    | VBottom -> raise (Failure "Unreachable")
    | VLoan lc -> (
        match lc with
        | VSharedLoan (_, v) -> translate v
        | VMutLoan _ -> raise (Failure "Unreachable"))
    | VBorrow bc -> (
        match bc with
        | VSharedBorrow bid ->
            (* Lookup the shared value in the context, and continue *)
            let sv = InterpreterBorrowsCore.lookup_shared_value ectx bid in
            translate sv
        | VReservedMutBorrow bid ->
            (* Same as for shared borrows. However, note that we use reserved borrows
             * only in *meta-data*: a value *actually used* in the translation can't come
             * from an unpromoted reserved borrow *)
            let sv = InterpreterBorrowsCore.lookup_shared_value ectx bid in
            translate sv
        | VMutBorrow (_, v) ->
            (* Borrows are the identity in the extraction *)
            translate v)
    | VSymbolic sv -> symbolic_value_to_texpression ctx sv
  in
  (* Debugging *)
  log#ldebug
    (lazy
      ("typed_value_to_texpression: result:" ^ "\n- input value:\n"
      ^ typed_value_to_string ctx v
      ^ "\n- translated expression:\n"
      ^ texpression_to_string ctx value));
  (* Sanity check *)
  type_check_texpression ctx value;
  (* Return *)
  value

(** Explore an abstraction value and convert it to a consumed value
    by collecting all the meta-values from the ended *loans*.

    Consumed values are rvalues because when an abstraction ends we
    introduce a call to a backward function in the synthesized program,
    which takes as inputs those consumed values:
    {[
      // Rust:
      fn choose<'a>(b: bool, x : &'a mut u32, y : &'a mut u32) -> &'a mut u32;

      // Synthesis:
      let ... = choose_back b x y nz in
                                  ^^
    ]}
 *)
let rec typed_avalue_to_consumed (ctx : bs_ctx) (ectx : C.eval_ctx)
    (av : V.typed_avalue) : texpression option =
  let translate = typed_avalue_to_consumed ctx ectx in
  let value =
    match av.value with
    | AAdt adt_v -> (
        (* Translate the field values *)
        let field_values = List.filter_map translate adt_v.field_values in
        (* For now, only tuples can contain borrows *)
        let adt_id, _ = TypesUtils.ty_as_adt av.ty in
        match adt_id with
        | TAdtId _ | TAssumed (TBox | TArray | TSlice | TStr) ->
            assert (field_values = []);
            None
        | TTuple ->
            (* Return *)
            if field_values = [] then None
            else
              (* Note that if there is exactly one field value,
               * [mk_simpl_tuple_rvalue] is the identity *)
              let rv = mk_simpl_tuple_texpression field_values in
              Some rv)
    | ABottom -> raise (Failure "Unreachable")
    | ALoan lc -> aloan_content_to_consumed ctx ectx lc
    | ABorrow bc -> aborrow_content_to_consumed ctx bc
    | ASymbolic aproj -> aproj_to_consumed ctx aproj
    | AIgnored -> None
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_texpression ctx value);
  (* Return *)
  value

and aloan_content_to_consumed (ctx : bs_ctx) (ectx : C.eval_ctx)
    (lc : V.aloan_content) : texpression option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> raise (Failure "Unreachable")
  | AEndedMutLoan { child = _; given_back = _; given_back_meta } ->
      (* Return the meta-value *)
      Some (typed_value_to_texpression ctx ectx given_back_meta)
  | AEndedSharedLoan (_, _) ->
      (* We don't dive into shared loans: there is nothing to give back
       * inside (note that there could be a mutable borrow in the shared
       * value, pointing to a mutable loan in the child avalue, but this
       * borrow is in practice immutable) *)
      None
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      raise (Failure "Unreachable")
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      None

and aborrow_content_to_consumed (_ctx : bs_ctx) (bc : V.aborrow_content) :
    texpression option =
  match bc with
  | V.AMutBorrow (_, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      raise (Failure "Unreachable")
  | AEndedMutBorrow (_, _) ->
      (* We collect consumed values: ignore *)
      None
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AEndedSharedBorrow | AProjSharedBorrow _ ->
      (* Ignore *)
      None

and aproj_to_consumed (ctx : bs_ctx) (aproj : V.aproj) : texpression option =
  match aproj with
  | V.AEndedProjLoans (msv, []) ->
      (* The symbolic value was left unchanged *)
      let var = lookup_var_for_symbolic_value msv ctx in
      Some (mk_texpression_from_var var)
  | V.AEndedProjLoans (_, [ (mnv, child_aproj) ]) ->
      assert (child_aproj = AIgnoredProjBorrows);
      (* The symbolic value was updated *)
      let var = lookup_var_for_symbolic_value mnv ctx in
      Some (mk_texpression_from_var var)
  | V.AEndedProjLoans (_, _) ->
      (* The symbolic value was updated, and the given back values come from sevearl
       * abstractions *)
      raise Unimplemented
  | AEndedProjBorrows _ -> (* We consider consumed values *) None
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      raise (Failure "Unreachable")

(** Convert the abstraction values in an abstraction to consumed values.

    See [typed_avalue_to_consumed].
 *)
let abs_to_consumed (ctx : bs_ctx) (ectx : C.eval_ctx) (abs : V.abs) :
    texpression list =
  log#ldebug (lazy ("abs_to_consumed:\n" ^ abs_to_string ctx abs));
  List.filter_map (typed_avalue_to_consumed ctx ectx) abs.avalues

let translate_mprojection_elem (pe : E.projection_elem) :
    mprojection_elem option =
  match pe with
  | Deref | DerefBox -> None
  | Field (pkind, field_id) -> Some { pkind; field_id }

let translate_mprojection (p : E.projection) : mprojection =
  List.filter_map translate_mprojection_elem p

(** Translate a "meta"-place *)
let translate_mplace (p : S.mplace) : mplace =
  let var_id = p.bv.index in
  let name = p.bv.name in
  let projection = translate_mprojection p.projection in
  { var_id; name; projection }

let translate_opt_mplace (p : S.mplace option) : mplace option =
  match p with None -> None | Some p -> Some (translate_mplace p)

(** Explore an abstraction value and convert it to a given back value
    by collecting all the meta-values from the ended *borrows*.

    Given back values are patterns, because when an abstraction ends, we
    introduce a call to a backward function in the synthesized program,
    which introduces new values:
    {[
      let (nx, ny) = f_back ... in
          ^^^^^^^^
    ]}
    
    [mp]: it is possible to provide some meta-place information, to guide
    the heuristics which later find pretty names for the variables.
 *)
let rec typed_avalue_to_given_back (mp : mplace option) (av : V.typed_avalue)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  let ctx, value =
    match av.value with
    | AAdt adt_v -> (
        (* Translate the field values *)
        (* For now we forget the meta-place information so that it doesn't get used
         * by several fields (which would then all have the same name...), but we
         * might want to do something smarter *)
        let mp = None in
        let ctx, field_values =
          List.fold_left_map
            (fun ctx fv -> typed_avalue_to_given_back mp fv ctx)
            ctx adt_v.field_values
        in
        let field_values = List.filter_map (fun x -> x) field_values in
        (* For now, only tuples can contain borrows - note that if we gave
         * something like a [&mut Vec] to a function, we give back the
         * vector value upon visiting the "abstraction borrow" node *)
        let adt_id, _ = TypesUtils.ty_as_adt av.ty in
        match adt_id with
        | TAdtId _ | TAssumed (TBox | TArray | TSlice | TStr) ->
            assert (field_values = []);
            (ctx, None)
        | TTuple ->
            (* Return *)
            let variant_id = adt_v.variant_id in
            assert (variant_id = None);
            if field_values = [] then (ctx, None)
            else
              (* Note that if there is exactly one field value, [mk_simpl_tuple_pattern]
               * is the identity *)
              let lv = mk_simpl_tuple_pattern field_values in
              (ctx, Some lv))
    | ABottom -> raise (Failure "Unreachable")
    | ALoan lc -> aloan_content_to_given_back mp lc ctx
    | ABorrow bc -> aborrow_content_to_given_back mp bc ctx
    | ASymbolic aproj -> aproj_to_given_back mp aproj ctx
    | AIgnored -> (ctx, None)
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with None -> () | Some value -> type_check_pattern ctx value);
  (* Return *)
  (ctx, value)

and aloan_content_to_given_back (_mp : mplace option) (lc : V.aloan_content)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  match lc with
  | AMutLoan (_, _) | ASharedLoan (_, _, _) -> raise (Failure "Unreachable")
  | AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
  | AEndedSharedLoan (_, _) ->
      (* We consider given back values, and thus ignore those *)
      (ctx, None)
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      raise (Failure "Unreachable")
  | AEndedIgnoredMutLoan _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AIgnoredSharedLoan _ ->
      (* Ignore *)
      (ctx, None)

and aborrow_content_to_given_back (mp : mplace option) (bc : V.aborrow_content)
    (ctx : bs_ctx) : bs_ctx * typed_pattern option =
  match bc with
  | V.AMutBorrow (_, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
      raise (Failure "Unreachable")
  | AEndedMutBorrow (msv, _) ->
      (* Return the meta-symbolic-value *)
      let ctx, var = fresh_var_for_symbolic_value msv ctx in
      (ctx, Some (mk_typed_pattern_from_var var mp))
  | AEndedIgnoredMutBorrow _ ->
      (* This happens with nested borrows: we need to dive in *)
      raise Unimplemented
  | AEndedSharedBorrow | AProjSharedBorrow _ ->
      (* Ignore *)
      (ctx, None)

and aproj_to_given_back (mp : mplace option) (aproj : V.aproj) (ctx : bs_ctx) :
    bs_ctx * typed_pattern option =
  match aproj with
  | V.AEndedProjLoans (_, child_projs) ->
      (* There may be children borrow projections in case of nested borrows,
       * in which case we need to dive in - we disallow nested borrows for now *)
      assert (
        List.for_all
          (fun (_, aproj) -> aproj = V.AIgnoredProjBorrows)
          child_projs);
      (ctx, None)
  | AEndedProjBorrows mv ->
      (* Return the meta-value *)
      let ctx, var = fresh_var_for_symbolic_value mv ctx in
      (ctx, Some (mk_typed_pattern_from_var var mp))
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      raise (Failure "Unreachable")

(** Convert the abstraction values in an abstraction to given back values.

    See [typed_avalue_to_given_back].
 *)
let abs_to_given_back (mpl : mplace option list option) (abs : V.abs)
    (ctx : bs_ctx) : bs_ctx * typed_pattern list =
  let avalues =
    match mpl with
    | None -> List.map (fun av -> (None, av)) abs.avalues
    | Some mpl -> List.combine mpl abs.avalues
  in
  let ctx, values =
    List.fold_left_map
      (fun ctx (mp, av) -> typed_avalue_to_given_back mp av ctx)
      ctx avalues
  in
  let values = List.filter_map (fun x -> x) values in
  (ctx, values)

(** Simply calls [abs_to_given_back] *)
let abs_to_given_back_no_mp (abs : V.abs) (ctx : bs_ctx) :
    bs_ctx * typed_pattern list =
  let mpl = List.map (fun _ -> None) abs.avalues in
  abs_to_given_back (Some mpl) abs ctx

(** Return the ordered list of the (transitive) parents of a given abstraction.

    Is used for instance when collecting the input values given to all the
    parent functions, in order to properly instantiate an 
 *)
let get_abs_ancestors (ctx : bs_ctx) (abs : V.abs) (call_id : V.FunCallId.id) :
    S.call * (V.abs * texpression list) list =
  let call_info = V.FunCallId.Map.find call_id ctx.calls in
  let abs_ancestors = list_ancestor_abstractions ctx abs call_id in
  (call_info.forward, abs_ancestors)

(** Add meta-information to an expression *)
let mk_emeta_symbolic_assignments (vars : var list) (values : texpression list)
    (e : texpression) : texpression =
  let var_values = List.combine vars values in
  List.fold_right
    (fun (var, arg) e -> mk_emeta (SymbolicAssignment (var_get_id var, arg)) e)
    var_values e

let rec translate_expression (e : S.expression) (ctx : bs_ctx) : texpression =
  match e with
  | S.Return (ectx, opt_v) -> translate_return ectx opt_v ctx
  | ReturnWithLoop (loop_id, is_continue) ->
      translate_return_with_loop loop_id is_continue ctx
  | Panic -> translate_panic ctx
  | FunCall (call, e) -> translate_function_call call e ctx
  | EndAbstraction (ectx, abs, e) -> translate_end_abstraction ectx abs e ctx
  | EvalGlobal (gid, sv, e) -> translate_global_eval gid sv e ctx
  | Assertion (ectx, v, e) -> translate_assertion ectx v e ctx
  | Expansion (p, sv, exp) -> translate_expansion p sv exp ctx
  | IntroSymbolic (ectx, p, sv, v, e) ->
      translate_intro_symbolic ectx p sv v e ctx
  | Meta (meta, e) -> translate_emeta meta e ctx
  | ForwardEnd (ectx, loop_input_values, e, back_e) ->
      translate_forward_end ectx loop_input_values e back_e ctx
  | Loop loop -> translate_loop loop ctx

and translate_panic (ctx : bs_ctx) : texpression =
  (* Here we use the function return type - note that it is ok because
   * we don't match on panics which happen inside the function body -
   * but it won't be true anymore once we translate individual blocks *)
  (* If we use a state monad, we need to add a lambda for the state variable *)
  (* Note that only forward functions return a state *)
  let output_ty =
    if ctx.inside_loop && Option.is_some ctx.bid then
      (* We are synthesizing the backward function of a loop body *)
      let bid = Option.get ctx.bid in
      let back_vars =
        T.RegionGroupId.Map.find bid (Option.get ctx.loop_backward_outputs)
      in
      let tys = List.map (fun (v : var) -> v.ty) back_vars in
      mk_simpl_tuple_ty tys
    else
      (* Regular function, or forward function (the forward translation for
         a loop has the same return type as the parent function)
      *)
      mk_simpl_tuple_ty ctx.sg.doutputs
  in
  (* TODO: we should use a [Fail] function *)
  if ctx.sg.info.effect_info.stateful then
    (* Create the [Fail] value *)
    let ret_ty = mk_simpl_tuple_ty [ mk_state_ty; output_ty ] in
    let ret_v =
      mk_result_fail_texpression_with_error_id error_failure_id ret_ty
    in
    ret_v
  else mk_result_fail_texpression_with_error_id error_failure_id output_ty

(** [opt_v]: the value to return, in case we translate a forward body *)
and translate_return (ectx : C.eval_ctx) (opt_v : V.typed_value option)
    (ctx : bs_ctx) : texpression =
  (* There are two cases:
     - either we reach the return of a forward function or a forward loop body,
       in which case the optional value should be [Some] (it is the returned value)
     - or we are translating a backward function, in which case it should be [None]
  *)
  (* Compute the values that we should return *without the state and the result
   * wrapper* *)
  let output =
    match ctx.bid with
    | None ->
        (* Forward function *)
        let v = Option.get opt_v in
        typed_value_to_texpression ctx ectx v
    | Some bid ->
        (* Backward function *)
        (* Sanity check *)
        assert (opt_v = None);
        (* Group the variables in which we stored the values we need to give back.
         * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
        let backward_outputs =
          T.RegionGroupId.Map.find bid ctx.backward_outputs
        in
        let field_values = List.map mk_texpression_from_var backward_outputs in
        mk_simpl_tuple_texpression field_values
  in
  (* We may need to return a state
   * - error-monad: Return x
   * - state-error: Return (state, x)
   * *)
  let effect_info = ctx.sg.info.effect_info in
  let output =
    if effect_info.stateful then
      let state_rvalue = mk_state_texpression ctx.state_var in
      mk_simpl_tuple_texpression [ state_rvalue; output ]
    else output
  in
  (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
  mk_result_return_texpression output

and translate_return_with_loop (loop_id : V.LoopId.id) (is_continue : bool)
    (ctx : bs_ctx) : texpression =
  assert (is_continue = ctx.inside_loop);
  let loop_id = V.LoopId.Map.find loop_id ctx.loop_ids_map in
  assert (loop_id = Option.get ctx.loop_id);

  (* Lookup the loop information *)
  let loop_id = Option.get ctx.loop_id in
  let loop_info = LoopId.Map.find loop_id ctx.loops in

  (* There are two cases depending on whether we translate a backward function
     or not.
  *)
  let output =
    match ctx.bid with
    | None ->
        (* Forward *)
        mk_texpression_from_var
          (Option.get loop_info.forward_output_no_state_no_result)
    | Some bid ->
        (* Backward *)
        (* Group the variables in which we stored the values we need to give back.
         * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
        let backward_outputs =
          let map =
            if ctx.inside_loop then
              (* We are synthesizing a loop body *)
              Option.get ctx.loop_backward_outputs
            else (* Regular function *)
              ctx.backward_outputs
          in
          T.RegionGroupId.Map.find bid map
        in
        let field_values = List.map mk_texpression_from_var backward_outputs in
        mk_simpl_tuple_texpression field_values
  in

  (* We may need to return a state
   * - error-monad: Return x
   * - state-error: Return (state, x)
   * Note that the loop function and the parent function live in the same
   * effect - in particular, one manipulates a state iff the other does
   * the same.
   * *)
  let effect_info = ctx.sg.info.effect_info in
  let output =
    if effect_info.stateful then
      let state_rvalue = mk_state_texpression ctx.state_var in
      mk_simpl_tuple_texpression [ state_rvalue; output ]
    else output
  in
  (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
  mk_result_return_texpression output

and translate_function_call (call : S.call) (e : S.expression) (ctx : bs_ctx) :
    texpression =
  log#ldebug
    (lazy
      ("translate_function_call:\n"
      ^ ctx_generic_args_to_string ctx call.generics));
  (* Translate the function call *)
  let generics = ctx_translate_fwd_generic_args ctx call.generics in
  let args =
    let args = List.map (typed_value_to_texpression ctx call.ctx) call.args in
    let args_mplaces = List.map translate_opt_mplace call.args_places in
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
      (List.combine args args_mplaces)
  in
  let dest_mplace = translate_opt_mplace call.dest_place in
  let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
  (* Retrieve the function id, and register the function call in the context
   * if necessary. *)
  let ctx, fun_id, effect_info, args, out_state =
    match call.call_id with
    | S.Fun (fid, call_id) ->
        (* Regular function call *)
        let fid_t = translate_fun_id_or_trait_method_ref ctx fid in
        let func = Fun (FromLlbc (fid_t, None, None)) in
        (* Retrieve the effect information about this function (can fail,
         * takes a state as input, etc.) *)
        let effect_info =
          get_fun_effect_info ctx.fun_context.fun_infos fid None None
        in
        (* Depending on the function effects:
           * - add the fuel
           * - add the state input argument
           * - generate a fresh state variable for the returned state
        *)
        let args, ctx, out_state =
          let fuel = mk_fuel_input_as_list ctx effect_info in
          if effect_info.stateful then
            let state_var = mk_state_texpression ctx.state_var in
            let ctx, nstate_var = bs_ctx_fresh_state_var ctx in
            (List.concat [ fuel; args; [ state_var ] ], ctx, Some nstate_var)
          else (List.concat [ fuel; args ], ctx, None)
        in
        (* Register the function call *)
        let ctx = bs_ctx_register_forward_call call_id call args ctx in
        (ctx, func, effect_info, args, out_state)
    | S.Unop E.Not ->
        let effect_info =
          {
            can_fail = false;
            stateful_group = false;
            stateful = false;
            can_diverge = false;
            is_rec = false;
          }
        in
        (ctx, Unop Not, effect_info, args, None)
    | S.Unop E.Neg -> (
        match args with
        | [ arg ] ->
            let int_ty = ty_as_integer arg.ty in
            (* Note that negation can lead to an overflow and thus fail (it
             * is thus monadic) *)
            let effect_info =
              {
                can_fail = true;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            (ctx, Unop (Neg int_ty), effect_info, args, None)
        | _ -> raise (Failure "Unreachable"))
    | S.Unop (E.Cast cast_kind) -> (
        match cast_kind with
        | CastScalar (src_ty, tgt_ty) ->
            (* Note that cast can fail *)
            let effect_info =
              {
                can_fail = true;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            (ctx, Unop (Cast (src_ty, tgt_ty)), effect_info, args, None)
        | CastFnPtr _ -> raise (Failure "TODO: function casts"))
    | S.Binop binop -> (
        match args with
        | [ arg0; arg1 ] ->
            let int_ty0 = ty_as_integer arg0.ty in
            let int_ty1 = ty_as_integer arg1.ty in
            (match binop with
            (* The Rust compiler accepts bitshifts for any integer type combination for ty0, ty1 *)
            | E.Shl | E.Shr -> ()
            | _ -> assert (int_ty0 = int_ty1));
            let effect_info =
              {
                can_fail = ExpressionsUtils.binop_can_fail binop;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            (ctx, Binop (binop, int_ty0), effect_info, args, None)
        | _ -> raise (Failure "Unreachable"))
  in
  let dest_v =
    let dest = mk_typed_pattern_from_var dest dest_mplace in
    match out_state with
    | None -> dest
    | Some out_state -> mk_simpl_tuple_pattern [ out_state; dest ]
  in
  let func = { id = FunOrOp fun_id; generics } in
  let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
  let ret_ty =
    if effect_info.can_fail then mk_result_ty dest_v.ty else dest_v.ty
  in
  let func_ty = mk_arrows input_tys ret_ty in
  let func = { e = Qualif func; ty = func_ty } in
  let call = mk_apps func args in
  (* Translate the next expression *)
  let next_e = translate_expression e ctx in
  (* Put together *)
  mk_let effect_info.can_fail dest_v call next_e

and translate_end_abstraction (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) : texpression =
  log#ldebug
    (lazy
      ("translate_end_abstraction: abstraction kind: "
     ^ V.show_abs_kind abs.kind));
  match abs.kind with
  | V.SynthInput rg_id ->
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.FunCall (call_id, rg_id) ->
      translate_end_abstraction_fun_call ectx abs e ctx call_id rg_id
  | V.SynthRet rg_id -> translate_end_abstraction_synth_ret ectx abs e ctx rg_id
  | V.Loop (loop_id, rg_id, abs_kind) ->
      translate_end_abstraction_loop ectx abs e ctx loop_id rg_id abs_kind
  | V.Identity -> translate_end_abstraction_identity ectx abs e ctx

and translate_end_abstraction_synth_input (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) (rg_id : T.RegionGroupId.id) : texpression
    =
  log#ldebug
    (lazy
      ("translate_end_abstraction_synth_input:" ^ "\n- function: "
      ^ name_to_string ctx ctx.fun_decl.name
      ^ "\n- rg_id: "
      ^ T.RegionGroupId.to_string rg_id
      ^ "\n- loop_id: "
      ^ Print.option_to_string Pure.LoopId.to_string ctx.loop_id
      ^ "\n- eval_ctx:\n" ^ eval_ctx_to_string ectx ^ "\n- abs:\n"
      ^ abs_to_string ctx abs ^ "\n"));

  (* When we end an input abstraction, this input abstraction gets back
   * the borrows which it introduced in the context through the input
   * values: by listing those values, we get the values which are given
   * back by one of the backward functions we are synthesizing. *)
  (* Note that we don't support nested borrows for now: if we find
   * an ended synthesized input abstraction, it must be the one corresponding
   * to the backward function wer are synthesizing, it can't be the one
   * for a parent backward function.
   *)
  let bid = Option.get ctx.bid in
  assert (rg_id = bid);

  (* The translation is done as follows:
   * - for a given backward function, we choose a set of variables [v_i]
   * - when we detect the ended input abstraction which corresponds
   *   to the backward function, and which consumed the values [consumed_i],
   *   we introduce:
   *   {[
       *   let v_i = consumed_i in
       *   ...
         *   ]}
   *   Then, when we reach the [Return] node, we introduce:
   *   {[
       *   (v_i)
       *   ]}
   * *)
  (* First, get the given back variables.

     We don't use the same given back variables if we translate a loop or
     the standard body of a function.
  *)
  let given_back_variables =
    let map =
      if ctx.inside_loop then
        (* We are synthesizing a loop body *)
        Option.get ctx.loop_backward_outputs
      else (* Regular function body *)
        ctx.backward_outputs
    in
    T.RegionGroupId.Map.find bid map
  in

  (* Get the list of values consumed by the abstraction upon ending *)
  let consumed_values = abs_to_consumed ctx ectx abs in

  log#ldebug
    (lazy
      ("translate_end_abstraction_synth_input:"
     ^ "\n\n- given back variables types:\n"
      ^ Print.list_to_string
          (fun (v : var) -> pure_ty_to_string ctx v.ty)
          given_back_variables
      ^ "\n\n- consumed values:\n"
      ^ Print.list_to_string
          (fun e ->
            texpression_to_string ctx e ^ " : " ^ pure_ty_to_string ctx e.ty)
          consumed_values
      ^ "\n"));

  (* Group the two lists *)
  let variables_values = List.combine given_back_variables consumed_values in
  (* Sanity check: the two lists match (same types) *)
  (* TODO: normalize the types *)
  if !Config.type_check_pure_code then
    List.iter
      (fun (var, v) -> assert ((var : var).ty = (v : texpression).ty))
      variables_values;
  (* Translate the next expression *)
  let next_e = translate_expression e ctx in
  (* Generate the assignemnts *)
  let monadic = false in
  List.fold_right
    (fun (var, value) (e : texpression) ->
      mk_let monadic (mk_typed_pattern_from_var var None) value e)
    variables_values next_e

and translate_end_abstraction_fun_call (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) (call_id : V.FunCallId.id)
    (rg_id : T.RegionGroupId.id) : texpression =
  let call_info = V.FunCallId.Map.find call_id ctx.calls in
  let call = call_info.forward in
  let fun_id =
    match call.call_id with
    | S.Fun (fun_id, _) -> fun_id
    | Unop _ | Binop _ ->
        (* Those don't have backward functions *)
        raise (Failure "Unreachable")
  in
  let effect_info =
    get_fun_effect_info ctx.fun_context.fun_infos fun_id None (Some rg_id)
  in
  let generics = ctx_translate_fwd_generic_args ctx call.generics in
  (* Retrieve the original call and the parent abstractions *)
  let _forward, backwards = get_abs_ancestors ctx abs call_id in
  (* Retrieve the values consumed when we called the forward function and
   * ended the parent backward functions: those give us part of the input
   * values (rem: for now, as we disallow nested lifetimes, there can't be
   * parent backward functions).
   * Note that the forward inputs **include the fuel and the input state**
   * (if we use those). *)
  let fwd_inputs = call_info.forward_inputs in
  let back_ancestors_inputs =
    List.concat (List.map (fun (_abs, args) -> args) backwards)
  in
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: those give us the remaining input values *)
  let back_inputs = abs_to_consumed ctx ectx abs in
  (* If the function is stateful:
   * - add the state input argument
   * - generate a fresh state variable for the returned state
   *)
  let back_state, ctx, nstate =
    if effect_info.stateful then
      let back_state = mk_state_texpression ctx.state_var in
      let ctx, nstate = bs_ctx_fresh_state_var ctx in
      ([ back_state ], ctx, Some nstate)
    else ([], ctx, None)
  in
  (* Concatenate all the inpus *)
  let inputs =
    List.concat [ fwd_inputs; back_ancestors_inputs; back_inputs; back_state ]
  in
  (* Retrieve the values given back by this function: those are the output
   * values. We rely on the fact that there are no nested borrows to use the
   * meta-place information from the input values given to the forward function
   * (we need to add [None] for the return avalue) *)
  let output_mpl =
    List.append (List.map translate_opt_mplace call.args_places) [ None ]
  in
  let ctx, outputs = abs_to_given_back (Some output_mpl) abs ctx in
  (* Group the output values together: first the updated inputs *)
  let output = mk_simpl_tuple_pattern outputs in
  (* Add the returned state if the function is stateful *)
  let output =
    match nstate with
    | None -> output
    | Some nstate -> mk_simpl_tuple_pattern [ nstate; output ]
  in
  (* Sanity check: there is the proper number of inputs and outputs, and they have the proper type *)
  (if (* TODO: normalize the types *) !Config.type_check_pure_code then
     match fun_id with
     | FunId fun_id ->
         let inst_sg =
           get_instantiated_fun_sig fun_id (Some rg_id) generics ctx
         in
         log#ldebug
           (lazy
             ("\n- fun_id: " ^ A.show_fun_id fun_id ^ "\n- inputs ("
             ^ string_of_int (List.length inputs)
             ^ "): "
             ^ String.concat ", " (List.map (texpression_to_string ctx) inputs)
             ^ "\n- inst_sg.inputs ("
             ^ string_of_int (List.length inst_sg.inputs)
             ^ "): "
             ^ String.concat ", "
                 (List.map (pure_ty_to_string ctx) inst_sg.inputs)));
         List.iter
           (fun (x, ty) -> assert ((x : texpression).ty = ty))
           (List.combine inputs inst_sg.inputs);
         log#ldebug
           (lazy
             ("\n- outputs: "
             ^ string_of_int (List.length outputs)
             ^ "\n- expected outputs: "
             ^ string_of_int (List.length inst_sg.doutputs)));
         List.iter
           (fun (x, ty) -> assert ((x : typed_pattern).ty = ty))
           (List.combine outputs inst_sg.doutputs)
     | _ -> (* TODO: trait methods *) ());
  (* Retrieve the function id, and register the function call in the context
   * if necessary *)
  let ctx, func =
    bs_ctx_register_backward_call abs call_id rg_id back_inputs ctx
  in
  (* Translate the next expression *)
  let next_e = translate_expression e ctx in
  (* Put everything together *)
  let args_mplaces = List.map (fun _ -> None) inputs in
  let args =
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
      (List.combine inputs args_mplaces)
  in
  let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
  let ret_ty =
    if effect_info.can_fail then mk_result_ty output.ty else output.ty
  in
  let func_ty = mk_arrows input_tys ret_ty in
  let func = { id = FunOrOp func; generics } in
  let func = { e = Qualif func; ty = func_ty } in
  let call = mk_apps func args in
  (* **Optimization**:
   * =================
   * We do a small optimization here: if the backward function doesn't
   * have any output, we don't introduce any function call.
   * See the comment in {!Config.filter_useless_monadic_calls}.
   *
   * TODO: use an option to disallow backward functions from updating the state.
   * TODO: a backward function which only gives back shared borrows shouldn't
   * update the state (state updates should only be used for mutable borrows,
   * with objects like Rc for instance).
   *)
  if !Config.filter_useless_monadic_calls && outputs = [] && nstate = None then (
    (* No outputs - we do a small sanity check: the backward function
     * should have exactly the same number of inputs as the forward:
     * this number can be different only if the forward function returned
     * a value containing mutable borrows, which can't be the case... *)
    assert (List.length inputs = List.length fwd_inputs);
    next_e)
  else mk_let effect_info.can_fail output call next_e

and translate_end_abstraction_identity (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) : texpression =
  (* We simply check that the abstraction only contains shared borrows/loans,
     and translate the next expression *)

  (* We can do this simply by checking that it consumes and gives back nothing *)
  let inputs = abs_to_consumed ctx ectx abs in
  let ctx, outputs = abs_to_given_back None abs ctx in
  assert (inputs = []);
  assert (outputs = []);

  (* Translate the next expression *)
  translate_expression e ctx

and translate_end_abstraction_synth_ret (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) (rg_id : T.RegionGroupId.id) : texpression
    =
  (* If we end the abstraction which consumed the return value of the function
     we are synthesizing, we get back the borrows which were inside. Those borrows
     are actually input arguments of the backward function we are synthesizing.
     So we simply need to introduce proper let bindings.

     For instance:
     {[
       fn id<'a>(x : &'a mut u32) -> &'a mut u32 {
         x
       }
     ]}

     Upon ending the return abstraction for 'a, we get back the borrow for [x].
     This new value is the second argument of the backward function:
     {[
       let id_back x nx = nx
     ]}

     In practice, upon ending this abstraction we introduce a useless
     let-binding:
     {[
       let id_back x nx =
         let s = nx in // the name [s] is not important (only collision matters)
                                                        ...
     ]}

     This let-binding later gets inlined, during a micro-pass.
  *)
  (* First, retrieve the list of variables used for the inputs for the
   * backward function *)
  let inputs = T.RegionGroupId.Map.find rg_id ctx.backward_inputs in
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: as there are no nested borrows, there should be none. *)
  let consumed = abs_to_consumed ctx ectx abs in
  assert (consumed = []);
  (* Retrieve the values given back upon ending this abstraction - note that
   * we don't provide meta-place information, because those assignments will
   * be inlined anyway... *)
  log#ldebug (lazy ("abs: " ^ abs_to_string ctx abs));
  let ctx, given_back = abs_to_given_back_no_mp abs ctx in
  (* Link the inputs to those given back values - note that this also
   * checks we have the same number of values, of course *)
  let given_back_inputs = List.combine given_back inputs in
  (* Sanity check *)
  List.iter
    (fun ((given_back, input) : typed_pattern * var) ->
      log#ldebug
        (lazy
          ("\n- given_back ty: "
          ^ pure_ty_to_string ctx given_back.ty
          ^ "\n- sig input ty: "
          ^ pure_ty_to_string ctx input.ty));
      assert (given_back.ty = input.ty))
    given_back_inputs;
  (* Translate the next expression *)
  let next_e = translate_expression e ctx in
  (* Generate the assignments *)
  let monadic = false in
  List.fold_right
    (fun (given_back, input_var) e ->
      mk_let monadic given_back (mk_texpression_from_var input_var) e)
    given_back_inputs next_e

and translate_end_abstraction_loop (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) (loop_id : V.LoopId.id)
    (rg_id : T.RegionGroupId.id option) (abs_kind : V.loop_abs_kind) :
    texpression =
  let vloop_id = loop_id in
  let loop_id = V.LoopId.Map.find loop_id ctx.loop_ids_map in
  assert (loop_id = Option.get ctx.loop_id);
  let rg_id = Option.get rg_id in
  (* There are two cases depending on the [abs_kind] (whether this is a
     synth input or a regular loop call) *)
  match abs_kind with
  | V.LoopSynthInput ->
      (* Actually the same case as [SynthInput] *)
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.LoopCall ->
      let fun_id = E.FRegular ctx.fun_decl.def_id in
      let effect_info =
        get_fun_effect_info ctx.fun_context.fun_infos (FunId fun_id)
          (Some vloop_id) (Some rg_id)
      in
      let loop_info = LoopId.Map.find loop_id ctx.loops in
      let generics = loop_info.generics in
      let fwd_inputs = Option.get loop_info.forward_inputs in
      (* Retrieve the additional backward inputs. Note that those are actually
         the backward inputs of the function we are synthesizing (and that we
         need to *transmit* to the loop backward function): they are not the
         values consumed upon ending the abstraction (i.e., we don't use
         [abs_to_consumed]) *)
      let back_inputs_vars =
        T.RegionGroupId.Map.find rg_id ctx.backward_inputs
      in
      let back_inputs = List.map mk_texpression_from_var back_inputs_vars in
      (* If the function is stateful:
       * - add the state input argument
       * - generate a fresh state variable for the returned state
       *)
      let back_state, ctx, nstate =
        if effect_info.stateful then
          let back_state = mk_state_texpression ctx.state_var in
          let ctx, nstate = bs_ctx_fresh_state_var ctx in
          ([ back_state ], ctx, Some nstate)
        else ([], ctx, None)
      in
      (* Concatenate all the inputs *)
      let inputs = List.concat [ fwd_inputs; back_inputs; back_state ] in
      (* Retrieve the values given back by this function *)
      let ctx, outputs = abs_to_given_back None abs ctx in
      (* Group the output values together: first the updated inputs *)
      let output = mk_simpl_tuple_pattern outputs in
      (* Add the returned state if the function is stateful *)
      let output =
        match nstate with
        | None -> output
        | Some nstate -> mk_simpl_tuple_pattern [ nstate; output ]
      in
      (* Translate the next expression *)
      let next_e = translate_expression e ctx in
      (* Put everything together *)
      let args_mplaces = List.map (fun _ -> None) inputs in
      let args =
        List.map
          (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
          (List.combine inputs args_mplaces)
      in
      let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
      let ret_ty =
        if effect_info.can_fail then mk_result_ty output.ty else output.ty
      in
      let func_ty = mk_arrows input_tys ret_ty in
      let func = Fun (FromLlbc (FunId fun_id, Some loop_id, Some rg_id)) in
      let func = { id = FunOrOp func; generics } in
      let func = { e = Qualif func; ty = func_ty } in
      let call = mk_apps func args in
      (* **Optimization**:
       * =================
       * We do a small optimization here: if the backward function doesn't
       * have any output, we don't introduce any function call.
       * See the comment in {!Config.filter_useless_monadic_calls}.
       *
       * TODO: use an option to disallow backward functions from updating the state.
       * TODO: a backward function which only gives back shared borrows shouldn't
       * update the state (state updates should only be used for mutable borrows,
       * with objects like Rc for instance).
       *)
      if !Config.filter_useless_monadic_calls && outputs = [] && nstate = None
      then (
        (* No outputs - we do a small sanity check: the backward function
         * should have exactly the same number of inputs as the forward:
         * this number can be different only if the forward function returned
         * a value containing mutable borrows, which can't be the case... *)
        assert (List.length inputs = List.length fwd_inputs);
        next_e)
      else
        (* Add meta-information - this is slightly hacky: we look at the
           values consumed by the abstraction (note that those come from
           *before* we applied the fixed-point context) and use them to
           guide the naming of the output vars.

           Also, we need to convert the backward outputs from patterns to
           variables.

           Finally, in practice, this works well only for loop bodies:
           we do this only in this case.
           TODO: improve the heuristics, to give weight to the hints for
           instance.
        *)
        let next_e =
          if ctx.inside_loop then
            let consumed_values = abs_to_consumed ctx ectx abs in
            let var_values = List.combine outputs consumed_values in
            let var_values =
              List.filter_map
                (fun (var, v) ->
                  match var.Pure.value with
                  | PatVar (var, _) -> Some (var, v)
                  | _ -> None)
                var_values
            in
            let vars, values = List.split var_values in
            mk_emeta_symbolic_assignments vars values next_e
          else next_e
        in

        (* Create the let-binding *)
        mk_let effect_info.can_fail output call next_e

and translate_global_eval (gid : A.GlobalDeclId.id) (sval : V.symbolic_value)
    (e : S.expression) (ctx : bs_ctx) : texpression =
  let ctx, var = fresh_var_for_symbolic_value sval ctx in
  let decl = A.GlobalDeclId.Map.find gid ctx.global_context.llbc_global_decls in
  let global_expr = { id = Global gid; generics = empty_generic_args } in
  (* We use translate_fwd_ty to translate the global type *)
  let ty = ctx_translate_fwd_ty ctx decl.ty in
  let gval = { e = Qualif global_expr; ty } in
  let e = translate_expression e ctx in
  mk_let false (mk_typed_pattern_from_var var None) gval e

and translate_assertion (ectx : C.eval_ctx) (v : V.typed_value)
    (e : S.expression) (ctx : bs_ctx) : texpression =
  let next_e = translate_expression e ctx in
  let monadic = true in
  let v = typed_value_to_texpression ctx ectx v in
  let args = [ v ] in
  let func =
    { id = FunOrOp (Fun (Pure Assert)); generics = empty_generic_args }
  in
  let func_ty = mk_arrow (TLiteral TBool) mk_unit_ty in
  let func = { e = Qualif func; ty = func_ty } in
  let assertion = mk_apps func args in
  mk_let monadic (mk_dummy_pattern mk_unit_ty) assertion next_e

and translate_expansion (p : S.mplace option) (sv : V.symbolic_value)
    (exp : S.expansion) (ctx : bs_ctx) : texpression =
  (* Translate the scrutinee *)
  let scrutinee_var = lookup_var_for_symbolic_value sv ctx in
  let scrutinee = mk_texpression_from_var scrutinee_var in
  let scrutinee_mplace = translate_opt_mplace p in
  (* Translate the branches *)
  match exp with
  | ExpandNoBranch (sexp, e) -> (
      match sexp with
      | V.SeLiteral _ ->
          (* We do not *register* symbolic expansions to literal
             values in the symbolic ADT *)
          raise (Failure "Unreachable")
      | SeMutRef (_, nsv) | SeSharedRef (_, nsv) ->
          (* The (mut/shared) borrow type is extracted to identity: we thus simply
             introduce an reassignment *)
          let ctx, var = fresh_var_for_symbolic_value nsv ctx in
          let next_e = translate_expression e ctx in
          let monadic = false in
          mk_let monadic
            (mk_typed_pattern_from_var var None)
            (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
            next_e
      | SeAdt _ ->
          (* Should be in the [ExpandAdt] case *)
          raise (Failure "Unreachable"))
  | ExpandAdt branches -> (
      (* We don't do the same thing if there is a branching or not *)
      match branches with
      | [] -> raise (Failure "Unreachable")
      | [ (variant_id, svl, branch) ]
        when not
               (TypesUtils.ty_is_custom_adt sv.V.sv_ty
               && !Config.always_deconstruct_adts_with_matches) ->
          (* There is exactly one branch: no branching.

             We can decompose the ADT value with a let-binding, unless
             the backend doesn't support this (see {!Config.always_deconstruct_adts_with_matches}):
             we *ignore* this branch (and go to the next one) if the ADT is a custom
             adt, and [always_deconstruct_adts_with_matches] is true.
          *)
          translate_ExpandAdt_one_branch sv scrutinee scrutinee_mplace
            variant_id svl branch ctx
      | branches ->
          let translate_branch (variant_id : T.VariantId.id option)
              (svl : V.symbolic_value list) (branch : S.expression) :
              match_branch =
            let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
            let vars =
              List.map (fun x -> mk_typed_pattern_from_var x None) vars
            in
            let pat_ty = scrutinee.ty in
            let pat = mk_adt_pattern pat_ty variant_id vars in
            let branch = translate_expression branch ctx in
            { pat; branch }
          in
          let branches =
            List.map (fun (vid, svl, e) -> translate_branch vid svl e) branches
          in
          let e =
            Switch
              ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
                Match branches )
          in
          (* There should be at least one branch *)
          let branch = List.hd branches in
          let ty = branch.branch.ty in
          (* Sanity check *)
          assert (List.for_all (fun br -> br.branch.ty = ty) branches);
          (* Return *)
          { e; ty })
  | ExpandBool (true_e, false_e) ->
      (* We don't need to update the context: we don't introduce any
         new values/variables *)
      let true_e = translate_expression true_e ctx in
      let false_e = translate_expression false_e ctx in
      let e =
        Switch
          ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
            If (true_e, false_e) )
      in
      let ty = true_e.ty in
      assert (ty = false_e.ty);
      { e; ty }
  | ExpandInt (int_ty, branches, otherwise) ->
      let translate_branch ((v, branch_e) : V.scalar_value * S.expression) :
          match_branch =
        (* We don't need to update the context: we don't introduce any
           new values/variables *)
        let branch = translate_expression branch_e ctx in
        let pat = mk_typed_pattern_from_literal (VScalar v) in
        { pat; branch }
      in
      let branches = List.map translate_branch branches in
      let otherwise = translate_expression otherwise ctx in
      let pat_ty = TLiteral (TInteger int_ty) in
      let otherwise_pat : typed_pattern = { value = PatDummy; ty = pat_ty } in
      let otherwise : match_branch =
        { pat = otherwise_pat; branch = otherwise }
      in
      let all_branches = List.append branches [ otherwise ] in
      let e =
        Switch
          ( mk_opt_mplace_texpression scrutinee_mplace scrutinee,
            Match all_branches )
      in
      let ty = otherwise.branch.ty in
      assert (
        List.for_all (fun (br : match_branch) -> br.branch.ty = ty) branches);
      { e; ty }

(* Translate and [ExpandAdt] when there is no branching (i.e., one branch).

   There are several possibilities:
   - if the ADT is an enumeration, we attempt to deconstruct it with a let-binding:
   {[
     let Cons x0 ... xn = y in
     ...
   ]}

   - if the ADT is a structure, we attempt to introduce one let-binding per field:
   {[
     let x0 = y.f0 in
     ...
       let xn = y.fn in
       ...
   ]}

   Of course, this is not always possible depending on the backend.
   Also, recursive structures, and more specifically structures mutually recursive
   with inductives, are usually not supported. We define such recursive structures
   as inductives, in which case it is not always possible to use a notation
   for the field projections.
*)
and translate_ExpandAdt_one_branch (sv : V.symbolic_value)
    (scrutinee : texpression) (scrutinee_mplace : mplace option)
    (variant_id : variant_id option) (svl : V.symbolic_value list)
    (branch : S.expression) (ctx : bs_ctx) : texpression =
  (* TODO: always introduce a match, and use micro-passes to turn the
     the match into a let? *)
  let type_id, _ = TypesUtils.ty_as_adt sv.V.sv_ty in
  let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
  let branch = translate_expression branch ctx in
  match type_id with
  | TAdtId adt_id ->
      (* Detect if this is an enumeration or not *)
      let tdef = bs_ctx_lookup_llbc_type_decl adt_id ctx in
      let is_enum = TypesUtils.type_decl_is_enum tdef in
      (* We deconstruct the ADT with a single let-binding in two situations:
         - if the ADT is an enumeration (which must have exactly one branch)
         - if we forbid using field projectors.
      *)
      let is_rec_def =
        T.TypeDeclId.Set.mem adt_id ctx.type_context.recursive_decls
      in
      let use_let_with_cons =
        is_enum
        || !Config.dont_use_field_projectors
        (* TODO: for now, we don't have field projectors over recursive ADTs in Lean. *)
        || (!Config.backend = Lean && is_rec_def)
        (* Also, there is a special case when the ADT is to be extracted as
           a tuple, because it is a structure with unnamed fields. Some backends
           like Lean have projectors for tuples (like so: `x.3`), but others
           like Coq don't, in which case we have to deconstruct the whole ADT
           at once (`let (a, b, c) = x in`) *)
        || TypesUtils.type_decl_from_type_id_is_tuple_struct
             ctx.type_context.type_infos type_id
           && not (Config.backend_has_tuple_projectors ())
      in
      if use_let_with_cons then
        (* Introduce a let binding which expands the ADT *)
        let lvars = List.map (fun v -> mk_typed_pattern_from_var v None) vars in
        let lv = mk_adt_pattern scrutinee.ty variant_id lvars in
        let monadic = false in

        mk_let monadic lv
          (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
          branch
      else
        (* This is not an enumeration: introduce let-bindings for every
         * field.
         * We use the [dest] variable in order not to have to recompute
         * the type of the result of the projection... *)
        let adt_id, generics = ty_as_adt scrutinee.ty in
        let gen_field_proj (field_id : FieldId.id) (dest : var) : texpression =
          let proj_kind = { adt_id; field_id } in
          let qualif = { id = Proj proj_kind; generics } in
          let proj_e = Qualif qualif in
          let proj_ty = mk_arrow scrutinee.ty dest.ty in
          let proj = { e = proj_e; ty = proj_ty } in
          mk_app proj scrutinee
        in
        let id_var_pairs = FieldId.mapi (fun fid v -> (fid, v)) vars in
        let monadic = false in
        List.fold_right
          (fun (fid, var) e ->
            let field_proj = gen_field_proj fid var in
            mk_let monadic (mk_typed_pattern_from_var var None) field_proj e)
          id_var_pairs branch
  | TTuple ->
      let vars = List.map (fun x -> mk_typed_pattern_from_var x None) vars in
      let monadic = false in
      mk_let monadic
        (mk_simpl_tuple_pattern vars)
        (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
        branch
  | TAssumed TBox ->
      (* There should be exactly one variable *)
      let var =
        match vars with [ v ] -> v | _ -> raise (Failure "Unreachable")
      in
      (* We simply introduce an assignment - the box type is the
       * identity when extracted ([box a = a]) *)
      let monadic = false in
      mk_let monadic
        (mk_typed_pattern_from_var var None)
        (mk_opt_mplace_texpression scrutinee_mplace scrutinee)
        branch
  | TAssumed (TArray | TSlice | TStr) ->
      (* We can't expand those values: we can access the fields only
       * through the functions provided by the API (note that we don't
       * know how to expand values like vectors or arrays, because they have a variable number
       * of fields!) *)
      raise (Failure "Attempt to expand a non-expandable value")

and translate_intro_symbolic (ectx : C.eval_ctx) (p : S.mplace option)
    (sv : V.symbolic_value) (v : S.value_aggregate) (e : S.expression)
    (ctx : bs_ctx) : texpression =
  log#ldebug
    (lazy
      ("translate_intro_symbolic:" ^ "\n- value aggregate: "
     ^ S.show_value_aggregate v));
  let mplace = translate_opt_mplace p in

  (* Introduce a fresh variable for the symbolic value. *)
  let ctx, var = fresh_var_for_symbolic_value sv ctx in

  (* Translate the next expression *)
  let next_e = translate_expression e ctx in

  (* Translate the value: there are several cases, depending on whether this
     is a "regular" let-binding, an array aggregate, a const generic or
     a trait associated constant.
  *)
  let v =
    match v with
    | VaSingleValue v -> typed_value_to_texpression ctx ectx v
    | VaArray values ->
        (* We use a struct update to encode the array aggregate, in order
           to preserve the structure and allow generating code of the shape
           `[x0, ...., xn]` *)
        let values = List.map (typed_value_to_texpression ctx ectx) values in
        let values = FieldId.mapi (fun fid v -> (fid, v)) values in
        let su : struct_update =
          { struct_id = TAssumed TArray; init = None; updates = values }
        in
        { e = StructUpdate su; ty = var.ty }
    | VaCgValue cg_id -> { e = CVar cg_id; ty = var.ty }
    | VaTraitConstValue (trait_ref, generics, const_name) ->
        let type_infos = ctx.type_context.type_infos in
        let trait_ref = translate_fwd_trait_ref type_infos trait_ref in
        let generics = translate_fwd_generic_args type_infos generics in
        let qualif_id = TraitConst (trait_ref, generics, const_name) in
        let qualif = { id = qualif_id; generics = empty_generic_args } in
        { e = Qualif qualif; ty = var.ty }
  in

  (* Make the let-binding *)
  let monadic = false in
  let var = mk_typed_pattern_from_var var mplace in
  mk_let monadic var v next_e

and translate_forward_end (ectx : C.eval_ctx)
    (loop_input_values : V.typed_value S.symbolic_value_id_map option)
    (e : S.expression) (back_e : S.expression S.region_group_id_map)
    (ctx : bs_ctx) : texpression =
  (* Update the current state with the additional state received by the backward
     function, if needs be, and lookup the proper expression *)
  let translate_end ctx =
    (* Update the current state with the additional state received by the backward
       function, if needs be, and lookup the proper expression *)
    let ctx, e =
      match ctx.bid with
      | None -> (ctx, e)
      | Some bid ->
          let ctx = { ctx with state_var = ctx.back_state_var } in
          let e = T.RegionGroupId.Map.find bid back_e in
          (ctx, e)
    in
    translate_expression e ctx
  in

  (* If we are (re-)entering a loop, we need to introduce a call to the
     forward translation of the loop. *)
  match loop_input_values with
  | None ->
      (* "Regular" case: we reached a return *)
      translate_end ctx
  | Some loop_input_values ->
      (* Loop *)
      let loop_id = Option.get ctx.loop_id in

      (* Lookup the loop information *)
      let loop_info = LoopId.Map.find loop_id ctx.loops in

      log#ldebug
        (lazy
          ("translate_forward_end:\n- loop_input_values:\n"
          ^ V.SymbolicValueId.Map.show
              (typed_value_to_string ctx)
              loop_input_values
          ^ "\n- loop_info.input_svl:\n"
          ^ Print.list_to_string
              (symbolic_value_to_string ctx)
              loop_info.input_svl
          ^ "\n"));

      (* Translate the input values *)
      let loop_input_values =
        List.map
          (fun sv ->
            log#ldebug
              (lazy
                ("translate_forward_end: looking up input_svl: "
                ^ V.SymbolicValueId.to_string sv.V.sv_id
                ^ "\n"));
            V.SymbolicValueId.Map.find sv.V.sv_id loop_input_values)
          loop_info.input_svl
      in
      let args =
        List.map (typed_value_to_texpression ctx ectx) loop_input_values
      in
      let org_args = args in

      (* Lookup the effect info for the loop function *)
      let fid = E.FRegular ctx.fun_decl.def_id in
      let effect_info =
        get_fun_effect_info ctx.fun_context.fun_infos (FunId fid) None ctx.bid
      in

      (* Introduce a fresh output value for the forward function *)
      let ctx, output_var =
        let output_ty = mk_simpl_tuple_ty ctx.fwd_sg.doutputs in
        fresh_var None output_ty ctx
      in
      let args, ctx, out_pats =
        let output_pat = mk_typed_pattern_from_var output_var None in

        (* Depending on the function effects:
         * - add the fuel
         * - add the state input argument
         * - generate a fresh state variable for the returned state
         *)
        let fuel = mk_fuel_input_as_list ctx effect_info in
        if effect_info.stateful then
          let state_var = mk_state_texpression ctx.state_var in
          let ctx, nstate_pat = bs_ctx_fresh_state_var ctx in
          ( List.concat [ fuel; args; [ state_var ] ],
            ctx,
            [ nstate_pat; output_pat ] )
        else (List.concat [ fuel; args ], ctx, [ output_pat ])
      in

      (* Update the loop information in the context *)
      let loop_info =
        {
          loop_info with
          forward_inputs = Some args;
          forward_output_no_state_no_result = Some output_var;
        }
      in
      let ctx =
        { ctx with loops = LoopId.Map.add loop_id loop_info ctx.loops }
      in

      (* Translate the end of the function *)
      let next_e = translate_end ctx in

      (* Introduce the call to the loop forward function in the generated AST *)
      let out_pat = mk_simpl_tuple_pattern out_pats in

      let loop_call =
        let fun_id = Fun (FromLlbc (FunId fid, Some loop_id, None)) in
        let func = { id = FunOrOp fun_id; generics = loop_info.generics } in
        let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
        let ret_ty =
          if effect_info.can_fail then mk_result_ty out_pat.ty else out_pat.ty
        in
        let func_ty = mk_arrows input_tys ret_ty in
        let func = { e = Qualif func; ty = func_ty } in
        let call = mk_apps func args in
        call
      in

      (* Create the let expression with the loop call *)
      let e = mk_let effect_info.can_fail out_pat loop_call next_e in

      (* Add meta-information linking the loop input parameters and the
         loop input values - we use this to derive proper names.

         There is something important here: as we group the end of the function
         and the loop body in a {!Loop} node, when exploring the function
         and applying micro passes, we introduce the variables specific to
         the loop body before exploring both the loop body and the end of
         the function. It means it is ok to reference some variables which might
         actually be defined, in the end, in a different branch.

         We then remove all the meta information from the body *before* calling
         {!PureMicroPasses.decompose_loops}.
      *)
      mk_emeta_symbolic_assignments loop_info.input_vars org_args e

and translate_loop (loop : S.loop) (ctx : bs_ctx) : texpression =
  let loop_id = V.LoopId.Map.find loop.loop_id ctx.loop_ids_map in

  (* Translate the loop inputs - some inputs are symbolic values already
     in the context, some inputs are introduced by the loop fixed point:
     we need to introduce fresh variables for those. *)
  (* First introduce fresh variables for the new inputs *)
  let ctx =
    (* We have to filter the list of symbolic values, to remove the not fresh ones *)
    let svl =
      List.filter
        (fun (sv : V.symbolic_value) ->
          V.SymbolicValueId.Set.mem sv.sv_id loop.fresh_svalues)
        loop.input_svalues
    in
    log#ldebug
      (lazy
        ("translate_loop:" ^ "\n- input_svalues: "
        ^ (Print.list_to_string (symbolic_value_to_string ctx))
            loop.input_svalues
        ^ "\n- filtered svl: "
        ^ (Print.list_to_string (symbolic_value_to_string ctx)) svl
        ^ "\n- rg_to_abs\n:"
        ^ T.RegionGroupId.Map.show
            (fun (rids, tys) ->
              "(" ^ T.RegionId.Set.show rids ^ ", "
              ^ Print.list_to_string (ty_to_string ctx) tys
              ^ ")")
            loop.rg_to_given_back_tys
        ^ "\n"));
    let ctx, _ = fresh_vars_for_symbolic_values svl ctx in
    ctx
  in

  (* Sanity check: all the non-fresh symbolic values are in the context *)
  assert (
    List.for_all
      (fun (sv : V.symbolic_value) ->
        V.SymbolicValueId.Map.mem sv.sv_id ctx.sv_to_var)
      loop.input_svalues);

  (* Translate the loop inputs *)
  let inputs =
    List.map
      (fun sv -> V.SymbolicValueId.Map.find sv.V.sv_id ctx.sv_to_var)
      loop.input_svalues
  in
  let inputs_lvs =
    List.map (fun var -> mk_typed_pattern_from_var var None) inputs
  in

  (* Compute the backward outputs *)
  let ctx = ref ctx in
  let loop_backward_outputs =
    T.RegionGroupId.Map.map
      (fun (_, tys) ->
        (* The types shouldn't contain borrows - we can translate them as forward types *)
        let vars =
          List.map
            (fun ty ->
              assert (
                not (TypesUtils.ty_has_borrows !ctx.type_context.type_infos ty));
              (None, ctx_translate_fwd_ty !ctx ty))
            tys
        in
        (* Introduce fresh variables *)
        let ctx', vars = fresh_vars vars !ctx in
        ctx := ctx';
        vars)
      loop.rg_to_given_back_tys
  in
  let ctx = !ctx in

  let back_output_tys =
    match ctx.bid with
    | None -> None
    | Some rg_id ->
        let back_outputs =
          T.RegionGroupId.Map.find rg_id loop_backward_outputs
        in
        let back_output_tys = List.map (fun (v : var) -> v.ty) back_outputs in
        Some back_output_tys
  in

  (* Add the loop information in the context *)
  let ctx =
    assert (not (LoopId.Map.mem loop_id ctx.loops));

    (* Note that we will retrieve the input values later in the [ForwardEnd]
       (and will introduce the outputs at that moment, together with the actual
       call to the loop forward function) *)
    let generics =
      let { types; const_generics; trait_clauses } = ctx.sg.generics in
      let types = List.map (fun (ty : T.type_var) -> TVar ty.T.index) types in
      let const_generics =
        List.map
          (fun (cg : T.const_generic_var) -> T.CgVar cg.T.index)
          const_generics
      in
      let trait_refs =
        List.map
          (fun (c : trait_clause) ->
            let trait_decl_ref =
              { trait_decl_id = c.trait_id; decl_generics = empty_generic_args }
            in
            {
              trait_id = Clause c.clause_id;
              generics = empty_generic_args;
              trait_decl_ref;
            })
          trait_clauses
      in
      { types; const_generics; trait_refs }
    in

    let loop_info =
      {
        loop_id;
        input_vars = inputs;
        input_svl = loop.input_svalues;
        generics;
        forward_inputs = None;
        forward_output_no_state_no_result = None;
      }
    in
    let loops = LoopId.Map.add loop_id loop_info ctx.loops in
    { ctx with loops }
  in

  (* Update the context to translate the function end *)
  let ctx_end =
    {
      ctx with
      loop_id = Some loop_id;
      loop_backward_outputs = Some loop_backward_outputs;
    }
  in
  let fun_end = translate_expression loop.end_expr ctx_end in

  (* Update the context for the loop body *)
  let ctx_loop = { ctx_end with inside_loop = true } in

  (* Add the input state *)
  let input_state =
    if ctx.sg.info.effect_info.stateful then Some ctx.state_var else None
  in

  (* Translate the loop body *)
  let loop_body = translate_expression loop.loop_expr ctx_loop in

  (* Create the loop node and return *)
  let loop =
    Loop
      {
        fun_end;
        loop_id;
        meta = loop.meta;
        fuel0 = ctx.fuel0;
        fuel = ctx.fuel;
        input_state;
        inputs;
        inputs_lvs;
        back_output_tys;
        loop_body;
      }
  in
  (* If we translate forward functions: the return type of a loop body is the
     same as the parent function *)
  assert (Option.is_some ctx.bid || fun_end.ty = loop_body.ty);
  let ty = fun_end.ty in
  { e = loop; ty }

and translate_emeta (meta : S.emeta) (e : S.expression) (ctx : bs_ctx) :
    texpression =
  let next_e = translate_expression e ctx in
  let meta =
    match meta with
    | S.Assignment (ectx, lp, rv, rp) ->
        let lp = translate_mplace lp in
        let rv = typed_value_to_texpression ctx ectx rv in
        let rp = translate_opt_mplace rp in
        Assignment (lp, rv, rp)
  in
  let e = Meta (meta, next_e) in
  let ty = next_e.ty in
  { e; ty }

(** Wrap a function body in a match over the fuel to control termination. *)
let wrap_in_match_fuel (fuel0 : VarId.id) (fuel : VarId.id) (body : texpression)
    : texpression =
  let fuel0_var : var = mk_fuel_var fuel0 in
  let fuel0 = mk_texpression_from_var fuel0_var in
  let nfuel_var : var = mk_fuel_var fuel in
  let nfuel_pat = mk_typed_pattern_from_var nfuel_var None in
  let fail_branch =
    mk_result_fail_texpression_with_error_id error_out_of_fuel_id body.ty
  in
  match !Config.backend with
  | FStar ->
      (* Generate an expression:
         {[
           if fuel0 = 0 then Fail OutOfFuel
           else
             let fuel = decrease fuel0 in
             ...
         }]
      *)
      (* Create the expression: [fuel0 = 0] *)
      let check_fuel =
        let func =
          {
            id = FunOrOp (Fun (Pure FuelEqZero));
            generics = empty_generic_args;
          }
        in
        let func_ty = mk_arrow mk_fuel_ty mk_bool_ty in
        let func = { e = Qualif func; ty = func_ty } in
        mk_app func fuel0
      in
      (* Create the expression: [decrease fuel0] *)
      let decrease_fuel =
        let func =
          {
            id = FunOrOp (Fun (Pure FuelDecrease));
            generics = empty_generic_args;
          }
        in
        let func_ty = mk_arrow mk_fuel_ty mk_fuel_ty in
        let func = { e = Qualif func; ty = func_ty } in
        mk_app func fuel0
      in

      (* Create the success branch *)
      let monadic = false in
      let success_branch = mk_let monadic nfuel_pat decrease_fuel body in

      (* Put everything together *)
      let match_e = Switch (check_fuel, If (fail_branch, success_branch)) in
      let match_ty = body.ty in
      { e = match_e; ty = match_ty }
  | Coq ->
      (* Generate an expression:
         {[
           match fuel0 with
           | O -> Fail OutOfFuel
           | S fuel ->
             ...
         }]
      *)
      (* Create the fail branch *)
      let fail_pat = mk_adt_pattern mk_fuel_ty (Some fuel_zero_id) [] in
      let fail_branch = { pat = fail_pat; branch = fail_branch } in
      (* Create the success branch *)
      let success_pat =
        mk_adt_pattern mk_fuel_ty (Some fuel_succ_id) [ nfuel_pat ]
      in
      let success_branch = body in
      let success_branch = { pat = success_pat; branch = success_branch } in
      (* Put everything together *)
      let match_ty = body.ty in
      let match_e = Switch (fuel0, Match [ fail_branch; success_branch ]) in
      { e = match_e; ty = match_ty }
  | Lean | HOL4 ->
      (* We should have checked the command line arguments before *)
      raise (Failure "Unexpected")

let translate_fun_decl (ctx : bs_ctx) (body : S.expression option) : fun_decl =
  (* Translate *)
  let def = ctx.fun_decl in
  let bid = ctx.bid in
  log#ldebug
    (lazy
      ("SymbolicToPure.translate_fun_decl: "
      ^ name_to_string ctx def.name
      ^ " ("
      ^ Print.option_to_string T.RegionGroupId.to_string bid
      ^ ")\n"));

  (* Translate the declaration *)
  let def_id = def.def_id in
  let llbc_name = def.name in
  let name = name_to_string ctx llbc_name in
  (* Retrieve the signature *)
  let signature = ctx.sg in
  let regions_hierarchy =
    FunIdMap.find (FRegular def_id) ctx.fun_context.regions_hierarchies
  in
  (* Translate the body, if there is *)
  let body =
    match body with
    | None -> None
    | Some body ->
        let effect_info =
          get_fun_effect_info ctx.fun_context.fun_infos
            (FunId (FRegular def_id)) None bid
        in
        let body = translate_expression body ctx in
        (* Add a match over the fuel, if necessary *)
        let body =
          if function_decreases_fuel effect_info then
            wrap_in_match_fuel ctx.fuel0 ctx.fuel body
          else body
        in
        (* Sanity check *)
        type_check_texpression ctx body;
        (* Introduce the fuel parameter, if necessary *)
        let fuel =
          if function_uses_fuel effect_info then
            let fuel_var =
              if function_decreases_fuel effect_info then ctx.fuel0
              else ctx.fuel
            in
            [ mk_fuel_var fuel_var ]
          else []
        in
        (* Introduce the forward input state (the state at call site of the
         * *forward* function), if necessary. *)
        let fwd_state =
          (* We check if the *whole group* is stateful. See {!effect_info} *)
          if effect_info.stateful_group then [ mk_state_var ctx.state_var ]
          else []
        in
        (* Compute the list of (properly ordered) backward input variables *)
        let backward_inputs : var list =
          match bid with
          | None -> []
          | Some back_id ->
              let parents_ids =
                list_ordered_ancestor_region_groups regions_hierarchy back_id
              in
              let backward_ids = List.append parents_ids [ back_id ] in
              List.concat
                (List.map
                   (fun id -> T.RegionGroupId.Map.find id ctx.backward_inputs)
                   backward_ids)
        in
        (* Introduce the backward input state (the state at call site of the
         * *backward* function), if necessary *)
        let back_state =
          if effect_info.stateful && Option.is_some bid then
            [ mk_state_var ctx.back_state_var ]
          else []
        in
        (* Group the inputs together *)
        let inputs =
          List.concat
            [ fuel; ctx.forward_inputs; fwd_state; backward_inputs; back_state ]
        in
        let inputs_lvs =
          List.map (fun v -> mk_typed_pattern_from_var v None) inputs
        in
        (* Sanity check *)
        log#ldebug
          (lazy
            ("SymbolicToPure.translate_fun_decl: "
            ^ name_to_string ctx def.name
            ^ " ("
            ^ Print.option_to_string T.RegionGroupId.to_string bid
            ^ ")" ^ "\n- forward_inputs: "
            ^ String.concat ", " (List.map show_var ctx.forward_inputs)
            ^ "\n- fwd_state: "
            ^ String.concat ", " (List.map show_var fwd_state)
            ^ "\n- backward_inputs: "
            ^ String.concat ", " (List.map show_var backward_inputs)
            ^ "\n- back_state: "
            ^ String.concat ", " (List.map show_var back_state)
            ^ "\n- signature.inputs: "
            ^ String.concat ", "
                (List.map (pure_ty_to_string ctx) signature.inputs)));
        (* TODO: we need to normalize the types *)
        if !Config.type_check_pure_code then
          assert (
            List.for_all
              (fun (var, ty) -> (var : var).ty = ty)
              (List.combine inputs signature.inputs));
        Some { inputs; inputs_lvs; body }
  in

  (* Note that for now, the loops are still *inside* the function body (and we
     haven't counted them): we will extract them from there later, in {!PureMicroPasses}
     (by "splitting" the definition).
  *)
  let num_loops = 0 in
  let loop_id = None in

  (* Assemble the declaration *)
  let def : fun_decl =
    {
      def_id;
      is_local = def.is_local;
      meta = def.meta;
      kind = def.kind;
      num_loops;
      loop_id;
      back_id = bid;
      llbc_name;
      name;
      signature;
      is_global_decl_body = def.is_global_decl_body;
      body;
    }
  in
  (* Debugging *)
  log#ldebug
    (lazy
      ("SymbolicToPure.translate_fun_decl: translated:\n"
     ^ fun_decl_to_string ctx def));
  (* return *)
  def

let translate_type_decls (ctx : Contexts.decls_ctx) : type_decl list =
  List.map (translate_type_decl ctx)
    (TypeDeclId.Map.values ctx.type_ctx.type_decls)

(** Translates function signatures.

    Takes as input a list of function information containing:
    - the function id
    - a list of optional names for the inputs
    - the function signature
    
    Returns a map from forward/backward functions identifiers to:
    - translated function signatures
    - optional names for the outputs values (we derive them for the backward
      functions)
 *)
let translate_fun_signatures (decls_ctx : C.decls_ctx)
    (functions : (A.fun_id * string option list * A.fun_sig) list) :
    fun_sig_named_outputs RegularFunIdNotLoopMap.t =
  (* For every function, translate the signatures of:
     - the forward function
     - the backward functions
  *)
  let translate_one (fun_id : A.fun_id) (input_names : string option list)
      (sg : A.fun_sig) : (regular_fun_id_not_loop * fun_sig_named_outputs) list
      =
    log#ldebug
      (lazy
        ("Translating signature of function: "
        ^ Print.Expressions.fun_id_to_string
            (Print.Contexts.decls_ctx_to_fmt_env decls_ctx)
            fun_id));
    (* Retrieve the regions hierarchy *)
    let regions_hierarchy =
      FunIdMap.find fun_id decls_ctx.fun_ctx.regions_hierarchies
    in
    (* The forward function *)
    let fwd_sg = translate_fun_sig decls_ctx fun_id sg input_names None in
    let fwd_id = (fun_id, None) in
    (* The backward functions *)
    let back_sgs =
      List.map
        (fun (rg : T.region_var_group) ->
          let tsg =
            translate_fun_sig decls_ctx fun_id sg input_names (Some rg.id)
          in
          let id = (fun_id, Some rg.id) in
          (id, tsg))
        regions_hierarchy
    in
    (* Return *)
    (fwd_id, fwd_sg) :: back_sgs
  in
  let translated =
    List.concat
      (List.map (fun (id, names, sg) -> translate_one id names sg) functions)
  in
  List.fold_left
    (fun m (id, sg) -> RegularFunIdNotLoopMap.add id sg m)
    RegularFunIdNotLoopMap.empty translated

let translate_trait_decl (ctx : Contexts.decls_ctx) (trait_decl : A.trait_decl)
    : trait_decl =
  let {
    def_id;
    is_local;
    name = llbc_name;
    meta;
    generics = llbc_generics;
    preds;
    parent_clauses = llbc_parent_clauses;
    consts;
    types;
    required_methods;
    provided_methods;
  } : A.trait_decl =
    trait_decl
  in
  let type_infos = ctx.type_ctx.type_infos in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      llbc_name
  in
  let generics = translate_generic_params llbc_generics in
  let preds = translate_predicates preds in
  let parent_clauses = List.map translate_trait_clause llbc_parent_clauses in
  let consts =
    List.map
      (fun (name, (ty, id)) -> (name, (translate_fwd_ty type_infos ty, id)))
      consts
  in
  let types =
    List.map
      (fun (name, (trait_clauses, ty)) ->
        ( name,
          ( List.map translate_trait_clause trait_clauses,
            Option.map (translate_fwd_ty type_infos) ty ) ))
      types
  in
  {
    def_id;
    is_local;
    llbc_name;
    name;
    meta;
    generics;
    llbc_generics;
    preds;
    parent_clauses;
    llbc_parent_clauses;
    consts;
    types;
    required_methods;
    provided_methods;
  }

let translate_trait_impl (ctx : Contexts.decls_ctx) (trait_impl : A.trait_impl)
    : trait_impl =
  let {
    A.def_id;
    is_local;
    name = llbc_name;
    meta;
    impl_trait = llbc_impl_trait;
    generics = llbc_generics;
    preds;
    parent_trait_refs;
    consts;
    types;
    required_methods;
    provided_methods;
  } =
    trait_impl
  in
  let type_infos = ctx.type_ctx.type_infos in
  let impl_trait =
    translate_trait_decl_ref (translate_fwd_ty type_infos) llbc_impl_trait
  in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      llbc_name
  in
  let generics = translate_generic_params llbc_generics in
  let preds = translate_predicates preds in
  let parent_trait_refs = List.map translate_strait_ref parent_trait_refs in
  let consts =
    List.map
      (fun (name, (ty, id)) -> (name, (translate_fwd_ty type_infos ty, id)))
      consts
  in
  let types =
    List.map
      (fun (name, (trait_refs, ty)) ->
        ( name,
          ( List.map (translate_fwd_trait_ref type_infos) trait_refs,
            translate_fwd_ty type_infos ty ) ))
      types
  in
  {
    def_id;
    is_local;
    llbc_name;
    name;
    meta;
    impl_trait;
    llbc_impl_trait;
    generics;
    llbc_generics;
    preds;
    parent_trait_refs;
    consts;
    types;
    required_methods;
    provided_methods;
  }
