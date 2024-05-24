open Utils
open LlbcAstUtils
open Pure
open PureUtils
open InterpreterUtils
open FunsAnalysis
open TypesAnalysis
open Errors
module T = Types
module V = Values
module C = Contexts
module A = LlbcAst
module S = SymbolicAst
module PP = PrintPure

(** The local logger *)
let log = Logging.symbolic_to_pure_log

type type_ctx = {
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

type fun_ctx = {
  llbc_fun_decls : A.fun_decl A.FunDeclId.Map.t;
  fun_infos : fun_info A.FunDeclId.Map.t;
  regions_hierarchies : T.region_var_groups FunIdMap.t;
}
[@@deriving show]

type global_ctx = { llbc_global_decls : A.global_decl A.GlobalDeclId.Map.t }
[@@deriving show]

type trait_decls_ctx = A.trait_decl A.TraitDeclId.Map.t [@@deriving show]
type trait_impls_ctx = A.trait_impl A.TraitImplId.Map.t [@@deriving show]

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
  back_funs : texpression option RegionGroupId.Map.t option;
      (** If we do not split between the forward/backward functions: the
          variables we introduced for the backward functions.

          Example:
          {[
            let x, back = Vec.index_mut n v in
                   ^^^^
                   here
            ...
          ]}

          The expression might be [None] in case the backward function
          has to be filtered (because it does nothing - the backward
          functions for shared borrows for instance).
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
  forward_output_no_state_no_result : texpression option;
      (** The forward outputs are initialized at [None] *)
  back_outputs : ty list RegionGroupId.Map.t;
      (** The map from region group ids to the types of the values given back
          by the corresponding loop abstractions.
          This map is partial.
       *)
  back_funs : texpression option RegionGroupId.Map.t option;
      (** Same as {!call_info.back_funs}.
          Initialized with [None], gets updated to [Some] only if we merge
          the fwd/back functions.
       *)
  fwd_effect_info : fun_effect_info;
  back_effect_infos : fun_effect_info RegionGroupId.Map.t;
}
[@@deriving show]

(** Body synthesis context *)
type bs_ctx = {
  (* TODO: there are a lot of duplications with the various decls ctx *)
  meta : Meta.meta;  (** The meta information about the current declaration *)
  decls_ctx : C.decls_ctx;
  type_ctx : type_ctx;
  fun_ctx : fun_ctx;
  global_ctx : global_ctx;
  trait_decls_ctx : trait_decls_ctx;
  trait_impls_ctx : trait_impls_ctx;
  fun_dsigs : decomposed_fun_sig FunDeclId.Map.t;
  fun_decl : A.fun_decl;
  bid : RegionGroupId.id option;
      (** TODO: rename

        The id of the group region we are currently translating.
        If we split the forward/backward functions, we set this id at the
        very beginning of the translation.
        If we don't split, we set it to `None`, then update it when we enter
        an expression which is specific to a backward function.
     *)
  sg : decomposed_fun_sig;
      (** Information about the function signature - useful in particular to
          translate [Panic] *)
  sv_to_var : var V.SymbolicValueId.Map.t;
      (** Whenever we encounter a new symbolic value (introduced because of
          a symbolic expansion or upon ending an abstraction, for instance)
          we introduce a new variable (with a let-binding).
       *)
  var_counter : VarId.generator ref;
      (** Using a ref to make sure all the variables identifiers are unique.
          TODO: this is not very clean, and the code was initially written without
          a reference (and it's shape hasn't changed). We should use DeBruijn indices.
       *)
  state_var : VarId.id;
      (** The current state variable, in case the function is stateful *)
  back_state_vars : VarId.id RegionGroupId.Map.t;
      (** The additional input state variable received by a stateful backward
          function, **in case we are splitting the forward/backward functions**.

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
          forward function and the call to the backward function. We also need
          to make sure we use the same variable in all the branches (because
          this variable is quantified at the definition level).
       *)
  fuel0 : VarId.id;
      (** The original fuel taken as input by the function (if we use fuel) *)
  fuel : VarId.id;
      (** The fuel to use for the recursive calls (if we use fuel) *)
  forward_inputs : var list;
      (** The input parameters for the forward function corresponding to the
          translated Rust inputs (no fuel, no state).
       *)
  backward_inputs_no_state : var list RegionGroupId.Map.t;
      (** The additional input parameters for the backward functions coming
          from the borrows consumed upon ending the lifetime (as a consequence
          those don't include the backward state, if there is one).

          If we split the forward/backward functions: we initialize this map
          when initializing the bs_ctx, because those variables are quantified
          at the definition level. Otherwise, we initialize it upon diving
          into the expressions which are specific to the backward functions.
       *)
  backward_inputs_with_state : var list RegionGroupId.Map.t;
      (** All the additional input parameters for the backward functions.

          Same remarks as for {!backward_inputs_no_state}.
       *)
  backward_outputs : var list option;
      (** The variables that the backward functions will output, corresponding
          to the borrows they give back (don't include the backward state).

          The translation is done as follows:
          - when we detect the ended input abstraction which corresponds
            to the backward function of the LLBC function we are translating,
            and which consumed the values [consumed_i] (that we need to give
            back to the caller), we introduce:
            {[
                let v_i = consumed_i in
                ...
            ]}
            where the [v_i] are fresh, and are stored in the [backward_output].
          - Then, upon reaching the [Return] node, we introduce:
            {[
                return (v_i)
            ]}

          The option is [None] before we detect the ended input abstraction,
          and [Some] afterwards.
       *)
  calls : call_info V.FunCallId.Map.t;
      (** The function calls we encountered so far *)
  abstractions : (V.abs * texpression list) V.AbstractionId.Map.t;
      (** The ended abstractions we encountered so far, with their additional
          input arguments. We store it here and not in {!call_info} because
          we need a map from abstraction id to abstraction (and not
          from call id + region group id to abstraction). *)
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
  mk_return : (bs_ctx -> texpression option -> texpression) option;
      (** Small helper: translate a [return] expression, given a value to "return".
          The translation of [return] depends on the context, and in particular depends on
          whether we are inside a subexpression like a loop or not.

          Note that the function consumes an optional expression, which is:
          - [Some] for a forward computation
          - [None] for a backward computation

          We initialize this at [None].
      *)
  mk_panic : texpression option;
      (** Small helper: translate a [fail] expression.

           We initialize this at [None].
       *)
}
[@@deriving show]

(* TODO: move *)
let bs_ctx_to_fmt_env (ctx : bs_ctx) : Print.fmt_env =
  let type_decls = ctx.type_ctx.llbc_type_decls in
  let fun_decls = ctx.fun_ctx.llbc_fun_decls in
  let global_decls = ctx.global_ctx.llbc_global_decls in
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
  let type_decls = ctx.type_ctx.llbc_type_decls in
  let fun_decls = ctx.fun_ctx.llbc_fun_decls in
  let global_decls = ctx.global_ctx.llbc_global_decls in
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
  Print.Values.typed_value_to_string ~meta:(Some ctx.meta) env v

let pure_ty_to_string (ctx : bs_ctx) (ty : ty) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.ty_to_string env false ty

let pure_var_to_string (ctx : bs_ctx) (v : var) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.var_to_string env v

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
  PrintPure.texpression_to_string ~metadata:(Some ctx.meta) env false "" "  " e

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
  PrintPure.typed_pattern_to_string ~meta:(Some ctx.meta) env p

let ctx_get_effect_info_for_bid (ctx : bs_ctx) (bid : RegionGroupId.id option) :
    fun_effect_info =
  match bid with
  | None -> ctx.sg.fwd_info.effect_info
  | Some bid ->
      let back_sg = RegionGroupId.Map.find bid ctx.sg.back_sg in
      back_sg.effect_info

let ctx_get_effect_info (ctx : bs_ctx) : fun_effect_info =
  ctx_get_effect_info_for_bid ctx ctx.bid

(* TODO: move *)
let abs_to_string (ctx : bs_ctx) (abs : V.abs) : string =
  let env = bs_ctx_to_fmt_env ctx in
  let verbose = false in
  let indent = "" in
  let indent_incr = "  " in
  Print.Values.abs_to_string ~meta:(Some ctx.meta) env verbose indent
    indent_incr abs

let bs_ctx_lookup_llbc_type_decl (id : TypeDeclId.id) (ctx : bs_ctx) :
    T.type_decl =
  TypeDeclId.Map.find id ctx.type_ctx.llbc_type_decls

let bs_ctx_lookup_llbc_fun_decl (id : A.FunDeclId.id) (ctx : bs_ctx) :
    A.fun_decl =
  A.FunDeclId.Map.find id ctx.fun_ctx.llbc_fun_decls

(* Some generic translation functions (we need to translate different "flavours"
   of types: forward types, backward types, etc.) *)
let rec translate_generic_args (meta : Meta.meta) (translate_ty : T.ty -> ty)
    (generics : T.generic_args) : generic_args =
  (* We ignore the regions: if they didn't cause trouble for the symbolic execution,
     then everything's fine *)
  let types = List.map translate_ty generics.types in
  let const_generics = generics.const_generics in
  let trait_refs =
    List.map (translate_trait_ref meta translate_ty) generics.trait_refs
  in
  { types; const_generics; trait_refs }

and translate_trait_ref (meta : Meta.meta) (translate_ty : T.ty -> ty)
    (tr : T.trait_ref) : trait_ref =
  let trait_id = translate_trait_instance_id meta translate_ty tr.trait_id in
  let generics = translate_generic_args meta translate_ty tr.generics in
  let trait_decl_ref =
    translate_trait_decl_ref meta translate_ty tr.trait_decl_ref
  in
  { trait_id; generics; trait_decl_ref }

and translate_trait_decl_ref (meta : Meta.meta) (translate_ty : T.ty -> ty)
    (tr : T.trait_decl_ref) : trait_decl_ref =
  let decl_generics =
    translate_generic_args meta translate_ty tr.decl_generics
  in
  { trait_decl_id = tr.trait_decl_id; decl_generics }

and translate_trait_instance_id (meta : Meta.meta) (translate_ty : T.ty -> ty)
    (id : T.trait_instance_id) : trait_instance_id =
  let translate_trait_instance_id =
    translate_trait_instance_id meta translate_ty
  in
  match id with
  | T.Self -> Self
  | TraitImpl id -> TraitImpl id
  | BuiltinOrAuto _ ->
      (* We should have eliminated those in the prepasses *)
      craise __FILE__ __LINE__ meta "Unreachable"
  | Clause id -> Clause id
  | ParentClause (inst_id, decl_id, clause_id) ->
      let inst_id = translate_trait_instance_id inst_id in
      ParentClause (inst_id, decl_id, clause_id)
  | ItemClause (inst_id, decl_id, item_name, clause_id) ->
      let inst_id = translate_trait_instance_id inst_id in
      ItemClause (inst_id, decl_id, item_name, clause_id)
  | TraitRef tr -> TraitRef (translate_trait_ref meta translate_ty tr)
  | FnPointer _ | Closure _ ->
      craise __FILE__ __LINE__ meta "Closures are not supported yet"
  | Unsolved _ -> craise __FILE__ __LINE__ meta "Couldn't solve trait bound"
  | UnknownTrait s -> craise __FILE__ __LINE__ meta ("Unknown trait found: " ^ s)

(** Translate a signature type - TODO: factor out the different translation functions *)
let rec translate_sty (meta : Meta.meta) (ty : T.ty) : ty =
  let translate = translate_sty in
  match ty with
  | T.TAdt (type_id, generics) -> (
      let generics = translate_sgeneric_args meta generics in
      match type_id with
      | T.TAdtId adt_id -> TAdt (TAdtId adt_id, generics)
      | T.TTuple ->
          sanity_check __FILE__ __LINE__ (generics.const_generics = []) meta;
          mk_simpl_tuple_ty generics.types
      | T.TAssumed aty -> (
          match aty with
          | T.TBox -> (
              (* Eliminate the boxes *)
              match generics.types with
              | [ ty ] -> ty
              | _ ->
                  craise __FILE__ __LINE__ meta
                    "Box/vec/option type with incorrect number of arguments")
          | T.TArray -> TAdt (TAssumed TArray, generics)
          | T.TSlice -> TAdt (TAssumed TSlice, generics)
          | T.TStr -> TAdt (TAssumed TStr, generics)))
  | TVar vid -> TVar vid
  | TLiteral ty -> TLiteral ty
  | TNever -> craise __FILE__ __LINE__ meta "Unreachable"
  | TRef (_, rty, _) -> translate meta rty
  | TRawPtr (ty, rkind) ->
      let mut = match rkind with RMut -> Mut | RShared -> Const in
      let ty = translate meta ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TAssumed (TRawPtr mut), generics)
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = translate_strait_ref meta trait_ref in
      TTraitType (trait_ref, type_name)
  | TArrow _ ->
      craise __FILE__ __LINE__ meta "Arrow types are not supported yet"

and translate_sgeneric_args (meta : Meta.meta) (generics : T.generic_args) :
    generic_args =
  translate_generic_args meta (translate_sty meta) generics

and translate_strait_ref (meta : Meta.meta) (tr : T.trait_ref) : trait_ref =
  translate_trait_ref meta (translate_sty meta) tr

and translate_strait_instance_id (meta : Meta.meta) (id : T.trait_instance_id) :
    trait_instance_id =
  translate_trait_instance_id meta (translate_sty meta) id

let translate_trait_clause (meta : Meta.meta) (clause : T.trait_clause) :
    trait_clause =
  let { T.clause_id; meta = _; trait_id; clause_generics } = clause in
  let generics = translate_sgeneric_args meta clause_generics in
  { clause_id; trait_id; generics }

let translate_strait_type_constraint (meta : Meta.meta)
    (ttc : T.trait_type_constraint) : trait_type_constraint =
  let { T.trait_ref; type_name; ty } = ttc in
  let trait_ref = translate_strait_ref meta trait_ref in
  let ty = translate_sty meta ty in
  { trait_ref; type_name; ty }

let translate_predicates (meta : Meta.meta) (preds : T.predicates) : predicates
    =
  let trait_type_constraints =
    List.map
      (translate_strait_type_constraint meta)
      preds.trait_type_constraints
  in
  { trait_type_constraints }

let translate_generic_params (meta : Meta.meta) (generics : T.generic_params) :
    generic_params =
  let { T.regions = _; types; const_generics; trait_clauses } = generics in
  let trait_clauses = List.map (translate_trait_clause meta) trait_clauses in
  { types; const_generics; trait_clauses }

let translate_field (meta : Meta.meta) (f : T.field) : field =
  let field_name = f.field_name in
  let field_ty = translate_sty meta f.field_ty in
  { field_name; field_ty }

let translate_fields (meta : Meta.meta) (fl : T.field list) : field list =
  List.map (translate_field meta) fl

let translate_variant (meta : Meta.meta) (v : T.variant) : variant =
  let variant_name = v.variant_name in
  let fields = translate_fields meta v.fields in
  { variant_name; fields }

let translate_variants (meta : Meta.meta) (vl : T.variant list) : variant list =
  List.map (translate_variant meta) vl

(** Translate a type def kind from LLBC *)
let translate_type_decl_kind (meta : Meta.meta) (kind : T.type_decl_kind) :
    type_decl_kind =
  match kind with
  | T.Struct fields -> Struct (translate_fields meta fields)
  | T.Enum variants -> Enum (translate_variants meta variants)
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
  cassert __FILE__ __LINE__ (regions = []) def.item_meta.meta
    "ADTs containing borrows are not supported yet";
  let trait_clauses =
    List.map (translate_trait_clause def.item_meta.meta) trait_clauses
  in
  let generics = { types; const_generics; trait_clauses } in
  let kind = translate_type_decl_kind def.item_meta.meta def.T.kind in
  let preds = translate_predicates def.item_meta.meta def.preds in
  let is_local = def.is_local in
  let meta = def.item_meta.meta in
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

let translate_type_id (meta : Meta.meta) (id : T.type_id) : type_id =
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
            craise __FILE__ __LINE__ meta "Unexpected box type"
      in
      TAssumed aty
  | TTuple -> TTuple

(** Translate a type, seen as an input/output of a forward function
    (preserve all borrows, etc.).

    Remark: it doesn't matter whether the types has regions or erased regions
    (both cases happen, actually).

    TODO: factor out the various translation functions.
*)
let rec translate_fwd_ty (meta : Meta.meta) (type_infos : type_infos)
    (ty : T.ty) : ty =
  let translate = translate_fwd_ty meta type_infos in
  match ty with
  | T.TAdt (type_id, generics) -> (
      let t_generics = translate_fwd_generic_args meta type_infos generics in
      (* Eliminate boxes and simplify tuples *)
      match type_id with
      | TAdtId _ | TAssumed (TArray | TSlice | TStr) ->
          let type_id = translate_type_id meta type_id in
          TAdt (type_id, t_generics)
      | TTuple ->
          (* Note that if there is exactly one type, [mk_simpl_tuple_ty] is the
             identity *)
          mk_simpl_tuple_ty t_generics.types
      | TAssumed TBox -> (
          (* We eliminate boxes *)
          (* No general parametricity for now *)
          cassert __FILE__ __LINE__
            (not
               (List.exists
                  (TypesUtils.ty_has_borrows type_infos)
                  generics.types))
            meta "ADTs containing borrows are not supported yet";
          match t_generics.types with
          | [ bty ] -> bty
          | _ ->
              craise __FILE__ __LINE__ meta
                "Unreachable: box/vec/option receives exactly one type \
                 parameter"))
  | TVar vid -> TVar vid
  | TNever -> craise __FILE__ __LINE__ meta "Unreachable"
  | TLiteral lty -> TLiteral lty
  | TRef (_, rty, _) -> translate rty
  | TRawPtr (ty, rkind) ->
      let mut = match rkind with RMut -> Mut | RShared -> Const in
      let ty = translate ty in
      let generics = { types = [ ty ]; const_generics = []; trait_refs = [] } in
      TAdt (TAssumed (TRawPtr mut), generics)
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = translate_fwd_trait_ref meta type_infos trait_ref in
      TTraitType (trait_ref, type_name)
  | TArrow _ ->
      craise __FILE__ __LINE__ meta "Arrow types are not supported yet"

and translate_fwd_generic_args (meta : Meta.meta) (type_infos : type_infos)
    (generics : T.generic_args) : generic_args =
  translate_generic_args meta (translate_fwd_ty meta type_infos) generics

and translate_fwd_trait_ref (meta : Meta.meta) (type_infos : type_infos)
    (tr : T.trait_ref) : trait_ref =
  translate_trait_ref meta (translate_fwd_ty meta type_infos) tr

and translate_fwd_trait_instance_id (meta : Meta.meta) (type_infos : type_infos)
    (id : T.trait_instance_id) : trait_instance_id =
  translate_trait_instance_id meta (translate_fwd_ty meta type_infos) id

(** Simply calls [translate_fwd_ty] *)
let ctx_translate_fwd_ty (ctx : bs_ctx) (ty : T.ty) : ty =
  let type_infos = ctx.type_ctx.type_infos in
  translate_fwd_ty ctx.meta type_infos ty

(** Simply calls [translate_fwd_generic_args] *)
let ctx_translate_fwd_generic_args (ctx : bs_ctx) (generics : T.generic_args) :
    generic_args =
  let type_infos = ctx.type_ctx.type_infos in
  translate_fwd_generic_args ctx.meta type_infos generics

(** Translate a type, when some regions may have ended.
    
    We return an option, because the translated type may be empty.
    
    [inside_mut]: are we inside a mutable borrow?
 *)
let rec translate_back_ty (meta : Meta.meta) (type_infos : type_infos)
    (keep_region : T.region -> bool) (inside_mut : bool) (ty : T.ty) : ty option
    =
  let translate = translate_back_ty meta type_infos keep_region inside_mut in
  (* A small helper for "leave" types *)
  let wrap ty = if inside_mut then Some ty else None in
  match ty with
  | T.TAdt (type_id, generics) -> (
      match type_id with
      | TAdtId _ | TAssumed (TArray | TSlice | TStr) ->
          let type_id = translate_type_id meta type_id in
          if inside_mut then
            (* We do not want to filter anything, so we translate the generics
               as "forward" types *)
            let generics =
              translate_fwd_generic_args meta type_infos generics
            in
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
              let generics =
                translate_fwd_generic_args meta type_infos generics
              in
              Some (TAdt (type_id, generics))
            else None
      | TAssumed TBox -> (
          (* Don't accept ADTs (which are not tuples) with borrows for now *)
          cassert __FILE__ __LINE__
            (not (TypesUtils.ty_has_borrows type_infos ty))
            meta "ADTs containing borrows are not supported yet";
          (* Eliminate the box *)
          match generics.types with
          | [ bty ] -> translate bty
          | _ ->
              craise __FILE__ __LINE__ meta
                "Unreachable: boxes receive exactly one type parameter")
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
  | TNever -> craise __FILE__ __LINE__ meta "Unreachable"
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
            translate_back_ty meta type_infos keep_region inside_mut rty
          else None)
  | TRawPtr _ ->
      (* TODO: not sure what to do here *)
      None
  | TTraitType (trait_ref, type_name) ->
      assert (
        AssociatedTypes.trait_instance_id_is_local_clause trait_ref.trait_id);
      if inside_mut then
        (* Translate the trait ref as a "forward" trait ref -
           we do not want to filter any type *)
        let trait_ref = translate_fwd_trait_ref meta type_infos trait_ref in
        Some (TTraitType (trait_ref, type_name))
      else None
  | TArrow _ ->
      craise __FILE__ __LINE__ meta "Arrow types are not supported yet"

(** Simply calls [translate_back_ty] *)
let ctx_translate_back_ty (ctx : bs_ctx) (keep_region : 'r -> bool)
    (inside_mut : bool) (ty : T.ty) : ty option =
  let type_infos = ctx.type_ctx.type_infos in
  translate_back_ty ctx.meta type_infos keep_region inside_mut ty

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
    PureTypeCheck.type_decls = ctx.type_ctx.type_decls;
    global_decls = ctx.global_ctx.llbc_global_decls;
    env;
    const_generics;
  }

let type_check_pattern (ctx : bs_ctx) (v : typed_pattern) : unit =
  let meta = ctx.meta in
  let ctx = mk_type_check_ctx ctx in
  let _ = PureTypeCheck.check_typed_pattern meta ctx v in
  ()

let type_check_texpression (ctx : bs_ctx) (e : texpression) : unit =
  if !Config.type_check_pure_code then
    let meta = ctx.meta in
    let ctx = mk_type_check_ctx ctx in
    PureTypeCheck.check_texpression meta ctx e

let translate_fun_id_or_trait_method_ref (ctx : bs_ctx)
    (id : A.fun_id_or_trait_method_ref) : fun_id_or_trait_method_ref =
  match id with
  | FunId fun_id -> FunId fun_id
  | TraitMethod (trait_ref, method_name, fun_decl_id) ->
      let type_infos = ctx.type_ctx.type_infos in
      let trait_ref = translate_fwd_trait_ref ctx.meta type_infos trait_ref in
      TraitMethod (trait_ref, method_name, fun_decl_id)

let bs_ctx_register_forward_call (call_id : V.FunCallId.id) (forward : S.call)
    (args : texpression list)
    (back_funs : texpression option RegionGroupId.Map.t option) (ctx : bs_ctx) :
    bs_ctx =
  let calls = ctx.calls in
  sanity_check __FILE__ __LINE__
    (not (V.FunCallId.Map.mem call_id calls))
    ctx.meta;
  let info = { forward; forward_inputs = args; back_funs } in
  let calls = V.FunCallId.Map.add call_id info calls in
  { ctx with calls }

(** [inherit_args]: the list of inputs inherited from the forward function and
    the ancestors backward functions, if pertinent.
    [back_args]: the *additional* list of inputs received by the backward function,
    including the state.

    Returns the updated context and the expression corresponding to the function
    that we need to call. This function may be [None] if it has to be ignored
    (because it does nothing).
 *)
let bs_ctx_register_backward_call (abs : V.abs) (call_id : V.FunCallId.id)
    (back_id : T.RegionGroupId.id) (back_args : texpression list) (ctx : bs_ctx)
    : bs_ctx * texpression option =
  (* Insert the abstraction in the call informations *)
  let info = V.FunCallId.Map.find call_id ctx.calls in
  let calls = V.FunCallId.Map.add call_id info ctx.calls in
  (* Insert the abstraction in the abstractions map *)
  let abstractions = ctx.abstractions in
  sanity_check __FILE__ __LINE__
    (not (V.AbstractionId.Map.mem abs.abs_id abstractions))
    ctx.meta;
  let abstractions =
    V.AbstractionId.Map.add abs.abs_id (abs, back_args) abstractions
  in
  (* Compute the expression corresponding to the function.
     We simply lookup the variable introduced for the backward function. *)
  let func = RegionGroupId.Map.find back_id (Option.get info.back_funs) in
  (* Update the context and return *)
  ({ ctx with calls; abstractions }, func)

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
let compute_raw_fun_effect_info (meta : Meta.meta)
    (fun_infos : fun_info A.FunDeclId.Map.t)
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
      sanity_check __FILE__ __LINE__ (lid = None) meta;
      {
        can_fail = Assumed.assumed_fun_can_fail aid;
        stateful_group = false;
        stateful = false;
        can_diverge = false;
        is_rec = false;
      }

(** TODO: not very clean. *)
let get_fun_effect_info (ctx : bs_ctx) (fun_id : A.fun_id_or_trait_method_ref)
    (lid : V.LoopId.id option) (gid : T.RegionGroupId.id option) :
    fun_effect_info =
  match lid with
  | None -> (
      match fun_id with
      | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
          let dsg = A.FunDeclId.Map.find fid ctx.fun_dsigs in
          let info =
            match gid with
            | None -> dsg.fwd_info.effect_info
            | Some gid -> (RegionGroupId.Map.find gid dsg.back_sg).effect_info
          in
          { info with is_rec = info.is_rec || Option.is_some lid }
      | FunId (FAssumed _) ->
          compute_raw_fun_effect_info ctx.meta ctx.fun_ctx.fun_infos fun_id lid
            gid)
  | Some lid -> (
      (* This is necessarily for the current function *)
      match fun_id with
      | FunId (FRegular fid) -> (
          sanity_check __FILE__ __LINE__ (fid = ctx.fun_decl.def_id) ctx.meta;
          (* Lookup the loop *)
          let lid = V.LoopId.Map.find lid ctx.loop_ids_map in
          let loop_info = LoopId.Map.find lid ctx.loops in
          match gid with
          | None -> loop_info.fwd_effect_info
          | Some gid -> RegionGroupId.Map.find gid loop_info.back_effect_infos)
      | _ -> craise __FILE__ __LINE__ ctx.meta "Unreachable")

(** Translate a function signature to a decomposed function signature.

    Note that the function also takes a list of names for the inputs, and
    computes, for every output for the backward functions, a corresponding
    name (outputs for backward functions come from borrows in the inputs
    of the forward function) which we use as hints to generate pretty names
    in the extracted code.

    We use [bid] ("backward function id") only if we split the forward
    and the backward functions.
 *)
let translate_fun_sig_with_regions_hierarchy_to_decomposed (meta : Meta.meta)
    (decls_ctx : C.decls_ctx) (fun_id : A.fun_id_or_trait_method_ref)
    (regions_hierarchy : T.region_var_groups) (sg : A.fun_sig)
    (input_names : string option list) : decomposed_fun_sig =
  let fun_infos = decls_ctx.fun_ctx.fun_infos in
  let type_infos = decls_ctx.type_ctx.type_infos in
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
      InterpreterUtils.initialize_eval_ctx meta decls_ctx region_groups
        sg.generics.types sg.generics.const_generics
    in
    (* Compute the normalization map for the *sty* types and add it to the context *)
    AssociatedTypes.ctx_add_norm_trait_types_from_preds meta ctx
      sg.preds.trait_type_constraints
  in

  (* Normalize the signature *)
  let sg =
    let ({ A.inputs; output; _ } : A.fun_sig) = sg in
    let norm = AssociatedTypes.ctx_normalize_ty meta ctx in
    let inputs = List.map norm inputs in
    let output = norm output in
    { sg with A.inputs; output }
  in

  (* Is the forward function stateful, and can it fail? *)
  let fwd_effect_info =
    compute_raw_fun_effect_info meta fun_infos fun_id None None
  in
  (* Compute the forward inputs *)
  let fwd_fuel = mk_fuel_input_ty_as_list fwd_effect_info in
  let fwd_inputs_no_fuel_no_state =
    List.map (translate_fwd_ty meta type_infos) sg.inputs
  in
  (* State input for the forward function *)
  let fwd_state_ty =
    (* For the forward state, we check if the *whole group* is stateful.
       See {!effect_info}. *)
    if fwd_effect_info.stateful_group then [ mk_state_ty ] else []
  in
  let fwd_inputs =
    List.concat [ fwd_fuel; fwd_inputs_no_fuel_no_state; fwd_state_ty ]
  in
  (* Compute the backward output, without the effect information *)
  let fwd_output = translate_fwd_ty meta type_infos sg.output in

  (* Compute the type information for the backward function *)
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
      | RErased -> craise __FILE__ __LINE__ meta "Unexpected erased region"
      | RBVar _ -> craise __FILE__ __LINE__ meta "Unexpected bound region"
      | RFVar rid -> T.RegionId.Set.mem rid gr_regions
    in
    let inside_mut = false in
    translate_back_ty meta type_infos keep_region inside_mut ty
  in
  let translate_back_inputs_for_gid (gid : T.RegionGroupId.id) : ty list =
    (* For now we don't supported nested borrows, so we check that there
       aren't parent regions *)
    let parents = list_ancestor_region_groups regions_hierarchy gid in
    cassert __FILE__ __LINE__
      (T.RegionGroupId.Set.is_empty parents)
      meta "Nested borrows are not supported yet";
    (* For now, we don't allow nested borrows, so the additional inputs to the
       backward function can only come from borrows that were returned like
       in (for the backward function we introduce for 'a):
       {[
         fn f<'a>(...) -> &'a mut u32;
       ]}
       Upon ending the abstraction for 'a, we need to get back the borrow
       the function returned.
    *)
    let inputs =
      List.filter_map (translate_back_ty_for_gid gid) [ sg.output ]
    in
    log#ldebug
      (lazy
        (let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
         let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
         let output = Print.Types.ty_to_string ctx sg.output in
         let inputs =
           Print.list_to_string (PrintPure.ty_to_string pctx false) inputs
         in
         "translate_back_inputs_for_gid:" ^ "\n- gid: "
         ^ RegionGroupId.to_string gid
         ^ "\n- output: " ^ output ^ "\n- back inputs: " ^ inputs ^ "\n"));
    inputs
  in
  let compute_back_outputs_for_gid (gid : RegionGroupId.id) :
      string option list * ty list =
    (* The outputs are the borrows inside the regions of the abstractions
       and which are present in the input values. For instance, see:
       {[
         fn f<'a>(x : &'a mut u32) -> ...;
       ]}
       Upon ending the abstraction for 'a, we give back the borrow which
       was consumed through the [x] parameter.
    *)
    let outputs =
      List.map
        (fun (name, input_ty) -> (name, translate_back_ty_for_gid gid input_ty))
        (List.combine input_names sg.inputs)
    in
    (* Filter *)
    let outputs =
      List.filter (fun (_, opt_ty) -> Option.is_some opt_ty) outputs
    in
    let outputs =
      List.map (fun (name, opt_ty) -> (name, Option.get opt_ty)) outputs
    in
    let names, outputs = List.split outputs in
    log#ldebug
      (lazy
        (let ctx = Print.Contexts.decls_ctx_to_fmt_env decls_ctx in
         let pctx = PrintPure.decls_ctx_to_fmt_env decls_ctx in
         let inputs =
           Print.list_to_string (Print.Types.ty_to_string ctx) sg.inputs
         in
         let outputs =
           Print.list_to_string (PrintPure.ty_to_string pctx false) outputs
         in
         "compute_back_outputs_for_gid:" ^ "\n- gid: "
         ^ RegionGroupId.to_string gid
         ^ "\n- inputs: " ^ inputs ^ "\n- back outputs: " ^ outputs ^ "\n"));
    (names, outputs)
  in
  let compute_back_info_for_group (rg : T.region_var_group) :
      RegionGroupId.id * back_sg_info =
    let gid = rg.id in
    let back_effect_info =
      compute_raw_fun_effect_info meta fun_infos fun_id None (Some gid)
    in
    let inputs_no_state = translate_back_inputs_for_gid gid in
    let inputs_no_state =
      List.map (fun ty -> (Some "ret", ty)) inputs_no_state
    in
    (* We consider a backward function as stateful and potentially failing
       **only if it has inputs** (for the "potentially failing": if it has
       not inputs, we directly evaluate it in the body of the forward function).

       For instance, we do the following:
       {[
         // Rust
         fn push<T, 'a>(v : &mut Vec<T>, x : T) { ... }

         (* Generated code: before doing unit elimination.
            We return (), as well as the backward function; as the backward
            function doesn't consume any inputs, it is a value that we compute
            directly in the body of [push].
          *)
         let push T (v : Vec T) (x : T) : Result (() * Vec T) = ...

         (* Generated code: after doing unit elimination, if we simplify the merged
            fwd/back functions (see below). *)
         let push T (v : Vec T) (x : T) : Result (Vec T) = ...
       ]}
    *)
    let back_effect_info =
      let b = inputs_no_state <> [] in
      {
        back_effect_info with
        stateful = back_effect_info.stateful && b;
        can_fail = back_effect_info.can_fail && b;
      }
    in
    let state =
      if back_effect_info.stateful then [ (None, mk_state_ty) ] else []
    in
    let inputs = inputs_no_state @ state in
    let output_names, outputs = compute_back_outputs_for_gid gid in
    let filter =
      !Config.simplify_merged_fwd_backs && inputs = [] && outputs = []
    in
    let info =
      {
        inputs;
        inputs_no_state;
        outputs;
        output_names;
        effect_info = back_effect_info;
        filter;
      }
    in
    (gid, info)
  in
  let back_sg =
    RegionGroupId.Map.of_list
      (List.map compute_back_info_for_group regions_hierarchy)
  in

  (* The additional information about the forward function *)
  let fwd_info =
    (* *)
    let has_fuel = fwd_fuel <> [] in
    let num_inputs_no_fuel_no_state = List.length fwd_inputs_no_fuel_no_state in
    let num_inputs_with_fuel_no_state =
      (* We use the fact that [fuel] has length 1 if we use some fuel, 0 otherwise *)
      List.length fwd_fuel + num_inputs_no_fuel_no_state
    in
    let fwd_info : inputs_info =
      {
        has_fuel;
        num_inputs_no_fuel_no_state;
        num_inputs_with_fuel_no_state;
        num_inputs_with_fuel_with_state =
          (* We use the fact that [fwd_state_ty] has length 1 if there is a state,
             and 0 otherwise *)
          num_inputs_with_fuel_no_state + List.length fwd_state_ty;
      }
    in
    let ignore_output =
      if !Config.simplify_merged_fwd_backs then
        ty_is_unit fwd_output
        && List.exists
             (fun (info : back_sg_info) -> not info.filter)
             (RegionGroupId.Map.values back_sg)
      else false
    in
    let info = { fwd_info; effect_info = fwd_effect_info; ignore_output } in
    sanity_check __FILE__ __LINE__ (fun_sig_info_is_wf info) meta;
    info
  in

  (* Generic parameters *)
  let generics = translate_generic_params meta sg.generics in

  (* Return *)
  let preds = translate_predicates meta sg.preds in
  {
    generics;
    llbc_generics = sg.generics;
    preds;
    fwd_inputs;
    fwd_output;
    back_sg;
    fwd_info;
  }

let translate_fun_sig_to_decomposed (decls_ctx : C.decls_ctx)
    (fun_id : FunDeclId.id) (sg : A.fun_sig) (input_names : string option list)
    : decomposed_fun_sig =
  (* Retrieve the list of parent backward functions *)
  let regions_hierarchy =
    FunIdMap.find (FRegular fun_id) decls_ctx.fun_ctx.regions_hierarchies
  in
  let meta =
    (FunDeclId.Map.find fun_id decls_ctx.fun_ctx.fun_decls).item_meta.meta
  in
  translate_fun_sig_with_regions_hierarchy_to_decomposed meta decls_ctx
    (FunId (FRegular fun_id)) regions_hierarchy sg input_names

let translate_fun_sig_from_decl_to_decomposed (decls_ctx : C.decls_ctx)
    (fdef : LlbcAst.fun_decl) : decomposed_fun_sig =
  let input_names =
    match fdef.body with
    | None -> List.map (fun _ -> None) fdef.signature.inputs
    | Some body ->
        List.map
          (fun (v : LlbcAst.var) -> v.name)
          (LlbcAstUtils.fun_body_get_input_vars body)
  in
  let sg =
    translate_fun_sig_to_decomposed decls_ctx fdef.def_id fdef.signature
      input_names
  in
  log#ldebug
    (lazy
      ("translate_fun_sig_from_decl_to_decomposed:" ^ "\n- name: "
     ^ T.show_name fdef.name ^ "\n- sg:\n" ^ show_decomposed_fun_sig sg ^ "\n"));
  sg

let mk_output_ty_from_effect_info (effect_info : fun_effect_info) (ty : ty) : ty
    =
  let output =
    if effect_info.stateful then mk_simpl_tuple_ty [ mk_state_ty; ty ] else ty
  in
  if effect_info.can_fail then mk_result_ty output else output

let mk_back_output_ty_from_effect_info (effect_info : fun_effect_info)
    (inputs : ty list) (ty : ty) : ty =
  let output =
    if effect_info.stateful then mk_simpl_tuple_ty [ mk_state_ty; ty ] else ty
  in
  if effect_info.can_fail && inputs <> [] then mk_result_ty output else output

(** Compute the arrow types for all the backward functions.

    If a backward function has no inputs/outputs we filter it.

    We may also filter the region group ids (param [keep_rg_ids]).
    This is useful for the loops: not all the
    parent function region groups can be linked to a region abstraction
    introduced by the loop.
 *)
let compute_back_tys_with_info (dsg : Pure.decomposed_fun_sig)
    ?(keep_rg_ids : RegionGroupId.Set.t option = None)
    (subst : (generic_args * trait_instance_id) option) :
    (back_sg_info * ty) option list =
  let keep_rg_id =
    match keep_rg_ids with
    | None -> fun _ -> true
    | Some ids -> fun id -> RegionGroupId.Set.mem id ids
  in
  List.map
    (fun ((rg_id, back_sg) : RegionGroupId.id * back_sg_info) ->
      if keep_rg_id rg_id then
        let effect_info = back_sg.effect_info in
        (* Compute the input/output types *)
        let inputs = List.map snd back_sg.inputs in
        let outputs = back_sg.outputs in
        (* Filter if necessary *)
        if !Config.simplify_merged_fwd_backs && inputs = [] && outputs = [] then
          None
        else
          let output = mk_simpl_tuple_ty outputs in
          let output =
            mk_back_output_ty_from_effect_info effect_info inputs output
          in
          let ty = mk_arrows inputs output in
          (* Substitute - TODO: normalize *)
          let ty =
            match subst with
            | None -> ty
            | Some (generics, tr_self) ->
                let subst =
                  make_subst_from_generics dsg.generics generics tr_self
                in
                ty_substitute subst ty
          in
          Some (back_sg, ty)
      else (* We ignore this region group *)
        None)
    (RegionGroupId.Map.bindings dsg.back_sg)

let compute_back_tys (dsg : Pure.decomposed_fun_sig)
    ?(keep_rg_ids : RegionGroupId.Set.t option = None)
    (subst : (generic_args * trait_instance_id) option) : ty option list =
  List.map (Option.map snd) (compute_back_tys_with_info dsg ~keep_rg_ids subst)

(** Compute the output type of a function, from a decomposed signature
    (the output type contains the type of the value returned by the forward
    function as well as the types of the returned backward functions). *)
let compute_output_ty_from_decomposed (dsg : Pure.decomposed_fun_sig) : ty =
  (* Compute the arrow types for all the backward functions *)
  let back_tys = List.filter_map (fun x -> x) (compute_back_tys dsg None) in
  (* Group the forward output and the types of the backward functions *)
  let effect_info = dsg.fwd_info.effect_info in
  let output =
    (* We might need to ignore the output of the forward function
       (if it is unit for instance) *)
    let tys =
      if dsg.fwd_info.ignore_output then back_tys
      else dsg.fwd_output :: back_tys
    in
    mk_simpl_tuple_ty tys
  in
  mk_output_ty_from_effect_info effect_info output

let translate_fun_sig_from_decomposed (dsg : Pure.decomposed_fun_sig) : fun_sig
    =
  let generics = dsg.generics in
  let llbc_generics = dsg.llbc_generics in
  let preds = dsg.preds in
  (* Compute the effects info *)
  let fwd_info = dsg.fwd_info in
  let back_effect_info =
    RegionGroupId.Map.of_list
      (List.map
         (fun ((gid, info) : RegionGroupId.id * back_sg_info) ->
           (gid, info.effect_info))
         (RegionGroupId.Map.bindings dsg.back_sg))
  in
  let inputs, output =
    let output = compute_output_ty_from_decomposed dsg in
    let inputs = dsg.fwd_inputs in
    (inputs, output)
  in
  { generics; llbc_generics; preds; inputs; output; fwd_info; back_effect_info }

let bs_ctx_fresh_state_var (ctx : bs_ctx) : bs_ctx * var * typed_pattern =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh !(ctx.var_counter) in
  let state_var =
    { id; basename = Some ConstStrings.state_basename; ty = mk_state_ty }
  in
  let state_pat = mk_typed_pattern_from_var state_var None in
  (* Update the context *)
  ctx.var_counter := var_counter;
  let ctx = { ctx with state_var = id } in
  (* Return *)
  (ctx, state_var, state_pat)

(** WARNING: do not call this function directly.
    Call [fresh_named_var_for_symbolic_value] instead. *)
let fresh_var_llbc_ty (basename : string option) (ty : T.ty) (ctx : bs_ctx) :
    bs_ctx * var =
  (* Generate the fresh variable *)
  let id, var_counter = VarId.fresh !(ctx.var_counter) in
  let ty = ctx_translate_fwd_ty ctx ty in
  let var = { id; basename; ty } in
  (* Update the context *)
  ctx.var_counter := var_counter;
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
  let id, var_counter = VarId.fresh !(ctx.var_counter) in
  let var = { id; basename; ty } in
  (* Update the context *)
  ctx.var_counter := var_counter;
  (* Return *)
  (ctx, var)

let fresh_vars (vars : (string option * ty) list) (ctx : bs_ctx) :
    bs_ctx * var list =
  List.fold_left_map (fun ctx (name, ty) -> fresh_var name ty ctx) ctx vars

let fresh_opt_vars (vars : (string option * ty) option list) (ctx : bs_ctx) :
    bs_ctx * var option list =
  List.fold_left_map
    (fun ctx var ->
      match var with
      | None -> (ctx, None)
      | Some (name, ty) ->
          let ctx, var = fresh_var name ty ctx in
          (ctx, Some var))
    ctx vars

(* Introduce variables for the backward functions.

   We may filter the region group ids. This is useful for the loops: not all the
   parent function region groups can be linked to a region abstraction
   introduced by the loop.
*)
let fresh_back_vars_for_current_fun (ctx : bs_ctx)
    (keep_rg_ids : RegionGroupId.Set.t option) : bs_ctx * var option list =
  (* We lookup the LLBC definition in an attempt to derive pretty names
     for the backward functions. *)
  let back_var_names =
    let def_id = ctx.fun_decl.def_id in
    let sg = ctx.fun_decl.signature in
    let regions_hierarchy =
      LlbcAstUtils.FunIdMap.find (FRegular def_id)
        ctx.fun_ctx.regions_hierarchies
    in
    List.map
      (fun (gid, _) ->
        let rg = RegionGroupId.nth regions_hierarchy gid in
        let region_names =
          List.map
            (fun rid -> (T.RegionVarId.nth sg.generics.regions rid).name)
            rg.regions
        in
        let name =
          match region_names with
          | [] -> "back"
          | [ Some r ] -> "back" ^ r
          | _ ->
              (* Concatenate all the region names *)
              "back"
              ^ String.concat "" (List.filter_map (fun x -> x) region_names)
        in
        Some name)
      (RegionGroupId.Map.bindings ctx.sg.back_sg)
  in
  let back_vars =
    List.combine back_var_names (compute_back_tys ctx.sg ~keep_rg_ids None)
  in
  let back_vars =
    List.map
      (fun (name, ty) ->
        match ty with
        | None -> None
        | Some ty ->
            (* If the type is not an arrow type, don't use the name "back"
               (it is a backward function with no inputs, that is to say a
               value) *)
            let name = if is_arrow_ty ty then name else None in
            Some (name, ty))
      back_vars
  in
  (* If there is one backward function or less, we use the name "back"
     (there is no point in using the lifetime name, and it makes the
     code generation more stable) *)
  let num_back_vars = List.length (List.filter_map (fun x -> x) back_vars) in
  let back_vars =
    if num_back_vars = 1 then
      List.map
        (Option.map (fun (name, ty) -> (Option.map (fun _ -> "back") name, ty)))
        back_vars
    else back_vars
  in
  fresh_opt_vars back_vars ctx

(** IMPORTANT: do not use this one directly, but rather {!symbolic_value_to_texpression} *)
let lookup_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) : var =
  match V.SymbolicValueId.Map.find_opt sv.sv_id ctx.sv_to_var with
  | Some v -> v
  | None ->
      craise __FILE__ __LINE__ ctx.meta
        ("Could not find var for symbolic value: "
        ^ V.SymbolicValueId.to_string sv.sv_id)

(** Peel boxes as long as the value is of the form [Box<T>] *)
let rec unbox_typed_value (meta : Meta.meta) (v : V.typed_value) : V.typed_value
    =
  match (v.value, v.ty) with
  | V.VAdt av, T.TAdt (T.TAssumed T.TBox, _) -> (
      match av.field_values with
      | [ bv ] -> unbox_typed_value meta bv
      | _ -> craise __FILE__ __LINE__ meta "Unreachable")
  | _ -> v

(** Translate a symbolic value.

    Because we do not necessarily introduce variables for the symbolic values
    of (translated) type unit, it is important that we do not lookup variables
    in case the symbolic value has type unit.
 *)
let symbolic_value_to_texpression (ctx : bs_ctx) (sv : V.symbolic_value) :
    texpression =
  (* Translate the type *)
  let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
  (* If the type is unit, directly return unit *)
  if ty_is_unit ty then mk_unit_rvalue
  else
    (* Otherwise lookup the variable *)
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
  let v = unbox_typed_value ctx.meta v in
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
            sanity_check __FILE__ __LINE__ (variant_id = None) ctx.meta;
            mk_simpl_tuple_texpression ctx.meta field_values
        | _ ->
            (* Retrieve the type and the translated generics from the translated
               type (simpler this way) *)
            let adt_id, generics = ty_as_adt ctx.meta ty in
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
            mk_apps ctx.meta cons field_values)
    | VBottom -> craise __FILE__ __LINE__ ctx.meta "Unexpected bottom value"
    | VLoan lc -> (
        match lc with
        | VSharedLoan (_, v) -> translate v
        | VMutLoan _ -> craise __FILE__ __LINE__ ctx.meta "Unreachable")
    | VBorrow bc -> (
        match bc with
        | VSharedBorrow bid ->
            (* Lookup the shared value in the context, and continue *)
            let sv =
              InterpreterBorrowsCore.lookup_shared_value ctx.meta ectx bid
            in
            translate sv
        | VReservedMutBorrow bid ->
            (* Same as for shared borrows. However, note that we use reserved borrows
             * only in *meta-data*: a value *actually used* in the translation can't come
             * from an unpromoted reserved borrow *)
            let sv =
              InterpreterBorrowsCore.lookup_shared_value ctx.meta ectx bid
            in
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
            cassert __FILE__ __LINE__ (field_values = []) ctx.meta
              "ADTs containing borrows are not supported yet";
            None
        | TTuple ->
            (* Return *)
            if field_values = [] then None
            else
              (* Note that if there is exactly one field value,
               * [mk_simpl_tuple_rvalue] is the identity *)
              let rv = mk_simpl_tuple_texpression ctx.meta field_values in
              Some rv)
    | ABottom -> craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
  | AMutLoan (_, _) | ASharedLoan (_, _, _) ->
      craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
      craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
      craise __FILE__ __LINE__ _ctx.meta "Unreachable"
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
      Some (symbolic_value_to_texpression ctx msv)
  | V.AEndedProjLoans (_, [ (mnv, child_aproj) ]) ->
      sanity_check __FILE__ __LINE__
        (child_aproj = AIgnoredProjBorrows)
        ctx.meta;
      (* The symbolic value was updated *)
      Some (symbolic_value_to_texpression ctx mnv)
  | V.AEndedProjLoans (_, _) ->
      (* The symbolic value was updated, and the given back values come from sevearl
       * abstractions *)
      raise Unimplemented
  | AEndedProjBorrows _ -> (* We consider consumed values *) None
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      craise __FILE__ __LINE__ ctx.meta "Unreachable"

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
            cassert __FILE__ __LINE__ (field_values = []) ctx.meta
              "ADTs with borrows are not supported yet";
            (ctx, None)
        | TTuple ->
            (* Return *)
            let variant_id = adt_v.variant_id in
            sanity_check __FILE__ __LINE__ (variant_id = None) ctx.meta;
            if field_values = [] then (ctx, None)
            else
              (* Note that if there is exactly one field value, [mk_simpl_tuple_pattern]
               * is the identity *)
              let lv = mk_simpl_tuple_pattern field_values in
              (ctx, Some lv))
    | ABottom -> craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
  | AMutLoan (_, _) | ASharedLoan (_, _, _) ->
      craise __FILE__ __LINE__ ctx.meta "Unreachable"
  | AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
  | AEndedSharedLoan (_, _) ->
      (* We consider given back values, and thus ignore those *)
      (ctx, None)
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* not ended mutable loans, but not outer ones *)
      craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
      craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
      cassert __FILE__ __LINE__
        (List.for_all
           (fun (_, aproj) -> aproj = V.AIgnoredProjBorrows)
           child_projs)
        ctx.meta "Nested borrows are not supported yet";
      (ctx, None)
  | AEndedProjBorrows mv ->
      (* Return the meta-value *)
      let ctx, var = fresh_var_for_symbolic_value mv ctx in
      (ctx, Some (mk_typed_pattern_from_var var mp))
  | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
      craise __FILE__ __LINE__ ctx.meta "Unreachable"

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
  let var_values = List.combine (List.map var_get_id vars) values in
  if var_values <> [] then mk_emeta (SymbolicAssignments var_values) e else e

(** Derive naming information from a context.

    We explore the context and look in which bindings the symbolic values appear:
    we use this information to derive naming information. *)
let eval_ctx_to_symbolic_assignments_info (ctx : bs_ctx)
    (ectx : Contexts.eval_ctx) : (VarId.id * string) list =
  let info : (VarId.id * string) list ref = ref [] in
  let push_info name sv = info := (name, sv) :: !info in
  let visitor =
    object (self)
      inherit [_] Contexts.iter_eval_ctx

      method! visit_env_elem _ ee =
        match ee with
        | EBinding (BVar { index = _; name = Some name }, v) ->
            self#visit_typed_value name v
        | _ -> () (* Ignore *)

      method! visit_value name v =
        match v with
        | VLiteral _ | VBottom -> ()
        | VBorrow (VMutBorrow (_, v)) | VLoan (VSharedLoan (_, v)) ->
            self#visit_typed_value name v
        | VSymbolic sv ->
            (* Translate the type *)
            let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
            (* If the type is unit, do nothing *)
            if ty_is_unit ty then ()
            else
              (* Otherwise lookup the variable *)
              let var = lookup_var_for_symbolic_value sv ctx in
              push_info var.id name
        | _ -> ()
    end
  in
  (* Visit the context *)
  visitor#visit_eval_ctx "x" ectx;
  (* Return the computed information *)
  !info

let translate_error (meta : Meta.meta option) (msg : string) : texpression =
  { e = EError (meta, msg); ty = Error }

let rec translate_expression (e : S.expression) (ctx : bs_ctx) : texpression =
  match e with
  | S.Return (ectx, opt_v) ->
      (* We reached a return.
         Remark: we can't get there if we are inside a loop. *)
      translate_return ectx opt_v ctx
  | ReturnWithLoop (loop_id, is_continue) ->
      (* We reached a return and are inside a loop. *)
      translate_return_with_loop loop_id is_continue ctx
  | Panic -> translate_panic ctx
  | FunCall (call, e) -> translate_function_call call e ctx
  | EndAbstraction (ectx, abs, e) -> translate_end_abstraction ectx abs e ctx
  | EvalGlobal (gid, generics, sv, e) ->
      translate_global_eval gid generics sv e ctx
  | Assertion (ectx, v, e) -> translate_assertion ectx v e ctx
  | Expansion (p, sv, exp) -> translate_expansion p sv exp ctx
  | IntroSymbolic (ectx, p, sv, v, e) ->
      translate_intro_symbolic ectx p sv v e ctx
  | Meta (meta, e) -> translate_emeta meta e ctx
  | ForwardEnd (ectx, loop_input_values, e, back_e) ->
      (* Translate the end of a function, or the end of a loop.

         The case where we (re-)enter a loop is handled here.
      *)
      translate_forward_end ectx loop_input_values e back_e ctx
  | Loop loop -> translate_loop loop ctx
  | Error (meta, msg) -> translate_error meta msg

and translate_panic (ctx : bs_ctx) : texpression = Option.get ctx.mk_panic

(** [opt_v]: the value to return, in case we translate a forward body.

    Remark: for now, we can't get there if we are inside a loop.
    If inside a loop, we use {!translate_return_with_loop}.

    Remark: in case we merge the forward/backward functions, we introduce
    those in [translate_forward_end].
*)
and translate_return (ectx : C.eval_ctx) (opt_v : V.typed_value option)
    (ctx : bs_ctx) : texpression =
  let opt_v = Option.map (typed_value_to_texpression ctx ectx) opt_v in
  (Option.get ctx.mk_return) ctx opt_v

and translate_return_with_loop (loop_id : V.LoopId.id) (is_continue : bool)
    (ctx : bs_ctx) : texpression =
  sanity_check __FILE__ __LINE__ (is_continue = ctx.inside_loop) ctx.meta;
  let loop_id = V.LoopId.Map.find loop_id ctx.loop_ids_map in
  sanity_check __FILE__ __LINE__ (loop_id = Option.get ctx.loop_id) ctx.meta;

  (* Lookup the loop information *)
  let loop_id = Option.get ctx.loop_id in
  let loop_info = LoopId.Map.find loop_id ctx.loops in

  (* There are two cases depending on whether we translate a backward function
     or not.
  *)
  let output =
    match ctx.bid with
    | None -> Option.get loop_info.forward_output_no_state_no_result
    | Some _ ->
        (* Backward *)
        (* Group the variables in which we stored the values we need to give back.
         * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
        (* It can happen that we did not end any output abstraction, because the
           loop didn't use borrows corresponding to the region we just ended.
           If this happens, there are no backward outputs.
        *)
        let backward_outputs =
          match ctx.backward_outputs with Some outputs -> outputs | None -> []
        in
        let field_values = List.map mk_texpression_from_var backward_outputs in
        mk_simpl_tuple_texpression ctx.meta field_values
  in

  (* We may need to return a state
   * - error-monad: Return x
   * - state-error: Return (state, x)
   * Note that the loop function and the parent function live in the same
   * effect - in particular, one manipulates a state iff the other does
   * the same.
   * *)
  let effect_info = ctx_get_effect_info ctx in
  let output =
    if effect_info.stateful then
      let state_rvalue = mk_state_texpression ctx.state_var in
      mk_simpl_tuple_texpression ctx.meta [ state_rvalue; output ]
    else output
  in
  (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
  mk_emeta (Tag "return_with_loop") (mk_result_ok_texpression ctx.meta output)

and translate_function_call (call : S.call) (e : S.expression) (ctx : bs_ctx) :
    texpression =
  log#ldebug
    (lazy
      ("translate_function_call:\n" ^ "\n- call.call_id:"
      ^ S.show_call_id call.call_id
      ^ "\n\n- call.generics:\n"
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
  (* Retrieve the function id, and register the function call in the context
   * if necessary. *)
  let ctx, fun_id, effect_info, args, dest_v =
    match call.call_id with
    | S.Fun (fid, call_id) ->
        (* Regular function call *)
        let fid_t = translate_fun_id_or_trait_method_ref ctx fid in
        let func = Fun (FromLlbc (fid_t, None)) in
        (* Retrieve the effect information about this function (can fail,
         * takes a state as input, etc.) *)
        let effect_info = get_fun_effect_info ctx fid None None in
        (* Depending on the function effects:
           - add the fuel
           - add the state input argument
           - generate a fresh state variable for the returned state
        *)
        let args, ctx, out_state =
          let fuel = mk_fuel_input_as_list ctx effect_info in
          if effect_info.stateful then
            let state_var = mk_state_texpression ctx.state_var in
            let ctx, _, nstate_var = bs_ctx_fresh_state_var ctx in
            (List.concat [ fuel; args; [ state_var ] ], ctx, Some nstate_var)
          else (List.concat [ fuel; args ], ctx, None)
        in
        (* Generate the variables for the backward functions returned by the forward
           function. *)
        let ctx, ignore_fwd_output, back_funs_map, back_funs =
          (* We need to compute the signatures of the backward functions. *)
          let sg = Option.get call.sg in
          let decls_ctx = ctx.decls_ctx in
          let dsg =
            translate_fun_sig_with_regions_hierarchy_to_decomposed ctx.meta
              decls_ctx fid call.regions_hierarchy sg
              (List.map (fun _ -> None) sg.inputs)
          in
          log#ldebug
            (lazy ("dsg.generics:\n" ^ show_generic_params dsg.generics));
          let tr_self, all_generics =
            match call.trait_method_generics with
            | None -> (UnknownTrait __FUNCTION__, generics)
            | Some (all_generics, tr_self) ->
                let all_generics =
                  ctx_translate_fwd_generic_args ctx all_generics
                in
                let tr_self =
                  translate_fwd_trait_instance_id ctx.meta
                    ctx.type_ctx.type_infos tr_self
                in
                (tr_self, all_generics)
          in
          let back_tys =
            compute_back_tys_with_info dsg (Some (all_generics, tr_self))
          in
          (* Introduce variables for the backward functions *)
          (* Compute a proper basename for the variables *)
          let back_fun_name =
            let name =
              match fid with
              | FunId (FAssumed fid) -> (
                  match fid with
                  | BoxNew -> "box_new"
                  | BoxFree -> "box_free"
                  | ArrayRepeat -> "array_repeat"
                  | ArrayIndexShared -> "index_shared"
                  | ArrayIndexMut -> "index_mut"
                  | ArrayToSliceShared -> "to_slice_shared"
                  | ArrayToSliceMut -> "to_slice_mut"
                  | SliceIndexShared -> "index_shared"
                  | SliceIndexMut -> "index_mut")
              | FunId (FRegular fid) | TraitMethod (_, _, fid) -> (
                  let decl =
                    FunDeclId.Map.find fid ctx.fun_ctx.llbc_fun_decls
                  in
                  match Collections.List.last decl.name with
                  | PeIdent (s, _) -> s
                  | PeImpl _ ->
                      (* We shouldn't get there *)
                      craise __FILE__ __LINE__ decl.item_meta.meta "Unexpected")
            in
            name ^ "_back"
          in
          let ctx, back_vars =
            fresh_opt_vars
              (List.map
                 (fun ty ->
                   match ty with
                   | None -> None
                   | Some (_back_sg, ty) ->
                       (* We insert a name for the variable only if the type
                          is an arrow type. If it is not, it means the backward
                          function is degenerate (it takes no inputs) so it is
                          not a function anymore but a value: it doesn't make
                          sense to use a name like "back...". *)
                       let name =
                         if is_arrow_ty ty then Some back_fun_name else None
                       in
                       Some (name, ty))
                 back_tys)
              ctx
          in
          let back_funs =
            List.filter_map
              (fun v ->
                match v with
                | None -> None
                | Some v -> Some (mk_typed_pattern_from_var v None))
              back_vars
          in
          let gids =
            List.map
              (fun (g : T.region_var_group) -> g.id)
              call.regions_hierarchy
          in
          let back_vars =
            List.map (Option.map mk_texpression_from_var) back_vars
          in
          let back_funs_map =
            RegionGroupId.Map.of_list (List.combine gids back_vars)
          in
          (ctx, dsg.fwd_info.ignore_output, Some back_funs_map, back_funs)
        in
        (* Compute the pattern for the destination *)
        let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
        let dest = mk_typed_pattern_from_var dest dest_mplace in
        let dest =
          (* Here there is something subtle: as we might ignore the output
             of the forward function (because it translates to unit) we doNOT
             necessarily introduce in the let-binding the variable to which we
             map the symbolic value which was introduced for the output of the
             function call. This would be problematic if later we need to
             translate this symbolic value, but we implemented
             {!symbolic_value_to_texpression} so that it doesn't perform any
             lookups if the symbolic value has type unit.
          *)
          let vars =
            if ignore_fwd_output then back_funs else dest :: back_funs
          in
          mk_simpl_tuple_pattern vars
        in
        let dest =
          match out_state with
          | None -> dest
          | Some out_state -> mk_simpl_tuple_pattern [ out_state; dest ]
        in
        (* Register the function call *)
        let ctx =
          bs_ctx_register_forward_call call_id call args back_funs_map ctx
        in
        (ctx, func, effect_info, args, dest)
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
        let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
        let dest = mk_typed_pattern_from_var dest dest_mplace in
        (ctx, Unop Not, effect_info, args, dest)
    | S.Unop E.Neg -> (
        match args with
        | [ arg ] ->
            let int_ty = ty_as_integer ctx.meta arg.ty in
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
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_typed_pattern_from_var dest dest_mplace in
            (ctx, Unop (Neg int_ty), effect_info, args, dest)
        | _ -> craise __FILE__ __LINE__ ctx.meta "Unreachable")
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
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_typed_pattern_from_var dest dest_mplace in
            (ctx, Unop (Cast (src_ty, tgt_ty)), effect_info, args, dest)
        | CastFnPtr _ ->
            craise __FILE__ __LINE__ ctx.meta "TODO: function casts")
    | S.Binop binop -> (
        match args with
        | [ arg0; arg1 ] ->
            let int_ty0 = ty_as_integer ctx.meta arg0.ty in
            let int_ty1 = ty_as_integer ctx.meta arg1.ty in
            (match binop with
            (* The Rust compiler accepts bitshifts for any integer type combination for ty0, ty1 *)
            | E.Shl | E.Shr -> ()
            | _ -> sanity_check __FILE__ __LINE__ (int_ty0 = int_ty1) ctx.meta);
            let effect_info =
              {
                can_fail = ExpressionsUtils.binop_can_fail binop;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_typed_pattern_from_var dest dest_mplace in
            (ctx, Binop (binop, int_ty0), effect_info, args, dest)
        | _ -> craise __FILE__ __LINE__ ctx.meta "Unreachable")
  in
  let func = { id = FunOrOp fun_id; generics } in
  let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
  let ret_ty =
    if effect_info.can_fail then mk_result_ty dest_v.ty else dest_v.ty
  in
  let func_ty = mk_arrows input_tys ret_ty in
  let func = { e = Qualif func; ty = func_ty } in
  let call = mk_apps ctx.meta func args in
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
      ^ "\n- eval_ctx:\n"
      ^ eval_ctx_to_string ~meta:(Some ctx.meta) ectx
      ^ "\n- abs:\n" ^ abs_to_string ctx abs ^ "\n"));

  (* When we end an input abstraction, this input abstraction gets back
     the borrows which it introduced in the context through the input
     values: by listing those values, we get the values which are given
     back by one of the backward functions we are synthesizing.

     Note that we don't support nested borrows for now: if we find
     an ended synthesized input abstraction, it must be the one corresponding
     to the backward function wer are synthesizing, it can't be the one
     for a parent backward function.
  *)
  let bid = Option.get ctx.bid in
  sanity_check __FILE__ __LINE__ (rg_id = bid) ctx.meta;

  (* First, introduce the given back variables.

     We don't use the same given back variables if we translate a loop or
     the standard body of a function.
  *)
  let ctx, given_back_variables =
    let vars =
      if ctx.inside_loop then
        (* We are synthesizing a loop body *)
        let loop_id = Option.get ctx.loop_id in
        let loop = LoopId.Map.find loop_id ctx.loops in
        let tys = RegionGroupId.Map.find bid loop.back_outputs in
        List.map (fun ty -> (None, ty)) tys
      else
        (* Regular function body *)
        let back_sg = RegionGroupId.Map.find bid ctx.sg.back_sg in
        List.combine back_sg.output_names back_sg.outputs
    in
    let ctx, vars = fresh_vars vars ctx in
    ({ ctx with backward_outputs = Some vars }, vars)
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
      (fun (var, v) ->
        sanity_check __FILE__ __LINE__
          ((var : var).ty = (v : texpression).ty)
          ctx.meta)
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
        craise __FILE__ __LINE__ ctx.meta "Unreachable"
  in
  let effect_info = get_fun_effect_info ctx fun_id None (Some rg_id) in
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
      let ctx, _, nstate = bs_ctx_fresh_state_var ctx in
      ([ back_state ], ctx, Some nstate)
    else ([], ctx, None)
  in
  let back_inputs = List.append back_inputs back_state in
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
  (* Retrieve the function id, and register the function call in the context
     if necessary.Arith_status *)
  let ctx, func =
    bs_ctx_register_backward_call abs call_id rg_id back_inputs ctx
  in
  (* Translate the next expression *)
  let next_e = translate_expression e ctx in
  (* Put everything together *)
  let inputs = back_inputs in
  let args_mplaces = List.map (fun _ -> None) inputs in
  let args =
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpression mp arg)
      (List.combine inputs args_mplaces)
  in
  (* The backward function might have been filtered it does nothing
     (consumes unit and returns unit). *)
  match func with
  | None -> next_e
  | Some func ->
      log#ldebug
        (lazy
          (let args = List.map (texpression_to_string ctx) args in
           "func: "
           ^ texpression_to_string ctx func
           ^ "\nfunc type: "
           ^ pure_ty_to_string ctx func.ty
           ^ "\n\nargs:\n" ^ String.concat "\n" args));
      let call = mk_apps ctx.meta func args in
      mk_let effect_info.can_fail output call next_e

and translate_end_abstraction_identity (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expression) (ctx : bs_ctx) : texpression =
  (* We simply check that the abstraction only contains shared borrows/loans,
     and translate the next expression *)

  (* We can do this simply by checking that it consumes and gives back nothing *)
  let inputs = abs_to_consumed ctx ectx abs in
  let ctx, outputs = abs_to_given_back None abs ctx in
  sanity_check __FILE__ __LINE__ (inputs = []) ctx.meta;
  sanity_check __FILE__ __LINE__ (outputs = []) ctx.meta;

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
  let inputs = T.RegionGroupId.Map.find rg_id ctx.backward_inputs_no_state in
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: as there are no nested borrows, there should be none. *)
  let consumed = abs_to_consumed ctx ectx abs in
  cassert __FILE__ __LINE__ (consumed = []) ctx.meta
    "Nested borrows are not supported yet";
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
      sanity_check __FILE__ __LINE__ (given_back.ty = input.ty) ctx.meta)
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
  sanity_check __FILE__ __LINE__ (loop_id = Option.get ctx.loop_id) ctx.meta;
  let rg_id = Option.get rg_id in
  (* There are two cases depending on the [abs_kind] (whether this is a
     synth input or a regular loop call) *)
  match abs_kind with
  | V.LoopSynthInput ->
      (* Actually the same case as [SynthInput] *)
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.LoopCall -> (
      (* We need to introduce a call to the backward function corresponding
         to a forward call which happened earlier *)
      let fun_id = E.FRegular ctx.fun_decl.def_id in
      let effect_info =
        get_fun_effect_info ctx (FunId fun_id) (Some vloop_id) (Some rg_id)
      in
      let loop_info = LoopId.Map.find loop_id ctx.loops in
      (* Retrieve the additional backward inputs. Note that those are actually
         the backward inputs of the function we are synthesizing (and that we
         need to *transmit* to the loop backward function): they are not the
         values consumed upon ending the abstraction (i.e., we don't use
         [abs_to_consumed]) *)
      let back_inputs_vars =
        T.RegionGroupId.Map.find rg_id ctx.backward_inputs_no_state
      in
      let back_inputs = List.map mk_texpression_from_var back_inputs_vars in
      (* If the function is stateful:
       * - add the state input argument
       * - generate a fresh state variable for the returned state
       *)
      let back_state, ctx, nstate =
        if effect_info.stateful then
          let back_state = mk_state_texpression ctx.state_var in
          let ctx, _, nstate = bs_ctx_fresh_state_var ctx in
          ([ back_state ], ctx, Some nstate)
        else ([], ctx, None)
      in
      (* Concatenate all the inputs *)
      let inputs = List.concat [ back_inputs; back_state ] in
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
      (* Create the expression for the function:
         - it is either a call to a top-level function, if we split the
           forward/backward functions
         - or a call to the variable we introduced for the backward function,
           if we merge the forward/backward functions *)
      let func =
        RegionGroupId.Map.find rg_id (Option.get loop_info.back_funs)
      in
      (* We may have filtered the backward function elsewhere if it doesn't
         do anything (doesn't consume anything and doesn't return anything) *)
      match func with
      | None -> next_e
      | Some func ->
          let call = mk_apps ctx.meta func args in
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
          mk_let effect_info.can_fail output call next_e)

and translate_global_eval (gid : A.GlobalDeclId.id) (generics : T.generic_args)
    (sval : V.symbolic_value) (e : S.expression) (ctx : bs_ctx) : texpression =
  let ctx, var = fresh_var_for_symbolic_value sval ctx in
  let decl = A.GlobalDeclId.Map.find gid ctx.global_ctx.llbc_global_decls in
  let generics = ctx_translate_fwd_generic_args ctx generics in
  let global_expr = { id = Global gid; generics } in
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
  let assertion = mk_apps ctx.meta func args in
  mk_let monadic (mk_dummy_pattern mk_unit_ty) assertion next_e

and translate_expansion (p : S.mplace option) (sv : V.symbolic_value)
    (exp : S.expansion) (ctx : bs_ctx) : texpression =
  (* Translate the scrutinee *)
  let scrutinee = symbolic_value_to_texpression ctx sv in
  let scrutinee_mplace = translate_opt_mplace p in
  (* Translate the branches *)
  match exp with
  | ExpandNoBranch (sexp, e) -> (
      match sexp with
      | V.SeLiteral _ ->
          (* We do not *register* symbolic expansions to literal
             values in the symbolic ADT *)
          craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
          craise __FILE__ __LINE__ ctx.meta "Unreachable")
  | ExpandAdt branches -> (
      (* We don't do the same thing if there is a branching or not *)
      match branches with
      | [] -> craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
          sanity_check __FILE__ __LINE__
            (List.for_all (fun br -> br.branch.ty = ty) branches)
            ctx.meta;
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
      log#ldebug
        (lazy
          ("true_e.ty: "
          ^ pure_ty_to_string ctx true_e.ty
          ^ "\n\nfalse_e.ty: "
          ^ pure_ty_to_string ctx false_e.ty));
      sanity_check __FILE__ __LINE__ (ty = false_e.ty) ctx.meta;
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
      sanity_check __FILE__ __LINE__
        (List.for_all (fun (br : match_branch) -> br.branch.ty = ty) branches)
        ctx.meta;
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
        T.TypeDeclId.Set.mem adt_id ctx.type_ctx.recursive_decls
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
             ctx.type_ctx.type_infos type_id
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
        let adt_id, generics = ty_as_adt ctx.meta scrutinee.ty in
        let gen_field_proj (field_id : FieldId.id) (dest : var) : texpression =
          let proj_kind = { adt_id; field_id } in
          let qualif = { id = Proj proj_kind; generics } in
          let proj_e = Qualif qualif in
          let proj_ty = mk_arrow scrutinee.ty dest.ty in
          let proj = { e = proj_e; ty = proj_ty } in
          mk_app ctx.meta proj scrutinee
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
        match vars with
        | [ v ] -> v
        | _ -> craise __FILE__ __LINE__ ctx.meta "Unreachable"
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
      craise __FILE__ __LINE__ ctx.meta
        "Attempt to expand a non-expandable value"

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
    | VaTraitConstValue (trait_ref, const_name) ->
        let type_infos = ctx.type_ctx.type_infos in
        let trait_ref = translate_fwd_trait_ref ctx.meta type_infos trait_ref in
        let qualif_id = TraitConst (trait_ref, const_name) in
        let qualif = { id = qualif_id; generics = empty_generic_args } in
        { e = Qualif qualif; ty = var.ty }
  in

  (* Make the let-binding *)
  let monadic = false in
  let var = mk_typed_pattern_from_var var mplace in
  mk_let monadic var v next_e

and translate_forward_end (ectx : C.eval_ctx)
    (loop_input_values : V.typed_value S.symbolic_value_id_map option)
    (fwd_e : S.expression) (back_e : S.expression S.region_group_id_map)
    (ctx : bs_ctx) : texpression =
  let translate_one_end ctx (bid : RegionGroupId.id option) =
    let ctx = { ctx with bid } in
    (* Update the current state with the additional state received by the backward
       function, if needs be, and lookup the proper expression *)
    let ctx, e, finish =
      match bid with
      | None ->
          (* We are translating the forward function - nothing to do *)
          (ctx, fwd_e, fun e -> e)
      | Some bid ->
          (* We need to update the state, and wrap the expression in a
             lambda, which introduces the additional inputs of the backward
             function.
          *)
          let ctx =
            (* Introduce variables for the inputs and the state variable
               and update the context.

               We need to introduce fresh variables for the additional inputs,
               because they are locally introduced in a lambda.
            *)
            let back_sg = RegionGroupId.Map.find bid ctx.sg.back_sg in
            let ctx, backward_inputs_no_state =
              fresh_vars back_sg.inputs_no_state ctx
            in
            let ctx, backward_inputs_with_state =
              if back_sg.effect_info.stateful then
                let ctx, var, _ = bs_ctx_fresh_state_var ctx in
                (ctx, backward_inputs_no_state @ [ var ])
              else (ctx, backward_inputs_no_state)
            in
            (* Update the functions mk_return and mk_panic *)
            let effect_info = back_sg.effect_info in
            let mk_return ctx v =
              assert (v = None);
              let output =
                (* Group the variables in which we stored the values we need to give back.
                   See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
                let backward_outputs = Option.get ctx.backward_outputs in
                let field_values =
                  List.map mk_texpression_from_var backward_outputs
                in
                mk_simpl_tuple_texpression ctx.meta field_values
              in
              let output =
                if effect_info.stateful then
                  let state_rvalue = mk_state_texpression ctx.state_var in
                  mk_simpl_tuple_texpression ctx.meta [ state_rvalue; output ]
                else output
              in
              (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
              mk_result_ok_texpression ctx.meta output
            in
            let mk_panic =
              (* TODO: we should use a [Fail] function *)
              let mk_output output_ty =
                if effect_info.stateful then
                  (* Create the [Fail] value *)
                  let ret_ty = mk_simpl_tuple_ty [ mk_state_ty; output_ty ] in
                  let ret_v =
                    mk_result_fail_texpression_with_error_id ctx.meta
                      error_failure_id ret_ty
                  in
                  ret_v
                else
                  mk_result_fail_texpression_with_error_id ctx.meta
                    error_failure_id output_ty
              in
              let output =
                mk_simpl_tuple_ty
                  (RegionGroupId.Map.find bid ctx.sg.back_sg).outputs
              in
              mk_output output
            in
            {
              ctx with
              backward_inputs_no_state =
                RegionGroupId.Map.add bid backward_inputs_no_state
                  ctx.backward_inputs_no_state;
              backward_inputs_with_state =
                RegionGroupId.Map.add bid backward_inputs_with_state
                  ctx.backward_inputs_with_state;
              mk_return = Some mk_return;
              mk_panic = Some mk_panic;
            }
          in

          let e = T.RegionGroupId.Map.find bid back_e in
          let finish e =
            (* Wrap in lambdas if necessary *)
            let inputs =
              RegionGroupId.Map.find bid ctx.backward_inputs_with_state
            in
            let places = List.map (fun _ -> None) inputs in
            mk_lambdas_from_vars inputs places e
          in
          (ctx, e, finish)
    in
    let e = translate_expression e ctx in
    finish e
  in

  (* We need to translate the end of the forward
     function (this is the value we will return) and generate the bodies
     of the backward functions (which we will also return).

     Update the current state with the additional state received by the backward
     function, if needs be, and lookup the proper expression.
  *)
  let translate_end ctx =
    (* Compute the output of the forward function *)
    let fwd_effect_info = ctx.sg.fwd_info.effect_info in
    let ctx, pure_fwd_var = fresh_var None ctx.sg.fwd_output ctx in
    let fwd_e = translate_one_end ctx None in

    (* If we reached a loop: if we are *inside* a loop, we need to ignore the
       backward functions which are not associated to region abstractions.
    *)
    let keep_rg_ids =
      match ctx.loop_id with
      | None -> None
      | Some loop_id ->
          if ctx.inside_loop then
            let loop_info = LoopId.Map.find loop_id ctx.loops in
            Some
              (RegionGroupId.Set.of_list
                 (RegionGroupId.Map.keys loop_info.back_outputs))
          else None
    in
    let keep_rg_id =
      match keep_rg_ids with
      | None -> fun _ -> true
      | Some ids -> fun id -> RegionGroupId.Set.mem id ids
    in

    let back_el =
      List.map
        (fun ((gid, _) : RegionGroupId.id * back_sg_info) ->
          if keep_rg_id gid then Some (translate_one_end ctx (Some gid))
          else None)
        (RegionGroupId.Map.bindings ctx.sg.back_sg)
    in

    (* Compute whether the backward expressions should be evaluated straight
       away or not (i.e., if we should bind them with monadic let-bindings
       or not). We evaluate them straight away if they can fail and have no
       inputs. *)
    let evaluate_backs =
      List.map
        (fun ((rg_id, sg) : RegionGroupId.id * back_sg_info) ->
          if keep_rg_id rg_id then
            Some
              (if !Config.simplify_merged_fwd_backs then
                 sg.inputs = [] && sg.effect_info.can_fail
               else false)
          else None)
        (RegionGroupId.Map.bindings ctx.sg.back_sg)
    in

    (* Introduce variables for the backward functions.
       We lookup the LLBC definition in an attempt to derive pretty names
       for those functions. *)
    let _, back_vars = fresh_back_vars_for_current_fun ctx keep_rg_ids in

    (* Create the return expressions *)
    let vars =
      let back_vars = List.filter_map (fun x -> x) back_vars in
      if ctx.sg.fwd_info.ignore_output then back_vars
      else pure_fwd_var :: back_vars
    in
    let vars = List.map mk_texpression_from_var vars in
    let ret = mk_simpl_tuple_texpression ctx.meta vars in

    (* Introduce a fresh input state variable for the forward expression *)
    let _ctx, state_var, state_pat =
      if fwd_effect_info.stateful then
        let ctx, var, pat = bs_ctx_fresh_state_var ctx in
        (ctx, [ var ], [ pat ])
      else (ctx, [], [])
    in

    let state_var = List.map mk_texpression_from_var state_var in
    let ret = mk_simpl_tuple_texpression ctx.meta (state_var @ [ ret ]) in
    let ret = mk_result_ok_texpression ctx.meta ret in

    (* Introduce all the let-bindings *)

    (* Combine:
       - the backward variables
       - whether we should evaluate the expression for the backward function
         (i.e., should we use a monadic let-binding or not - we do if the
         backward functions don't have inputs and can fail)
       - the expressions for the backward functions
    *)
    let back_vars_els =
      List.filter_map
        (fun (v, (eval, el)) ->
          match v with
          | None -> None
          | Some v -> Some (v, Option.get eval, Option.get el))
        (List.combine back_vars (List.combine evaluate_backs back_el))
    in
    let e =
      List.fold_right
        (fun (var, evaluate, back_e) e ->
          mk_let evaluate (mk_typed_pattern_from_var var None) back_e e)
        back_vars_els ret
    in
    (* Bind the expression for the forward output *)
    let fwd_var = mk_typed_pattern_from_var pure_fwd_var None in
    let pat = mk_simpl_tuple_pattern (state_pat @ [ fwd_var ]) in
    mk_let fwd_effect_info.can_fail pat fwd_e e
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
      let effect_info = get_fun_effect_info ctx (FunId fid) None ctx.bid in

      (* Introduce a fresh output value for the forward function *)
      let ctx, fwd_output, output_pat =
        if ctx.sg.fwd_info.ignore_output then
          (* Note that we still need the forward output (which is unit),
             because even though the loop function will ignore the forward output,
             the forward expression will still compute an output (which
             will have type unit - otherwise we can't ignore it). *)
          (ctx, mk_unit_rvalue, [])
        else
          let ctx, output_var = fresh_var None ctx.sg.fwd_output ctx in
          ( ctx,
            mk_texpression_from_var output_var,
            [ mk_typed_pattern_from_var output_var None ] )
      in

      (* Introduce fresh variables for the backward functions of the loop.

         For now, the backward functions of the loop are the same as the
         backward functions of the outer function.
      *)
      let ctx, back_funs_map, back_funs =
        (* We need to filter the region groups which are not linked to region
           abstractions appearing in the loop, so as not to introduce unnecessary
           backward functions. *)
        let keep_rg_ids =
          RegionGroupId.Set.of_list
            (RegionGroupId.Map.keys loop_info.back_outputs)
        in
        let ctx, back_vars =
          fresh_back_vars_for_current_fun ctx (Some keep_rg_ids)
        in
        let back_funs =
          List.filter_map
            (fun v ->
              match v with
              | None -> None
              | Some v -> Some (mk_typed_pattern_from_var v None))
            back_vars
        in
        let gids = RegionGroupId.Map.keys ctx.sg.back_sg in
        let back_funs_map =
          RegionGroupId.Map.of_list
            (List.combine gids
               (List.map (Option.map mk_texpression_from_var) back_vars))
        in
        (ctx, Some back_funs_map, back_funs)
      in

      (* Introduce patterns *)
      let args, ctx, out_pats =
        (* Add the returned backward functions (they might be empty) *)
        let output_pat = mk_simpl_tuple_pattern (output_pat @ back_funs) in

        (* Depending on the function effects:
         * - add the fuel
         * - add the state input argument
         * - generate a fresh state variable for the returned state
         *)
        let fuel = mk_fuel_input_as_list ctx effect_info in
        if effect_info.stateful then
          let state_var = mk_state_texpression ctx.state_var in
          let ctx, _, nstate_pat = bs_ctx_fresh_state_var ctx in
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
          forward_output_no_state_no_result = Some fwd_output;
          back_funs = back_funs_map;
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
        let fun_id = Fun (FromLlbc (FunId fid, Some loop_id)) in
        let func = { id = FunOrOp fun_id; generics = loop_info.generics } in
        let input_tys = (List.map (fun (x : texpression) -> x.ty)) args in
        let ret_ty =
          if effect_info.can_fail then mk_result_ty out_pat.ty else out_pat.ty
        in
        let func_ty = mk_arrows input_tys ret_ty in
        let func = { e = Qualif func; ty = func_ty } in
        let call = mk_apps ctx.meta func args in
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
            (Print.list_to_string (ty_to_string ctx))
            loop.rg_to_given_back_tys
        ^ "\n"));
    let ctx, _ = fresh_vars_for_symbolic_values svl ctx in
    ctx
  in

  (* Sanity check: all the non-fresh symbolic values are in the context *)
  sanity_check __FILE__ __LINE__
    (List.for_all
       (fun (sv : V.symbolic_value) ->
         V.SymbolicValueId.Map.mem sv.sv_id ctx.sv_to_var)
       loop.input_svalues)
    ctx.meta;

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
  let rg_to_given_back_tys =
    RegionGroupId.Map.map
      (fun tys ->
        (* The types shouldn't contain borrows - we can translate them as forward types *)
        List.map
          (fun ty ->
            cassert __FILE__ __LINE__
              (not (TypesUtils.ty_has_borrows ctx.type_ctx.type_infos ty))
              ctx.meta "The types shouldn't contain borrows";
            ctx_translate_fwd_ty ctx ty)
          tys)
      loop.rg_to_given_back_tys
  in

  (* The output type of the loop function *)
  let fwd_effect_info = { ctx.sg.fwd_info.effect_info with is_rec = true } in
  let back_effect_infos, output_ty =
    (* The loop backward functions consume the same additional inputs as the parent
       function, but have custom outputs *)
    log#ldebug
      (lazy
        (let back_sgs = RegionGroupId.Map.bindings ctx.sg.back_sg in
         "translate_loop:" ^ "\n- back_sgs: "
         ^ (Print.list_to_string
              (Print.pair_to_string RegionGroupId.to_string show_back_sg_info))
             back_sgs
         ^ "\n- given_back_tys: "
         ^ (RegionGroupId.Map.to_string None
              (Print.list_to_string (pure_ty_to_string ctx)))
             rg_to_given_back_tys
         ^ "\n"));
    let back_info_tys =
      List.map
        (fun ((rg_id, given_back) : RegionGroupId.id * ty list) ->
          (* Lookup the effect information about the parent function region group
             associated to this loop region abstraction *)
          let back_sg = RegionGroupId.Map.find rg_id ctx.sg.back_sg in
          (* Remark: the effect info of the backward function for the loop
             is almost the same as for the backward function of the parent function.
             Quite importantly, the fact that the function is stateful and/or can fail
             mostly depends on whether it has inputs or not, and the backward functions
             for the loops have the same inputs as the backward functions for the parent
             function.
          *)
          let effect_info = back_sg.effect_info in
          let effect_info = { effect_info with is_rec = true } in
          (* Compute the input/output types *)
          let inputs = List.map snd back_sg.inputs in
          let outputs = given_back in
          (* Filter if necessary *)
          let ty =
            if !Config.simplify_merged_fwd_backs && inputs = [] && outputs = []
            then None
            else
              let output = mk_simpl_tuple_ty outputs in
              let output =
                mk_back_output_ty_from_effect_info effect_info inputs output
              in
              let ty = mk_arrows inputs output in
              Some ty
          in
          ((rg_id, effect_info), ty))
        (RegionGroupId.Map.bindings rg_to_given_back_tys)
    in
    let back_info = List.map fst back_info_tys in
    let back_info = RegionGroupId.Map.of_list back_info in
    let back_tys = List.filter_map snd back_info_tys in
    let output =
      if ctx.sg.fwd_info.ignore_output then back_tys
      else ctx.sg.fwd_output :: back_tys
    in
    let output = mk_simpl_tuple_ty output in
    let effect_info = ctx.sg.fwd_info.effect_info in
    let output =
      if effect_info.stateful then mk_simpl_tuple_ty [ mk_state_ty; output ]
      else output
    in
    let output =
      if effect_info.can_fail && inputs <> [] then mk_result_ty output
      else output
    in
    (back_info, output)
  in

  (* Add the loop information in the context *)
  let ctx =
    sanity_check __FILE__ __LINE__
      (not (LoopId.Map.mem loop_id ctx.loops))
      ctx.meta;

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

    (* Update the helpers to translate the fail and return expressions *)
    let mk_panic =
      (* Note that we reuse the effect information from the parent function *)
      let effect_info = ctx_get_effect_info ctx in
      let back_tys = compute_back_tys ctx.sg None in
      let back_tys = List.filter_map (fun x -> x) back_tys in
      let tys =
        if ctx.sg.fwd_info.ignore_output then back_tys
        else ctx.sg.fwd_output :: back_tys
      in
      let output_ty = mk_simpl_tuple_ty tys in
      if effect_info.stateful then
        (* Create the [Fail] value *)
        let ret_ty = mk_simpl_tuple_ty [ mk_state_ty; output_ty ] in
        let ret_v =
          mk_result_fail_texpression_with_error_id ctx.meta error_failure_id
            ret_ty
        in
        ret_v
      else
        mk_result_fail_texpression_with_error_id ctx.meta error_failure_id
          output_ty
    in
    let mk_return ctx v =
      match v with
      | None -> raise (Failure "Unexpected")
      | Some output ->
          let effect_info = ctx_get_effect_info ctx in
          let output =
            if effect_info.stateful then
              let state_rvalue = mk_state_texpression ctx.state_var in
              mk_simpl_tuple_texpression ctx.meta [ state_rvalue; output ]
            else output
          in
          (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
          mk_result_ok_texpression ctx.meta output
    in

    let loop_info =
      {
        loop_id;
        input_vars = inputs;
        input_svl = loop.input_svalues;
        generics;
        forward_inputs = None;
        forward_output_no_state_no_result = None;
        back_outputs = rg_to_given_back_tys;
        back_funs = None;
        fwd_effect_info;
        back_effect_infos;
      }
    in
    let loops = LoopId.Map.add loop_id loop_info ctx.loops in
    { ctx with loops; mk_return = Some mk_return; mk_panic = Some mk_panic }
  in

  (* Update the context to translate the function end *)
  let ctx_end = { ctx with loop_id = Some loop_id } in
  let fun_end = translate_expression loop.end_expr ctx_end in

  (* Update the context for the loop body *)
  let ctx_loop = { ctx_end with inside_loop = true } in

  (* Add the input state *)
  let input_state =
    if (ctx_get_effect_info ctx).stateful then Some ctx.state_var else None
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
        output_ty;
        loop_body;
      }
  in
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
        Some (Assignment (lp, rv, rp))
    | S.Snapshot ectx ->
        let infos = eval_ctx_to_symbolic_assignments_info ctx ectx in
        if infos <> [] then
          (* If often happens that the next expression contains exactly the
             same meta information *)
          match next_e.e with
          | Meta (SymbolicPlaces infos1, _) when infos1 = infos -> None
          | _ -> Some (SymbolicPlaces infos)
        else None
  in
  match meta with
  | Some meta ->
      let e = Meta (meta, next_e) in
      let ty = next_e.ty in
      { e; ty }
  | None -> next_e

(** Wrap a function body in a match over the fuel to control termination. *)
let wrap_in_match_fuel (meta : Meta.meta) (fuel0 : VarId.id) (fuel : VarId.id)
    (body : texpression) : texpression =
  let fuel0_var : var = mk_fuel_var fuel0 in
  let fuel0 = mk_texpression_from_var fuel0_var in
  let nfuel_var : var = mk_fuel_var fuel in
  let nfuel_pat = mk_typed_pattern_from_var nfuel_var None in
  let fail_branch =
    mk_result_fail_texpression_with_error_id meta error_out_of_fuel_id body.ty
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
        mk_app meta func fuel0
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
        mk_app meta func fuel0
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
  assert (ctx.bid = None);
  log#ldebug
    (lazy
      ("SymbolicToPure.translate_fun_decl: "
      ^ name_to_string ctx def.name
      ^ "\n"));

  (* Translate the declaration *)
  let def_id = def.def_id in
  let llbc_name = def.name in
  let name = name_to_string ctx llbc_name in
  (* Translate the signature *)
  let signature = translate_fun_sig_from_decomposed ctx.sg in
  (* Translate the body, if there is *)
  let body =
    match body with
    | None -> None
    | Some body ->
        let effect_info =
          get_fun_effect_info ctx (FunId (FRegular def_id)) None None
        in
        let mk_return ctx v =
          match v with
          | None ->
              raise
                (Failure
                   "Unexpected: reached a return expression without value in a \
                    function forward expression")
          | Some output ->
              let output =
                if effect_info.stateful then
                  let state_rvalue = mk_state_texpression ctx.state_var in
                  mk_simpl_tuple_texpression ctx.meta [ state_rvalue; output ]
                else output
              in
              (* Wrap in a result - TODO: check effect_info.can_fail to not always wrap *)
              mk_result_ok_texpression ctx.meta output
        in
        let mk_panic =
          (* TODO: we should use a [Fail] function *)
          let mk_output output_ty =
            if effect_info.stateful then
              (* Create the [Fail] value *)
              let ret_ty = mk_simpl_tuple_ty [ mk_state_ty; output_ty ] in
              let ret_v =
                mk_result_fail_texpression_with_error_id ctx.meta
                  error_failure_id ret_ty
              in
              ret_v
            else
              mk_result_fail_texpression_with_error_id ctx.meta error_failure_id
                output_ty
          in
          let back_tys = compute_back_tys ctx.sg None in
          let back_tys = List.filter_map (fun x -> x) back_tys in
          let tys =
            if ctx.sg.fwd_info.ignore_output then back_tys
            else ctx.sg.fwd_output :: back_tys
          in
          let output = mk_simpl_tuple_ty tys in
          mk_output output
        in
        let ctx =
          { ctx with mk_return = Some mk_return; mk_panic = Some mk_panic }
        in
        let body = translate_expression body ctx in
        (* Add a match over the fuel, if necessary *)
        let body =
          if function_decreases_fuel effect_info then
            wrap_in_match_fuel def.item_meta.meta ctx.fuel0 ctx.fuel body
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
        (* Group the inputs together *)
        let inputs = List.concat [ fuel; ctx.forward_inputs; fwd_state ] in
        let inputs_lvs =
          List.map (fun v -> mk_typed_pattern_from_var v None) inputs
        in
        (* Sanity check *)
        log#ldebug
          (lazy
            ("SymbolicToPure.translate_fun_decl: "
            ^ name_to_string ctx def.name
            ^ "\n- inputs: "
            ^ String.concat ", " (List.map show_var ctx.forward_inputs)
            ^ "\n- state: "
            ^ String.concat ", " (List.map show_var fwd_state)
            ^ "\n- signature.inputs: "
            ^ String.concat ", "
                (List.map (pure_ty_to_string ctx) signature.inputs)));
        (* TODO: we need to normalize the types *)
        if !Config.type_check_pure_code then
          sanity_check __FILE__ __LINE__
            (List.for_all
               (fun (var, ty) -> (var : var).ty = ty)
               (List.combine inputs signature.inputs))
            def.item_meta.meta;
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
      meta = def.item_meta.meta;
      kind = def.kind;
      num_loops;
      loop_id;
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
  List.filter_map
    (fun d ->
      try Some (translate_type_decl ctx d)
      with CFailure (meta, _) ->
        let env = PrintPure.decls_ctx_to_fmt_env ctx in
        let name = PrintPure.name_to_string env d.name in
        let name_pattern = TranslateCore.name_to_pattern_string ctx d.name in
        save_error __FILE__ __LINE__ meta
          ("Could not translate type decl '" ^ name
         ^ " because of previous error\nName pattern: '" ^ name_pattern ^ "'");
        None)
    (TypeDeclId.Map.values ctx.type_ctx.type_decls)

let translate_trait_decl (ctx : Contexts.decls_ctx) (trait_decl : A.trait_decl)
    : trait_decl =
  let {
    def_id;
    is_local;
    name = llbc_name;
    item_meta;
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
  let generics =
    translate_generic_params trait_decl.item_meta.meta llbc_generics
  in
  let preds = translate_predicates trait_decl.item_meta.meta preds in
  let parent_clauses =
    List.map
      (translate_trait_clause trait_decl.item_meta.meta)
      llbc_parent_clauses
  in
  let consts =
    List.map
      (fun (name, (ty, id)) ->
        (name, (translate_fwd_ty trait_decl.item_meta.meta type_infos ty, id)))
      consts
  in
  let types =
    List.map
      (fun (name, (trait_clauses, ty)) ->
        ( name,
          ( List.map
              (translate_trait_clause trait_decl.item_meta.meta)
              trait_clauses,
            Option.map
              (translate_fwd_ty trait_decl.item_meta.meta type_infos)
              ty ) ))
      types
  in
  {
    def_id;
    is_local;
    llbc_name;
    name;
    meta = item_meta.meta;
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
    item_meta;
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
    translate_trait_decl_ref trait_impl.item_meta.meta
      (translate_fwd_ty trait_impl.item_meta.meta type_infos)
      llbc_impl_trait
  in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      llbc_name
  in
  let generics =
    translate_generic_params trait_impl.item_meta.meta llbc_generics
  in
  let preds = translate_predicates trait_impl.item_meta.meta preds in
  let parent_trait_refs =
    List.map (translate_strait_ref trait_impl.item_meta.meta) parent_trait_refs
  in
  let consts =
    List.map
      (fun (name, (ty, id)) ->
        (name, (translate_fwd_ty trait_impl.item_meta.meta type_infos ty, id)))
      consts
  in
  let types =
    List.map
      (fun (name, (trait_refs, ty)) ->
        ( name,
          ( List.map
              (translate_fwd_trait_ref trait_impl.item_meta.meta type_infos)
              trait_refs,
            translate_fwd_ty trait_impl.item_meta.meta type_infos ty ) ))
      types
  in
  {
    def_id;
    is_local;
    llbc_name;
    name;
    meta = item_meta.meta;
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

let translate_global (ctx : Contexts.decls_ctx) (decl : A.global_decl) :
    global_decl =
  let {
    A.item_meta;
    def_id;
    is_local;
    name = llbc_name;
    generics = llbc_generics;
    preds;
    ty;
    kind;
    body = body_id;
  } =
    decl
  in
  let name =
    Print.Types.name_to_string
      (Print.Contexts.decls_ctx_to_fmt_env ctx)
      llbc_name
  in
  let generics = translate_generic_params decl.item_meta.meta llbc_generics in
  let preds = translate_predicates decl.item_meta.meta preds in
  let ty = translate_fwd_ty decl.item_meta.meta ctx.type_ctx.type_infos ty in
  {
    meta = item_meta.meta;
    def_id;
    is_local;
    llbc_name;
    name;
    llbc_generics;
    generics;
    preds;
    ty;
    kind;
    body_id;
  }
