open LlbcAstUtils
open Pure
open PureUtils
open FunsAnalysis
open TypesAnalysis
open PrintSymbolicAst
module T = Types
module V = Values
module C = Contexts
module A = LlbcAst
module S = SymbolicAst

let match_name_find_opt = TranslateCore.match_name_find_opt

let match_name_with_generics_find_opt =
  TranslateCore.match_name_with_generics_find_opt

type type_ctx = {
  llbc_type_decls : T.type_decl TypeDeclId.Map.t;
  type_decls : type_decl TypeDeclId.Map.t;
      (** We use this for type-checking (for sanity checks) when translating
          values and functions. This map is empty when we translate the types,
          then contains all the translated types when we translate the
          functions. *)
  type_infos : type_infos;
  recursive_decls : T.TypeDeclId.Set.t;
}
[@@deriving show]

type fun_sig_named_outputs = {
  sg : fun_sig;  (** A function signature *)
  output_names : string option list;
      (** In case the signature is for a backward function, we may provides
          names for the outputs. The reason is that the outputs of backward
          functions come from (in case there are no nested borrows) borrows
          present in the inputs of the original rust function. In this
          situation, we can use the names of those inputs to name the outputs.
          Those names are very useful to generate beautiful codes (we may need
          to introduce temporary variables in the bodies of the backward
          functions to store the returned values, in which case we use those
          names). *)
}
[@@deriving show]

type fun_ctx = {
  llbc_fun_decls : A.fun_decl A.FunDeclId.Map.t;
  fun_infos : fun_info A.FunDeclId.Map.t;
  regions_hierarchies : T.region_var_groups FunIdMap.t;
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

    The various input and output fields are for this unique loop call, if there
    is one. *)
type loop_info = {
  loop_id : LoopId.id;
  input_vars : fvar list;
  input_svl : V.symbolic_value list;
  generics : generic_args;
  forward_inputs : texpr list option;
      (** The forward inputs are initialized at [None] *)
  forward_output_no_state_no_result : texpr option;
      (** The forward outputs are initialized at [None] *)
  back_outputs : ty list RegionGroupId.Map.t;
      (** The map from region group ids to the types of the values given back by
          the corresponding loop abstractions. This map is partial. *)
  back_funs : texpr option RegionGroupId.Map.t option;
      (** If we do not split between the forward/backward functions: the
          variables we introduced for the backward functions.

          Example:
          {[
            let x, back = Vec.index_mut n v in
                   ^^^^
                   here
            ...
          ]}

          The expression might be [None] in case the backward function has to be
          filtered (because it does nothing - the backward functions for shared
          borrows for instance).

          Initialized with [None], gets updated to [Some] only if we merge the
          fwd/back functions. *)
  fwd_effect_info : fun_effect_info;
  back_effect_infos : fun_effect_info RegionGroupId.Map.t;
}
[@@deriving show]

type back_fun_info = { fvar : texpr; can_fail : bool } [@@deriving show]

(** Some meta-information. See [bs_ctx.meta_symb_places] *)
type meta_symb_place = texpr * string [@@deriving show, ord]

module MetaSymbPlaceOrd :
  Collections.OrderedType with type t = meta_symb_place = struct
  type t = meta_symb_place

  let compare = compare_meta_symb_place
  let to_string = show_meta_symb_place
  let pp_t = pp_meta_symb_place
  let show_t = show_meta_symb_place
end

module MetaSymbPlaceSet = Collections.MakeSet (MetaSymbPlaceOrd)

(** Body synthesis context *)
type bs_ctx = {
  (* TODO: there are a lot of duplications with the various decls ctx *)
  span : Meta.span;  (** The span information about the current declaration *)
  decls_ctx : C.decls_ctx;
  type_ctx : type_ctx;
  fun_ctx : fun_ctx;
  fun_dsigs : decomposed_fun_sig FunDeclId.Map.t;
  fun_decl : A.fun_decl;
  bid : RegionGroupId.id option;
      (** TODO: rename

          The id of the group region we are currently translating. We initially
          set it to `None`, then update it when we enter an expression which is
          specific to a backward function. *)
  sg : decomposed_fun_sig;
      (** Information about the function signature - useful in particular to
          translate [Panic] *)
  sv_to_var : fvar V.SymbolicValueId.Map.t;
      (** Whenever we encounter a new symbolic value (introduced because of a
          symbolic expansion or upon ending an abstraction, for instance) we
          introduce a new variable (with a let-binding). *)
  fresh_fvar_id : unit -> fvar_id;
  fvars : fvar FVarId.Map.t;
      (** The free variables introduced so far.

          Remark: we never remove the variables from here (after closing an
          expression for instance), but it is ok because we generate a fresh,
          unique identifier whenever we insert a free variable. *)
  fvars_tys : ty FVarId.Map.t;  (** The free variables introduced so far *)
  forward_inputs : fvar list;
      (** The input parameters for the forward function corresponding to the
          translated Rust inputs (no fuel, no state). *)
  backward_inputs : fvar list RegionGroupId.Map.t;
      (** The additional input parameters for the backward functions coming from
          the borrows consumed upon ending the lifetime (as a consequence those
          don't include the backward state, if there is one).

          If we split the forward/backward functions: we initialize this map
          when initializing the bs_ctx, because those variables are quantified
          at the definition level. Otherwise, we initialize it upon diving into
          the expressions which are specific to the backward functions. *)
  backward_outputs : fvar list option;
      (** The variables that the backward functions will output, corresponding
          to the borrows they give back (don't include the backward state).

          The translation is done as follows:
          {ul
           {- when we detect the ended input abstraction which corresponds to
              the backward function of the LLBC function we are translating, and
              which consumed the values [consumed_i] (that we need to give back
              to the caller), we introduce:
              {[
                let v_i = consumed_i in
                ...
              ]}
              where the [v_i] are fresh, and are stored in the
              [backward_output].
           }
           {- Then, upon reaching the [Return] node, we introduce:
              {[
                return v_i
              ]}
           }
          }

          The option is [None] before we detect the ended input abstraction, and
          [Some] afterwards. *)
  calls : S.call V.FunCallId.Map.t;
      (** The function calls we encountered so far *)
  loop_ids_map : LoopId.id V.LoopId.Map.t;  (** Ids to use for the loops *)
  mk_return : (bs_ctx -> texpr option -> texpr) option;
      (** Small helper: translate a [return] expression, given a value to
          "return". The translation of [return] depends on the context, and in
          particular depends on whether we are inside a subexpression like a
          loop or not.

          Note that the function consumes an optional expression, which is:
          - [Some] for a forward computation
          - [None] for a backward computation

          We initialize this at [None]. *)
  mk_panic : texpr option;
      (** Small helper: translate a [fail] expression.

          We initialize this at [None]. *)
  mk_continue : (bs_ctx -> texpr -> texpr) option;
  mk_break : (bs_ctx -> texpr -> texpr) option;
  mut_borrow_to_consumed : texpr V.BorrowId.Map.t;
      (** A map from mutable borrows consumed by region abstractions to consumed
          values.

          We use this to compute default values during the translation. We need
          them because of the following case:
          {[
            fn wrap_in_option(x: &'a mut T) -> Option<&'a mut T> {
                Some(x)
              }
          ]}

          The translation should look like so:
          {[
            let wrap_in_option (x : T) : T & (Option T -> T) =
              (x, fun x' => let Some x' = x' in x')
          ]}

          The problem is that the backward function requires unwrapping the
          value from the option, which should have the variant [Some]. This is
          however not something we can easily enforce in the type system at the
          backend side, which means we actually have to generate a match which
          might fail. In particular, for the (unreachable) [None] branch we have
          to produce some value for [x']: we use the original value of [x], like
          so (note that we simplify the [let x' = match ... in ...] expression
          later in a micro-pass):
          {[
            let wrap_in_option (x : T) : T & (Option T -> T) =
              let back x' =
                let x' =
                  match x' with
                  | Some x' -> x'
                  | _ -> x
                in
                x'
                  (x, back)
          ]}

          **Remarks:** We attempted to do store the consumed values directly
          when doing the symbolic execution. It proved cumbersome for the
          following reasons:
          - the symbolic execution is already quite complex, and keeping track
            of those consumed values is actually non trivial especially in the
            context of the join operation (for instance: when we join two
            mutable borrows, which default value should we use?). Generally
            speaking, we want to keep the symbolic execution as tight as
            possible because this is the core of the engine.
          - when we store a value (as a meta-value for instance), we need to
            store the evaluation context at the same time, otherwise we cannot
            translate it to a pure expression in the presence of shared borrows
            (we need the evaluation context to follow the borrow indirections).
            Making this possible would have required an important refactoring of
            the code, as the values would have been mutually recursive with the
            evaluation contexts. On the contrary, computing this information
            when transforming the symbolic trace to a pure model may not be the
            most obvious way of retrieving those consumed values but in practice
            it is quite straightforward and easy to debug. *)
  var_id_to_default : texpr FVarId.Map.t;
      (** Map from the variable identifier of a given back value and introduced
          when deconstructing an ended abstraction, to the default value that we
          can use when introducing the otherwise branch of the deconstructing
          match (see [mut_borrow_to_consumed]). *)
  abs_id_to_info : back_fun_info V.AbsId.Map.t;
      (** This maps the abstraction ids to the corresponding variables we
          introduced in the translation, together with additional information.
      *)
  ignored_abs_ids : V.AbsId.Set.t;
      (** For sanity purposes, we keep track of the region abstractions for
          which we did not introduce any variable in the translation: when we
          fail to lookup a region abstraction in [abs_id_to_fvar] we check that
          it is registered in this set. *)
  meta_symb_places : MetaSymbPlaceSet.t;
      (** Keep track of the [SymbolicPlaces] meta-information that we already
          inserted, to prevent duplication (there tends to be a *lot* of
          meta-information in the generated expressions. *)
}
[@@deriving show]

(* TODO: move *)
let bs_ctx_to_fmt_env (ctx : bs_ctx) : Print.fmt_env =
  {
    crate = ctx.decls_ctx.crate;
    generics = [ ctx.fun_decl.signature.generics ];
    locals = [];
  }

let bs_ctx_to_pure_fmt_env (ctx : bs_ctx) : PrintPure.fmt_env =
  {
    crate = ctx.decls_ctx.crate;
    generics = [ ctx.sg.generics ];
    fvars = FVarId.Map.empty;
    bvars = [];
    bvar_id_counter = 0;
    pbvars = None;
    pbvars_counter = BVarId.zero;
  }

let ctx_generic_args_to_string (ctx : bs_ctx) (args : T.generic_args) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.generic_args_to_string env args

let name_to_string (ctx : bs_ctx) =
  Print.Types.name_to_string (bs_ctx_to_fmt_env ctx)

let symbolic_value_to_string (ctx : bs_ctx) (sv : V.symbolic_value) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.symbolic_value_to_string env sv

let tvalue_to_string (ctx : bs_ctx) (v : V.tvalue) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.tvalue_to_string ~span:(Some ctx.span) env v

let tavalue_to_string (ctx : bs_ctx) ?(with_ended = false) (v : V.tavalue) :
    string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.tavalue_to_string ~span:(Some ctx.span) ~with_ended env v

let tepat_to_string (ctx : bs_ctx) (v : V.tepat) : string =
  let env = bs_ctx_to_fmt_env ctx in
  snd
    (Print.Values.tepat_to_string ~span:(Some ctx.span) env
       Print.Values.empty_evalue_env "" "  " v)

let tevalue_to_string (ctx : bs_ctx) ?(with_ended = false) (v : V.tevalue) :
    string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Values.tevalue_to_string ~span:(Some ctx.span) ~with_ended env
    Print.Values.empty_evalue_env "" "  " v

let pure_ty_to_string (ctx : bs_ctx) (ty : ty) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.ty_to_string env false ty

let fvar_to_string (ctx : bs_ctx) (v : fvar) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.fvar_to_string env v

let ty_to_string (ctx : bs_ctx) (ty : T.ty) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.ty_to_string env ty

let type_decl_to_string (ctx : bs_ctx) (def : T.type_decl) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.type_decl_to_string env def

let pure_type_decl_to_string (ctx : bs_ctx) (def : type_decl) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.type_decl_to_string env def

let texpr_to_string (ctx : bs_ctx) (e : texpr) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.texpr_to_string ~span:(Some ctx.span) env false "" "  " e

let fun_id_to_string (ctx : bs_ctx) (id : A.fun_id) : string =
  let env = bs_ctx_to_fmt_env ctx in
  Print.Types.fun_id_to_string env id

let fun_sig_to_string (ctx : bs_ctx) (sg : fun_sig) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_sig_to_string env sg

let fun_decl_to_string (ctx : bs_ctx) (def : Pure.fun_decl) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_decl_to_string env def

let tpat_to_string (ctx : bs_ctx) (p : Pure.tpat) : string =
  let env = bs_ctx_to_pure_fmt_env ctx in
  PrintPure.tpat_to_string ~span:ctx.span env p

let abs_to_string ?(with_ended : bool = false) (ctx : bs_ctx) (abs : V.abs) :
    string =
  let env = bs_ctx_to_fmt_env ctx in
  let verbose = false in
  let indent = "" in
  let indent_incr = "  " in
  Print.Values.abs_to_string ~span:(Some ctx.span) ~with_ended env verbose
    indent indent_incr abs

let bs_ctx_expr_to_string (ctx : bs_ctx) (e : S.expr) : string =
  let env = bs_ctx_to_fmt_env ctx in
  expr_to_string env "" "  " e

let bs_ctx_expansion_to_string (ctx : bs_ctx) (scrut : V.symbolic_value)
    (e : S.expansion) : string =
  let env = bs_ctx_to_fmt_env ctx in
  expansion_to_string env "" "  " scrut e

let ctx_get_effect_info_for_bid (ctx : bs_ctx) (bid : RegionGroupId.id option) :
    fun_effect_info =
  match bid with
  | None -> ctx.sg.fun_ty.fwd_info.effect_info
  | Some bid ->
      let back_sg = RegionGroupId.Map.find bid ctx.sg.fun_ty.back_sg in
      back_sg.effect_info

let ctx_get_effect_info (ctx : bs_ctx) : fun_effect_info =
  ctx_get_effect_info_for_bid ctx ctx.bid

let bs_ctx_lookup_llbc_type_decl (id : TypeDeclId.id) (ctx : bs_ctx) :
    T.type_decl =
  TypeDeclId.Map.find id ctx.type_ctx.llbc_type_decls

let bs_ctx_lookup_llbc_fun_decl (id : A.FunDeclId.id) (ctx : bs_ctx) :
    A.fun_decl =
  A.FunDeclId.Map.find id ctx.fun_ctx.llbc_fun_decls

let bs_ctx_lookup_type_decl (id : TypeDeclId.id) (ctx : bs_ctx) : type_decl =
  TypeDeclId.Map.find id ctx.type_ctx.type_decls

(** This generates a fresh variable **which is not to be linked to any symbolic
    value** *)
let fresh_var (basename : string option) (ty : ty) (ctx : bs_ctx) :
    bs_ctx * fvar =
  (* Generate the fresh variable *)
  let id = ctx.fresh_fvar_id () in
  let var = { id; basename; ty } in
  (* Insert in the context *)
  let ctx = { ctx with fvars = FVarId.Map.add id var ctx.fvars } in
  let ctx = { ctx with fvars_tys = FVarId.Map.add id var.ty ctx.fvars_tys } in
  (* Return *)
  (ctx, var)

let fresh_vars (vars : (string option * ty) list) (ctx : bs_ctx) :
    bs_ctx * fvar list =
  List.fold_left_map (fun ctx (name, ty) -> fresh_var name ty ctx) ctx vars

let fresh_opt_vars (vars : (string option * ty) option list) (ctx : bs_ctx) :
    bs_ctx * fvar option list =
  List.fold_left_map
    (fun ctx var ->
      match var with
      | None -> (ctx, None)
      | Some (name, ty) ->
          let ctx, var = fresh_var name ty ctx in
          (ctx, Some var))
    ctx vars

(** IMPORTANT: do not use this one directly, but rather
    {!symbolic_value_to_texpr} *)
let lookup_var_for_symbolic_value (id : V.symbolic_value_id) (ctx : bs_ctx) :
    fvar option =
  match V.SymbolicValueId.Map.find_opt id ctx.sv_to_var with
  | Some v -> Some v
  | None ->
      [%save_error] ctx.span
        ("Could not find var for symbolic value: "
        ^ V.SymbolicValueId.to_string id);
      None

let mk_closed_checked_let file line ctx can_fail pat bound next =
  mk_closed_checked_let file line ctx.span can_fail pat bound next

let mk_closed_checked_lets file line ctx can_fail pat_bounds next =
  mk_closed_checked_lets file line ctx.span can_fail pat_bounds next
