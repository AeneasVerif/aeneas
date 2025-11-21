open Pure

(** Default logger *)
let log = Logging.pure_utils_log

module TyOrd = struct
  type t = ty

  let compare = compare_ty
  let to_string = show_ty
  let pp_t = pp_ty
  let show_t = show_ty
end

module TyMap = Collections.MakeMap (TyOrd)

module RegularFunIdOrderedType = struct
  type t = regular_fun_id

  let compare = compare_regular_fun_id
  let to_string = show_regular_fun_id
  let pp_t = pp_regular_fun_id
  let show_t = show_regular_fun_id
end

module RegularFunIdMap = Collections.MakeMap (RegularFunIdOrderedType)

(** We use this type as a key for lookups *)
type regular_fun_id_not_loop = LlbcAst.fun_id * RegionGroupId.id option
[@@deriving show, ord]

(** We use this type as a key for lookups *)
type fun_loop_id = FunDeclId.id * LoopId.id option [@@deriving show, ord]

module RegularFunIdNotLoopOrderedType = struct
  type t = regular_fun_id_not_loop

  let compare = compare_regular_fun_id_not_loop
  let to_string = show_regular_fun_id_not_loop
  let pp_t = pp_regular_fun_id_not_loop
  let show_t = show_regular_fun_id_not_loop
end

module RegularFunIdNotLoopMap =
  Collections.MakeMap (RegularFunIdNotLoopOrderedType)

module FunOrOpIdOrderedType = struct
  type t = fun_or_op_id

  let compare = compare_fun_or_op_id
  let to_string = show_fun_or_op_id
  let pp_t = pp_fun_or_op_id
  let show_t = show_fun_or_op_id
end

module FunOrOpIdMap = Collections.MakeMap (FunOrOpIdOrderedType)
module FunOrOpIdSet = Collections.MakeSet (FunOrOpIdOrderedType)

module FunLoopIdOrderedType = struct
  type t = fun_loop_id

  let compare = compare_fun_loop_id
  let to_string = show_fun_loop_id
  let pp_t = pp_fun_loop_id
  let show_t = show_fun_loop_id
end

module FunLoopIdMap = Collections.MakeMap (FunLoopIdOrderedType)
module FunLoopIdSet = Collections.MakeSet (FunLoopIdOrderedType)

module ExprOrderedType = struct
  type t = expr

  let compare = compare_expr
  let to_string = show_expr
  let pp_t = pp_expr
  let show_t = show_expr
end

module ExprMap = Collections.MakeMap (ExprOrderedType)
module ExprSet = Collections.MakeSet (ExprOrderedType)

module TExprOrderedType = struct
  type t = texpr

  let compare = compare_texpr
  let to_string = show_texpr
  let pp_t = pp_texpr
  let show_t = show_texpr
end

module TExprMap = Collections.MakeMap (TExprOrderedType)
module TExprSet = Collections.MakeSet (TExprOrderedType)

(** A pure environment where we do not open binders.

    Every map binds a bound variable id to a variable, and the list represents
    the stack of binders in which we dived. *)
type benv = var BVarId.Map.t list

(** A pure environment where we *do* open binders by introducing fresh
    variables. *)
type fenv = var FVarId.Map.t

(** An iter visitor for expressions where the environment is the current
    scope/level (we increment it whenever we enter a binder) *)
class ['self] scoped_iter_expr =
  object (self : 'self)
    inherit [_] iter_expr

    method! visit_Switch scope e body =
      let scope' = scope + 1 in
      self#visit_texpr scope e;
      match body with
      | If (e0, e1) ->
          self#visit_texpr scope' e0;
          self#visit_texpr scope' e1
      | Match branches ->
          List.iter
            (fun (b : match_branch) ->
              let { pat; branch } = b in
              self#visit_tpat scope pat;
              self#visit_texpr scope' branch)
            branches

    method! visit_Let scope _ pat bound next =
      let scope' = scope + 1 in
      self#visit_tpat scope pat;
      self#visit_texpr scope bound;
      self#visit_texpr scope' next

    method! visit_Lambda scope pat body =
      let scope' = scope + 1 in
      self#visit_tpat scope pat;
      self#visit_texpr scope' body

    method! visit_loop_body scope body =
      let { inputs; loop_body } = body in
      (* Visit the patterns *)
      List.iter (self#visit_tpat scope) inputs;
      (* Enter the inner expression *)
      let scope' = scope + 1 in
      self#visit_texpr scope' loop_body
  end

(** A map visitor for expressions where the environment is the current
    scope/level (we increment it whenever we enter a binder) *)
class ['self] scoped_map_expr =
  object (self : 'self)
    inherit [_] map_expr

    method! visit_Switch scope e body =
      let e = self#visit_texpr scope e in
      let body =
        match body with
        | If (e0, e1) ->
            If (self#visit_texpr scope e0, self#visit_texpr scope e1)
        | Match branches ->
            Match
              (List.map
                 (fun (b : match_branch) ->
                   let { pat; branch } = b in
                   let pat = self#visit_tpat scope pat in
                   let branch = self#visit_texpr (scope + 1) branch in
                   { pat; branch })
                 branches)
      in
      Switch (e, body)

    method! visit_Let scope monadic pat bound next =
      let scope' = scope + 1 in
      let pat = self#visit_tpat scope pat in
      let bound = self#visit_texpr scope bound in
      let next = self#visit_texpr scope' next in
      Let (monadic, pat, bound, next)

    method! visit_Lambda scope pat body =
      let scope' = scope + 1 in
      let pat = self#visit_tpat scope pat in
      let body = self#visit_texpr scope' body in
      Lambda (pat, body)

    method! visit_loop_body scope body =
      let { inputs; loop_body } = body in
      (* Visit the patterns *)
      let inputs = List.map (self#visit_tpat scope) inputs in
      (* Enter the inner expression *)
      let scope' = scope + 1 in
      let loop_body = self#visit_texpr scope' loop_body in
      { inputs; loop_body }
  end

let mk_fresh_fvar (fresh_fvar_id : unit -> fvar_id) ?(basename = None) (ty : ty)
    : fvar =
  let id = fresh_fvar_id () in
  { id; basename; ty }

let opt_dest_arrow_ty (ty : ty) : (ty * ty) option =
  match ty with
  | TArrow (arg_ty, ret_ty) -> Some (arg_ty, ret_ty)
  | _ -> None

let as_tuple_ty file line span (ty : ty) : ty list =
  match ty with
  | TAdt (TTuple, generics) -> generics.types
  | _ -> Errors.internal_error file line span

let is_tuple_ty (ty : ty) : bool =
  match ty with
  | TAdt (TTuple, _) -> true
  | _ -> false

let is_arrow_ty (ty : ty) : bool = Option.is_some (opt_dest_arrow_ty ty)

let opt_dest_result_ty (ty : ty) : ty option =
  match ty with
  | TAdt
      ( TBuiltin TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) -> Some ty
  | _ -> None

let dest_result_ty span (ty : ty) : ty =
  match opt_dest_result_ty ty with
  | None -> [%craise] span "Not a result type"
  | Some ty -> ty

let is_result_ty (ty : ty) : bool = Option.is_some (opt_dest_result_ty ty)

let dest_arrow_ty (span : Meta.span) (ty : ty) : ty * ty =
  match opt_dest_arrow_ty ty with
  | Some (arg_ty, ret_ty) -> (arg_ty, ret_ty)
  | None -> [%craise] span "Not an arrow type"

let compute_literal_type (cv : literal) : literal_type =
  match cv with
  | VScalar (SignedScalar (ty, _)) -> TInt ty
  | VScalar (UnsignedScalar (ty, _)) -> TUInt ty
  | VBool _ -> TBool
  | VChar _ -> TChar
  | VFloat _ | VStr _ | VByteStr _ ->
      [%craise_opt_span] None
        "Float, string and byte string literals are unsupported"

let fvar_get_id (v : fvar) : fvar_id = v.id

let mk_tpat_from_literal (cv : literal) : tpat =
  let ty = TLiteral (compute_literal_type cv) in
  { pat = PConstant cv; ty }

let mk_tag (msg : string) (next_e : texpr) : texpr =
  let e = Meta (Tag msg, next_e) in
  let ty = next_e.ty in
  { e; ty }

let empty_generic_params : generic_params =
  { types = []; const_generics = []; trait_clauses = [] }

let empty_generic_args : generic_args =
  { types = []; const_generics = []; trait_refs = [] }

let mk_generic_args_from_types (types : ty list) : generic_args =
  { types; const_generics = []; trait_refs = [] }

type subst = {
  ty_subst : TypeVarId.id -> ty;
  cg_subst : ConstGenericVarId.id -> const_generic;
  tr_subst : TraitClauseId.id -> trait_instance_id;
  tr_self : trait_instance_id;
}

class ['self] subst_visitor =
  object (_self : 'self)
    inherit [_] map_expr

    method! visit_TVar subst var =
      subst.ty_subst (Substitute.expect_free_var None var)

    method! visit_CgVar subst var =
      subst.cg_subst (Substitute.expect_free_var None var)

    method! visit_Clause subst var =
      subst.tr_subst (Substitute.expect_free_var None var)

    method! visit_Self subst = subst.tr_self
  end

(** Type substitution *)
let ty_substitute (subst : subst) (ty : ty) : ty =
  let visitor =
    object
      inherit [_] subst_visitor
    end
  in
  visitor#visit_ty subst ty

let generic_args_substitute (subst : subst) (generics : generic_args) :
    generic_args =
  let visitor =
    object
      inherit [_] subst_visitor
    end
  in
  visitor#visit_generic_args subst generics

let make_type_subst (vars : type_param list) (tys : ty list) :
    TypeVarId.id -> ty =
  let var_ids = List.map (fun k -> (k : type_param).index) vars in
  let mp = TypeVarId.Map.of_list (List.combine var_ids tys) in
  fun id -> TypeVarId.Map.find id mp

let make_const_generic_subst (vars : const_generic_param list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  Substitute.make_const_generic_subst_from_vars vars cgs

let make_trait_subst (clauses : trait_param list) (refs : trait_ref list) :
    TraitClauseId.id -> trait_instance_id =
  let clauses = List.map (fun x -> x.clause_id) clauses in
  let refs = List.map (fun (x : trait_ref) -> x.trait_id) refs in
  let mp = TraitClauseId.Map.of_list (List.combine clauses refs) in
  fun id -> TraitClauseId.Map.find id mp

(** Like [make_subst_from_generics] but also substitute the [Self] clause. Use
    this when substituting for trait generics. *)
let make_subst_from_generics_for_trait (params : generic_params)
    (tr_self : trait_instance_id) (args : generic_args) : subst =
  let ty_subst = make_type_subst params.types args.types in
  let cg_subst =
    make_const_generic_subst params.const_generics args.const_generics
  in
  let tr_subst = make_trait_subst params.trait_clauses args.trait_refs in
  { ty_subst; cg_subst; tr_subst; tr_self }

let make_subst_from_generics (params : generic_params) (args : generic_args) :
    subst =
  make_subst_from_generics_for_trait params
    (UnknownTrait "make_subst_from_generics") args

(** Retrieve the list of fields for the given variant of a
    {!type:Aeneas.Pure.type_decl}.

    Raises [Invalid_argument] if the arguments are incorrect. *)
let type_decl_get_fields (def : type_decl)
    (opt_variant_id : VariantId.id option) : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      let opt_variant_id =
        Print.option_to_string VariantId.to_string opt_variant_id
      in
      raise
        (Invalid_argument
           ("The variant id should be [Some] if and only if the definition is \
             an enumeration:\n\
             - def.name: " ^ def.name ^ "\n- opt_variant_id: " ^ opt_variant_id
           ))

(** Instantiate the type variables for the chosen variant in an ADT definition,
    and return the list of the types of its fields *)
let type_decl_get_instantiated_fields_types (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  let subst = make_subst_from_generics def.generics generics in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.field_ty) fields

let fun_sig_substitute (subst : subst) (sg : fun_sig) : inst_fun_sig =
  let subst = ty_substitute subst in
  let inputs = List.map subst sg.inputs in
  let output = subst sg.output in
  { inputs; output }

(** We use this to check whether we need to add parentheses around expressions.
    We only look for outer monadic let-bindings. This is used when printing the
    branches of [if ... then ... else ...].

    Rem.: this function will *fail* if there are {!Pure.Loop} nodes (you should
    call it on an expression where those nodes have been eliminated). *)
let rec let_group_requires_parentheses (span : Meta.span) (e : texpr) : bool =
  match e.e with
  | BVar _ | FVar _ | CVar _ | Const _ | App _ | Qualif _ | StructUpdate _ ->
      false
  | Let (monadic, _, _, next_e) ->
      if monadic then true else let_group_requires_parentheses span next_e
  | Switch (_, _) -> false
  | Meta (_, next_e) -> let_group_requires_parentheses span next_e
  | Lambda (_, _) ->
      (* Being conservative here *)
      true
  | Loop _ ->
      (* Should have been eliminated *)
      [%craise] span "Unreachable"
  | EError (span, msg) ->
      [%craise_opt_span] span
        msg (* TODO : check if true should'nt be returned instead ? *)

let texpr_requires_parentheses span e =
  match Config.backend () with
  | FStar | Lean -> false
  | Coq | HOL4 -> let_group_requires_parentheses span e

let is_fvar (e : texpr) : bool =
  match e.e with
  | FVar _ -> true
  | _ -> false

let as_fvar (span : Meta.span) (e : texpr) : fvar_id =
  match e.e with
  | FVar v -> v
  | _ -> [%craise] span "Not an fvar"

let as_qualif (span : Meta.span) (e : texpr) : qualif =
  match e.e with
  | Qualif qualif -> qualif
  | _ -> [%craise] span "Not a qualif"

let is_bvar (e : texpr) : bool =
  match e.e with
  | BVar _ -> true
  | _ -> false

let as_bvar (span : Meta.span) (e : texpr) : bvar =
  match e.e with
  | BVar v -> v
  | _ -> [%craise] span "Not a bvar"

let is_cvar (e : texpr) : bool =
  match e.e with
  | CVar _ -> true
  | _ -> false

let is_pat_open (p : tpat) : bool =
  match p.pat with
  | POpen _ -> true
  | _ -> false

let as_pat_open file line span (p : tpat) : fvar * mplace option =
  match p.pat with
  | POpen (v, pm) -> (v, pm)
  | _ -> Errors.craise file line span "Not an open binder"

let as_pat_open_fvar_id file line span (p : tpat) : fvar_id =
  (fst (as_pat_open file line span p)).id

let as_opt_pat_bound (p : tpat) : (var * mplace option) option =
  match p.pat with
  | PBound (v, mp) -> Some (v, mp)
  | _ -> None

let as_pat_bound (span : Meta.span) (p : tpat) : var * mplace option =
  match as_opt_pat_bound p with
  | None -> [%craise] span "Not a var"
  | Some (v, mp) -> (v, mp)

let is_pat_bound (p : tpat) : bool = Option.is_some (as_opt_pat_bound p)

let as_opt_pat_tuple (p : tpat) : tpat list option =
  match p with
  | { pat = PAdt { variant_id = None; fields }; ty = TAdt (TTuple, _) } ->
      Some fields
  | _ -> None

let as_pat_tuple file line span (p : tpat) : tpat list =
  match as_opt_pat_tuple p with
  | Some fields -> fields
  | None -> Errors.craise file line span "Not a tuple"

(** Replace all the ignored variables in a pattern with free variables *)
let tpat_replace_ignored_vars_with_free_vars (fresh_fvar_id : unit -> fvar_id)
    (p : tpat) : tpat =
  let visitor =
    object
      inherit [_] map_tpat as super

      method! visit_tpat env p =
        match p.pat with
        | PIgnored ->
            let pat = { id = fresh_fvar_id (); basename = None; ty = p.ty } in
            { p with pat = POpen (pat, None) }
        | _ -> super#visit_tpat env p
    end
  in
  visitor#visit_tpat () p

let is_pat_tuple (p : tpat) : bool = Option.is_some (as_opt_pat_tuple p)

let is_global (e : texpr) : bool =
  match e.e with
  | Qualif { id = Global _; _ } -> true
  | _ -> false

let is_const (e : texpr) : bool =
  match e.e with
  | Const _ -> true
  | _ -> false

let is_adt_cons (e : texpr) : bool =
  match e.e with
  | Qualif { id = AdtCons _; _ } -> true
  | _ -> false

let is_fail_panic (e : expr) : bool =
  match e with
  | App
      ( {
          e =
            Qualif
              {
                id =
                  AdtCons
                    { adt_id = TBuiltin TResult; variant_id = Some res_id };
                generics = _;
              };
          ty = _;
        },
        {
          e =
            Qualif
              {
                id =
                  AdtCons
                    { adt_id = TBuiltin TError; variant_id = Some error_id };
                generics = _;
              };
          ty = _;
        } ) -> res_id = result_fail_id && error_id = error_failure_id
  | _ -> false

let ty_as_adt (span : Meta.span) (ty : ty) : type_id * generic_args =
  match ty with
  | TAdt (id, generics) -> (id, generics)
  | _ -> [%craise] span "Not an ADT"

let ty_as_opt_result (ty : ty) : ty option =
  match ty with
  | TAdt
      ( TBuiltin TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) -> Some ty
  | _ -> None

let ty_as_opt_array (ty : ty) : (ty * const_generic) option =
  match ty with
  | TAdt
      ( TBuiltin TArray,
        { types = [ ty ]; const_generics = [ n ]; trait_refs = [] } ) ->
      Some (ty, n)
  | _ -> None

let ty_as_array (span : Meta.span) (ty : ty) : ty * const_generic =
  match ty_as_opt_array ty with
  | Some (ty, n) -> (ty, n)
  | None -> [%craise] span "Not an ADT"

let ty_as_opt_slice (ty : ty) : ty option =
  match ty with
  | TAdt
      (TBuiltin TSlice, { types = [ ty ]; const_generics = []; trait_refs = [] })
    -> Some ty
  | _ -> None

let ty_as_slice (span : Meta.span) (ty : ty) : ty =
  match ty_as_opt_slice ty with
  | Some ty -> ty
  | None -> [%craise] span "Not an ADT"

let ty_as_opt_arrow (ty : ty) : (ty * ty) option =
  match ty with
  | TArrow (ty0, ty1) -> Some (ty0, ty1)
  | _ -> None

(** Remove the external occurrences of {!Meta} *)
let rec unmeta (e : texpr) : texpr =
  match e.e with
  | Meta (_, e) -> unmeta e
  | _ -> e

(** Remove *all* the meta information *)
let remove_meta (e : texpr) : texpr =
  let obj =
    object
      inherit [_] map_expr as super
      method! visit_Meta env _ e = super#visit_expr env e.e
    end
  in
  obj#visit_texpr () e

let mk_arrow (ty0 : ty) (ty1 : ty) : ty = TArrow (ty0, ty1)

(** Construct a type as a list of arrows: ty1 -> ... tyn *)
let mk_arrows (inputs : ty list) (output : ty) =
  let rec aux (tys : ty list) : ty =
    match tys with
    | [] -> output
    | ty :: tys' -> TArrow (ty, aux tys')
  in
  aux inputs

(** Destruct an [App] expression into an expression and a list of arguments.

    We simply destruct the expression as long as it is of the form [App (f, x)].
*)
let destruct_apps (e : texpr) : texpr * texpr list =
  let rec aux (args : texpr list) (e : texpr) : texpr * texpr list =
    match e.e with
    | App (f, x) -> aux (x :: args) f
    | _ -> (e, args)
  in
  aux [] e

(** Make an [App (app, arg)] expr *)
let mk_app (file : string) (line : int) (span : Meta.span) (app : texpr)
    (arg : texpr) : texpr =
  let raise_or_return msg =
    (* We shouldn't get there, so we save an error (and eventually raise an exception) *)
    Errors.save_error file line span msg;
    let e = App (app, arg) in
    (* Dummy type - TODO: introduce an error type *)
    let ty = app.ty in
    { e; ty }
  in
  match app.ty with
  | TArrow (ty0, ty1) ->
      (* Sanity check *)
      if
        (* TODO: we need to normalize the types *)
        !Config.type_check_pure_code && ty0 <> arg.ty
      then raise_or_return "App: wrong input type"
      else
        let e = App (app, arg) in
        let ty = ty1 in
        { e; ty }
  | _ -> raise_or_return "Expected an arrow type"

(** The reverse of {!destruct_apps} *)
let mk_apps (file : string) (line : int) (span : Meta.span) (app : texpr)
    (args : texpr list) : texpr =
  List.fold_left (fun app arg -> mk_app file line span app arg) app args

let mk_qualif_apps (file : string) (line : int) (span : Meta.span)
    (app : qualif) (args : texpr list) (ty : ty) : texpr =
  let app =
    {
      e = Qualif app;
      ty = mk_arrows (List.map (fun (e : texpr) -> e.ty) args) ty;
    }
  in
  mk_apps file line span app args

(** Destruct an expression into a qualif identifier and a list of arguments, *
    if possible *)
let opt_destruct_qualif_apps (e : texpr) : (qualif * texpr list) option =
  let app, args = destruct_apps e in
  match app.e with
  | Qualif qualif -> Some (qualif, args)
  | _ -> None

(** Destruct an expression into a qualif identifier and a list of arguments *)
let destruct_qualif_apps (e : texpr) : qualif * texpr list =
  Option.get (opt_destruct_qualif_apps e)

(** Destruct an expression into a function call, if possible *)
let opt_destruct_function_call (e : texpr) :
    (fun_or_op_id * generic_args * texpr list) option =
  match opt_destruct_qualif_apps e with
  | None -> None
  | Some (qualif, args) -> (
      match qualif.id with
      | FunOrOp fun_id -> Some (fun_id, qualif.generics, args)
      | _ -> None)

let opt_destruct_result (span : Meta.span) (ty : ty) : ty option =
  match ty with
  | TAdt (TBuiltin TResult, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      Some (Collections.List.to_cons_nil generics.types)
  | _ -> None

let destruct_result (span : Meta.span) (ty : ty) : ty =
  Option.get (opt_destruct_result span ty)

let opt_destruct_tuple (span : Meta.span) (ty : ty) : ty list option =
  match ty with
  | TAdt (TTuple, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      Some generics.types
  | _ -> None

let opt_destruct_tuple_texpr (span : Meta.span) (e : texpr) : texpr list option
    =
  match e.ty with
  | TAdt (TTuple, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      let cons, fields = destruct_apps e in
      [%sanity_check] span
        (match cons.e with
        | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ } ->
            List.length generics.types = List.length fields
        | _ -> true);
      Some fields
  | _ -> None

let destruct_tuple_texpr file line (span : Meta.span) (e : texpr) : texpr list =
  match opt_destruct_tuple_texpr span e with
  | None -> Errors.internal_error file line span
  | Some xl -> xl

let try_destruct_tuple_texpr span e =
  match opt_destruct_tuple_texpr span e with
  | None -> [ e ]
  | Some fields -> fields

let try_destruct_tuple span ty =
  match opt_destruct_tuple span ty with
  | None -> [ ty ]
  | Some tys -> tys

let opt_destruct_tuple_tpat (span : Meta.span) (e : tpat) : tpat list option =
  match e.ty with
  | TAdt (TTuple, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      begin
        match e.pat with
        | PAdt { fields; _ } -> Some fields
        | _ -> None
      end
  | _ -> None

let try_destruct_tuple_tpat span e =
  match opt_destruct_tuple_tpat span e with
  | None -> [ e ]
  | Some fields -> fields

(** Attempt to destruct a tuple pattern.

    If it is not a tuple, we return a singleton list (the original pattern). We
    have a special case for the ignored pattern, if its type is a tuple: we
    decompose it into a tuple of dummies, and thus return a list of ignored
    patterns. *)
let try_destruct_tuple_or_ignored_tpat span (e : tpat) =
  match e.ty with
  | TAdt (TTuple, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      begin
        match e.pat with
        | PAdt { fields; _ } -> fields
        | PIgnored ->
            List.map (fun ty -> ({ pat = PIgnored; ty } : tpat)) generics.types
        | _ -> [%internal_error] span
      end
  | _ -> [ e ]

let try_destruct_tuple_or_ignored_or_open_tpat span (e : tpat) =
  match e.ty with
  | TAdt (TTuple, generics) ->
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      begin
        match e.pat with
        | PAdt { fields; _ } -> fields
        | PIgnored ->
            List.map (fun ty -> ({ pat = PIgnored; ty } : tpat)) generics.types
        | POpen _ -> [ e ]
        | _ -> [%internal_error] span
      end
  | _ -> [ e ]

let destruct_arrow (span : Meta.span) (ty : ty) : ty * ty =
  match ty with
  | TArrow (ty0, ty1) -> (ty0, ty1)
  | _ -> [%craise] span "Not an arrow type"

let rec destruct_arrows (ty : ty) : ty list * ty =
  match ty with
  | TArrow (ty0, ty1) ->
      let tys, out_ty = destruct_arrows ty1 in
      (ty0 :: tys, out_ty)
  | _ -> ([], ty)

let get_switch_body_ty (sb : switch_body) : ty =
  match sb with
  | If (e_then, _) -> e_then.ty
  | Match branches ->
      (* There should be at least one branch *)
      (List.hd branches).branch.ty

let map_switch_body_branches (f : texpr -> texpr) (sb : switch_body) :
    switch_body =
  match sb with
  | If (e_then, e_else) -> If (f e_then, f e_else)
  | Match branches ->
      Match
        (List.map
           (fun (b : match_branch) -> { b with branch = f b.branch })
           branches)

let iter_switch_body_branches (f : texpr -> unit) (sb : switch_body) : unit =
  match sb with
  | If (e_then, e_else) ->
      f e_then;
      f e_else
  | Match branches -> List.iter (fun (b : match_branch) -> f b.branch) branches

(** Make a "simplified" tuple type from a list of types:
    - if there is exactly one type, just return it
    - if there is > one type: wrap them in a tuple *)
let mk_simpl_tuple_ty (tys : ty list) : ty =
  match tys with
  | [ ty ] -> ty
  | _ -> TAdt (TTuple, mk_generic_args_from_types tys)

let mk_bool_ty : ty = TLiteral TBool
let mk_unit_ty : ty = TAdt (TTuple, empty_generic_args)
let ty_is_unit ty : bool = ty = mk_unit_ty

let mk_bool_value (b : bool) : texpr =
  { e = Const (VBool b); ty = TLiteral TBool }

let mk_true : texpr = mk_bool_value true
let mk_false : texpr = mk_bool_value false

let mk_unit_texpr : texpr =
  let id = AdtCons { adt_id = TTuple; variant_id = None } in
  let qualif = { id; generics = empty_generic_args } in
  let e = Qualif qualif in
  let ty = mk_unit_ty in
  { e; ty }

let mk_texpr_from_fvar (v : fvar) : texpr =
  let e = FVar v.id in
  let ty = v.ty in
  { e; ty }

let mk_tpat_from_fvar (mp : mplace option) (v : fvar) : tpat =
  let pat = POpen (v, mp) in
  let ty = v.ty in
  { pat; ty }

let mk_ignored_pat (ty : ty) : tpat =
  let pat = PIgnored in
  { pat; ty }

let is_ignored_pat (p : tpat) : bool =
  match p.pat with
  | PIgnored -> true
  | _ -> false

let mk_emeta (m : emeta) (e : texpr) : texpr =
  let ty = e.ty in
  let e = Meta (m, e) in
  { e; ty }

let mk_mplace_texpr (mp : mplace) (e : texpr) : texpr = mk_emeta (MPlace mp) e

let mk_opt_mplace_texpr (mp : mplace option) (e : texpr) : texpr =
  match mp with
  | None -> e
  | Some mp -> mk_mplace_texpr mp e

let mk_switch file line span (scrut : texpr) (body : switch_body) : texpr =
  let ty =
    match body with
    | If (e, _) -> e.ty
    | Match [] ->
        Errors.craise file line span "Unexpected: match with no branches"
    | Match (br :: _) -> br.branch.ty
  in
  { e = Switch (scrut, body); ty }

(** Make a "simplified" tuple value from a list of values:
    - if there is exactly one value, just return it
    - if there is > one value: wrap them in a tuple *)
let mk_simpl_tuple_pat (vl : tpat list) : tpat =
  match vl with
  | [ v ] -> v
  | _ ->
      let tys = List.map (fun (v : tpat) -> v.ty) vl in
      let ty = TAdt (TTuple, mk_generic_args_from_types tys) in
      let pat = PAdt { variant_id = None; fields = vl } in
      { pat; ty }

(** Similar to {!mk_simpl_tuple_pat} *)
let mk_simpl_tuple_texpr (span : Meta.span) (vl : texpr list) : texpr =
  match vl with
  | [ v ] -> v
  | _ ->
      (* Compute the types of the fields, and the type of the tuple constructor *)
      let tys = List.map (fun (v : texpr) -> v.ty) vl in
      let ty = TAdt (TTuple, mk_generic_args_from_types tys) in
      let ty = mk_arrows tys ty in
      (* Construct the tuple constructor qualifier *)
      let id = AdtCons { adt_id = TTuple; variant_id = None } in
      let qualif = { id; generics = mk_generic_args_from_types tys } in
      (* Put everything together *)
      let cons = { e = Qualif qualif; ty } in
      [%add_loc] mk_apps span cons vl

let mk_adt_pat (adt_ty : ty) (variant_id : VariantId.id option) (vl : tpat list)
    : tpat =
  let pat = PAdt { variant_id; fields = vl } in
  { pat; ty = adt_ty }

let mk_adt_texpr (span : span) (adt_ty : ty) (variant_id : VariantId.id option)
    (fields : texpr list) : texpr =
  let adt_id, generics = ty_as_adt span adt_ty in
  let qualif : expr =
    Qualif { id = AdtCons { adt_id; variant_id }; generics }
  in
  let qualif_ty =
    mk_arrows (List.map (fun (f : texpr) -> f.ty) fields) adt_ty
  in
  let qualif = { e = qualif; ty = qualif_ty } in
  [%add_loc] mk_apps span qualif fields

let mk_adt_proj (span : span) (adt : texpr) (field_id : field_id)
    (field_ty : ty) : texpr =
  let adt_id, generics = ty_as_adt span adt.ty in
  let qualif = Qualif { id = Proj { adt_id; field_id }; generics } in
  let qualif = { e = qualif; ty = mk_arrow adt.ty field_ty } in
  [%add_loc] mk_app span qualif adt

let ty_as_integer (span : Meta.span) (t : ty) : T.integer_type =
  match t with
  | TLiteral (TInt int_ty) -> Signed int_ty
  | TLiteral (TUInt int_ty) -> Unsigned int_ty
  | _ -> [%craise] span "Unreachable"

let ty_as_literal (span : Meta.span) (t : ty) : T.literal_type =
  match t with
  | TLiteral ty -> ty
  | _ -> [%craise] span "Unreachable"

let mk_result_ty (ty : ty) : ty =
  TAdt (TBuiltin TResult, mk_generic_args_from_types [ ty ])

let mk_error_ty : ty = TAdt (TBuiltin TError, empty_generic_args)
let mk_fuel_ty : ty = TAdt (TBuiltin TFuel, empty_generic_args)

let mk_error (error : VariantId.id) : texpr =
  let ty = mk_error_ty in
  let id = AdtCons { adt_id = TBuiltin TError; variant_id = Some error } in
  let qualif = { id; generics = empty_generic_args } in
  let e = Qualif qualif in
  { e; ty }

let unwrap_result_ty (span : Meta.span) (ty : ty) : ty =
  match ty with
  | TAdt
      ( TBuiltin TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) -> ty
  | _ -> [%craise] span "not a result type"

let unwrap_result_or_loop_result_ty_with_loc file line (span : Meta.span)
    (ty : ty) : ty =
  match ty with
  | TAdt
      ( TBuiltin TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) -> ty
  | TAdt
      ( TBuiltin TLoopResult,
        { types = [ _; break_ty ]; const_generics = []; trait_refs = [] } ) ->
      break_ty
  | _ -> Errors.craise file line span "not a result type"

let try_unwrap_loop_result (ty : ty) : (ty * ty) option =
  match ty with
  | TAdt
      ( TBuiltin TLoopResult,
        {
          types = [ continue_ty; break_ty ];
          const_generics = [];
          trait_refs = [];
        } ) -> Some (continue_ty, break_ty)
  | _ -> None

let mk_result_fail_texpr (span : Meta.span) (error : texpr) (ty : ty) : texpr =
  let type_args = [ ty ] in
  let generics = mk_generic_args_from_types type_args in
  let ty = TAdt (TBuiltin TResult, generics) in
  let id =
    AdtCons { adt_id = TBuiltin TResult; variant_id = Some result_fail_id }
  in
  let qualif = { id; generics } in
  let cons_e = Qualif qualif in
  let cons_ty = mk_arrow error.ty ty in
  let cons = { e = cons_e; ty = cons_ty } in
  [%add_loc] mk_app span cons error

let mk_result_fail_texpr_with_error_id (span : Meta.span) (error : VariantId.id)
    (ty : ty) : texpr =
  let error = mk_error error in
  mk_result_fail_texpr span error ty

let mk_result_ok_texpr (span : Meta.span) (v : texpr) : texpr =
  let type_args = [ v.ty ] in
  let generics = mk_generic_args_from_types type_args in
  let ty = TAdt (TBuiltin TResult, generics) in
  let id =
    AdtCons { adt_id = TBuiltin TResult; variant_id = Some result_ok_id }
  in
  let qualif = { id; generics } in
  let cons_e = Qualif qualif in
  let cons_ty = mk_arrow v.ty ty in
  let cons = { e = cons_e; ty = cons_ty } in
  [%add_loc] mk_app span cons v

(** Create a [Fail err] pattern which captures the error *)
let mk_result_fail_pat (error_pat : pat) (ty : ty) : tpat =
  let error_pat : tpat = { pat = error_pat; ty = mk_error_ty } in
  let ty = TAdt (TBuiltin TResult, mk_generic_args_from_types [ ty ]) in
  let pat = PAdt { variant_id = Some result_fail_id; fields = [ error_pat ] } in
  { pat; ty }

(** Create a [Fail _] pattern (we ignore the error) *)
let mk_result_fail_pat_ignore_error (ty : ty) : tpat =
  let error_pat : pat = PIgnored in
  mk_result_fail_pat error_pat ty

let mk_result_ok_pat (v : tpat) : tpat =
  let ty = TAdt (TBuiltin TResult, mk_generic_args_from_types [ v.ty ]) in
  let pat = PAdt { variant_id = Some result_ok_id; fields = [ v ] } in
  { pat; ty }

let mk_sum_ty (left : ty) (right : ty) : ty =
  TAdt (TBuiltin TSum, mk_generic_args_from_types [ left; right ])

let mk_sum_left_texpr (span : span) (left : texpr) (right : ty) : texpr =
  let ty = mk_sum_ty left.ty right in
  mk_adt_texpr span ty (Some sum_left_id) [ left ]

let mk_sum_right_texpr (span : span) (left : ty) (right : texpr) : texpr =
  let ty = mk_sum_ty left right.ty in
  mk_adt_texpr span ty (Some sum_right_id) [ right ]

let mk_loop_result_ty (continue : ty) (break : ty) : ty =
  TAdt (TBuiltin TLoopResult, mk_generic_args_from_types [ continue; break ])

let mk_loop_result_fail_texpr (span : span) (continue : ty) (break : ty)
    (error : texpr) : texpr =
  let ty = mk_loop_result_ty continue break in
  mk_adt_texpr span ty (Some loop_result_fail_id) [ error ]

let mk_loop_result_fail_texpr_with_error_id (span : span) (continue : ty)
    (break : ty) (error : VariantId.id) : texpr =
  let error = mk_error error in
  mk_loop_result_fail_texpr span continue break error

let mk_continue_texpr (span : span) (continue : texpr) (break : ty) : texpr =
  let ty = mk_loop_result_ty continue.ty break in
  mk_adt_texpr span ty (Some loop_result_continue_id) [ continue ]

let mk_break_texpr (span : span) (continue : ty) (break : texpr) : texpr =
  let ty = mk_loop_result_ty continue break.ty in
  mk_adt_texpr span ty (Some loop_result_break_id) [ break ]

let mk_rec_loop_call_texpr file line (span : span) (input : texpr)
    (output_ty : ty) : texpr =
  let func =
    Qualif
      {
        id = FunOrOp (Fun (Pure (RecLoopCall 0)));
        generics = mk_generic_args_from_types [ input.ty; output_ty ];
      }
  in
  let func : texpr =
    { e = func; ty = mk_arrow input.ty (mk_result_ty output_ty) }
  in
  mk_app file line span func input

let opt_unmeta_mplace (e : texpr) : mplace option * texpr =
  match e.e with
  | Meta (MPlace mp, e) -> (Some mp, e)
  | _ -> (None, e)

let mk_fuel_fvar (id : FVarId.id) : fvar =
  { id; basename = Some ConstStrings.fuel_basename; ty = mk_fuel_ty }

let mk_fuel_texpr (id : FVarId.id) : texpr = { e = FVar id; ty = mk_fuel_ty }

(** Convert an **open** pattern to an expression *)
let rec tpat_to_texpr (span : Meta.span) (pat : tpat) : texpr option =
  let e_opt =
    match pat.pat with
    | PConstant pv -> Some (Const pv)
    | POpen (v, _) -> Some (FVar v.id)
    | PBound (_, _) -> [%internal_error] span
    | PIgnored -> None
    | PAdt av ->
        let fields = List.map (tpat_to_texpr span) av.fields in
        if List.mem None fields then None
        else
          let fields_values = List.map (fun e -> Option.get e) fields in

          (* Retrieve the type id and the type args from the pat type (simpler this way *)
          let adt_id, generics = ty_as_adt span pat.ty in

          (* Create the constructor *)
          let qualif_id = AdtCons { adt_id; variant_id = av.variant_id } in
          let qualif = { id = qualif_id; generics } in
          let cons_e = Qualif qualif in
          let field_tys = List.map (fun (v : texpr) -> v.ty) fields_values in
          let cons_ty = mk_arrows field_tys pat.ty in
          let cons = { e = cons_e; ty = cons_ty } in

          (* Apply the constructor *)
          Some ([%add_loc] mk_apps span cons fields_values).e
  in
  match e_opt with
  | None -> None
  | Some e -> Some { e; ty = pat.ty }

(** Open a typed pattern by introducing fresh free variables for the bound
    variables. *)
let open_tpat (span : Meta.span) (fresh_fvar_id : var -> fvar_id) (pat : tpat) :
    tpat =
  let visitor =
    object
      inherit [_] map_tpat
      method! visit_POpen _ _ = [%internal_error] span

      method! visit_PBound _ v m =
        let id = fresh_fvar_id v in
        let { basename; ty } : var = v in
        POpen ({ id; basename; ty }, m)
    end
  in
  visitor#visit_tpat () pat

(** Close a list of typed patterns by replacing their free variables with bound
    variables. We also return the map from free variable ids to bound variables.

    We use this when handling function bodies: the list of type patterns is the
    list of input variables, that we treat as a single binder group. *)
let close_tpats (span : Meta.span) (patl : tpat list) :
    BVarId.id FVarId.Map.t * tpat list =
  let _, fresh_bvar_id = BVarId.fresh_stateful_generator () in
  let map = ref FVarId.Map.empty in
  let visitor =
    object
      inherit [_] map_tpat

      method! visit_POpen _ v m =
        let bid = fresh_bvar_id () in
        let { id; basename; ty } : fvar = v in
        map := FVarId.Map.add id bid !map;
        PBound ({ basename; ty }, m)

      method! visit_PBound _ _ _ = [%internal_error] span
    end
  in
  let patl = List.map (visitor#visit_tpat ()) patl in
  (!map, patl)

(** Close a typed pattern by replacing its free variables with bound variables.
    We also return the map from free variable ids to bound variables. *)
let close_tpat (span : Meta.span) (pat : tpat) : BVarId.id FVarId.Map.t * tpat =
  let map, patl = close_tpats span [ pat ] in
  (map, List.hd patl)

(** Open a binder in an expression.

    Return the opened binders (where the bound variables have been replaced with
    fresh free variables).

    We use this when handling function bodies: the list of type patterns is the
    list of input variables, that we treat as a single binder group. *)
let open_binders fresh_fvar_id (span : Meta.span) (patl : tpat list) (e : texpr)
    : fvar FVarId.Map.t * tpat list * texpr =
  (* We start by introducing the free variables in the pattern *)
  (* The map from bound var ids to freshly introduced fvar ids *)
  let m = ref BVarId.Map.empty in
  let fvars : fvar FVarId.Map.t ref = ref FVarId.Map.empty in
  (* We need to count the bound vars *)
  let _, fresh_bvar_id = BVarId.fresh_stateful_generator () in
  let fresh_fvar_id (v : var) =
    let bid = fresh_bvar_id () in
    let fid = fresh_fvar_id () in
    m := BVarId.Map.add bid fid !m;
    fvars :=
      FVarId.Map.add fid { id = fid; ty = v.ty; basename = v.basename } !fvars;
    fid
  in
  let patl = List.map (open_tpat span fresh_fvar_id) patl in
  (* We can now open the expression *)
  let visitor =
    object
      inherit [_] scoped_map_expr

      method! visit_BVar scope (var : bvar) =
        if var.scope = scope then FVar (BVarId.Map.find var.id !m) else BVar var
    end
  in
  let e = visitor#visit_texpr 0 e in
  (!fvars, patl, e)

(** Open a binder in an expression.

    Return the opened binder (where the bound variables have been replaced with
    fresh free variables).*)
let open_binder fresh_fvar_id (span : Meta.span) (pat : tpat) (e : texpr) :
    fvar FVarId.Map.t * tpat * texpr =
  let fvars, patl, e = open_binders fresh_fvar_id span [ pat ] e in
  (fvars, List.hd patl, e)

(** Helper visitor to close a binder group.

    Return the closed binder (where the free variables have been replaced with
    bound variables).

    We use this when handling function bodies: the list of type patterns is the
    list of input variables, that we treat as a single binder group. *)
let close_binders_visitor (span : Meta.span) (patl : tpat list) =
  (* Close the pattern *)
  let map, patl = close_tpats span patl in
  (* Use the map to update the expression *)
  (* We can now open the expression *)
  let visitor =
    object
      inherit [_] scoped_map_expr

      method! visit_FVar scope fid =
        match FVarId.Map.find_opt fid map with
        | None -> FVar fid
        | Some id -> BVar { scope; id }

      method! visit_BVar scope var =
        (* We may need to increment the scope *)
        if var.scope >= scope then BVar { var with scope = var.scope + 1 }
        else BVar var
    end
  in
  (patl, visitor)

(** Close a binder group in an expression.

    Return the closed binder (where the free variables have been replaced with
    bound variables).

    We use this when handling function bodies: the list of type patterns is the
    list of input variables, that we treat as a single binder group. *)
let close_binders (span : Meta.span) (patl : tpat list) (e : texpr) :
    tpat list * texpr =
  let patl, visitor = close_binders_visitor span patl in
  let e = visitor#visit_texpr 0 e in
  (patl, e)

(** Close a binder in an expression.

    Return the close binder (where the free variables have been replaced with
    bound variables). *)
let close_binder (span : Meta.span) (pat : tpat) (e : texpr) : tpat * texpr =
  let patl, e = close_binders span [ pat ] e in
  (List.hd patl, e)

(** Destruct an expression into a list of nested lets.

    We introduce free variables for the variables bound in the lets while doing
    so. *)
let rec open_lets fresh_fvar_id span
    ?(fresh_fvars : FVarId.Set.t ref option = None) (e : texpr) :
    (bool * tpat * texpr) list * texpr =
  match e.e with
  | Let (monadic, lv, re, next_e) ->
      let _, lv, next_e = open_binder fresh_fvar_id span lv next_e in
      let lets, last_e = open_lets ~fresh_fvars fresh_fvar_id span next_e in
      ((monadic, lv, re) :: lets, last_e)
  | _ -> ([], e)

(** Destruct an expression into a list of nested lets.

    We expect the binders to be open and *do not* introduce fresh free
    variables. *)
let rec raw_destruct_lets (e : texpr) : (bool * tpat * texpr) list * texpr =
  match e.e with
  | Let (monadic, lv, re, next_e) ->
      let lets, last_e = raw_destruct_lets next_e in
      ((monadic, lv, re) :: lets, last_e)
  | _ -> ([], e)

(** Destruct an expression into a list of nested lets, where there is no
    interleaving between monadic and non-monadic lets.

    We expect the binders to be open and do not introduce fresh free variables.
*)
let raw_destruct_lets_no_interleave (span : Meta.span) (e : texpr) :
    (bool * tpat * texpr) list * texpr =
  (* Find the "kind" of the first let (monadic or non-monadic) *)
  let m =
    match e.e with
    | Let (monadic, _, _, _) -> monadic
    | _ -> [%craise] span "Not a let-binding"
  in
  (* Destruct the rest *)
  let rec destruct_lets (e : texpr) : (bool * tpat * texpr) list * texpr =
    match e.e with
    | Let (monadic, lv, re, next_e) ->
        if monadic = m then
          let lets, last_e = destruct_lets next_e in
          ((monadic, lv, re) :: lets, last_e)
        else ([], e)
    | _ -> ([], e)
  in
  destruct_lets e

let trait_decl_is_empty (trait_decl : trait_decl) : bool =
  let {
    def_id = _;
    name = _;
    item_meta = _;
    builtin_info = _;
    generics = _;
    explicit_info = _;
    llbc_generics = _;
    preds = _;
    parent_clauses;
    llbc_parent_clauses = _;
    consts;
    types;
    methods;
  } =
    trait_decl
  in
  parent_clauses = [] && consts = [] && types = [] && methods = []

let trait_impl_is_empty (trait_impl : trait_impl) : bool =
  let {
    def_id = _;
    name = _;
    item_meta = _;
    builtin_info = _;
    impl_trait = _;
    llbc_impl_trait = _;
    generics = _;
    explicit_info = _;
    llbc_generics = _;
    preds = _;
    parent_trait_refs;
    consts;
    types;
    methods;
  } =
    trait_impl
  in
  parent_trait_refs = [] && consts = [] && types = [] && methods = []

let tpat_is_open (pat : tpat) : bool =
  let visitor =
    object
      inherit [_] iter_tpat
      method! visit_PBound _ _ = raise Utils.Found
    end
  in
  try
    visitor#visit_tpat () pat;
    true
  with Utils.Found -> false

(** Return true if a type declaration should be extracted as a tuple, because it
    is a non-recursive structure with unnamed fields. *)
let type_decl_from_type_id_is_tuple_struct (ctx : TypesAnalysis.type_infos)
    (id : type_id) : bool =
  match id with
  | TTuple -> true
  | TAdtId id ->
      let info = TypeDeclId.Map.find id ctx in
      info.is_tuple_struct
  | TBuiltin _ -> false

(** Make a closed lambda expression.

    The typed pattern should be open (i.e., use free variables): this function
    will close the binders while making the lambda. *)
let mk_closed_lambda span (x : tpat) (e : texpr) : texpr =
  let ty = TArrow (x.ty, e.ty) in
  let x, e = close_binder span x e in
  let e = Lambda (x, e) in
  { e; ty }

let close_loop span (loop : loop) : loop =
  let { inputs; loop_body } = loop.loop_body in
  let inputs, visitor = close_binders_visitor span inputs in
  let loop_body = visitor#visit_texpr 0 loop_body in
  let loop_body : loop_body = { inputs; loop_body } in
  { loop with loop_body }

(** Make an open lambda expression.

    The typed pattern should be open (i.e., use free variables) and will be left
    open. *)
let mk_opened_lambda span (x : tpat) (e : texpr) : texpr =
  [%sanity_check] span (tpat_is_open x);
  let ty = TArrow (x.ty, e.ty) in
  let e = Lambda (x, e) in
  { e; ty }

(** Make a closed lambda expression.

    The typed pattern should be open (i.e., use free variables): this function
    will close the binders while making the lambda. *)
let mk_closed_lambdas span (xl : tpat list) (e : texpr) : texpr =
  List.fold_right (mk_closed_lambda span) xl e

let close_lambdas = mk_closed_lambdas

let mk_opened_lambdas span (xl : tpat list) (e : texpr) : texpr =
  List.fold_right (mk_opened_lambda span) xl e

let mk_closed_lambda_from_fvar span (var : fvar) (mp : mplace option)
    (e : texpr) : texpr =
  let pat = POpen (var, mp) in
  let pat = { pat; ty = var.ty } in
  mk_closed_lambda span pat e

let mk_opened_lambda_from_fvar span (var : fvar) (mp : mplace option)
    (e : texpr) : texpr =
  let pat = POpen (var, mp) in
  let pat = { pat; ty = var.ty } in
  mk_opened_lambda span pat e

let mk_closed_lambdas_from_fvars span (vars : fvar list)
    (mps : mplace option list) (e : texpr) : texpr =
  let vars = List.combine vars mps in
  List.fold_right
    (fun (v, mp) e -> mk_closed_lambda_from_fvar span v mp e)
    vars e

let mk_opened_lambdas_from_fvars span (vars : fvar list)
    (mps : mplace option list) (e : texpr) : texpr =
  let vars = List.combine vars mps in
  List.fold_right
    (fun (v, mp) e -> mk_opened_lambda_from_fvar span v mp e)
    vars e

(** Destruct lambdas.

    We introduce free variables for the variables bound in the lambdas while
    doing so. *)
let rec open_lambdas fresh_fvar_id span (e : texpr) :
    fvar FVarId.Map.t * tpat list * texpr =
  match e.e with
  | Lambda (pat, e) ->
      let fvars, pat, e = open_binder fresh_fvar_id span pat e in
      let fvars', pats, e = open_lambdas fresh_fvar_id span e in
      ( FVarId.Map.union (fun _ _ _ -> [%internal_error] span) fvars fvars',
        pat :: pats,
        e )
  | _ -> (FVarId.Map.empty, [], e)

(** Destruct lambdas without introducing free variables

    TODO: rename *)
let rec raw_destruct_lambdas (e : texpr) : tpat list * texpr =
  match e.e with
  | Lambda (pat, e) ->
      let pats, e = raw_destruct_lambdas e in
      (pat :: pats, e)
  | _ -> ([], e)

let opt_dest_tuple_texpr (e : texpr) : texpr list option =
  let app, args = destruct_apps e in
  match app.e with
  | Qualif { id = AdtCons { adt_id = TTuple; variant_id = None }; generics = _ }
    -> Some args
  | _ -> None

let opt_dest_struct_pat (pat : tpat) : tpat list option =
  match pat.pat with
  | PAdt { variant_id = None; fields } -> Some fields
  | _ -> None

(** Destruct a [ret ...] expression *)
let opt_destruct_ret (e : texpr) : texpr option =
  match e.e with
  | App
      ( {
          e =
            Qualif
              {
                id = AdtCons { adt_id = TBuiltin TResult; variant_id };
                generics = _;
              };
          ty = _;
        },
        arg )
    when variant_id = Some result_ok_id -> Some arg
  | _ -> None

let decompose_mplace_to_local (p : mplace) :
    (E.LocalId.id * string option * mprojection_elem list) option =
  let rec decompose (proj : mprojection_elem list) (p : mplace) =
    match p with
    | PlaceLocal (id, name) -> Some (id, name, proj)
    | PlaceGlobal _ -> None
    | PlaceProjection (p, pe) -> decompose (pe :: proj) p
  in
  decompose [] p

let tpats_get_fvars (x : tpat list) : FVarId.Set.t =
  let vars = ref FVarId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_fvar_id _ var_id = vars := FVarId.Set.add var_id !vars
    end
  in
  List.iter (visitor#visit_tpat ()) x;
  !vars

let tpat_get_fvars (x : tpat) : FVarId.Set.t = tpats_get_fvars [ x ]

let texpr_get_fvars (e : texpr) : FVarId.Set.t =
  let vars = ref FVarId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_fvar_id _ var_id = vars := FVarId.Set.add var_id !vars
    end
  in
  visitor#visit_texpr () e;
  !vars

let texpr_get_bound_fvars (e : texpr) : FVarId.Set.t =
  let vars = ref FVarId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_POpen _ fv _ = vars := FVarId.Set.add fv.id !vars
    end
  in
  visitor#visit_texpr () e;
  !vars

let loop_body_get_bound_fvars (e : loop_body) : FVarId.Set.t =
  let vars = ref FVarId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_POpen _ fv _ = vars := FVarId.Set.add fv.id !vars
    end
  in
  visitor#visit_loop_body () e;
  !vars

let texpr_has_fvars (e : texpr) : bool =
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_fvar_id _ _ = raise Utils.Found
    end
  in
  try
    visitor#visit_texpr () e;
    false
  with Utils.Found -> true

let texpr_has_bvars (e : texpr) : bool =
  let visitor =
    object
      inherit [_] iter_expr
      method! visit_bvar_id _ _ = raise Utils.Found
    end
  in
  try
    visitor#visit_texpr () e;
    false
  with Utils.Found -> true

let mk_to_result_texpr (span : Meta.span) (e : texpr) : texpr =
  let type_args = [ e.ty ] in
  let generics = mk_generic_args_from_types type_args in
  let ty = TAdt (TBuiltin TResult, generics) in
  let id = FunOrOp (Fun (Pure ToResult)) in
  let qualif = { id; generics } in
  let qualif = Qualif qualif in
  let qualif_ty = mk_arrow e.ty ty in
  let qualif = { e = qualif; ty = qualif_ty } in
  [%add_loc] mk_app span qualif e

let append_generic_args (g0 : generic_args) (g1 : generic_args) : generic_args =
  {
    types = g0.types @ g1.types;
    const_generics = g0.const_generics @ g1.const_generics;
    trait_refs = g0.trait_refs @ g1.trait_refs;
  }

(** Ajust the explicit information coming from a signature.

    If the function called is a trait method, we need to remove the prefix which
    accounts for the generics of the impl. *)
let adjust_explicit_info (explicit : explicit_info) (is_trait_method : bool)
    (generics : generic_args) : explicit_info =
  if is_trait_method then
    (* We simply adjust the length of the explicit information to
       the number of generic arguments *)
    let open Collections.List in
    let { Pure.explicit_types; explicit_const_generics } = explicit in
    {
      explicit_types =
        drop (length explicit_types - length generics.types) explicit_types;
      explicit_const_generics =
        drop
          (length explicit_const_generics - length generics.const_generics)
          explicit_const_generics;
    }
  else explicit

let mk_visited_params_visitor () =
  let tys = ref Pure.TypeVarId.Set.empty in
  let cgs = ref Pure.ConstGenericVarId.Set.empty in
  let visitor =
    object
      inherit [_] Pure.iter_type_decl
      method! visit_type_var_id _ id = tys := Pure.TypeVarId.Set.add id !tys

      method! visit_const_generic_var_id _ id =
        cgs := Pure.ConstGenericVarId.Set.add id !cgs
    end
  in
  (visitor, tys, cgs)

(** Compute which input parameters should be implicit or explicit.

    The way we do it is simple: if a parameter appears in one of the inputs,
    then it should be implicit. For instance, the type parameter of [Vec::get]
    should be implicit, while the type parameter of [Vec::new] should be
    explicit (it only appears in the output). Also note that here we consider
    the trait obligations as inputs from which we can deduce an implicit
    parameter. For instance:
    {[
      let f {a : Type} (clause0 : Foo a) : ...
             ^^^^^^^^
          implied by clause0
    ]}

    The [input_tys] are the types of the input arguments, in case we are
    translating a function. *)
let compute_explicit_info (generics : Pure.generic_params) (input_tys : ty list)
    : explicit_info =
  let visitor, implicit_tys, implicit_cgs = mk_visited_params_visitor () in
  List.iter (visitor#visit_trait_param ()) generics.trait_clauses;
  List.iter (visitor#visit_ty ()) input_tys;
  let make_explicit_ty (v : type_param) : Pure.explicit =
    if Pure.TypeVarId.Set.mem v.index !implicit_tys then Implicit else Explicit
  in
  let make_explicit_cg (v : const_generic_param) : Pure.explicit =
    if Pure.ConstGenericVarId.Set.mem v.index !implicit_cgs then Implicit
    else Explicit
  in
  {
    explicit_types = List.map make_explicit_ty generics.types;
    explicit_const_generics = List.map make_explicit_cg generics.const_generics;
  }

(** Compute which input parameters can be infered if only the explicit types and
    the trait refs are provided.

    This is similar to [compute_explicit_info]. *)
let compute_known_info (explicit : explicit_info)
    (generics : Pure.generic_params) : known_info =
  let visitor, known_tys, known_cgs = mk_visited_params_visitor () in
  List.iter (visitor#visit_trait_param ()) generics.trait_clauses;
  let make_known_ty ((e, v) : explicit * type_param) : Pure.known =
    if e = Explicit || Pure.TypeVarId.Set.mem v.index !known_tys then Known
    else Unknown
  in
  let make_known_cg ((e, v) : explicit * const_generic_param) : Pure.known =
    if e = Explicit || Pure.ConstGenericVarId.Set.mem v.index !known_cgs then
      Known
    else Unknown
  in
  {
    known_types =
      List.map make_known_ty
        (List.combine explicit.explicit_types generics.types);
    known_const_generics =
      List.map make_known_cg
        (List.combine explicit.explicit_const_generics generics.const_generics);
  }

(** This helper closes the binder *)
let mk_closed_let span (monadic : bool) (lv : tpat) (re : texpr)
    (next_e : texpr) : texpr =
  let lv, next_e = close_binder span lv next_e in
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

(** This helper closes the binders *)
let mk_closed_lets span (monadic : bool) (lets : (tpat * texpr) list)
    (next_e : texpr) : texpr =
  List.fold_right
    (fun (pat, value) (e : texpr) -> mk_closed_let span monadic pat value e)
    lets next_e

let mk_closed_heterogeneous_lets span (lets : (bool * tpat * texpr) list)
    (next_e : texpr) : texpr =
  List.fold_right
    (fun (monadic, pat, value) (e : texpr) ->
      mk_closed_let span monadic pat value e)
    lets next_e

(** This helper closes the binder *)
let mk_closed_checked_let file line span (monadic : bool) (lv : tpat)
    (re : texpr) (next_e : texpr) : texpr =
  let re_ty =
    if monadic then
      unwrap_result_or_loop_result_ty_with_loc file line span re.ty
    else re.ty
  in
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span (lv.ty = re_ty);
  mk_closed_let span monadic lv re next_e

(** This helper does not close the binder *)
let mk_opened_let (monadic : bool) (lv : tpat) (re : texpr) (next_e : texpr) :
    texpr =
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

(** This helper does not close the binders *)
let mk_opened_lets (monadic : bool) (lets : (tpat * texpr) list)
    (next_e : texpr) : texpr =
  List.fold_right
    (fun (pat, value) (e : texpr) -> mk_opened_let monadic pat value e)
    lets next_e

(** This helper does not close the binder *)
let mk_opened_checked_let file line span (monadic : bool) (lv : tpat)
    (re : texpr) (next_e : texpr) : texpr =
  let re_ty = if monadic then unwrap_result_ty span re.ty else re.ty in
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span (lv.ty = re_ty);
  mk_opened_let monadic lv re next_e

(** This helper opens the binder *)
let open_branch fresh_fvar_id span (branch : match_branch) :
    fvar FVarId.Map.t * tpat * texpr =
  let { pat; branch } = branch in
  open_binder fresh_fvar_id span pat branch

(** This helper closes the binder *)
let close_branch span (pat : tpat) (branch : texpr) : match_branch =
  let pat, branch = close_binder span pat branch in
  { pat; branch }

(** This helper does not close the binder *)
let mk_opened_branch (pat : tpat) (branch : texpr) : match_branch =
  { pat; branch }

(** This helper closes the binder *)
let mk_closed_checked_lets file line span (monadic : bool)
    (lets : (tpat * texpr) list) (next_e : texpr) : texpr =
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span
      (List.for_all
         (fun ((pat, e) : tpat * texpr) ->
           let e_ty = if monadic then unwrap_result_ty span e.ty else e.ty in
           pat.ty = e_ty)
         lets);
  mk_closed_lets span monadic lets next_e

(** This helper does not close the binder *)
let mk_opened_checked_lets file line span (monadic : bool)
    (lets : (tpat * texpr) list) (next_e : texpr) : texpr =
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span
      (List.for_all
         (fun ((pat, e) : tpat * texpr) ->
           let e_ty = if monadic then unwrap_result_ty span e.ty else e.ty in
           pat.ty = e_ty)
         lets);
  mk_closed_lets span monadic lets next_e

(** Wrap a function body in a match over the fuel to control termination.

    This helper closes the binders. *)
let wrap_in_match_fuel (span : Meta.span) (fuel0 : FVarId.id) (fuel : FVarId.id)
    ~(close : bool) (body : texpr) : texpr =
  let fuel0_var = mk_fuel_fvar fuel0 in
  let fuel0 = mk_texpr_from_fvar fuel0_var in
  let nfuel_var = mk_fuel_fvar fuel in
  let nfuel_pat = mk_tpat_from_fvar None nfuel_var in
  let fail_branch =
    mk_result_fail_texpr_with_error_id span error_out_of_fuel_id body.ty
  in
  let mk_let = if close then mk_closed_checked_let else mk_opened_checked_let in
  let mk_branch = if close then close_branch span else mk_opened_branch in
  match Config.backend () with
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
        [%add_loc] mk_app span func fuel0
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
        [%add_loc] mk_app span func fuel0
      in

      (* Create the success branch *)
      let monadic = false in
      let success_branch =
        [%add_loc] mk_let span monadic nfuel_pat decrease_fuel body
      in

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
      let fail_pat = mk_adt_pat mk_fuel_ty (Some fuel_zero_id) [] in
      let fail_branch = mk_branch fail_pat fail_branch in
      (* Create the success branch *)
      let success_pat =
        mk_adt_pat mk_fuel_ty (Some fuel_succ_id) [ nfuel_pat ]
      in
      let success_branch = body in
      let success_branch = mk_branch success_pat success_branch in
      (* Put everything together *)
      let match_ty = body.ty in
      let match_e = Switch (fuel0, Match [ fail_branch; success_branch ]) in
      { e = match_e; ty = match_ty }
  | Lean | HOL4 ->
      (* We should have checked the command line arguments before *)
      raise (Failure "Unexpected")

let mk_closed_fun_body span (inputs : tpat list) (body : texpr) : fun_body =
  let inputs, body = close_binders span inputs body in
  { inputs; body }

(** Helper visitor to open/close *all* the bound variables in an expression.

    We use a reference to the environment to update the bindings. As a
    consequence we pay attention to pop binders whenever they become out of
    scope. *)
class virtual ['self] open_close_all_visitor =
  object (self : 'self)
    inherit [_] map_expr
    method virtual start_scope : 'env ref -> unit
    method virtual push_scope : 'env ref -> unit
    method virtual pop_scope : 'env ref -> unit
    method virtual push_var : 'env ref -> var -> fvar_id
    method virtual push_fvar : 'env ref -> fvar -> var
    method virtual get_bvar : 'env ref -> bvar -> fvar_id option
    method virtual get_fvar : 'env ref -> fvar_id -> bvar option

    method! visit_POpen env v mp =
      let _ = self#push_fvar env v in
      let { basename; ty; id = _ } = v in
      PBound ({ basename; ty }, mp)

    method! visit_PBound env (v : var) mp =
      let fid = self#push_var env v in
      let { basename; ty } : var = v in
      POpen ({ basename; ty; id = fid }, mp)

    method! visit_Lambda env pat inner =
      self#start_scope env;
      let pat = self#visit_tpat env pat in
      self#push_scope env;
      let inner = self#visit_texpr env inner in
      self#pop_scope env;
      Lambda (pat, inner)

    method! visit_Let env monadic pat bound next =
      let bound = self#visit_texpr env bound in
      self#start_scope env;
      let pat = self#visit_tpat env pat in
      self#push_scope env;
      let next = self#visit_texpr env next in
      self#pop_scope env;
      Let (monadic, pat, bound, next)

    method! visit_match_branch env branch =
      let { pat; branch } : match_branch = branch in
      self#start_scope env;
      let pat = self#visit_tpat env pat in
      self#push_scope env;
      let branch = self#visit_texpr env branch in
      self#pop_scope env;
      { pat; branch }

    method visit_fun_body env (fbody : fun_body) : fun_body =
      let { inputs; body } = fbody in
      self#start_scope env;
      let inputs = List.map (self#visit_tpat env) inputs in
      self#push_scope env;
      let body = self#visit_texpr env body in
      self#pop_scope env;
      { inputs; body }

    method! visit_loop_body env body =
      let { inputs; loop_body } = body in
      (* Visit the pats to push a new scope *)
      self#start_scope env;
      let inputs = List.map (self#visit_tpat env) inputs in
      self#push_scope env;
      (* Enter the inner expression *)
      let loop_body = self#visit_texpr env loop_body in
      (* Pop the stack *)
      self#pop_scope env;
      (* *)
      { inputs; loop_body }

    method! visit_FVar env (id : fvar_id) =
      match self#get_fvar env id with
      | None -> FVar id
      | Some bv -> BVar bv

    method! visit_BVar env (v : bvar) =
      match self#get_bvar env v with
      | None -> BVar v
      | Some fv -> FVar fv
  end

type open_all_env = {
  benv : fvar_id BVarId.Map.t list;
  penv : fvar_id BVarId.Map.t option;
      (** Partial map that we're in the process of constructing (we use this
          when exploring patterns: we construct the map for the binder
          progressively and then push it to [benv]. This is similar to
          [PrintPure.fmt_env] *)
  pvarid : BVarId.id;
  fvars : fvar FVarId.Map.t;
}

let empty_open_all_env : open_all_env =
  { benv = []; penv = None; pvarid = BVarId.zero; fvars = FVarId.Map.empty }

(** Start a new partial map (call this before exploring a binder) *)
let open_all_env_start_scope (env : open_all_env) : open_all_env =
  assert (env.penv = None);
  { env with penv = Some BVarId.Map.empty; pvarid = BVarId.zero }

(** After we're done accumulating the bound variables of a pattern in [penv],
    push this partial map to [bvars] *)
let open_all_env_push_scope (env : open_all_env) : open_all_env =
  let penv = Option.get env.penv in
  {
    benv = penv :: env.benv;
    penv = None;
    pvarid = BVarId.zero;
    fvars = env.fvars;
  }

let open_all_env_pop_scope (env : open_all_env) : open_all_env =
  assert (env.penv = None);
  { env with benv = List.tl env.benv }

(** Register a bound variable.

    Only call this between [open_all_env_start_penv] and
    [open_all_env_push_penv]. *)
let open_all_env_push_var fresh_fvar_id (env : open_all_env) (v : var) :
    open_all_env * fvar_id =
  let penv = Option.get env.penv in
  let bvar_id = env.pvarid in
  let fvar_id = fresh_fvar_id () in
  let penv = Some (BVarId.Map.add bvar_id fvar_id penv) in
  let fvar : fvar = { id = fvar_id; basename = v.basename; ty = v.ty } in
  let env =
    {
      env with
      penv;
      pvarid = BVarId.incr env.pvarid;
      fvars = FVarId.Map.add_strict fvar_id fvar env.fvars;
    }
  in
  (env, fvar_id)

let open_all_env_get_var span (env : open_all_env) (v : bvar) : fvar_id option =
  [%sanity_check] span (env.penv = None);
  match Collections.List.nth_opt env.benv v.scope with
  | Some scope -> BVarId.Map.find_opt v.id scope
  | None -> None

(** Visitor to open *all* the bound variables in an expression.

    All the closed patterns are replaced with open patterns.

    We use a reference to the environment to update the bindings. As a
    consequence we pay attention to pop binders whenever they become out of
    scope. *)
let open_all_visitor fresh_fvar_id (span : Meta.span) =
  object (_ : 'self)
    inherit [_] open_close_all_visitor

    method start_scope (env : open_all_env ref) =
      env := open_all_env_start_scope !env

    method push_scope (env : open_all_env ref) =
      env := open_all_env_push_scope !env

    method pop_scope (env : open_all_env ref) =
      env := open_all_env_pop_scope !env

    method push_var (env : open_all_env ref) v =
      let env', id = open_all_env_push_var fresh_fvar_id !env v in
      env := env';
      id

    method push_fvar _ _ = [%internal_error] span

    method get_bvar (env : open_all_env ref) v =
      open_all_env_get_var span !env v

    method get_fvar _ _ = None

    method! visit_POpen _ fv mp =
      (* Leave it unchanged (it is already open) *) POpen (fv, mp)
  end

let open_all_texpr fresh_fvar_id (span : Meta.span) (e : texpr) : texpr =
  (open_all_visitor fresh_fvar_id span)#visit_texpr (ref empty_open_all_env) e

let open_all_fun_body fresh_fvar_id (span : Meta.span) (fbody : fun_body) :
    fvar FVarId.Map.t * fun_body =
  let env = ref empty_open_all_env in
  let fbody = (open_all_visitor fresh_fvar_id span)#visit_fun_body env fbody in
  (!env.fvars, fbody)

type close_all_env = {
  fenv : bvar FVarId.Map.t;
      (** We use scopes in a slightly different way here: we count scopes from
          the outer scopes. This way, we do not have to open the map when
          entering a new binder: the scope to use is the current scope (see
          field [scope] below) minus the scope of the variable as registered in
          the map *)
  scope : int;
      (** This is actually the next scope (i.e., the current scope + 1) *)
  bvar_id : BVarId.id option;
      (** We use this when exploring patterns: this gives us the next bound var
          id to use *)
}

let empty_close_all_env : close_all_env =
  { fenv = FVarId.Map.empty; scope = 0; bvar_id = None }

let close_all_env_start_scope (env : close_all_env) : close_all_env =
  { env with bvar_id = Some BVarId.zero }

let close_all_env_push_scope (env : close_all_env) : close_all_env =
  { env with scope = env.scope + 1; bvar_id = None }

let close_all_env_pop_scope span (env : close_all_env) : close_all_env =
  [%sanity_check] span (env.scope > 0);
  [%sanity_check] span (env.bvar_id = None);
  { env with scope = env.scope - 1 }

(** Register a free variable.

    Only call this between [close_all_env_start_penv] and
    [close_all_env_push_penv]. *)
let close_all_env_push_var (env : close_all_env) (fid : fvar_id) :
    close_all_env * bvar_id =
  let bvar_id = Option.get env.bvar_id in
  let fenv = FVarId.Map.add fid { scope = env.scope; id = bvar_id } env.fenv in
  let env = { env with fenv; bvar_id = Some (BVarId.incr bvar_id) } in
  (env, bvar_id)

let close_all_env_get_var _span (env : close_all_env) (fid : fvar_id) :
    bvar option =
  match FVarId.Map.find_opt fid env.fenv with
  | None -> None
  | Some v -> Some { v with scope = env.scope - v.scope - 1 }

(** Visitor to close *all* the bound variables in an expression.

    All the closed patterns are replaced with close patterns.

    We use a reference to the environment to update the bindings. As a
    consequence we pay attention to pop binders whenever they become out of
    scope. *)
let close_all_visitor (span : Meta.span) =
  object (_ : 'self)
    inherit [_] open_close_all_visitor

    method start_scope (env : close_all_env ref) =
      env := close_all_env_start_scope !env

    method push_scope (env : close_all_env ref) =
      env := close_all_env_push_scope !env

    method pop_scope (env : close_all_env ref) =
      env := close_all_env_pop_scope span !env

    method push_var _ _ = [%internal_error] span

    method push_fvar (env : close_all_env ref) (v : fvar) =
      let env', _ = close_all_env_push_var !env v.id in
      env := env';
      let { basename; ty; id = _ } = v in
      { basename; ty }

    method get_bvar _ _ = None

    method get_fvar (env : close_all_env ref) v =
      close_all_env_get_var span !env v

    method! visit_PBound _ var mp =
      (* Leave it unchanged: it is already bound *)
      PBound (var, mp)
  end

let close_all_texpr (span : Meta.span) (e : texpr) : texpr =
  (close_all_visitor span)#visit_texpr (ref empty_close_all_env) e

let close_all_fun_body (span : Meta.span) (fbody : fun_body) : fun_body =
  (close_all_visitor span)#visit_fun_body (ref empty_close_all_env) fbody

let open_fun_body fresh_fvar_id (span : Meta.span) (fbody : fun_body) :
    fvar FVarId.Map.t * fun_body =
  let { inputs; body } = fbody in
  let fvars, inputs, body = open_binders fresh_fvar_id span inputs body in
  (fvars, { inputs; body })

let close_fun_body (span : Meta.span) (fbody : fun_body) : fun_body =
  let { inputs; body } = fbody in
  let inputs, body = close_binders span inputs body in
  { inputs; body }

let open_loop_body fresh_fvar_id (span : Meta.span) (body : loop_body) :
    fvar FVarId.Map.t * loop_body =
  let { inputs; loop_body } = body in
  let fvars, inputs, loop_body =
    open_binders fresh_fvar_id span inputs loop_body
  in
  (fvars, { inputs; loop_body })

let close_loop_body (span : Meta.span) (body : loop_body) : loop_body =
  let { inputs; loop_body } = body in
  let inputs, loop_body = close_binders span inputs loop_body in
  { inputs; loop_body }

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables *)
let open_close_all_fun_body fresh_fvar_id (span : Meta.span)
    (f : fun_body -> fun_body) (fbody : fun_body) : fun_body =
  if !Config.sanity_checks then
    [%sanity_check] span (not (texpr_has_fvars fbody.body));
  let _, fbody = open_all_fun_body fresh_fvar_id span fbody in
  if !Config.sanity_checks then
    [%sanity_check] span (not (texpr_has_bvars fbody.body));
  let fbody = f fbody in
  if !Config.sanity_checks then
    [%sanity_check] span (not (texpr_has_bvars fbody.body));
  let fbody = close_all_fun_body span fbody in
  if !Config.sanity_checks then
    [%sanity_check] span (not (texpr_has_fvars fbody.body));
  fbody

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables *)
let open_close_all_fun_decl fresh_fvar_id (f : fun_body -> fun_body)
    (fdef : fun_decl) : fun_decl =
  let body =
    Option.map
      (open_close_all_fun_body fresh_fvar_id fdef.item_meta.span f)
      fdef.body
  in
  { fdef with body }

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables.

    We reset the fvar id counter before doing this. *)
let map_open_all_fun_decl_body fresh_fvar_id (f : fun_body -> fun_body)
    (fdef : fun_decl) : fun_decl =
  let body =
    Option.map
      (open_close_all_fun_body fresh_fvar_id fdef.item_meta.span f)
      fdef.body
  in
  { fdef with body }

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables.

    We reset the fvar id counter before doing this. *)
let map_open_all_fun_decl_body_expr fresh_fvar_id (f : texpr -> texpr)
    (fdef : fun_decl) : fun_decl =
  map_open_all_fun_decl_body fresh_fvar_id
    (fun (fb : fun_body) -> { fb with body = f fb.body })
    fdef

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables.

    We reset the fvar id counter before doing this. *)
let iter_open_all_fun_decl_body fresh_fvar_id (f : fun_body -> unit)
    (fdef : fun_decl) : unit =
  Option.iter
    (fun x ->
      let _ =
        open_close_all_fun_body fresh_fvar_id fdef.item_meta.span
          (fun x ->
            f x;
            x)
          x
      in
      ())
    fdef.body

(** Open all the bound variables in a function body, apply a function, then
    close those bound variables.

    We reset the fvar id counter before doing this. *)
let iter_open_all_fun_decl_body_expr fresh_fvar_id (f : texpr -> unit)
    (fdef : fun_decl) : unit =
  iter_open_all_fun_decl_body fresh_fvar_id
    (fun (fb : fun_body) -> f fb.body)
    fdef

type generics_filter = {
  types : bool list;  (** [true] means we should keep the parameter *)
  const_generics : bool list;
  trait_clauses : bool list;
}
[@@deriving show]

(** Filter a list of generic arguments to only preserve the variables which are
    inside of an expression.

    We *do not* re-index the variables, because it is a bit tricky to do
    correctly (in particular, propagating the changes can be tricky). Instead,
    we leverage the fact that all functions which lookup generics from the
    generic params do not assume anything about the indices they use (in
    particular, they do not have to be contiguous).

    Side remark: some functions (for computing names for trait clauses) actually
    *need* the indices of the trait clauses to be preserved from the LLBC code
    to the pure code. *)
let filter_generic_params_used_in_texpr (generic : generic_params) (e : texpr) :
    generic_params * generics_filter =
  (* Collect the sets of parameters used in the expression *)
  let type_ids = ref TypeVarId.Set.empty in
  let cg_ids = ref ConstGenericVarId.Set.empty in
  let clause_ids = ref TraitClauseId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expr

      method! visit_type_var_id _ id =
        type_ids := TypeVarId.Set.add id !type_ids

      method! visit_const_generic_var_id _ id =
        cg_ids := ConstGenericVarId.Set.add id !cg_ids

      method! visit_trait_clause_id _ id =
        clause_ids := TraitClauseId.Set.add id !clause_ids
    end
  in
  visitor#visit_texpr () e;

  (* Filter *)
  let { types; const_generics; trait_clauses } : generic_params = generic in
  let types =
    List.map
      (fun (v : type_param) -> (TypeVarId.Set.mem v.index !type_ids, v))
      types
  in
  let const_generics =
    List.map
      (fun (cg : const_generic_param) ->
        (ConstGenericVarId.Set.mem cg.index !cg_ids, cg))
      const_generics
  in
  let trait_clauses =
    List.map
      (fun (clause : trait_param) ->
        (TraitClauseId.Set.mem clause.clause_id !clause_ids, clause))
      trait_clauses
  in

  let filter : generics_filter =
    {
      types = List.map fst types;
      const_generics = List.map fst const_generics;
      trait_clauses = List.map fst trait_clauses;
    }
  in

  let types =
    List.filter_map (fun (b, x) -> if b then Some x else None) types
  in
  let const_generics =
    List.filter_map (fun (b, x) -> if b then Some x else None) const_generics
  in
  (* WARNING: the indices and generics inside the trait clause are not correct!
     We update them below. *)
  let trait_clauses =
    List.filter_map (fun (b, x) -> if b then Some x else None) trait_clauses
  in

  (* Reindex the generic params *)
  let generics : generic_params = { types; const_generics; trait_clauses } in
  (generics, filter)

let generic_args_of_params (generics : generic_params) : generic_args =
  let types =
    List.map (fun (v : type_param) -> TVar (Free v.index)) generics.types
  in
  let const_generics =
    List.map
      (fun (v : const_generic_param) -> T.CgVar (Free v.index))
      generics.const_generics
  in
  let trait_refs =
    List.map
      (fun (c : trait_param) ->
        {
          trait_id = Clause (Free c.clause_id);
          trait_decl_ref =
            { trait_decl_id = c.trait_id; decl_generics = c.generics };
        })
      generics.trait_clauses
  in
  { types; const_generics; trait_refs }

type decomposed_loop_result = {
  variant_id : variant_id;
  args : texpr list;  (** The decomposed tuple argument *)
  arg : texpr;  (** The non-decomposed argument *)
  continue_ty : ty;
  break_ty : ty;
}

(** Attempt to destruct a [LoopResult::Continue], [LoopResult::Break] or
    [LoopResult::Panic] expression, by decomposing its arguments.

    In case we find [Continue] or [Break] we analyze the argument, which should
    have the type tuple, and decompose it. This helper is required by the
    micro-passes to always be able to decompose the tuple argument into its
    sub-elements. If the tuple expression is not actually a tuple (for instance,
    it is a call to a function evaluating to a tuple), we decompose the
    expression by either introducing an intermediate let-binding (if [intro_let]
    is [true]) or by duplicating the expression and projecting it (e.g.,
    [f x ~> ((f x).0, (f x).1)]).

    The returned continuation allows reconstructing the decomposition, in case
    we introduced a let-binding. *)
let opt_destruct_loop_result_decompose_outputs fresh_fvar_id span
    ~(intro_let : bool) (e : texpr) :
    (decomposed_loop_result * (texpr -> texpr)) option =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif
      {
        id =
          AdtCons
            { adt_id = TBuiltin TLoopResult; variant_id = Some variant_id };
        generics;
      } ->
      (* There should be exactly one argument *)
      let arg =
        match args with
        | [ x ] -> x
        | _ -> [%internal_error] span
      in
      let continue_ty, break_ty =
        match generics with
        | { types = [ continue; break ]; const_generics = []; trait_refs = [] }
          -> (continue, break)
        | _ -> [%internal_error] span
      in

      (* Attempt to destruct a tuple. If the type is a tuple but the expression
         is not a tuple constructor applied to some fields (for instance, it is
         a function call), introduce an intermediate let-binding to deconstruct
         the tuple. *)
      let destruct_rebind_tuple (span : Meta.span) (e : texpr) :
          texpr list * texpr * (texpr -> texpr) =
        match e.ty with
        | TAdt (TTuple, generics) -> (
            [%sanity_check] span (generics.const_generics = []);
            [%sanity_check] span (generics.trait_refs = []);
            let cons, fields = destruct_apps e in
            match cons.e with
            | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ } ->
                [%sanity_check] span
                  (List.length generics.types = List.length fields);
                (fields, e, fun x -> x)
            | _ ->
                (* We need to decompose the tuple. Either we introduce projectors
                   (this duplicates the expression) or we introduce an intermediate
                   let-bindings *)
                if intro_let then
                  let fvars =
                    List.map (mk_fresh_fvar fresh_fvar_id) generics.types
                  in
                  let pat =
                    mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) fvars)
                  in
                  let fields = List.map mk_texpr_from_fvar fvars in
                  let tuple = mk_simpl_tuple_texpr span fields in
                  let mk_bind e' = mk_closed_let span false pat e e' in
                  (fields, tuple, mk_bind)
                else
                  let fields =
                    FieldId.mapi
                      (fun field_id ty ->
                        let proj =
                          let ty = mk_arrow e.ty ty in
                          let e =
                            Qualif
                              {
                                id = Proj { adt_id = TTuple; field_id };
                                generics;
                              }
                          in
                          ({ e; ty } : texpr)
                        in
                        [%add_loc] mk_app span proj e)
                      generics.types
                  in
                  (fields, e, fun e -> e))
        | _ -> ([ e ], e, fun e -> e)
      in

      if variant_id = loop_result_break_id then
        (* The argument should be a tuple, but may be a function call *)
        let outputs, arg, mk_bind = destruct_rebind_tuple span arg in
        Some
          ({ variant_id; args = outputs; arg; continue_ty; break_ty }, mk_bind)
      else if variant_id = loop_result_continue_id then
        (* We leave the expression unchanged but have to modify its type *)
        (* The argument should be a tuple *)
        let outputs, arg, mk_bind = destruct_rebind_tuple span arg in
        Some
          ({ variant_id; args = outputs; arg; continue_ty; break_ty }, mk_bind)
      else
        Some
          ( { variant_id; args = [ arg ]; arg; continue_ty; break_ty },
            fun e -> e )
  | _ -> None

type decomposed_rec_loop_call = {
  i : int;
  args : texpr list;  (** The decomposed tuple argument *)
  arg : texpr;  (** The non-decomposed argument *)
  continue_ty : ty;
  break_ty : ty;
}

let opt_destruct_rec_loop_call span (e : texpr) :
    decomposed_rec_loop_call option =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif { id = FunOrOp (Fun (Pure (RecLoopCall i))); generics } ->
      (* There should be exactly one argument *)
      let arg =
        match args with
        | [ x ] -> x
        | _ -> [%internal_error] span
      in
      let continue_ty, break_ty =
        match generics with
        | { types = [ continue; break ]; const_generics = []; trait_refs = [] }
          -> (continue, break)
        | _ -> [%internal_error] span
      in
      let args = try_destruct_tuple_texpr span arg in
      Some { i; args; arg; continue_ty; break_ty }
  | _ -> None

(** Return [true] if the pattern decomposes an enumeration with > 1 variants *)
let tpat_decomposes_enum span (type_decls : type_decl TypeDeclId.Map.t)
    (pat : tpat) : bool =
  let visitor =
    object
      inherit [_] iter_expr as super
      method! visit_tpat _ pat = super#visit_tpat pat.ty pat

      method! visit_adt_pat ty pat =
        (* Lookup the type decl *)
        let type_id, _ = ty_as_adt span ty in
        match type_id with
        | TAdtId id ->
            let decl = TypeDeclId.Map.find id type_decls in
            begin
              match decl.kind with
              | Struct _ | Opaque -> ()
              | Enum vl -> if List.length vl > 1 then raise Utils.Found
            end;
            super#visit_adt_pat ty pat
        | TTuple ->
            (* ok *)
            super#visit_adt_pat ty pat
        | TBuiltin _ ->
            (* Shouldn't happen *)
            [%craise] span "Unreachable"
    end
  in
  try
    visitor#visit_tpat pat.ty pat;
    false
  with Utils.Found -> true

(** Small helper.

    We use this to properly deconstruct the values given back by backward
    functions in the presence of enumerations.

    This helper transforms a let-bound pattern and a bound expression to
    properly introduce matches if necessary.

    For instance, we use it to transform this:
    {[
      let Some x = e in
          ^^^^^^   ^
           pat     let-bound expression
    ]}
    into:
    {[
       let x = match e with | Some x -> x | _ -> default_value in
           ^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      new pat     new let-bound expression
    ]}

    The input function [get_default_expr] is called on all the variables found
    in the pattern to compute a default expression for this variable, to
    construct the "otherwise" branch.

    **Remarks:** the function receives an open pattern and outputs an open
    pattern. *)
let decompose_let_match span (refresh_var : fvar -> fvar)
    (get_default_expr : fvar -> texpr) (type_decls : type_decl TypeDeclId.Map.t)
    (pat : tpat) (bound : texpr) : tpat * texpr =
  (* We update the pattern if it deconstructs an enumeration with > 1 variants *)
  let found_enum = tpat_decomposes_enum span type_decls pat in

  (* *)
  if found_enum then
    (* Found an enumeration with > 1 variants: we have to deconstruct
       the pattern *)
    (* First, refresh the variables - we will use fresh variables
       in the patterns of the internal match *)
    let visitor =
      object
        inherit [_] mapreduce_expr
        method zero : (fvar * fvar) list = []
        method plus vars0 vars1 = vars0 @ vars1
        method! visit_PBound _ _ _ = [%internal_error] span

        method! visit_POpen _ var mp =
          let var' = refresh_var var in
          (POpen (var', mp), [ (var, var') ])
      end
    in
    let match_pat, subst = visitor#visit_tpat pat.ty pat in
    let vars, fresh_vars = List.split subst in

    (* Create the correct branch *)
    let match_e = List.map mk_texpr_from_fvar fresh_vars in
    let match_e = mk_simpl_tuple_texpr span match_e in
    let match_branch = close_branch span match_pat match_e in
    (* Create the otherwise branch *)
    let default_e = List.map get_default_expr vars in
    let default_e = mk_simpl_tuple_texpr span default_e in
    let default_pat = mk_ignored_pat pat.ty in
    let default_branch = close_branch span default_pat default_e in
    let switch_e = Switch (bound, Match [ match_branch; default_branch ]) in
    let bound = { e = switch_e; ty = match_e.ty } in
    (* Update the pattern itself *)
    let pat = mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) vars) in
    (* *)
    (pat, bound)
  else (* Nothing to do *)
    (pat, bound)

let is_result_fail (e : texpr) : bool =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif
      {
        id = AdtCons { adt_id = TBuiltin TResult; variant_id = Some variant_id };
        _;
      }
    when variant_id = result_fail_id -> List.length args = 1
  | _ -> false

let is_result_ok (e : texpr) : bool =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif
      {
        id = AdtCons { adt_id = TBuiltin TResult; variant_id = Some variant_id };
        _;
      }
    when variant_id = result_ok_id -> List.length args = 1
  | _ -> false

let is_loop_result_fail_break_continue (e : texpr) : bool =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif
      {
        id =
          AdtCons
            { adt_id = TBuiltin TLoopResult; variant_id = Some variant_id };
        _;
      }
    when variant_id = loop_result_break_id
         || variant_id = loop_result_continue_id
         || variant_id = loop_result_fail_id -> List.length args = 1
  | _ -> false

let get_tuple_size (e : texpr) : int option =
  let f, args = destruct_apps e in
  match f.e with
  | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ } -> Some (List.length args)
  | _ -> None
