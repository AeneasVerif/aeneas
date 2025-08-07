open Pure

(** Default logger *)
let log = Logging.pure_utils_log

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
  type t = expression

  let compare = compare_expression
  let to_string = show_expression
  let pp_t = pp_expression
  let show_t = show_expression
end

module ExprMap = Collections.MakeMap (ExprOrderedType)
module ExprSet = Collections.MakeSet (ExprOrderedType)

module TExprOrderedType = struct
  type t = texpression

  let compare = compare_texpression
  let to_string = show_texpression
  let pp_t = pp_texpression
  let show_t = show_texpression
end

module TExprMap = Collections.MakeMap (TExprOrderedType)
module TExprSet = Collections.MakeSet (TExprOrderedType)

let inputs_info_is_wf (info : inputs_info) : bool =
  let {
    has_fuel;
    num_inputs_no_fuel_no_state;
    num_inputs_with_fuel_no_state;
    num_inputs_with_fuel_with_state;
  } =
    info
  in
  let fuel = if has_fuel then 1 else 0 in
  num_inputs_no_fuel_no_state >= 0
  && num_inputs_with_fuel_no_state = num_inputs_no_fuel_no_state + fuel
  && num_inputs_with_fuel_with_state >= num_inputs_with_fuel_no_state

let fun_sig_info_is_wf (info : fun_sig_info) : bool =
  inputs_info_is_wf info.fwd_info

let opt_dest_arrow_ty (ty : ty) : (ty * ty) option =
  match ty with
  | TArrow (arg_ty, ret_ty) -> Some (arg_ty, ret_ty)
  | _ -> None

let is_arrow_ty (ty : ty) : bool = Option.is_some (opt_dest_arrow_ty ty)

let opt_dest_result_ty (ty : ty) : ty option =
  match ty with
  | TAdt
      ( TBuiltin TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) -> Some ty
  | _ -> None

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

let var_get_id (v : var) : LocalId.id = v.id

let mk_typed_pattern_from_literal (cv : literal) : typed_pattern =
  let ty = TLiteral (compute_literal_type cv) in
  { value = PatConstant cv; ty }

let mk_let (monadic : bool) (lv : typed_pattern) (re : texpression)
    (next_e : texpression) : texpression =
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

let mk_lets (monadic : bool) (lets : (typed_pattern * texpression) list)
    (next_e : texpression) : texpression =
  List.fold_right
    (fun (pat, value) (e : texpression) -> mk_let monadic pat value e)
    lets next_e

let mk_tag (msg : string) (next_e : texpression) : texpression =
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

let subst_visitor =
  object
    inherit [_] map_ty

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
  subst_visitor#visit_ty subst ty

let make_type_subst (vars : type_var list) (tys : ty list) : TypeVarId.id -> ty
    =
  let var_ids = List.map (fun k -> (k : type_var).index) vars in
  let mp = TypeVarId.Map.of_list (List.combine var_ids tys) in
  fun id -> TypeVarId.Map.find id mp

let make_const_generic_subst (vars : const_generic_var list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  Substitute.make_const_generic_subst_from_vars vars cgs

let make_trait_subst (clauses : trait_clause list) (refs : trait_ref list) :
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
let rec let_group_requires_parentheses (span : Meta.span) (e : texpression) :
    bool =
  match e.e with
  | Var _ | CVar _ | Const _ | App _ | Qualif _ | StructUpdate _ -> false
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

let texpression_requires_parentheses span e =
  match Config.backend () with
  | FStar | Lean -> false
  | Coq | HOL4 -> let_group_requires_parentheses span e

let is_var (e : texpression) : bool =
  match e.e with
  | Var _ -> true
  | _ -> false

let as_var (span : Meta.span) (e : texpression) : LocalId.id =
  match e.e with
  | Var v -> v
  | _ -> [%craise] span "Not a var"

let is_cvar (e : texpression) : bool =
  match e.e with
  | CVar _ -> true
  | _ -> false

let as_opt_pat_var (p : typed_pattern) : (var * mplace option) option =
  match p.value with
  | PatVar (v, mp) -> Some (v, mp)
  | _ -> None

let as_pat_var (span : Meta.span) (p : typed_pattern) : var * mplace option =
  match as_opt_pat_var p with
  | None -> [%craise] span "Not a var"
  | Some (v, mp) -> (v, mp)

let is_pat_var (p : typed_pattern) : bool = Option.is_some (as_opt_pat_var p)

let as_opt_pat_tuple (p : typed_pattern) : typed_pattern list option =
  match p with
  | {
   value = PatAdt { variant_id = None; field_values };
   ty = TAdt (TTuple, _);
  } -> Some field_values
  | _ -> None

(** Replace all the dummy variables in a pattern with fresh variables *)
let typed_pattern_replace_dummy_vars (fresh_var_id : unit -> LocalId.id)
    (p : typed_pattern) : typed_pattern =
  let visitor =
    object
      inherit [_] map_typed_pattern as super

      method! visit_typed_pattern env p =
        match p.value with
        | PatDummy ->
            let id = fresh_var_id () in
            { p with value = PatVar ({ id; basename = None; ty = p.ty }, None) }
        | _ -> super#visit_typed_pattern env p
    end
  in
  visitor#visit_typed_pattern () p

let is_pat_tuple (p : typed_pattern) : bool =
  Option.is_some (as_opt_pat_tuple p)

let is_global (e : texpression) : bool =
  match e.e with
  | Qualif { id = Global _; _ } -> true
  | _ -> false

let is_const (e : texpression) : bool =
  match e.e with
  | Const _ -> true
  | _ -> false

let is_adt_cons (e : texpression) : bool =
  match e.e with
  | Qualif { id = AdtCons _; _ } -> true
  | _ -> false

let is_fail_panic (e : expression) : bool =
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
let rec unmeta (e : texpression) : texpression =
  match e.e with
  | Meta (_, e) -> unmeta e
  | _ -> e

(** Remove *all* the meta information *)
let remove_meta (e : texpression) : texpression =
  let obj =
    object
      inherit [_] map_expression as super
      method! visit_Meta env _ e = super#visit_expression env e.e
    end
  in
  obj#visit_texpression () e

let mk_arrow (ty0 : ty) (ty1 : ty) : ty = TArrow (ty0, ty1)

(** Construct a type as a list of arrows: ty1 -> ... tyn *)
let mk_arrows (inputs : ty list) (output : ty) =
  let rec aux (tys : ty list) : ty =
    match tys with
    | [] -> output
    | ty :: tys' -> TArrow (ty, aux tys')
  in
  aux inputs

(** Destruct an expression into a list of nested lets *)
let rec destruct_lets (e : texpression) :
    (bool * typed_pattern * texpression) list * texpression =
  match e.e with
  | Let (monadic, lv, re, next_e) ->
      let lets, last_e = destruct_lets next_e in
      ((monadic, lv, re) :: lets, last_e)
  | _ -> ([], e)

(** Destruct an expression into a list of nested lets, where there is no
    interleaving between monadic and non-monadic lets. *)
let destruct_lets_no_interleave (span : Meta.span) (e : texpression) :
    (bool * typed_pattern * texpression) list * texpression =
  (* Find the "kind" of the first let (monadic or non-monadic) *)
  let m =
    match e.e with
    | Let (monadic, _, _, _) -> monadic
    | _ -> [%craise] span "Not a let-binding"
  in
  (* Destruct the rest *)
  let rec destruct_lets (e : texpression) :
      (bool * typed_pattern * texpression) list * texpression =
    match e.e with
    | Let (monadic, lv, re, next_e) ->
        if monadic = m then
          let lets, last_e = destruct_lets next_e in
          ((monadic, lv, re) :: lets, last_e)
        else ([], e)
    | _ -> ([], e)
  in
  destruct_lets e

(** Destruct an [App] expression into an expression and a list of arguments.

    We simply destruct the expression as long as it is of the form [App (f, x)].
*)
let destruct_apps (e : texpression) : texpression * texpression list =
  let rec aux (args : texpression list) (e : texpression) :
      texpression * texpression list =
    match e.e with
    | App (f, x) -> aux (x :: args) f
    | _ -> (e, args)
  in
  aux [] e

(** Make an [App (app, arg)] expression *)
let mk_app (span : Meta.span) (app : texpression) (arg : texpression) :
    texpression =
  let raise_or_return msg =
    (* We shouldn't get there, so we save an error (and eventually raise an exception) *)
    [%save_error] span msg;
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
let mk_apps (span : Meta.span) (app : texpression) (args : texpression list) :
    texpression =
  List.fold_left (fun app arg -> mk_app span app arg) app args

(** Destruct an expression into a qualif identifier and a list of arguments, *
    if possible *)
let opt_destruct_qualif_app (e : texpression) :
    (qualif * texpression list) option =
  let app, args = destruct_apps e in
  match app.e with
  | Qualif qualif -> Some (qualif, args)
  | _ -> None

(** Destruct an expression into a qualif identifier and a list of arguments *)
let destruct_qualif_app (e : texpression) : qualif * texpression list =
  Option.get (opt_destruct_qualif_app e)

(** Destruct an expression into a function call, if possible *)
let opt_destruct_function_call (e : texpression) :
    (fun_or_op_id * generic_args * texpression list) option =
  match opt_destruct_qualif_app e with
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

let map_switch_body_branches (f : texpression -> texpression) (sb : switch_body)
    : switch_body =
  match sb with
  | If (e_then, e_else) -> If (f e_then, f e_else)
  | Match branches ->
      Match
        (List.map
           (fun (b : match_branch) -> { b with branch = f b.branch })
           branches)

let iter_switch_body_branches (f : texpression -> unit) (sb : switch_body) :
    unit =
  match sb with
  | If (e_then, e_else) ->
      f e_then;
      f e_else
  | Match branches -> List.iter (fun (b : match_branch) -> f b.branch) branches

let mk_switch (span : Meta.span) (scrut : texpression) (sb : switch_body) :
    texpression =
  (* Sanity check: the scrutinee has the proper type *)
  (match sb with
  | If (_, _) -> [%sanity_check] span (scrut.ty = TLiteral TBool)
  | Match branches ->
      List.iter
        (fun (b : match_branch) -> [%sanity_check] span (b.pat.ty = scrut.ty))
        branches);
  (* Sanity check: all the branches have the same type *)
  let ty = get_switch_body_ty sb in
  iter_switch_body_branches (fun e -> [%sanity_check] span (e.ty = ty)) sb;
  (* Put together *)
  let e = Switch (scrut, sb) in
  { e; ty }

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

let mk_bool_value (b : bool) : texpression =
  { e = Const (VBool b); ty = TLiteral TBool }

let mk_true : texpression = mk_bool_value true
let mk_false : texpression = mk_bool_value false

let mk_unit_rvalue : texpression =
  let id = AdtCons { adt_id = TTuple; variant_id = None } in
  let qualif = { id; generics = empty_generic_args } in
  let e = Qualif qualif in
  let ty = mk_unit_ty in
  { e; ty }

let mk_texpression_from_var (v : var) : texpression =
  let e = Var v.id in
  let ty = v.ty in
  { e; ty }

let mk_typed_pattern_from_var (v : var) (mp : mplace option) : typed_pattern =
  let value = PatVar (v, mp) in
  let ty = v.ty in
  { value; ty }

let mk_dummy_pattern (ty : ty) : typed_pattern =
  let value = PatDummy in
  { value; ty }

let is_dummy_pattern (p : typed_pattern) : bool =
  match p.value with
  | PatDummy -> true
  | _ -> false

let mk_emeta (m : emeta) (e : texpression) : texpression =
  let ty = e.ty in
  let e = Meta (m, e) in
  { e; ty }

let mk_mplace_texpression (mp : mplace) (e : texpression) : texpression =
  mk_emeta (MPlace mp) e

let mk_opt_mplace_texpression (mp : mplace option) (e : texpression) :
    texpression =
  match mp with
  | None -> e
  | Some mp -> mk_mplace_texpression mp e

(** Make a "simplified" tuple value from a list of values:
    - if there is exactly one value, just return it
    - if there is > one value: wrap them in a tuple *)
let mk_simpl_tuple_pattern (vl : typed_pattern list) : typed_pattern =
  match vl with
  | [ v ] -> v
  | _ ->
      let tys = List.map (fun (v : typed_pattern) -> v.ty) vl in
      let ty = TAdt (TTuple, mk_generic_args_from_types tys) in
      let value = PatAdt { variant_id = None; field_values = vl } in
      { value; ty }

(** Similar to {!mk_simpl_tuple_pattern} *)
let mk_simpl_tuple_texpression (span : Meta.span) (vl : texpression list) :
    texpression =
  match vl with
  | [ v ] -> v
  | _ ->
      (* Compute the types of the fields, and the type of the tuple constructor *)
      let tys = List.map (fun (v : texpression) -> v.ty) vl in
      let ty = TAdt (TTuple, mk_generic_args_from_types tys) in
      let ty = mk_arrows tys ty in
      (* Construct the tuple constructor qualifier *)
      let id = AdtCons { adt_id = TTuple; variant_id = None } in
      let qualif = { id; generics = mk_generic_args_from_types tys } in
      (* Put everything together *)
      let cons = { e = Qualif qualif; ty } in
      mk_apps span cons vl

let mk_adt_pattern (adt_ty : ty) (variant_id : VariantId.id option)
    (vl : typed_pattern list) : typed_pattern =
  let value = PatAdt { variant_id; field_values = vl } in
  { value; ty = adt_ty }

let mk_adt_value (span : span) (adt_ty : ty) (variant_id : VariantId.id option)
    (fields : texpression list) : texpression =
  let adt_id, generics = ty_as_adt span adt_ty in
  let qualif : expression =
    Qualif { id = AdtCons { adt_id; variant_id }; generics }
  in
  let qualif_ty =
    mk_arrows (List.map (fun (f : texpression) -> f.ty) fields) adt_ty
  in
  let qualif = { e = qualif; ty = qualif_ty } in
  mk_apps span qualif fields

let mk_adt_proj (span : span) (adt : texpression) (field_id : field_id)
    (field_ty : ty) : texpression =
  let adt_id, generics = ty_as_adt span adt.ty in
  let qualif = Qualif { id = Proj { adt_id; field_id }; generics } in
  let qualif = { e = qualif; ty = mk_arrow adt.ty field_ty } in
  mk_app span qualif adt

let ty_as_integer (span : Meta.span) (t : ty) : T.integer_type =
  match t with
  | TLiteral (TInt int_ty) -> Signed int_ty
  | TLiteral (TUInt int_ty) -> Unsigned int_ty
  | _ -> [%craise] span "Unreachable"

let ty_as_literal (span : Meta.span) (t : ty) : T.literal_type =
  match t with
  | TLiteral ty -> ty
  | _ -> [%craise] span "Unreachable"

let mk_state_ty : ty = TAdt (TBuiltin TState, empty_generic_args)

let mk_result_ty (ty : ty) : ty =
  TAdt (TBuiltin TResult, mk_generic_args_from_types [ ty ])

let mk_error_ty : ty = TAdt (TBuiltin TError, empty_generic_args)
let mk_fuel_ty : ty = TAdt (TBuiltin TFuel, empty_generic_args)

let mk_error (error : VariantId.id) : texpression =
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

let mk_result_fail_texpression (span : Meta.span) (error : texpression)
    (ty : ty) : texpression =
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
  mk_app span cons error

let mk_result_fail_texpression_with_error_id (span : Meta.span)
    (error : VariantId.id) (ty : ty) : texpression =
  let error = mk_error error in
  mk_result_fail_texpression span error ty

let mk_result_ok_texpression (span : Meta.span) (v : texpression) : texpression
    =
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
  mk_app span cons v

(** Create a [Fail err] pattern which captures the error *)
let mk_result_fail_pattern (error_pat : pattern) (ty : ty) : typed_pattern =
  let error_pat : typed_pattern = { value = error_pat; ty = mk_error_ty } in
  let ty = TAdt (TBuiltin TResult, mk_generic_args_from_types [ ty ]) in
  let value =
    PatAdt { variant_id = Some result_fail_id; field_values = [ error_pat ] }
  in
  { value; ty }

(** Create a [Fail _] pattern (we ignore the error) *)
let mk_result_fail_pattern_ignore_error (ty : ty) : typed_pattern =
  let error_pat : pattern = PatDummy in
  mk_result_fail_pattern error_pat ty

let mk_result_ok_pattern (v : typed_pattern) : typed_pattern =
  let ty = TAdt (TBuiltin TResult, mk_generic_args_from_types [ v.ty ]) in
  let value = PatAdt { variant_id = Some result_ok_id; field_values = [ v ] } in
  { value; ty }

let opt_unmeta_mplace (e : texpression) : mplace option * texpression =
  match e.e with
  | Meta (MPlace mp, e) -> (Some mp, e)
  | _ -> (None, e)

let mk_state_var (id : LocalId.id) : var =
  { id; basename = Some ConstStrings.state_basename; ty = mk_state_ty }

let mk_state_texpression (id : LocalId.id) : texpression =
  { e = Var id; ty = mk_state_ty }

let mk_fuel_var (id : LocalId.id) : var =
  { id; basename = Some ConstStrings.fuel_basename; ty = mk_fuel_ty }

let mk_fuel_texpression (id : LocalId.id) : texpression =
  { e = Var id; ty = mk_fuel_ty }

let rec typed_pattern_to_texpression (span : Meta.span) (pat : typed_pattern) :
    texpression option =
  let e_opt =
    match pat.value with
    | PatConstant pv -> Some (Const pv)
    | PatVar (v, _) -> Some (Var v.id)
    | PatDummy -> None
    | PatAdt av ->
        let fields =
          List.map (typed_pattern_to_texpression span) av.field_values
        in
        if List.mem None fields then None
        else
          let fields_values = List.map (fun e -> Option.get e) fields in

          (* Retrieve the type id and the type args from the pat type (simpler this way *)
          let adt_id, generics = ty_as_adt span pat.ty in

          (* Create the constructor *)
          let qualif_id = AdtCons { adt_id; variant_id = av.variant_id } in
          let qualif = { id = qualif_id; generics } in
          let cons_e = Qualif qualif in
          let field_tys =
            List.map (fun (v : texpression) -> v.ty) fields_values
          in
          let cons_ty = mk_arrows field_tys pat.ty in
          let cons = { e = cons_e; ty = cons_ty } in

          (* Apply the constructor *)
          Some (mk_apps span cons fields_values).e
  in
  match e_opt with
  | None -> None
  | Some e -> Some { e; ty = pat.ty }

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

let mk_lambda (x : typed_pattern) (e : texpression) : texpression =
  let ty = TArrow (x.ty, e.ty) in
  let e = Lambda (x, e) in
  { e; ty }

let mk_lambdas (xl : typed_pattern list) (e : texpression) : texpression =
  List.fold_right mk_lambda xl e

let mk_lambda_from_var (var : var) (mp : mplace option) (e : texpression) :
    texpression =
  let pat = PatVar (var, mp) in
  let pat = { value = pat; ty = var.ty } in
  mk_lambda pat e

let mk_lambdas_from_vars (vars : var list) (mps : mplace option list)
    (e : texpression) : texpression =
  let vars = List.combine vars mps in
  List.fold_right (fun (v, mp) e -> mk_lambda_from_var v mp e) vars e

let rec destruct_lambdas (e : texpression) : typed_pattern list * texpression =
  match e.e with
  | Lambda (pat, e) ->
      let pats, e = destruct_lambdas e in
      (pat :: pats, e)
  | _ -> ([], e)

let opt_dest_tuple_texpression (e : texpression) : texpression list option =
  let app, args = destruct_apps e in
  match app.e with
  | Qualif { id = AdtCons { adt_id = TTuple; variant_id = None }; generics = _ }
    -> Some args
  | _ -> None

let opt_dest_struct_pattern (pat : typed_pattern) : typed_pattern list option =
  match pat.value with
  | PatAdt { variant_id = None; field_values } -> Some field_values
  | _ -> None

(** Destruct a [ret ...] expression *)
let opt_destruct_ret (e : texpression) : texpression option =
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

let texpression_get_vars (e : texpression) : LocalId.Set.t =
  let vars = ref LocalId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expression
      method! visit_Var _ var_id = vars := LocalId.Set.add var_id !vars
    end
  in
  visitor#visit_texpression () e;
  !vars

let typed_pattern_get_vars (pat : typed_pattern) : LocalId.Set.t =
  let vars = ref LocalId.Set.empty in
  let visitor =
    object
      inherit [_] iter_expression
      method! visit_PatVar _ var _ = vars := LocalId.Set.add var.id !vars
    end
  in
  visitor#visit_typed_pattern () pat;
  !vars

let mk_to_result_texpression (span : Meta.span) (e : texpression) : texpression
    =
  let type_args = [ e.ty ] in
  let generics = mk_generic_args_from_types type_args in
  let ty = TAdt (TBuiltin TResult, generics) in
  let id = FunOrOp (Fun (Pure ToResult)) in
  let qualif = { id; generics } in
  let qualif = Qualif qualif in
  let qualif_ty = mk_arrow e.ty ty in
  let qualif = { e = qualif; ty = qualif_ty } in
  mk_app span qualif e

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
  List.iter (visitor#visit_trait_clause ()) generics.trait_clauses;
  List.iter (visitor#visit_ty ()) input_tys;
  let make_explicit_ty (v : Pure.type_var) : Pure.explicit =
    if Pure.TypeVarId.Set.mem v.index !implicit_tys then Implicit else Explicit
  in
  let make_explicit_cg (v : Pure.const_generic_var) : Pure.explicit =
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
  List.iter (visitor#visit_trait_clause ()) generics.trait_clauses;
  let make_known_ty ((e, v) : explicit * Pure.type_var) : Pure.known =
    if e = Explicit || Pure.TypeVarId.Set.mem v.index !known_tys then Known
    else Unknown
  in
  let make_known_cg ((e, v) : explicit * Pure.const_generic_var) : Pure.known =
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

let mk_checked_let file line span (monadic : bool) (lv : typed_pattern)
    (re : texpression) (next_e : texpression) : texpression =
  let re_ty = if monadic then unwrap_result_ty span re.ty else re.ty in
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span (lv.ty = re_ty);
  mk_let monadic lv re next_e

let mk_checked_lets file line span (monadic : bool)
    (lets : (typed_pattern * texpression) list) (next_e : texpression) :
    texpression =
  if !Config.type_check_pure_code then
    Errors.sanity_check file line span
      (List.for_all
         (fun ((pat, e) : typed_pattern * texpression) ->
           let e_ty = if monadic then unwrap_result_ty span e.ty else e.ty in
           pat.ty = e_ty)
         lets);
  mk_lets monadic lets next_e

(** Wrap a function body in a match over the fuel to control termination. *)
let wrap_in_match_fuel (span : Meta.span) (fuel0 : LocalId.id)
    (fuel : LocalId.id) (body : texpression) : texpression =
  let fuel0_var : var = mk_fuel_var fuel0 in
  let fuel0 = mk_texpression_from_var fuel0_var in
  let nfuel_var : var = mk_fuel_var fuel in
  let nfuel_pat = mk_typed_pattern_from_var nfuel_var None in
  let fail_branch =
    mk_result_fail_texpression_with_error_id span error_out_of_fuel_id body.ty
  in
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
        mk_app span func fuel0
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
        mk_app span func fuel0
      in

      (* Create the success branch *)
      let monadic = false in
      let success_branch =
        mk_checked_let __FILE__ __LINE__ span monadic nfuel_pat decrease_fuel
          body
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
