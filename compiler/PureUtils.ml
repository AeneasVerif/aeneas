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

let dest_arrow_ty (ty : ty) : ty * ty =
  match ty with
  | TArrow (arg_ty, ret_ty) -> (arg_ty, ret_ty)
  | _ -> raise (Failure "Unreachable")

let compute_literal_type (cv : literal) : literal_type =
  match cv with
  | VScalar sv -> TInteger sv.int_ty
  | VBool _ -> TBool
  | VChar _ -> TChar

let var_get_id (v : var) : VarId.id = v.id

let mk_typed_pattern_from_literal (cv : literal) : typed_pattern =
  let ty = TLiteral (compute_literal_type cv) in
  { value = PatConstant cv; ty }

let mk_let (monadic : bool) (lv : typed_pattern) (re : texpression)
    (next_e : texpression) : texpression =
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

let mk_tag (msg : string) (next_e : texpression) : texpression =
  let e = Meta (Tag msg, next_e) in
  let ty = next_e.ty in
  { e; ty }

let mk_mplace (var_id : E.VarId.id) (name : string option)
    (projection : mprojection) : mplace =
  { var_id; name; projection }

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

(** Type substitution *)
let ty_substitute (subst : subst) (ty : ty) : ty =
  let obj =
    object
      inherit [_] map_ty
      method! visit_TVar _ var_id = subst.ty_subst var_id
      method! visit_CGVar _ var_id = subst.cg_subst var_id
      method! visit_Clause _ id = subst.tr_subst id
      method! visit_Self _ = subst.tr_self
    end
  in
  obj#visit_ty () ty

let make_type_subst (vars : type_var list) (tys : ty list) : TypeVarId.id -> ty
    =
  let ls = List.combine vars tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TypeVarId.Map.add (k : type_var).index v mp)
      TypeVarId.Map.empty ls
  in
  fun id -> TypeVarId.Map.find id mp

let make_const_generic_subst (vars : const_generic_var list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  Substitute.make_const_generic_subst_from_vars vars cgs

let make_trait_subst (clauses : trait_clause list) (refs : trait_ref list) :
    TraitClauseId.id -> trait_instance_id =
  let clauses = List.map (fun x -> x.clause_id) clauses in
  let refs = List.map (fun x -> TraitRef x) refs in
  let ls = List.combine clauses refs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TraitClauseId.Map.add k v mp)
      TraitClauseId.Map.empty ls
  in
  fun id -> TraitClauseId.Map.find id mp

(** Retrieve the list of fields for the given variant of a {!type:Aeneas.Pure.type_decl}.

    Raises [Invalid_argument] if the arguments are incorrect.
 *)
let type_decl_get_fields (def : type_decl)
    (opt_variant_id : VariantId.id option) : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      let opt_variant_id =
        match opt_variant_id with None -> "None" | Some _ -> "Some"
      in
      raise
        (Invalid_argument
           ("The variant id should be [Some] if and only if the definition is \
             an enumeration:\n\
             - def: " ^ show_type_decl def ^ "\n- opt_variant_id: "
          ^ opt_variant_id))

let make_subst_from_generics (params : generic_params) (args : generic_args)
    (tr_self : trait_instance_id) : subst =
  let ty_subst = make_type_subst params.types args.types in
  let cg_subst =
    make_const_generic_subst params.const_generics args.const_generics
  in
  let tr_subst = make_trait_subst params.trait_clauses args.trait_refs in
  { ty_subst; cg_subst; tr_subst; tr_self }

(** Instantiate the type variables for the chosen variant in an ADT definition,
    and return the list of the types of its fields *)
let type_decl_get_instantiated_fields_types (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.generics generics tr_self in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.field_ty) fields

let fun_sig_substitute (subst : subst) (sg : fun_sig) : inst_fun_sig =
  let subst = ty_substitute subst in
  let inputs = List.map subst sg.inputs in
  let output = subst sg.output in
  let doutputs = List.map subst sg.doutputs in
  let info = sg.info in
  { inputs; output; doutputs; info }

(** We use this to check whether we need to add parentheses around expressions.
    We only look for outer monadic let-bindings.
    This is used when printing the branches of [if ... then ... else ...].

    Rem.: this function will *fail* if there are {!constructor:Aeneas.Pure.expression.Loop}
    nodes (you should call it on an expression where those nodes have been eliminated).
 *)
let rec let_group_requires_parentheses (e : texpression) : bool =
  match e.e with
  | Var _ | CVar _ | Const _ | App _ | Abs _ | Qualif _ | StructUpdate _ ->
      false
  | Let (monadic, _, _, next_e) ->
      if monadic then true else let_group_requires_parentheses next_e
  | Switch (_, _) -> false
  | Meta (_, next_e) -> let_group_requires_parentheses next_e
  | Loop _ ->
      (* Should have been eliminated *)
      raise (Failure "Unreachable")

let texpression_requires_parentheses e =
  match !Config.backend with
  | FStar | Lean -> false
  | Coq | HOL4 -> let_group_requires_parentheses e

let is_var (e : texpression) : bool =
  match e.e with Var _ -> true | _ -> false

let as_var (e : texpression) : VarId.id =
  match e.e with Var v -> v | _ -> raise (Failure "Unreachable")

let is_cvar (e : texpression) : bool =
  match e.e with CVar _ -> true | _ -> false

let is_global (e : texpression) : bool =
  match e.e with Qualif { id = Global _; _ } -> true | _ -> false

let is_const (e : texpression) : bool =
  match e.e with Const _ -> true | _ -> false

let ty_as_adt (ty : ty) : type_id * generic_args =
  match ty with
  | TAdt (id, generics) -> (id, generics)
  | _ -> raise (Failure "Unreachable")

(** Remove the external occurrences of {!Meta} *)
let rec unmeta (e : texpression) : texpression =
  match e.e with Meta (_, e) -> unmeta e | _ -> e

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

(** Construct a type as a list of arrows: ty1 -> ... tyn  *)
let mk_arrows (inputs : ty list) (output : ty) =
  let rec aux (tys : ty list) : ty =
    match tys with [] -> output | ty :: tys' -> TArrow (ty, aux tys')
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

(** Destruct an expression into a list of nested lets, where there
    is no interleaving between monadic and non-monadic lets.
 *)
let destruct_lets_no_interleave (e : texpression) :
    (bool * typed_pattern * texpression) list * texpression =
  (* Find the "kind" of the first let (monadic or non-monadic) *)
  let m =
    match e.e with
    | Let (monadic, _, _, _) -> monadic
    | _ -> raise (Failure "Unreachable")
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
    match e.e with App (f, x) -> aux (x :: args) f | _ -> (e, args)
  in
  aux [] e

(** Make an [App (app, arg)] expression *)
let mk_app (app : texpression) (arg : texpression) : texpression =
  match app.ty with
  | TArrow (ty0, ty1) ->
      (* Sanity check *)
      assert (ty0 = arg.ty);
      let e = App (app, arg) in
      let ty = ty1 in
      { e; ty }
  | _ -> raise (Failure "Expected an arrow type")

(** The reverse of {!destruct_apps} *)
let mk_apps (app : texpression) (args : texpression list) : texpression =
  List.fold_left (fun app arg -> mk_app app arg) app args

(** Destruct an expression into a qualif identifier and a list of arguments,
 *  if possible *)
let opt_destruct_qualif_app (e : texpression) :
    (qualif * texpression list) option =
  let app, args = destruct_apps e in
  match app.e with Qualif qualif -> Some (qualif, args) | _ -> None

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

let opt_destruct_result (ty : ty) : ty option =
  match ty with
  | TAdt (TAssumed TResult, generics) ->
      assert (generics.const_generics = []);
      assert (generics.trait_refs = []);
      Some (Collections.List.to_cons_nil generics.types)
  | _ -> None

let destruct_result (ty : ty) : ty = Option.get (opt_destruct_result ty)

let opt_destruct_tuple (ty : ty) : ty list option =
  match ty with
  | TAdt (TTuple, generics) ->
      assert (generics.const_generics = []);
      assert (generics.trait_refs = []);
      Some generics.types
  | _ -> None

let mk_abs (x : typed_pattern) (e : texpression) : texpression =
  let ty = TArrow (x.ty, e.ty) in
  let e = Abs (x, e) in
  { e; ty }

let rec destruct_abs_list (e : texpression) : typed_pattern list * texpression =
  match e.e with
  | Abs (x, e') ->
      let xl, e'' = destruct_abs_list e' in
      (x :: xl, e'')
  | _ -> ([], e)

let destruct_arrow (ty : ty) : ty * ty =
  match ty with
  | TArrow (ty0, ty1) -> (ty0, ty1)
  | _ -> raise (Failure "Not an arrow type")

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

let mk_switch (scrut : texpression) (sb : switch_body) : texpression =
  (* Sanity check: the scrutinee has the proper type *)
  (match sb with
  | If (_, _) -> assert (scrut.ty = TLiteral TBool)
  | Match branches ->
      List.iter
        (fun (b : match_branch) -> assert (b.pat.ty = scrut.ty))
        branches);
  (* Sanity check: all the branches have the same type *)
  let ty = get_switch_body_ty sb in
  iter_switch_body_branches (fun e -> assert (e.ty = ty)) sb;
  (* Put together *)
  let e = Switch (scrut, sb) in
  { e; ty }

(** Make a "simplified" tuple type from a list of types:
    - if there is exactly one type, just return it
    - if there is > one type: wrap them in a tuple
 *)
let mk_simpl_tuple_ty (tys : ty list) : ty =
  match tys with
  | [ ty ] -> ty
  | _ -> TAdt (TTuple, mk_generic_args_from_types tys)

let mk_bool_ty : ty = TLiteral TBool
let mk_unit_ty : ty = TAdt (TTuple, empty_generic_args)

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

let mk_meta (m : meta) (e : texpression) : texpression =
  let ty = e.ty in
  let e = Meta (m, e) in
  { e; ty }

let mk_mplace_texpression (mp : mplace) (e : texpression) : texpression =
  mk_meta (MPlace mp) e

let mk_opt_mplace_texpression (mp : mplace option) (e : texpression) :
    texpression =
  match mp with None -> e | Some mp -> mk_mplace_texpression mp e

(** Make a "simplified" tuple value from a list of values:
    - if there is exactly one value, just return it
    - if there is > one value: wrap them in a tuple
 *)
let mk_simpl_tuple_pattern (vl : typed_pattern list) : typed_pattern =
  match vl with
  | [ v ] -> v
  | _ ->
      let tys = List.map (fun (v : typed_pattern) -> v.ty) vl in
      let ty = TAdt (TTuple, mk_generic_args_from_types tys) in
      let value = PatAdt { variant_id = None; field_values = vl } in
      { value; ty }

(** Similar to {!mk_simpl_tuple_pattern} *)
let mk_simpl_tuple_texpression (vl : texpression list) : texpression =
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
      mk_apps cons vl

let mk_adt_pattern (adt_ty : ty) (variant_id : VariantId.id option)
    (vl : typed_pattern list) : typed_pattern =
  let value = PatAdt { variant_id; field_values = vl } in
  { value; ty = adt_ty }

let ty_as_integer (t : ty) : T.integer_type =
  match t with
  | TLiteral (TInteger int_ty) -> int_ty
  | _ -> raise (Failure "Unreachable")

let ty_as_literal (t : ty) : T.literal_type =
  match t with TLiteral ty -> ty | _ -> raise (Failure "Unreachable")

let mk_state_ty : ty = TAdt (TAssumed TState, empty_generic_args)

let mk_result_ty (ty : ty) : ty =
  TAdt (TAssumed TResult, mk_generic_args_from_types [ ty ])

let mk_error_ty : ty = TAdt (TAssumed TError, empty_generic_args)
let mk_fuel_ty : ty = TAdt (TAssumed TFuel, empty_generic_args)

let mk_error (error : VariantId.id) : texpression =
  let ty = mk_error_ty in
  let id = AdtCons { adt_id = TAssumed TError; variant_id = Some error } in
  let qualif = { id; generics = empty_generic_args } in
  let e = Qualif qualif in
  { e; ty }

let unwrap_result_ty (ty : ty) : ty =
  match ty with
  | TAdt
      ( TAssumed TResult,
        { types = [ ty ]; const_generics = []; trait_refs = [] } ) ->
      ty
  | _ -> raise (Failure "not a result type")

let mk_result_fail_texpression (error : texpression) (ty : ty) : texpression =
  let type_args = [ ty ] in
  let ty = TAdt (TAssumed TResult, mk_generic_args_from_types type_args) in
  let id =
    AdtCons { adt_id = TAssumed TResult; variant_id = Some result_fail_id }
  in
  let qualif = { id; generics = mk_generic_args_from_types type_args } in
  let cons_e = Qualif qualif in
  let cons_ty = mk_arrow error.ty ty in
  let cons = { e = cons_e; ty = cons_ty } in
  mk_app cons error

let mk_result_fail_texpression_with_error_id (error : VariantId.id) (ty : ty) :
    texpression =
  let error = mk_error error in
  mk_result_fail_texpression error ty

let mk_result_return_texpression (v : texpression) : texpression =
  let type_args = [ v.ty ] in
  let ty = TAdt (TAssumed TResult, mk_generic_args_from_types type_args) in
  let id =
    AdtCons { adt_id = TAssumed TResult; variant_id = Some result_return_id }
  in
  let qualif = { id; generics = mk_generic_args_from_types type_args } in
  let cons_e = Qualif qualif in
  let cons_ty = mk_arrow v.ty ty in
  let cons = { e = cons_e; ty = cons_ty } in
  mk_app cons v

(** Create a [Fail err] pattern which captures the error *)
let mk_result_fail_pattern (error_pat : pattern) (ty : ty) : typed_pattern =
  let error_pat : typed_pattern = { value = error_pat; ty = mk_error_ty } in
  let ty = TAdt (TAssumed TResult, mk_generic_args_from_types [ ty ]) in
  let value =
    PatAdt { variant_id = Some result_fail_id; field_values = [ error_pat ] }
  in
  { value; ty }

(** Create a [Fail _] pattern (we ignore the error) *)
let mk_result_fail_pattern_ignore_error (ty : ty) : typed_pattern =
  let error_pat : pattern = PatDummy in
  mk_result_fail_pattern error_pat ty

let mk_result_return_pattern (v : typed_pattern) : typed_pattern =
  let ty = TAdt (TAssumed TResult, mk_generic_args_from_types [ v.ty ]) in
  let value =
    PatAdt { variant_id = Some result_return_id; field_values = [ v ] }
  in
  { value; ty }

let opt_unmeta_mplace (e : texpression) : mplace option * texpression =
  match e.e with Meta (MPlace mp, e) -> (Some mp, e) | _ -> (None, e)

let mk_state_var (id : VarId.id) : var =
  { id; basename = Some ConstStrings.state_basename; ty = mk_state_ty }

let mk_state_texpression (id : VarId.id) : texpression =
  { e = Var id; ty = mk_state_ty }

let mk_fuel_var (id : VarId.id) : var =
  { id; basename = Some ConstStrings.fuel_basename; ty = mk_fuel_ty }

let mk_fuel_texpression (id : VarId.id) : texpression =
  { e = Var id; ty = mk_fuel_ty }

let rec typed_pattern_to_texpression (pat : typed_pattern) : texpression option
    =
  let e_opt =
    match pat.value with
    | PatConstant pv -> Some (Const pv)
    | PatVar (v, _) -> Some (Var v.id)
    | PatDummy -> None
    | PatAdt av ->
        let fields = List.map typed_pattern_to_texpression av.field_values in
        if List.mem None fields then None
        else
          let fields_values = List.map (fun e -> Option.get e) fields in

          (* Retrieve the type id and the type args from the pat type (simpler this way *)
          let adt_id, generics = ty_as_adt pat.ty in

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
          Some (mk_apps cons fields_values).e
  in
  match e_opt with None -> None | Some e -> Some { e; ty = pat.ty }

type trait_decl_method_decl_id = { is_provided : bool; id : fun_decl_id }

let trait_decl_get_method (trait_decl : trait_decl) (method_name : string) :
    trait_decl_method_decl_id =
  (* First look in the required methods *)
  let method_id =
    List.find_opt (fun (s, _) -> s = method_name) trait_decl.required_methods
  in
  match method_id with
  | Some (_, id) -> { is_provided = false; id }
  | None ->
      (* Must be a provided method *)
      let _, id =
        List.find (fun (s, _) -> s = method_name) trait_decl.provided_methods
      in
      { is_provided = true; id = Option.get id }

let trait_decl_is_empty (trait_decl : trait_decl) : bool =
  let {
    def_id = _;
    name = _;
    llbc_name = _;
    generics = _;
    preds = _;
    parent_clauses;
    consts;
    types;
    required_methods;
    provided_methods;
  } =
    trait_decl
  in
  parent_clauses = [] && consts = [] && types = [] && required_methods = []
  && provided_methods = []

let trait_impl_is_empty (trait_impl : trait_impl) : bool =
  let {
    def_id = _;
    name = _;
    llbc_name = _;
    impl_trait = _;
    generics = _;
    preds = _;
    parent_trait_refs;
    consts;
    types;
    required_methods;
    provided_methods;
  } =
    trait_impl
  in
  parent_trait_refs = [] && consts = [] && types = [] && required_methods = []
  && provided_methods = []
