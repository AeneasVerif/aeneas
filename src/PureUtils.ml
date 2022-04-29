open Pure

(** Default logger *)
let log = Logging.pure_utils_log

type regular_fun_id = A.fun_id * T.RegionGroupId.id option
[@@deriving show, ord]
(** We use this type as a key for lookups *)

module RegularFunIdOrderedType = struct
  type t = regular_fun_id

  let compare = compare_regular_fun_id

  let to_string = show_regular_fun_id

  let pp_t = pp_regular_fun_id

  let show_t = show_regular_fun_id
end

module RegularFunIdMap = Collections.MakeMap (RegularFunIdOrderedType)

module FunIdOrderedType = struct
  type t = fun_id

  let compare = compare_fun_id

  let to_string = show_fun_id

  let pp_t = pp_fun_id

  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

(* TODO : move *)
let binop_can_fail (binop : E.binop) : bool =
  match binop with
  | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt -> false
  | Div | Rem | Add | Sub | Mul -> true
  | Shl | Shr -> raise Errors.Unimplemented

(*let mk_arrow_ty (arg_ty : ty) (ret_ty : ty) : ty = Arrow (arg_ty, ret_ty)*)

let dest_arrow_ty (ty : ty) : ty * ty =
  match ty with
  | Arrow (arg_ty, ret_ty) -> (arg_ty, ret_ty)
  | _ -> raise (Failure "Unreachable")

let compute_constant_value_ty (cv : constant_value) : ty =
  match cv with
  | V.Scalar sv -> Integer sv.V.int_ty
  | Bool _ -> Bool
  | Char _ -> Char
  | String _ -> Str

let mk_typed_lvalue_from_constant_value (cv : constant_value) : typed_lvalue =
  let ty = compute_constant_value_ty cv in
  { value = LvConcrete cv; ty }

(*let mk_value_expression (v : typed_rvalue) (mp : mplace option) : texpression =
    let e = Value (v, mp) in
    let ty = v.ty in
  { e; ty }*)

let mk_let (monadic : bool) (lv : typed_lvalue) (re : texpression)
    (next_e : texpression) : texpression =
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

(** Type substitution *)
let ty_substitute (tsubst : TypeVarId.id -> ty) (ty : ty) : ty =
  let obj =
    object
      inherit [_] map_ty

      method! visit_TypeVar _ var_id = tsubst var_id
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

(** Retrieve the list of fields for the given variant of a [type_decl].

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

(** Instantiate the type variables for the chosen variant in an ADT definition,
    and return the list of the types of its fields *)
let type_decl_get_instantiated_fields_types (def : type_decl)
    (opt_variant_id : VariantId.id option) (types : ty list) : ty list =
  let ty_subst = make_type_subst def.type_params types in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute ty_subst f.field_ty) fields

let fun_sig_substitute (tsubst : TypeVarId.id -> ty) (sg : fun_sig) :
    inst_fun_sig =
  let subst = ty_substitute tsubst in
  let inputs = List.map subst sg.inputs in
  let outputs = List.map subst sg.outputs in
  { inputs; outputs }

(** Return true if a list of functions are *not* mutually recursive, false otherwise.
    This function is meant to be applied on a set of (forward, backwards) functions
    generated for one recursive function.
    The way we do the test is very simple:
    - we explore the functions one by one, in the order
    - if all functions only call functions we already explored, they are not
      mutually recursive
 *)
let functions_not_mutually_recursive (funs : fun_decl list) : bool =
  (* Compute the set of function identifiers in the group *)
  let ids =
    FunIdSet.of_list
      (List.map
         (fun (f : fun_decl) -> Regular (A.Regular f.def_id, f.back_id))
         funs)
  in
  let ids = ref ids in
  (* Explore every body *)
  let body_only_calls_itself (fdef : fun_decl) : bool =
    (* Remove the current id from the id set *)
    ids := FunIdSet.remove (Regular (A.Regular fdef.def_id, fdef.back_id)) !ids;

    (* Check if we call functions from the updated id set *)
    let obj =
      object
        inherit [_] iter_expression as super

        method! visit_qualif env qualif =
          match qualif.id with
          | Func fun_id ->
              if FunIdSet.mem fun_id !ids then raise Utils.Found
              else super#visit_qualif env qualif
          | _ -> super#visit_qualif env qualif
      end
    in

    try
      match fdef.body with
      | None -> true
      | Some body ->
          obj#visit_texpression () body.body;
          true
    with Utils.Found -> false
  in
  List.for_all body_only_calls_itself funs

(** We use this to check whether we need to add parentheses around expressions.
    We only look for outer monadic let-bindings.
    This is used when printing the branches of `if ... then ... else ...`.
 *)
let rec let_group_requires_parentheses (e : texpression) : bool =
  match e.e with
  | Local _ | Const _ | App _ | Abs _ | Qualif _ -> false
  | Let (monadic, _, _, next_e) ->
      if monadic then true else let_group_requires_parentheses next_e
  | Switch (_, _) -> false
  | Meta (_, next_e) -> let_group_requires_parentheses next_e

let is_var (e : texpression) : bool =
  match e.e with Local _ -> true | _ -> false

let as_var (e : texpression) : VarId.id =
  match e.e with Local v -> v | _ -> raise (Failure "Unreachable")

(** Remove the external occurrences of [Meta] *)
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

let mk_arrow (ty0 : ty) (ty1 : ty) : ty = Arrow (ty0, ty1)

(** Construct a type as a list of arrows: ty1 -> ... tyn  *)
let mk_arrows (inputs : ty list) (output : ty) =
  let rec aux (tys : ty list) : ty =
    match tys with [] -> output | ty :: tys' -> Arrow (ty, aux tys')
  in
  aux inputs

(** Destruct an `App` expression into an expression and a list of arguments.

    We simply destruct the expression as long as it is of the form `App (f, x)`.
 *)
let destruct_apps (e : texpression) : texpression * texpression list =
  let rec aux (args : texpression list) (e : texpression) :
      texpression * texpression list =
    match e.e with App (f, x) -> aux (x :: args) f | _ -> (e, args)
  in
  aux [] e

(** Make an `App (app, arg)` expression *)
let mk_app (app : texpression) (arg : texpression) : texpression =
  match app.ty with
  | Arrow (ty0, ty1) ->
      (* Sanity check *)
      assert (ty0 = arg.ty);
      let e = App (app, arg) in
      let ty = ty1 in
      { e; ty }
  | _ -> raise (Failure "Expected an arrow type")

(** The reverse of [destruct_app] *)
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
    (fun_id * ty list * texpression list) option =
  match opt_destruct_qualif_app e with
  | None -> None
  | Some (qualif, args) -> (
      match qualif.id with
      | Func fun_id -> Some (fun_id, qualif.type_params, args)
      | _ -> None)

let opt_destruct_result (ty : ty) : ty option =
  match ty with
  | Adt (Assumed Result, tys) -> Some (Collections.List.to_cons_nil tys)
  | _ -> None

let destruct_result (ty : ty) : ty = Option.get (opt_destruct_result ty)

let opt_destruct_tuple (ty : ty) : ty list option =
  match ty with Adt (Tuple, tys) -> Some tys | _ -> None

let mk_abs (x : typed_lvalue) (e : texpression) : texpression =
  let ty = Arrow (x.ty, e.ty) in
  let e = Abs (x, e) in
  { e; ty }

let rec destruct_abs_list (e : texpression) : typed_lvalue list * texpression =
  match e.e with
  | Abs (x, e') ->
      let xl, e'' = destruct_abs_list e' in
      (x :: xl, e'')
  | _ -> ([], e)

let destruct_arrow (ty : ty) : ty * ty =
  match ty with
  | Arrow (ty0, ty1) -> (ty0, ty1)
  | _ -> raise (Failure "Not an arrow type")

let rec destruct_arrows (ty : ty) : ty list * ty =
  match ty with
  | Arrow (ty0, ty1) ->
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
  (* TODO: check the type of the scrutinee *)
  let ty = get_switch_body_ty sb in
  (* Sanity check: all the branches have the same type *)
  iter_switch_body_branches (fun e -> assert (e.ty = ty)) sb;
  (* Put together *)
  let e = Switch (scrut, sb) in
  { e; ty }

(** Make a "simplified" tuple type from a list of types:
    - if there is exactly one type, just return it
    - if there is > one type: wrap them in a tuple
 *)
let mk_simpl_tuple_ty (tys : ty list) : ty =
  match tys with [ ty ] -> ty | _ -> Adt (Tuple, tys)

(** TODO: rename to "mk_..." *)
let unit_ty : ty = Adt (Tuple, [])

(** TODO: rename to "mk_..." *)
let unit_rvalue : texpression =
  let id = AdtCons { adt_id = Tuple; variant_id = None } in
  let qualif = { id; type_params = [] } in
  let e = Qualif qualif in
  let ty = unit_ty in
  { e; ty }

let mk_texpression_from_var (v : var) : texpression =
  let e = Local v.id in
  let ty = v.ty in
  { e; ty }

let mk_typed_lvalue_from_var (v : var) (mp : mplace option) : typed_lvalue =
  let value = LvVar (Var (v, mp)) in
  let ty = v.ty in
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
let mk_simpl_tuple_lvalue (vl : typed_lvalue list) : typed_lvalue =
  match vl with
  | [ v ] -> v
  | _ ->
      let tys = List.map (fun (v : typed_lvalue) -> v.ty) vl in
      let ty = Adt (Tuple, tys) in
      let value = LvAdt { variant_id = None; field_values = vl } in
      { value; ty }

(** Similar to [mk_simpl_tuple_lvalue] *)
let mk_simpl_tuple_texpression (vl : texpression list) : texpression =
  match vl with
  | [ v ] -> v
  | _ ->
      (* Compute the types of the fields, and the type of the tuple constructor *)
      let tys = List.map (fun (v : texpression) -> v.ty) vl in
      let ty = Adt (Tuple, tys) in
      let ty = mk_arrows tys ty in
      (* Construct the tuple constructor qualifier *)
      let id = AdtCons { adt_id = Tuple; variant_id = None } in
      let qualif = { id; type_params = tys } in
      (* Put everything together *)
      let cons = { e = Qualif qualif; ty } in
      mk_apps cons vl

let mk_adt_lvalue (adt_ty : ty) (variant_id : VariantId.id)
    (vl : typed_lvalue list) : typed_lvalue =
  let value = LvAdt { variant_id = Some variant_id; field_values = vl } in
  { value; ty = adt_ty }

let ty_as_integer (t : ty) : T.integer_type =
  match t with Integer int_ty -> int_ty | _ -> raise (Failure "Unreachable")

(* TODO: move *)
let type_decl_is_enum (def : T.type_decl) : bool =
  match def.kind with T.Struct _ -> false | Enum _ -> true | Opaque -> false

let mk_state_ty : ty = Adt (Assumed State, [])

let mk_result_ty (ty : ty) : ty = Adt (Assumed Result, [ ty ])

(* TODO: rename *)
let mk_result_fail_rvalue (ty : ty) : texpression =
  let type_args = [ ty ] in
  let ty = Adt (Assumed Result, type_args) in
  let id =
    AdtCons { adt_id = Assumed Result; variant_id = Some result_fail_id }
  in
  let qualif = { id; type_params = type_args } in
  let cons_e = Qualif qualif in
  let cons_ty = ty in
  let cons = { e = cons_e; ty = cons_ty } in
  cons

(* TODO: rename *)
let mk_result_return_rvalue (v : texpression) : texpression =
  let type_args = [ v.ty ] in
  let ty = Adt (Assumed Result, type_args) in
  let id =
    AdtCons { adt_id = Assumed Result; variant_id = Some result_return_id }
  in
  let qualif = { id; type_params = type_args } in
  let cons_e = Qualif qualif in
  let cons_ty = mk_arrow v.ty ty in
  let cons = { e = cons_e; ty = cons_ty } in
  mk_app cons v

let mk_result_fail_lvalue (ty : ty) : typed_lvalue =
  let ty = Adt (Assumed Result, [ ty ]) in
  let value = LvAdt { variant_id = Some result_fail_id; field_values = [] } in
  { value; ty }

let mk_result_return_lvalue (v : typed_lvalue) : typed_lvalue =
  let ty = Adt (Assumed Result, [ v.ty ]) in
  let value =
    LvAdt { variant_id = Some result_return_id; field_values = [ v ] }
  in
  { value; ty }

let opt_destruct_state_monad_result (ty : ty) : ty option =
  (* Checking:
   * ty == state -> result (state & _) ? *)
  match ty with
  | Arrow (ty0, ty1) ->
      (* ty == ty0 -> ty1
       * Checking: ty0 == state ?
       * *)
      if ty0 = mk_state_ty then
        (* Checking: ty1 == result (state & _) *)
        match opt_destruct_result ty1 with
        | None -> None
        | Some ty2 -> (
            (* Checking: ty2 == state & _ *)
            match opt_destruct_tuple ty2 with
            | Some [ ty3; ty4 ] -> if ty3 = mk_state_ty then Some ty4 else None
            | _ -> None)
      else None
  | _ -> None

let opt_unmeta_mplace (e : texpression) : mplace option * texpression =
  match e.e with Meta (MPlace mp, e) -> (Some mp, e) | _ -> (None, e)

(** Utility function, used for type checking - TODO: move *)
let get_adt_field_types (type_decls : type_decl TypeDeclId.Map.t)
    (type_id : type_id) (variant_id : VariantId.id option) (tys : ty list) :
    ty list =
  match type_id with
  | Tuple ->
      (* Tuple *)
      assert (variant_id = None);
      tys
  | AdtId def_id ->
      (* "Regular" ADT *)
      let def = TypeDeclId.Map.find def_id type_decls in
      type_decl_get_instantiated_fields_types def variant_id tys
  | Assumed aty -> (
      (* Assumed type *)
      match aty with
      | State ->
          (* `State` is opaque *)
          raise (Failure "Unreachable: `State` values are opaque")
      | Result ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = result_return_id then [ ty ]
          else if variant_id = result_fail_id then []
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | Option ->
          let ty = Collections.List.to_cons_nil tys in
          let variant_id = Option.get variant_id in
          if variant_id = option_some_id then [ ty ]
          else if variant_id = option_none_id then []
          else
            raise (Failure "Unreachable: improper variant id for result type")
      | Vec -> raise (Failure "Unreachable: `Vector` values are opaque"))

(** Module to perform type checking - we use this for sanity checks only

    TODO: move to a special file (so that we can also use PrintPure for
    debugging)
 *)
module TypeCheck = struct
  type tc_ctx = {
    type_decls : type_decl TypeDeclId.Map.t;  (** The type declarations *)
    env : ty VarId.Map.t;  (** Environment from variables to types *)
  }

  let check_constant_value (v : constant_value) (ty : ty) : unit =
    match (ty, v) with
    | Integer int_ty, V.Scalar sv -> assert (int_ty = sv.V.int_ty)
    | Bool, Bool _ | Char, Char _ | Str, String _ -> ()
    | _ -> raise (Failure "Inconsistent type")

  let rec check_typed_lvalue (ctx : tc_ctx) (v : typed_lvalue) : tc_ctx =
    log#ldebug (lazy ("check_typed_lvalue: " ^ show_typed_lvalue v));
    match v.value with
    | LvConcrete cv ->
        check_constant_value cv v.ty;
        ctx
    | LvVar Dummy -> ctx
    | LvVar (Var (var, _)) ->
        assert (var.ty = v.ty);
        let env = VarId.Map.add var.id var.ty ctx.env in
        { ctx with env }
    | LvAdt av ->
        (* Compute the field types *)
        let type_id, tys =
          match v.ty with
          | Adt (type_id, tys) -> (type_id, tys)
          | _ -> raise (Failure "Inconsistently typed value")
        in
        let field_tys =
          get_adt_field_types ctx.type_decls type_id av.variant_id tys
        in
        let check_value (ctx : tc_ctx) (ty : ty) (v : typed_lvalue) : tc_ctx =
          if ty <> v.ty then (
            log#serror
              ("check_typed_lvalue: not the same types:" ^ "\n- ty: "
             ^ show_ty ty ^ "\n- v.ty: " ^ show_ty v.ty);
            raise (Failure "Inconsistent types"));
          check_typed_lvalue ctx v
        in
        (* Check the field types - TODO: we might also want to check that the
         * type of the applied constructor is correct *)
        List.fold_left
          (fun ctx (ty, v) -> check_value ctx ty v)
          ctx
          (List.combine field_tys av.field_values)

  let rec check_texpression (ctx : tc_ctx) (e : texpression) : unit =
    match e.e with
    | Local var_id -> (
        (* Lookup the variable - note that the variable may not be there,
         * if we type-check a subexpression (i.e.: if the variable is introduced
         * "outside" of the expression) - TODO: this won't happen once
         * we use a locally nameless representation *)
        match VarId.Map.find_opt var_id ctx.env with
        | None -> ()
        | Some ty -> assert (ty = e.ty))
    | Const cv -> check_constant_value cv e.ty
    | App (app, arg) ->
        let input_ty, output_ty = destruct_arrow app.ty in
        assert (input_ty = arg.ty);
        assert (output_ty = e.ty);
        check_texpression ctx app;
        check_texpression ctx arg
    | Abs (pat, body) ->
        let pat_ty, body_ty = destruct_arrow e.ty in
        assert (pat.ty = pat_ty);
        assert (body.ty = body_ty);
        (* Check the pattern and register the introduced variables at the same time *)
        let ctx = check_typed_lvalue ctx pat in
        check_texpression ctx body
    | Qualif qualif -> (
        match qualif.id with
        | Func _ -> () (* TODO *)
        | Proj (ProjField (type_id, field_id)) ->
            (* Note we can only project fields of structurs (not enumerations) *)
            let variant_id = None in
            let expected_field_tys =
              get_adt_field_types ctx.type_decls type_id variant_id
                qualif.type_params
            in
            let expected_field_ty = FieldId.nth expected_field_tys field_id in
            let _adt_ty, field_ty = destruct_arrow e.ty in
            (* TODO: check the adt_ty *)
            assert (expected_field_ty = field_ty)
        | Proj (ProjTuple field_id) -> (
            let tuple_ty, field_ty = destruct_arrow e.ty in
            match tuple_ty with
            | Adt (Tuple, tys) ->
                let expected_field_ty = List.nth tys field_id in
                assert (field_ty = expected_field_ty)
            | _ -> raise (Failure "Inconsistently typed projector"))
        | AdtCons id ->
            (* TODO: we might also want to check the out type *)
            let expected_field_tys =
              get_adt_field_types ctx.type_decls id.adt_id id.variant_id
                qualif.type_params
            in
            let field_tys, _ = destruct_arrows e.ty in
            assert (expected_field_tys = field_tys))
    | Let (monadic, pat, re, e_next) ->
        let expected_pat_ty =
          if monadic then destruct_result re.ty else re.ty
        in
        assert (pat.ty = expected_pat_ty);
        assert (e.ty = e_next.ty);
        (* Check the right-expression *)
        check_texpression ctx re;
        (* Check the pattern and register the introduced variables at the same time *)
        let ctx = check_typed_lvalue ctx pat in
        (* Check the next expression *)
        check_texpression ctx e_next
    | Switch (scrut, switch_body) -> (
        check_texpression ctx scrut;
        match switch_body with
        | If (e_then, e_else) ->
            assert (scrut.ty = Bool);
            assert (e_then.ty = e.ty);
            assert (e_else.ty = e.ty);
            check_texpression ctx e_then;
            check_texpression ctx e_else
        | Match branches ->
            let check_branch (br : match_branch) : unit =
              assert (br.pat.ty = scrut.ty);
              let ctx = check_typed_lvalue ctx br.pat in
              check_texpression ctx br.branch
            in
            List.iter check_branch branches)
    | Meta (_, e_next) ->
        assert (e_next.ty = e.ty);
        check_texpression ctx e_next
end
