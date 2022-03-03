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

let mk_place_from_var (v : var) : place = { var = v.id; projection = [] }

(** Make a "simplified" tuple type from a list of types:
    - if there is exactly one type, just return it
    - if there is > one type: wrap them in a tuple
 *)
let mk_simpl_tuple_ty (tys : ty list) : ty =
  match tys with [ ty ] -> ty | _ -> Adt (Tuple, tys)

let unit_ty : ty = Adt (Tuple, [])

let unit_rvalue : typed_rvalue =
  let value = RvAdt { variant_id = None; field_values = [] } in
  let ty = unit_ty in
  { value; ty }

let mk_typed_rvalue_from_var (v : var) : typed_rvalue =
  let value = RvPlace (mk_place_from_var v) in
  let ty = v.ty in
  { value; ty }

let mk_typed_lvalue_from_var (v : var) (mp : mplace option) : typed_lvalue =
  let value = LvVar (Var (v, mp)) in
  let ty = v.ty in
  { value; ty }

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
let mk_simpl_tuple_rvalue (vl : typed_rvalue list) : typed_rvalue =
  match vl with
  | [ v ] -> v
  | _ ->
      let tys = List.map (fun (v : typed_rvalue) -> v.ty) vl in
      let ty = Adt (Tuple, tys) in
      let value = RvAdt { variant_id = None; field_values = vl } in
      { value; ty }

let mk_adt_lvalue (adt_ty : ty) (variant_id : VariantId.id)
    (vl : typed_lvalue list) : typed_lvalue =
  let value = LvAdt { variant_id = Some variant_id; field_values = vl } in
  { value; ty = adt_ty }

let ty_as_integer (t : ty) : T.integer_type =
  match t with Integer int_ty -> int_ty | _ -> raise (Failure "Unreachable")

(* TODO: move *)
let type_decl_is_enum (def : T.type_decl) : bool =
  match def.kind with T.Struct _ -> false | Enum _ -> true

let mk_state_ty : ty = Adt (Assumed State, [])

let mk_result_ty (ty : ty) : ty = Adt (Assumed Result, [ ty ])

let mk_result_fail_rvalue (ty : ty) : typed_rvalue =
  let ty = Adt (Assumed Result, [ ty ]) in
  let value = RvAdt { variant_id = Some result_fail_id; field_values = [] } in
  { value; ty }

let mk_result_return_rvalue (v : typed_rvalue) : typed_rvalue =
  let ty = Adt (Assumed Result, [ v.ty ]) in
  let value =
    RvAdt { variant_id = Some result_return_id; field_values = [ v ] }
  in
  { value; ty }

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

let mk_arrow_ty (arg_ty : ty) (ret_ty : ty) : ty = Arrow (arg_ty, ret_ty)

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

let mk_value_expression (v : typed_rvalue) (mp : mplace option) : texpression =
  let e = Value (v, mp) in
  let ty = v.ty in
  { e; ty }

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
let type_decl_get_fields (def : type_decl) (opt_variant_id : VariantId.id option)
    : field list =
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
         (fun (f : fun_decl) -> Regular (A.Local f.def_id, f.back_id))
         funs)
  in
  let ids = ref ids in
  (* Explore every body *)
  let body_only_calls_itself (fdef : fun_decl) : bool =
    (* Remove the current id from the id set *)
    ids := FunIdSet.remove (Regular (A.Local fdef.def_id, fdef.back_id)) !ids;

    (* Check if we call functions from the updated id set *)
    let obj =
      object
        inherit [_] iter_expression as super

        method! visit_call env call =
          if FunIdSet.mem call.func !ids then raise Utils.Found
          else super#visit_call env call
      end
    in

    try
      obj#visit_texpression () fdef.body;
      true
    with Utils.Found -> false
  in
  List.for_all body_only_calls_itself funs

(** We use this to check whether we need to add parentheses around expressions.
    We only look for outer monadic let-bindings.
    This is used when printing the branches of `if ... then ... else ...`.
 *)
let rec expression_requires_parentheses (e : texpression) : bool =
  match e.e with
  | Value _ | Call _ -> false
  | Let (monadic, _, _, next_e) ->
      if monadic then true else expression_requires_parentheses next_e
  | Switch (_, _) -> false
  | Meta (_, next_e) -> expression_requires_parentheses next_e

(** Module to perform type checking - we use this for sanity checks only *)
module TypeCheck = struct
  type tc_ctx = { type_decls : type_decl TypeDeclId.Map.t }

  let check_constant_value (ty : ty) (v : constant_value) : unit =
    match (ty, v) with
    | Integer int_ty, V.Scalar sv -> assert (int_ty = sv.V.int_ty)
    | Bool, Bool _ | Char, Char _ | Str, String _ -> ()
    | _ -> raise (Failure "Inconsistent type")

  let check_adt_g_value (ctx : tc_ctx) (check_value : ty -> 'v -> unit)
      (variant_id : VariantId.id option) (field_values : 'v list) (ty : ty) :
      unit =
    (* Retrieve the field types *)
    let field_tys =
      match ty with
      | Adt (Tuple, tys) ->
          (* Tuple *)
          tys
      | Adt (AdtId def_id, tys) ->
          (* "Regular" ADT *)
          let def = TypeDeclId.Map.find def_id ctx.type_decls in
          type_decl_get_instantiated_fields_types def variant_id tys
      | Adt (Assumed aty, tys) -> (
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
                raise
                  (Failure "Unreachable: improper variant id for result type")
          | Option ->
              let ty = Collections.List.to_cons_nil tys in
              let variant_id = Option.get variant_id in
              if variant_id = option_some_id then [ ty ]
              else if variant_id = option_none_id then []
              else
                raise
                  (Failure "Unreachable: improper variant id for result type")
          | Vec ->
              assert (variant_id = None);
              let ty = Collections.List.to_cons_nil tys in
              List.map (fun _ -> ty) field_values)
      | _ -> raise (Failure "Inconsistently typed value")
    in
    (* Check that the field values have the expected types *)
    List.iter
      (fun (ty, v) -> check_value ty v)
      (List.combine field_tys field_values)

  let rec check_typed_lvalue (ctx : tc_ctx) (v : typed_lvalue) : unit =
    log#ldebug (lazy ("check_typed_lvalue: " ^ show_typed_lvalue v));
    match v.value with
    | LvConcrete cv -> check_constant_value v.ty cv
    | LvVar _ -> ()
    | LvAdt av ->
        check_adt_g_value ctx
          (fun ty (v : typed_lvalue) ->
            if ty <> v.ty then (
              log#serror
                ("check_typed_lvalue: not the same types:" ^ "\n- ty: "
               ^ show_ty ty ^ "\n- v.ty: " ^ show_ty v.ty);
              raise (Failure "Inconsistent types"));
            check_typed_lvalue ctx v)
          av.variant_id av.field_values v.ty

  let rec check_typed_rvalue (ctx : tc_ctx) (v : typed_rvalue) : unit =
    log#ldebug (lazy ("check_typed_rvalue: " ^ show_typed_rvalue v));
    match v.value with
    | RvConcrete cv -> check_constant_value v.ty cv
    | RvPlace _ ->
        (* TODO: *)
        ()
    | RvAdt av ->
        check_adt_g_value ctx
          (fun ty (v : typed_rvalue) ->
            if ty <> v.ty then (
              log#serror
                ("check_typed_rvalue: not the same types:" ^ "\n- ty: "
               ^ show_ty ty ^ "\n- v.ty: " ^ show_ty v.ty);
              raise (Failure "Inconsistent types"));
            check_typed_rvalue ctx v)
          av.variant_id av.field_values v.ty
end

let is_value (e : texpression) : bool =
  match e.e with Value _ -> true | _ -> false

let is_var (e : texpression) : bool =
  match e.e with
  | Value (v, _) -> (
      match v.value with
      | RvPlace { var = _; projection = [] } -> true
      | _ -> false)
  | _ -> false

let as_var (e : texpression) : VarId.id =
  match e.e with
  | Value (v, _) -> (
      match v.value with
      | RvPlace { var; projection = [] } -> var
      | _ -> raise (Failure "Unreachable"))
  | _ -> raise (Failure "Unreachable")

(** Remove the external occurrences of [Meta] *)
let rec unmeta (e : texpression) : texpression =
  match e.e with Meta (_, e) -> unmeta e | _ -> e
