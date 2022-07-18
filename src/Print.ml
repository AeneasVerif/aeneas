open Names
module T = Types
module TU = TypesUtils
module V = Values
module VU = ValuesUtils
module E = Expressions
module A = LlbcAst
module C = Contexts
module M = Modules

let option_to_string (to_string : 'a -> string) (x : 'a option) : string =
  match x with Some x -> "Some (" ^ to_string x ^ ")" | None -> "None"

let name_to_string (name : name) : string = Names.name_to_string name
let fun_name_to_string (name : fun_name) : string = name_to_string name
let global_name_to_string (name : global_name) : string = name_to_string name

(** Pretty-printing for types *)
module Types = struct
  let type_var_to_string (tv : T.type_var) : string = tv.name

  let region_var_to_string (rv : T.region_var) : string =
    match rv.name with
    | Some name -> name
    | None -> T.RegionVarId.to_string rv.index

  let region_var_id_to_string (rid : T.RegionVarId.id) : string =
    "rv@" ^ T.RegionVarId.to_string rid

  let region_id_to_string (rid : T.RegionId.id) : string =
    "r@" ^ T.RegionId.to_string rid

  let region_to_string (rid_to_string : 'rid -> string) (r : 'rid T.region) :
      string =
    match r with Static -> "'static" | Var rid -> rid_to_string rid

  let erased_region_to_string (_ : T.erased_region) : string = "'_"

  let ref_kind_to_string (rk : T.ref_kind) : string =
    match rk with Mut -> "Mut" | Shared -> "Shared"

  let assumed_ty_to_string (_ : T.assumed_ty) : string = "Box"

  type 'r type_formatter = {
    r_to_string : 'r -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
  }

  type stype_formatter = T.RegionVarId.id T.region type_formatter
  type rtype_formatter = T.RegionId.id T.region type_formatter
  type etype_formatter = T.erased_region type_formatter

  let integer_type_to_string = function
    | T.Isize -> "isize"
    | T.I8 -> "i8"
    | T.I16 -> "i16"
    | T.I32 -> "i32"
    | T.I64 -> "i64"
    | T.I128 -> "i128"
    | T.Usize -> "usize"
    | T.U8 -> "u8"
    | T.U16 -> "u16"
    | T.U32 -> "u32"
    | T.U64 -> "u64"
    | T.U128 -> "u128"

  let type_id_to_string (fmt : 'r type_formatter) (id : T.type_id) : string =
    match id with
    | T.AdtId id -> fmt.type_decl_id_to_string id
    | T.Tuple -> ""
    | T.Assumed aty -> (
        match aty with
        | Box -> "alloc::boxed::Box"
        | Vec -> "alloc::vec::Vec"
        | Option -> "core::option::Option")

  let rec ty_to_string (fmt : 'r type_formatter) (ty : 'r T.ty) : string =
    match ty with
    | T.Adt (id, regions, tys) ->
        let is_tuple = match id with T.Tuple -> true | _ -> false in
        let params = params_to_string fmt is_tuple regions tys in
        type_id_to_string fmt id ^ params
    | T.TypeVar tv -> fmt.type_var_id_to_string tv
    | T.Bool -> "bool"
    | T.Char -> "char"
    | T.Never -> "⊥"
    | T.Integer int_ty -> integer_type_to_string int_ty
    | T.Str -> "str"
    | T.Array aty -> "[" ^ ty_to_string fmt aty ^ "; ?]"
    | T.Slice sty -> "[" ^ ty_to_string fmt sty ^ "]"
    | T.Ref (r, rty, ref_kind) -> (
        match ref_kind with
        | T.Mut ->
            "&" ^ fmt.r_to_string r ^ " mut (" ^ ty_to_string fmt rty ^ ")"
        | T.Shared ->
            "&" ^ fmt.r_to_string r ^ " (" ^ ty_to_string fmt rty ^ ")")

  and params_to_string (fmt : 'r type_formatter) (is_tuple : bool)
      (regions : 'r list) (types : 'r T.ty list) : string =
    let regions = List.map fmt.r_to_string regions in
    let types = List.map (ty_to_string fmt) types in
    let params = String.concat ", " (List.append regions types) in
    if is_tuple then "(" ^ params ^ ")"
    else if List.length regions + List.length types > 0 then "<" ^ params ^ ">"
    else ""

  let sty_to_string (fmt : stype_formatter) (ty : T.sty) : string =
    ty_to_string fmt ty

  let rty_to_string (fmt : rtype_formatter) (ty : T.rty) : string =
    ty_to_string fmt ty

  let ety_to_string (fmt : etype_formatter) (ty : T.ety) : string =
    ty_to_string fmt ty

  let field_to_string fmt (f : T.field) : string =
    match f.field_name with
    | Some field_name -> field_name ^ " : " ^ ty_to_string fmt f.field_ty
    | None -> ty_to_string fmt f.field_ty

  let variant_to_string fmt (v : T.variant) : string =
    v.variant_name ^ "("
    ^ String.concat ", " (List.map (field_to_string fmt) v.fields)
    ^ ")"

  let type_decl_to_string (type_decl_id_to_string : T.TypeDeclId.id -> string)
      (def : T.type_decl) : string =
    let regions = def.region_params in
    let types = def.type_params in
    let rid_to_string rid =
      match List.find_opt (fun rv -> rv.T.index = rid) regions with
      | Some rv -> region_var_to_string rv
      | None -> failwith "Unreachable"
    in
    let r_to_string = region_to_string rid_to_string in
    let type_var_id_to_string id =
      match List.find_opt (fun tv -> tv.T.index = id) types with
      | Some tv -> type_var_to_string tv
      | None -> failwith "Unreachable"
    in
    let fmt = { r_to_string; type_var_id_to_string; type_decl_id_to_string } in
    let name = name_to_string def.name in
    let params =
      if List.length regions + List.length types > 0 then
        let regions = List.map region_var_to_string regions in
        let types = List.map type_var_to_string types in
        let params = String.concat ", " (List.append regions types) in
        "<" ^ params ^ ">"
      else ""
    in
    match def.kind with
    | T.Struct fields ->
        if List.length fields > 0 then
          let fields =
            String.concat ","
              (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
          in
          "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
        else "struct " ^ name ^ params ^ "{}"
    | T.Enum variants ->
        let variants =
          List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
        in
        let variants = String.concat "\n" variants in
        "enum " ^ name ^ params ^ " =\n" ^ variants
    | T.Opaque -> "opaque type " ^ name ^ params
end

module PT = Types (* local module *)

(** Pretty-printing for values *)
module Values = struct
  type value_formatter = {
    rvar_to_string : T.RegionVarId.id -> string;
    r_to_string : T.RegionId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
    adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
    var_id_to_string : V.VarId.id -> string;
    adt_field_names :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option;
  }

  let value_to_etype_formatter (fmt : value_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let value_to_rtype_formatter (fmt : value_formatter) : PT.rtype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.r_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let value_to_stype_formatter (fmt : value_formatter) : PT.stype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.rvar_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let var_id_to_string (id : V.VarId.id) : string =
    "var@" ^ V.VarId.to_string id

  let big_int_to_string (bi : V.big_int) : string = Z.to_string bi

  let scalar_value_to_string (sv : V.scalar_value) : string =
    big_int_to_string sv.value ^ ": " ^ PT.integer_type_to_string sv.int_ty

  let constant_value_to_string (cv : V.constant_value) : string =
    match cv with
    | Scalar sv -> scalar_value_to_string sv
    | Bool b -> Bool.to_string b
    | Char c -> String.make 1 c
    | String s -> s

  let symbolic_value_id_to_string (id : V.SymbolicValueId.id) : string =
    "s@" ^ V.SymbolicValueId.to_string id

  let symbolic_value_to_string (fmt : PT.rtype_formatter)
      (sv : V.symbolic_value) : string =
    symbolic_value_id_to_string sv.sv_id ^ " : " ^ PT.rty_to_string fmt sv.sv_ty

  let symbolic_value_proj_to_string (fmt : value_formatter)
      (sv : V.symbolic_value) (rty : T.rty) : string =
    symbolic_value_id_to_string sv.sv_id
    ^ " : "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) sv.sv_ty
    ^ " <: "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) rty

  (* TODO: it may be a good idea to try to factorize this function with
   * typed_avalue_to_string. At some point we had done it, because [typed_value]
   * and [typed_avalue] were instances of the same general type [g_typed_value],
   * but then we removed this general type because it proved to be a bad idea. *)
  let rec typed_value_to_string (fmt : value_formatter) (v : V.typed_value) :
      string =
    let ty_fmt : PT.etype_formatter = value_to_etype_formatter fmt in
    match v.value with
    | Concrete cv -> constant_value_to_string cv
    | Adt av -> (
        let field_values =
          List.map (typed_value_to_string fmt) av.field_values
        in
        match v.ty with
        | T.Adt (T.Tuple, _, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | T.Adt (T.AdtId def_id, _, _) ->
            (* "Regular" ADT *)
            let adt_ident =
              match av.variant_id with
              | Some vid -> fmt.adt_variant_to_string def_id vid
              | None -> fmt.type_decl_id_to_string def_id
            in
            if List.length field_values > 0 then
              match fmt.adt_field_names def_id av.V.variant_id with
              | None ->
                  let field_values = String.concat ", " field_values in
                  adt_ident ^ " (" ^ field_values ^ ")"
              | Some field_names ->
                  let field_values = List.combine field_names field_values in
                  let field_values =
                    List.map
                      (fun (field, value) -> field ^ " = " ^ value ^ ";")
                      field_values
                  in
                  let field_values = String.concat " " field_values in
                  adt_ident ^ " { " ^ field_values ^ " }"
            else adt_ident
        | T.Adt (T.Assumed aty, _, _) -> (
            (* Assumed type *)
            match (aty, field_values) with
            | Box, [ bv ] -> "@Box(" ^ bv ^ ")"
            | Option, _ ->
                if av.variant_id = Some T.option_some_id then
                  "@Option::Some("
                  ^ Collections.List.to_cons_nil field_values
                  ^ ")"
                else if av.variant_id = Some T.option_none_id then (
                  assert (field_values = []);
                  "@Option::None")
                else failwith "Unreachable"
            | Vec, _ -> "@Vec[" ^ String.concat ", " field_values ^ "]"
            | _ -> failwith "Inconsistent value")
        | _ -> failwith "Inconsistent typed value")
    | Bottom -> "⊥ : " ^ PT.ty_to_string ty_fmt v.ty
    | Borrow bc -> borrow_content_to_string fmt bc
    | Loan lc -> loan_content_to_string fmt lc
    | Symbolic s -> symbolic_value_to_string (value_to_rtype_formatter fmt) s

  and borrow_content_to_string (fmt : value_formatter) (bc : V.borrow_content) :
      string =
    match bc with
    | SharedBorrow (_, bid) -> "⌊shared@" ^ V.BorrowId.to_string bid ^ "⌋"
    | MutBorrow (bid, tv) ->
        "&mut@" ^ V.BorrowId.to_string bid ^ " ("
        ^ typed_value_to_string fmt tv
        ^ ")"
    | InactivatedMutBorrow (_, bid) ->
        "⌊inactivated_mut@" ^ V.BorrowId.to_string bid ^ "⌋"

  and loan_content_to_string (fmt : value_formatter) (lc : V.loan_content) :
      string =
    match lc with
    | SharedLoan (loans, v) ->
        let loans = V.BorrowId.Set.to_string None loans in
        "@shared_loan(" ^ loans ^ ", " ^ typed_value_to_string fmt v ^ ")"
    | MutLoan bid -> "⌊mut@" ^ V.BorrowId.to_string bid ^ "⌋"

  let abstract_shared_borrow_to_string (fmt : value_formatter)
      (abs : V.abstract_shared_borrow) : string =
    match abs with
    | AsbBorrow bid -> V.BorrowId.to_string bid
    | AsbProjReborrows (sv, rty) ->
        "{" ^ symbolic_value_proj_to_string fmt sv rty ^ "}"

  let abstract_shared_borrows_to_string (fmt : value_formatter)
      (abs : V.abstract_shared_borrows) : string =
    "{"
    ^ String.concat "," (List.map (abstract_shared_borrow_to_string fmt) abs)
    ^ "}"

  let rec aproj_to_string (fmt : value_formatter) (pv : V.aproj) : string =
    match pv with
    | AProjLoans (sv, given_back) ->
        let given_back =
          if given_back = [] then ""
          else
            let given_back = List.map snd given_back in
            let given_back = List.map (aproj_to_string fmt) given_back in
            " (" ^ String.concat "," given_back ^ ") "
        in
        "⌊"
        ^ symbolic_value_to_string (value_to_rtype_formatter fmt) sv
        ^ given_back ^ "⌋"
    | AProjBorrows (sv, rty) ->
        "(" ^ symbolic_value_proj_to_string fmt sv rty ^ ")"
    | AEndedProjLoans (_, given_back) ->
        if given_back = [] then "_"
        else
          let given_back = List.map snd given_back in
          let given_back = List.map (aproj_to_string fmt) given_back in
          "ended_aproj_loans (" ^ String.concat "," given_back ^ ")"
    | AEndedProjBorrows _mv -> "_"
    | AIgnoredProjBorrows -> "_"

  let rec typed_avalue_to_string (fmt : value_formatter) (v : V.typed_avalue) :
      string =
    let ty_fmt : PT.rtype_formatter = value_to_rtype_formatter fmt in
    match v.value with
    | AConcrete cv -> constant_value_to_string cv
    | AAdt av -> (
        let field_values =
          List.map (typed_avalue_to_string fmt) av.field_values
        in
        match v.ty with
        | T.Adt (T.Tuple, _, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | T.Adt (T.AdtId def_id, _, _) ->
            (* "Regular" ADT *)
            let adt_ident =
              match av.variant_id with
              | Some vid -> fmt.adt_variant_to_string def_id vid
              | None -> fmt.type_decl_id_to_string def_id
            in
            if List.length field_values > 0 then
              match fmt.adt_field_names def_id av.V.variant_id with
              | None ->
                  let field_values = String.concat ", " field_values in
                  adt_ident ^ " (" ^ field_values ^ ")"
              | Some field_names ->
                  let field_values = List.combine field_names field_values in
                  let field_values =
                    List.map
                      (fun (field, value) -> field ^ " = " ^ value ^ ";")
                      field_values
                  in
                  let field_values = String.concat " " field_values in
                  adt_ident ^ " { " ^ field_values ^ " }"
            else adt_ident
        | T.Adt (T.Assumed aty, _, _) -> (
            (* Assumed type *)
            match (aty, field_values) with
            | Box, [ bv ] -> "@Box(" ^ bv ^ ")"
            | _ -> failwith "Inconsistent value")
        | _ -> failwith "Inconsistent typed value")
    | ABottom -> "⊥ : " ^ PT.ty_to_string ty_fmt v.ty
    | ABorrow bc -> aborrow_content_to_string fmt bc
    | ALoan lc -> aloan_content_to_string fmt lc
    | ASymbolic s -> aproj_to_string fmt s
    | AIgnored -> "_"

  and aloan_content_to_string (fmt : value_formatter) (lc : V.aloan_content) :
      string =
    match lc with
    | AMutLoan (bid, av) ->
        "⌊mut@" ^ V.BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ "⌋"
    | ASharedLoan (loans, v, av) ->
        let loans = V.BorrowId.Set.to_string None loans in
        "@shared_loan(" ^ loans ^ ", "
        ^ typed_value_to_string fmt v
        ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AEndedMutLoan ml ->
        "@ended_mut_loan{"
        ^ typed_avalue_to_string fmt ml.child
        ^ "; "
        ^ typed_avalue_to_string fmt ml.given_back
        ^ " }"
    | AEndedSharedLoan (v, av) ->
        "@ended_shared_loan("
        ^ typed_value_to_string fmt v
        ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AIgnoredMutLoan (bid, av) ->
        "@ignored_mut_loan(" ^ V.BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_loan{ "
        ^ typed_avalue_to_string fmt ml.child
        ^ "; "
        ^ typed_avalue_to_string fmt ml.given_back
        ^ "}"
    | AIgnoredSharedLoan sl ->
        "@ignored_shared_loan(" ^ typed_avalue_to_string fmt sl ^ ")"

  and aborrow_content_to_string (fmt : value_formatter) (bc : V.aborrow_content)
      : string =
    match bc with
    | AMutBorrow (_, bid, av) ->
        "&mut@" ^ V.BorrowId.to_string bid ^ " ("
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | ASharedBorrow bid -> "⌊shared@" ^ V.BorrowId.to_string bid ^ "⌋"
    | AIgnoredMutBorrow (opt_bid, av) ->
        "@ignored_mut_borrow("
        ^ option_to_string V.BorrowId.to_string opt_bid
        ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AEndedMutBorrow (_mv, child) ->
        "@ended_mut_borrow(" ^ typed_avalue_to_string fmt child ^ ")"
    | AEndedIgnoredMutBorrow
        { child; given_back_loans_proj; given_back_meta = _ } ->
        "@ended_ignored_mut_borrow{ "
        ^ typed_avalue_to_string fmt child
        ^ "; "
        ^ typed_avalue_to_string fmt given_back_loans_proj
        ^ ")"
    | AEndedSharedBorrow -> "@ended_shared_borrow"
    | AProjSharedBorrow sb ->
        "@ignored_shared_borrow("
        ^ abstract_shared_borrows_to_string fmt sb
        ^ ")"

  let abs_to_string (fmt : value_formatter) (indent : string)
      (indent_incr : string) (abs : V.abs) : string =
    let indent2 = indent ^ indent_incr in
    let avs =
      List.map (fun av -> indent2 ^ typed_avalue_to_string fmt av) abs.avalues
    in
    let avs = String.concat ",\n" avs in
    indent ^ "abs@"
    ^ V.AbstractionId.to_string abs.abs_id
    ^ "{parents="
    ^ V.AbstractionId.Set.to_string None abs.parents
    ^ "}" ^ "{regions="
    ^ T.RegionId.Set.to_string None abs.regions
    ^ "}" ^ " {\n" ^ avs ^ "\n" ^ indent ^ "}"
end

module PV = Values (* local module *)

(** Pretty-printing for contexts *)
module Contexts = struct
  let binder_to_string (bv : C.binder) : string =
    match bv.name with
    | None -> PV.var_id_to_string bv.index
    | Some name -> name

  let env_elem_to_string (fmt : PV.value_formatter) (indent : string)
      (indent_incr : string) (ev : C.env_elem) : string =
    match ev with
    | Var (var, tv) ->
        let bv =
          match var with Some var -> binder_to_string var | None -> "_"
        in
        indent ^ bv ^ " -> " ^ PV.typed_value_to_string fmt tv ^ " ;"
    | Abs abs -> PV.abs_to_string fmt indent indent_incr abs
    | Frame -> failwith "Can't print a Frame element"

  let opt_env_elem_to_string (fmt : PV.value_formatter) (indent : string)
      (indent_incr : string) (ev : C.env_elem option) : string =
    match ev with
    | None -> indent ^ "..."
    | Some ev -> env_elem_to_string fmt indent indent_incr ev

  (** Filters "dummy" bindings from an environment, to gain space and clarity/
      See [env_to_string]. *)
  let filter_env (env : C.env) : C.env_elem option list =
    (* We filter:
     * - non-dummy bindings which point to ⊥
     * - dummy bindings which don't contain loans nor borrows
     * Note that the first case can sometimes be confusing: we may try to improve
     * it...
     *)
    let filter_elem (ev : C.env_elem) : C.env_elem option =
      match ev with
      | Var (Some _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if VU.is_bottom tv.value then None else Some ev
      | Var (None, tv) ->
          (* Dummy binding: check if the value contains borrows or loans *)
          if VU.borrows_in_value tv || VU.loans_in_value tv then Some ev
          else None
      | _ -> Some ev
    in
    let env = List.map filter_elem env in
    (* We collapse groups of filtered values - so that we can print one
     * single "..." for a whole group of filtered values *)
    let rec group_filtered (env : C.env_elem option list) :
        C.env_elem option list =
      match env with
      | [] -> []
      | None :: None :: env -> group_filtered (None :: env)
      | x :: env -> x :: group_filtered env
    in
    group_filtered env

  (** Environments can have a lot of dummy or uninitialized values: [filter]
      allows to filter them when printing, replacing groups of such bindings with
      "..." to gain space and clarity.
   *)
  let env_to_string (filter : bool) (fmt : PV.value_formatter) (env : C.env) :
      string =
    let env =
      if filter then filter_env env else List.map (fun ev -> Some ev) env
    in
    "{\n"
    ^ String.concat "\n"
        (List.map (fun ev -> opt_env_elem_to_string fmt "  " "  " ev) env)
    ^ "\n}"

  type ctx_formatter = PV.value_formatter

  let ctx_to_etype_formatter (fmt : ctx_formatter) : PT.etype_formatter =
    PV.value_to_etype_formatter fmt

  let ctx_to_rtype_formatter (fmt : ctx_formatter) : PT.rtype_formatter =
    PV.value_to_rtype_formatter fmt

  let type_ctx_to_adt_variant_to_string_fun
      (ctx : T.type_decl T.TypeDeclId.Map.t) :
      T.TypeDeclId.id -> T.VariantId.id -> string =
   fun def_id variant_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    match def.kind with
    | Struct _ | Opaque -> failwith "Unreachable"
    | Enum variants ->
        let variant = T.VariantId.nth variants variant_id in
        name_to_string def.name ^ "::" ^ variant.variant_name

  let type_ctx_to_adt_field_names_fun (ctx : T.type_decl T.TypeDeclId.Map.t) :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option =
   fun def_id opt_variant_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    let fields = TU.type_decl_get_fields def opt_variant_id in
    (* There are two cases: either all the fields have names, or none of them
     * has names *)
    let has_names =
      List.exists (fun f -> Option.is_some f.T.field_name) fields
    in
    if has_names then
      let fields = List.map (fun f -> Option.get f.T.field_name) fields in
      Some fields
    else None

  let eval_ctx_to_ctx_formatter (ctx : C.eval_ctx) : ctx_formatter =
    (* We shouldn't use rvar_to_string *)
    let rvar_to_string _r = failwith "Unexpected use of rvar_to_string" in
    let r_to_string r = PT.region_id_to_string r in

    let type_var_id_to_string vid =
      let v = C.lookup_type_var ctx vid in
      v.name
    in
    let type_decl_id_to_string def_id =
      let def = C.ctx_lookup_type_decl ctx def_id in
      name_to_string def.name
    in
    let adt_variant_to_string =
      type_ctx_to_adt_variant_to_string_fun ctx.type_context.type_decls
    in
    let var_id_to_string vid =
      let bv = C.ctx_lookup_binder ctx vid in
      binder_to_string bv
    in
    let adt_field_names =
      type_ctx_to_adt_field_names_fun ctx.type_context.type_decls
    in
    {
      rvar_to_string;
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      adt_variant_to_string;
      var_id_to_string;
      adt_field_names;
    }

  (** Split an [env] at every occurrence of [Frame], eliminating those elements.
          Also reorders the frames and the values in the frames according to the
          following order:
          * frames: from the current frame to the first pushed (oldest frame)
          * values: from the first pushed (oldest) to the last pushed
       *)
  let split_env_according_to_frames (env : C.env) : C.env list =
    let rec split_aux (frames : C.env list) (curr_frame : C.env) (env : C.env) =
      match env with
      | [] ->
          if List.length curr_frame > 0 then curr_frame :: frames else frames
      | Frame :: env' -> split_aux (curr_frame :: frames) [] env'
      | ev :: env' -> split_aux frames (ev :: curr_frame) env'
    in
    let frames = split_aux [] [] env in
    frames

  let eval_ctx_to_string (ctx : C.eval_ctx) : string =
    let fmt = eval_ctx_to_ctx_formatter ctx in
    let ended_regions = T.RegionId.Set.to_string None ctx.ended_regions in
    let frames = split_env_according_to_frames ctx.env in
    let num_frames = List.length frames in
    let frames =
      List.mapi
        (fun i f ->
          let num_bindings = ref 0 in
          let num_dummies = ref 0 in
          let num_abs = ref 0 in
          List.iter
            (fun ev ->
              match ev with
              | C.Var (None, _) -> num_dummies := !num_abs + 1
              | C.Var (Some _, _) -> num_bindings := !num_bindings + 1
              | C.Abs _ -> num_abs := !num_abs + 1
              | _ -> raise (Failure "Unreachable"))
            f;
          "\n# Frame " ^ string_of_int i ^ ":" ^ "\n- locals: "
          ^ string_of_int !num_bindings
          ^ "\n- dummy bindings: " ^ string_of_int !num_dummies
          ^ "\n- abstractions: " ^ string_of_int !num_abs ^ "\n"
          ^ env_to_string true fmt f ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames
end

module PC = Contexts (* local module *)

(** Pretty-printing for contexts (generic functions) *)
module LlbcAst = struct
  let var_to_string (var : A.var) : string =
    match var.name with
    | None -> V.VarId.to_string var.index
    | Some name -> name

  type ast_formatter = {
    rvar_to_string : T.RegionVarId.id -> string;
    r_to_string : T.RegionId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
    adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
    adt_field_to_string :
      T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option;
    var_id_to_string : V.VarId.id -> string;
    adt_field_names :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option;
    fun_decl_id_to_string : A.FunDeclId.id -> string;
    global_decl_id_to_string : A.GlobalDeclId.id -> string;
  }

  let ast_to_ctx_formatter (fmt : ast_formatter) : PC.ctx_formatter =
    {
      PV.rvar_to_string = fmt.rvar_to_string;
      PV.r_to_string = fmt.r_to_string;
      PV.type_var_id_to_string = fmt.type_var_id_to_string;
      PV.type_decl_id_to_string = fmt.type_decl_id_to_string;
      PV.adt_variant_to_string = fmt.adt_variant_to_string;
      PV.var_id_to_string = fmt.var_id_to_string;
      PV.adt_field_names = fmt.adt_field_names;
    }

  let ast_to_value_formatter (fmt : ast_formatter) : PV.value_formatter =
    ast_to_ctx_formatter fmt

  let ast_to_etype_formatter (fmt : ast_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let ast_to_rtype_formatter (fmt : ast_formatter) : PT.rtype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.r_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let ast_to_stype_formatter (fmt : ast_formatter) : PT.stype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.rvar_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
    }

  let type_ctx_to_adt_field_to_string_fun (ctx : T.type_decl T.TypeDeclId.Map.t)
      :
      T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option
      =
   fun def_id opt_variant_id field_id ->
    let def = T.TypeDeclId.Map.find def_id ctx in
    let fields = TU.type_decl_get_fields def opt_variant_id in
    let field = T.FieldId.nth fields field_id in
    field.T.field_name

  let eval_ctx_to_ast_formatter (ctx : C.eval_ctx) : ast_formatter =
    let ctx_fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let adt_field_to_string =
      type_ctx_to_adt_field_to_string_fun ctx.type_context.type_decls
    in
    let fun_decl_id_to_string def_id =
      let def = C.ctx_lookup_fun_decl ctx def_id in
      fun_name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = C.ctx_lookup_global_decl ctx def_id in
      global_name_to_string def.name
    in
    {
      rvar_to_string = ctx_fmt.PV.rvar_to_string;
      r_to_string = ctx_fmt.PV.r_to_string;
      type_var_id_to_string = ctx_fmt.PV.type_var_id_to_string;
      type_decl_id_to_string = ctx_fmt.PV.type_decl_id_to_string;
      adt_variant_to_string = ctx_fmt.PV.adt_variant_to_string;
      var_id_to_string = ctx_fmt.PV.var_id_to_string;
      adt_field_names = ctx_fmt.PV.adt_field_names;
      adt_field_to_string;
      fun_decl_id_to_string;
      global_decl_id_to_string;
    }

  let fun_decl_to_ast_formatter
      (type_decls : T.type_decl T.TypeDeclId.Map.t)
      (fun_decls : A.fun_decl A.FunDeclId.Map.t)
      (global_decls : A.global_decl A.GlobalDeclId.Map.t)
      (fdef : A.fun_decl) :
      ast_formatter =
    let rvar_to_string r =
      let rvar = T.RegionVarId.nth fdef.signature.region_params r in
      PT.region_var_to_string rvar
    in
    let r_to_string r = PT.region_id_to_string r in

    let type_var_id_to_string vid =
      let var = T.TypeVarId.nth fdef.signature.type_params vid in
      PT.type_var_to_string var
    in
    let type_decl_id_to_string def_id =
      let def = T.TypeDeclId.Map.find def_id type_decls in
      name_to_string def.name
    in
    let adt_variant_to_string =
      PC.type_ctx_to_adt_variant_to_string_fun type_decls
    in
    let var_id_to_string vid =
      let var = V.VarId.nth (Option.get fdef.body).locals vid in
      var_to_string var
    in
    let adt_field_names = PC.type_ctx_to_adt_field_names_fun type_decls in
    let adt_field_to_string = type_ctx_to_adt_field_to_string_fun type_decls in
    let fun_decl_id_to_string def_id =
      let def = A.FunDeclId.Map.find def_id fun_decls in
      fun_name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = A.GlobalDeclId.Map.find def_id global_decls in
      global_name_to_string def.name
    in
    {
      rvar_to_string;
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      adt_variant_to_string;
      var_id_to_string;
      adt_field_names;
      adt_field_to_string;
      fun_decl_id_to_string;
      global_decl_id_to_string;
    }

  let rec projection_to_string (fmt : ast_formatter) (inside : string)
      (p : E.projection) : string =
    match p with
    | [] -> inside
    | pe :: p' -> (
        let s = projection_to_string fmt inside p' in
        match pe with
        | E.Deref -> "*(" ^ s ^ ")"
        | E.DerefBox -> "deref_box(" ^ s ^ ")"
        | E.Field (E.ProjOption variant_id, fid) ->
            assert (variant_id = T.option_some_id);
            assert (fid = T.FieldId.zero);
            "(" ^ s ^ " as Option::Some)." ^ T.FieldId.to_string fid
        | E.Field (E.ProjTuple _, fid) ->
            "(" ^ s ^ ")." ^ T.FieldId.to_string fid
        | E.Field (E.ProjAdt (adt_id, opt_variant_id), fid) -> (
            let field_name =
              match fmt.adt_field_to_string adt_id opt_variant_id fid with
              | Some field_name -> field_name
              | None -> T.FieldId.to_string fid
            in
            match opt_variant_id with
            | None -> "(" ^ s ^ ")." ^ field_name
            | Some variant_id ->
                let variant_name =
                  fmt.adt_variant_to_string adt_id variant_id
                in
                "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name))

  let place_to_string (fmt : ast_formatter) (p : E.place) : string =
    let var = fmt.var_id_to_string p.E.var_id in
    projection_to_string fmt var p.E.projection

  let unop_to_string (unop : E.unop) : string =
    match unop with
    | E.Not -> "¬"
    | E.Neg -> "-"
    | E.Cast (src, tgt) ->
        "cast<"
        ^ PT.integer_type_to_string src
        ^ ","
        ^ PT.integer_type_to_string tgt
        ^ ">"

  let binop_to_string (binop : E.binop) : string =
    match binop with
    | E.BitXor -> "^"
    | E.BitAnd -> "&"
    | E.BitOr -> "|"
    | E.Eq -> "=="
    | E.Lt -> "<"
    | E.Le -> "<="
    | E.Ne -> "!="
    | E.Ge -> ">="
    | E.Gt -> ">"
    | E.Div -> "/"
    | E.Rem -> "%"
    | E.Add -> "+"
    | E.Sub -> "-"
    | E.Mul -> "*"
    | E.Shl -> "<<"
    | E.Shr -> ">>"

  let operand_to_string (fmt : ast_formatter) (op : E.operand) : string =
    match op with
    | E.Copy p -> "copy " ^ place_to_string fmt p
    | E.Move p -> "move " ^ place_to_string fmt p
    | E.Constant (ty, cv) ->
        "("
        ^ PV.constant_value_to_string cv
        ^ " : "
        ^ PT.ety_to_string (ast_to_etype_formatter fmt) ty
        ^ ")"

  let rvalue_to_string (fmt : ast_formatter) (rv : E.rvalue) : string =
    match rv with
    | E.Use op -> operand_to_string fmt op
    | E.Ref (p, bk) -> (
        let p = place_to_string fmt p in
        match bk with
        | E.Shared -> "&" ^ p
        | E.Mut -> "&mut " ^ p
        | E.TwoPhaseMut -> "&two-phase " ^ p)
    | E.UnaryOp (unop, op) ->
        unop_to_string unop ^ " " ^ operand_to_string fmt op
    | E.BinaryOp (binop, op1, op2) ->
        operand_to_string fmt op1 ^ " " ^ binop_to_string binop ^ " "
        ^ operand_to_string fmt op2
    | E.Discriminant p -> "discriminant(" ^ place_to_string fmt p ^ ")"
    | E.Aggregate (akind, ops) -> (
        let ops = List.map (operand_to_string fmt) ops in
        match akind with
        | E.AggregatedTuple -> "(" ^ String.concat ", " ops ^ ")"
        | E.AggregatedOption (variant_id, _ty) ->
            if variant_id == T.option_none_id then (
              assert (ops == []);
              "@Option::None")
            else if variant_id == T.option_some_id then (
              assert (List.length ops == 1);
              let op = List.hd ops in
              "@Option::Some(" ^ op ^ ")")
            else raise (Failure "Unreachable")
        | E.AggregatedAdt (def_id, opt_variant_id, _regions, _types) ->
            let adt_name = fmt.type_decl_id_to_string def_id in
            let variant_name =
              match opt_variant_id with
              | None -> adt_name
              | Some variant_id ->
                  adt_name ^ "::" ^ fmt.adt_variant_to_string def_id variant_id
            in
            let fields =
              match fmt.adt_field_names def_id opt_variant_id with
              | None -> "(" ^ String.concat ", " ops ^ ")"
              | Some field_names ->
                  let fields = List.combine field_names ops in
                  let fields =
                    List.map
                      (fun (field, value) -> field ^ " = " ^ value ^ ";")
                      fields
                  in
                  let fields = String.concat " " fields in
                  "{ " ^ fields ^ " }"
            in
            variant_name ^ " " ^ fields)

  let rec statement_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (st : A.statement) : string =
    match st with
    | A.Assign (p, rv) ->
        indent ^ place_to_string fmt p ^ " := " ^ rvalue_to_string fmt rv
    | A.AssignGlobal { dst; global } ->
        indent ^ fmt.var_id_to_string dst ^ " := global " ^ fmt.global_decl_id_to_string global
    | A.FakeRead p -> indent ^ "fake_read " ^ place_to_string fmt p
    | A.SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        indent ^ "set_discriminant(" ^ place_to_string fmt p ^ ", "
        ^ T.VariantId.to_string variant_id
        ^ ")"
    | A.Drop p -> indent ^ "drop(" ^ place_to_string fmt p ^ ")"
    | A.Assert a ->
        let cond = operand_to_string fmt a.A.cond in
        if a.A.expected then indent ^ "assert(" ^ cond ^ ")"
        else indent ^ "assert(¬" ^ cond ^ ")"
    | A.Call call ->
        let ty_fmt = ast_to_etype_formatter fmt in
        let t_params =
          if List.length call.A.type_args > 0 then
            "<"
            ^ String.concat ","
                (List.map (PT.ty_to_string ty_fmt) call.A.type_args)
            ^ ">"
          else ""
        in
        let args = List.map (operand_to_string fmt) call.A.args in
        let args = "(" ^ String.concat ", " args ^ ")" in
        let name_args =
          match call.A.func with
          | A.Regular fid -> fmt.fun_decl_id_to_string fid ^ t_params
          | A.Assumed fid -> (
              match fid with
              | A.Replace -> "core::mem::replace" ^ t_params
              | A.BoxNew -> "alloc::boxed::Box" ^ t_params ^ "::new"
              | A.BoxDeref ->
                  "core::ops::deref::Deref<Box" ^ t_params ^ ">::deref"
              | A.BoxDerefMut ->
                  "core::ops::deref::DerefMut" ^ t_params ^ "::deref_mut"
              | A.BoxFree -> "alloc::alloc::box_free" ^ t_params
              | A.VecNew -> "alloc::vec::Vec" ^ t_params ^ "::new"
              | A.VecPush -> "alloc::vec::Vec" ^ t_params ^ "::push"
              | A.VecInsert -> "alloc::vec::Vec" ^ t_params ^ "::insert"
              | A.VecLen -> "alloc::vec::Vec" ^ t_params ^ "::len"
              | A.VecIndex ->
                  "core::ops::index::Index<alloc::vec::Vec" ^ t_params
                  ^ ">::index"
              | A.VecIndexMut ->
                  "core::ops::index::IndexMut<alloc::vec::Vec" ^ t_params
                  ^ ">::index_mut")
        in
        let dest = place_to_string fmt call.A.dest in
        indent ^ dest ^ " := move " ^ name_args ^ args
    | A.Panic -> indent ^ "panic"
    | A.Return -> indent ^ "return"
    | A.Break i -> indent ^ "break " ^ string_of_int i
    | A.Continue i -> indent ^ "continue " ^ string_of_int i
    | A.Nop -> indent ^ "nop"
    | A.Sequence (st1, st2) ->
        statement_to_string fmt indent indent_incr st1
        ^ ";\n"
        ^ statement_to_string fmt indent indent_incr st2
    | A.Switch (op, tgts) -> (
        let op = operand_to_string fmt op in
        match tgts with
        | A.If (true_st, false_st) ->
            let inner_indent = indent ^ indent_incr in
            let inner_to_string =
              statement_to_string fmt inner_indent indent_incr
            in
            let true_st = inner_to_string true_st in
            let false_st = inner_to_string false_st in
            indent ^ "if (" ^ op ^ ") {\n" ^ true_st ^ "\n" ^ indent ^ "}\n"
            ^ indent ^ "else {\n" ^ false_st ^ "\n" ^ indent ^ "}"
        | A.SwitchInt (_ty, branches, otherwise) ->
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 =
              statement_to_string fmt indent2 indent_incr
            in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map (fun sv -> "| " ^ PV.scalar_value_to_string sv) svl
                  in
                  let svl = String.concat " " svl in
                  indent1 ^ svl ^ " => {\n" ^ inner_to_string2 be ^ "\n"
                  ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              branches ^ "\n" ^ indent1 ^ "_ => {\n"
              ^ inner_to_string2 otherwise ^ "\n" ^ indent1 ^ "}"
            in
            indent ^ "switch (" ^ op ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | A.Loop loop_st ->
        indent ^ "loop {\n"
        ^ statement_to_string fmt (indent ^ indent_incr) indent_incr loop_st
        ^ "\n" ^ indent ^ "}"

  let var_to_string (v : A.var) : string =
    match v.name with None -> PV.var_id_to_string v.index | Some name -> name

  let fun_decl_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.fun_decl) : string =
    let sty_fmt = ast_to_stype_formatter fmt in
    let sty_to_string = PT.sty_to_string sty_fmt in
    let ety_fmt = ast_to_etype_formatter fmt in
    let ety_to_string = PT.ety_to_string ety_fmt in
    let sg = def.signature in

    (* Function name *)
    let name = fun_name_to_string def.A.name in

    (* Region/type parameters *)
    let regions = sg.region_params in
    let types = sg.type_params in
    let params =
      if List.length regions + List.length types = 0 then ""
      else
        let regions = List.map PT.region_var_to_string regions in
        let types = List.map PT.type_var_to_string types in
        "<" ^ String.concat "," (List.append regions types) ^ ">"
    in

    (* Return type *)
    let ret_ty = sg.output in
    let ret_ty =
      if TU.ty_is_unit ret_ty then "" else " -> " ^ sty_to_string ret_ty
    in

    (* We print the declaration differently if it is opaque (no body) or transparent
     * (we have access to a body) *)
    match def.body with
    | None ->
        (* Arguments *)
        let input_tys = sg.inputs in
        let args = List.map sty_to_string input_tys in
        let args = String.concat ", " args in

        (* Put everything together *)
        indent ^ "opaque fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty
    | Some body ->
        (* Arguments *)
        let inputs = List.tl body.locals in
        let inputs, _aux_locals =
          Collections.List.split_at inputs body.arg_count
        in
        let args = List.combine inputs sg.inputs in
        let args =
          List.map
            (fun (var, rty) -> var_to_string var ^ " : " ^ sty_to_string rty)
            args
        in
        let args = String.concat ", " args in

        (* All the locals (with erased regions) *)
        let locals =
          List.map
            (fun var ->
              indent ^ indent_incr ^ var_to_string var ^ " : "
              ^ ety_to_string var.var_ty ^ ";")
            body.locals
        in
        let locals = String.concat "\n" locals in

        (* Body *)
        let body =
          statement_to_string fmt (indent ^ indent_incr) indent_incr body.body
        in

        (* Put everything together *)
        indent ^ "fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ " {\n"
        ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"
end

module PA = LlbcAst (* local module *)

(** Pretty-printing for ASTs (functions based on a definition context) *)
module Module = struct
  (** This function pretty-prints a type definition by using a definition
      context *)
  let type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (def : T.type_decl) : string =
    let type_decl_id_to_string (id : T.TypeDeclId.id) : string =
      let def = T.TypeDeclId.Map.find id type_context in
      name_to_string def.name
    in
    PT.type_decl_to_string type_decl_id_to_string def

  (** Generate an [ast_formatter] by using a definition context in combination
      with the variables local to a function's definition *)
  let def_ctx_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (def : A.fun_decl) :
      PA.ast_formatter =
    let rvar_to_string vid =
      let var = T.RegionVarId.nth def.signature.region_params vid in
      PT.region_var_to_string var
    in
    let r_to_string vid =
      (* TODO: we might want something more informative *)
      PT.region_id_to_string vid
    in
    let type_var_id_to_string vid =
      let var = T.TypeVarId.nth def.signature.type_params vid in
      PT.type_var_to_string var
    in
    let type_decl_id_to_string def_id =
      let def = T.TypeDeclId.Map.find def_id type_context in
      name_to_string def.name
    in
    let fun_decl_id_to_string def_id =
      let def = A.FunDeclId.Map.find def_id fun_context in
      fun_name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = A.GlobalDeclId.Map.find def_id global_context in
      global_name_to_string def.name
    in
    let var_id_to_string vid =
      let var = V.VarId.nth (Option.get def.body).locals vid in
      PA.var_to_string var
    in
    let adt_variant_to_string =
      PC.type_ctx_to_adt_variant_to_string_fun type_context
    in
    let adt_field_to_string =
      PA.type_ctx_to_adt_field_to_string_fun type_context
    in
    let adt_field_names = PC.type_ctx_to_adt_field_names_fun type_context in
    {
      rvar_to_string;
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      adt_variant_to_string;
      adt_field_to_string;
      var_id_to_string;
      adt_field_names;
      fun_decl_id_to_string;
      global_decl_id_to_string;
    }

  (** This function pretty-prints a function definition by using a definition
      context *)
  let fun_decl_to_string
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (def : A.fun_decl) : string =
    let fmt = def_ctx_to_ast_formatter type_context fun_context global_context def in
    PA.fun_decl_to_string fmt "" "  " def

  let module_to_string (m : M.llbc_module) : string =
    let types_defs_map, funs_defs_map, globals_defs_map = M.compute_defs_maps m in

    (* The types *)
    let type_decls = List.map (type_decl_to_string types_defs_map) m.M.types in

    (* The functions *)
    let fun_decls =
      List.map (fun_decl_to_string types_defs_map funs_defs_map globals_defs_map) m.M.functions
    in

    (* Put everything together *)
    let all_defs = List.append type_decls fun_decls in
    String.concat "\n\n" all_defs
end

(** Pretty-printing for LLBC ASTs (functions based on an evaluation context) *)
module EvalCtxLlbcAst = struct
  let ety_to_string (ctx : C.eval_ctx) (t : T.ety) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_etype_formatter fmt in
    PT.ety_to_string fmt t

  let rty_to_string (ctx : C.eval_ctx) (t : T.rty) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_rtype_formatter fmt in
    PT.rty_to_string fmt t

  let borrow_content_to_string (ctx : C.eval_ctx) (bc : V.borrow_content) :
      string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.borrow_content_to_string fmt bc

  let loan_content_to_string (ctx : C.eval_ctx) (lc : V.loan_content) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.loan_content_to_string fmt lc

  let aborrow_content_to_string (ctx : C.eval_ctx) (bc : V.aborrow_content) :
      string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.aborrow_content_to_string fmt bc

  let aloan_content_to_string (ctx : C.eval_ctx) (lc : V.aloan_content) : string
      =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.aloan_content_to_string fmt lc

  let aproj_to_string (ctx : C.eval_ctx) (p : V.aproj) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.aproj_to_string fmt p

  let symbolic_value_to_string (ctx : C.eval_ctx) (sv : V.symbolic_value) :
      string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_rtype_formatter fmt in
    PV.symbolic_value_to_string fmt sv

  let typed_value_to_string (ctx : C.eval_ctx) (v : V.typed_value) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.typed_value_to_string fmt v

  let typed_avalue_to_string (ctx : C.eval_ctx) (v : V.typed_avalue) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.typed_avalue_to_string fmt v

  let place_to_string (ctx : C.eval_ctx) (op : E.place) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.place_to_string fmt op

  let operand_to_string (ctx : C.eval_ctx) (op : E.operand) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.operand_to_string fmt op

  let statement_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (e : A.statement) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.statement_to_string fmt indent indent_incr e
end
