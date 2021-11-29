(* TODO: use one letter abbreviations for modules *)

open Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst

open Types
(** Pretty-printing for types *)

module Types = struct
  let type_var_to_string (tv : type_var) : string = tv.tv_name

  let region_var_to_string (rv : region_var) : string =
    match rv.rv_name with
    | Some name -> name
    | None -> RegionVarId.to_string rv.rv_index

  let region_to_string (rid_to_string : 'rid -> string) (r : 'rid region) :
      string =
    match r with Static -> "'static" | Var rid -> rid_to_string rid

  let erased_region_to_string (_ : erased_region) : string = "'_"

  let ref_kind_to_string (rk : ref_kind) : string =
    match rk with Mut -> "Mut" | Shared -> "Shared"

  let assumed_ty_to_string (_ : assumed_ty) : string = "Box"

  (* TODO: This is probably not the most OCaml-like way of doing this *)
  type 'r type_formatter = {
    r_to_string : 'r -> string;
    (* TODO: remove this and put the name everywhere instead? *)
    type_var_id_to_string : TypeVarId.id -> string;
    (* TODO: remove this and put the name everywhere instead? *)
    type_def_id_to_string : TypeDefId.id -> string;
  }

  type etype_formatter = erased_region type_formatter

  type rtype_formatter = RegionVarId.id region type_formatter

  let integer_type_to_string = function
    | Isize -> "isize"
    | I8 -> "i8"
    | I16 -> "i16"
    | I32 -> "i32"
    | I64 -> "i64"
    | I128 -> "i128"
    | Usize -> "usize"
    | U8 -> "u8"
    | U16 -> "u16"
    | U32 -> "u32"
    | U64 -> "u64"
    | U128 -> "u128"

  let rec ty_to_string (fmt : 'r type_formatter) (ty : 'r ty) : string =
    match ty with
    | Adt (id, regions, tys) ->
        let params = params_to_string fmt regions tys in
        fmt.type_def_id_to_string id ^ params
    | TypeVar tv -> fmt.type_var_id_to_string tv
    | Bool -> "bool"
    | Char -> "char"
    | Never -> "⊥"
    | Integer int_ty -> integer_type_to_string int_ty
    | Str -> "str"
    | Array aty -> "[" ^ ty_to_string fmt aty ^ "; ?]"
    | Slice sty -> "[" ^ ty_to_string fmt sty ^ "]"
    | Ref (r, rty, ref_kind) -> (
        match ref_kind with
        | Mut -> "&" ^ fmt.r_to_string r ^ " mut (" ^ ty_to_string fmt rty ^ ")"
        | Shared -> "&" ^ fmt.r_to_string r ^ " (" ^ ty_to_string fmt rty ^ ")")
    | Tuple tys ->
        "(" ^ String.concat ",  " (List.map (ty_to_string fmt) tys) ^ ")"
    | Assumed (aty, regions, tys) -> (
        let params = params_to_string fmt regions tys in
        match aty with Box -> "std::boxed::Box" ^ params)

  and params_to_string (fmt : 'r type_formatter) (regions : 'r list)
      (types : 'r ty list) : string =
    if List.length regions + List.length types > 0 then
      let regions = List.map fmt.r_to_string regions in
      let types = List.map (ty_to_string fmt) types in
      let params = String.concat ", " (List.append regions types) in
      "<" ^ params ^ ">"
    else ""

  let rty_to_string fmt (ty : rty) : string = ty_to_string fmt ty

  let ety_to_string fmt (ty : ety) : string = ty_to_string fmt ty

  let field_to_string fmt (f : field) : string =
    f.field_name ^ " : " ^ ty_to_string fmt f.field_ty

  let variant_to_string fmt (v : variant) : string =
    v.variant_name ^ "("
    ^ String.concat ", "
        (List.map (field_to_string fmt) (FieldId.vector_to_list v.fields))
    ^ ")"

  let name_to_string (name : name) : string = String.concat "::" name

  let type_def_to_string (type_def_id_to_string : TypeDefId.id -> string)
      (def : type_def) : string =
    let regions : region_var list =
      RegionVarId.vector_to_list def.region_params
    in
    let types : type_var list = TypeVarId.vector_to_list def.type_params in
    let rid_to_string rid =
      match List.find_opt (fun rv -> rv.rv_index = rid) regions with
      | Some rv -> region_var_to_string rv
      | None -> failwith "Unreachable"
    in
    let r_to_string = region_to_string rid_to_string in
    let type_var_id_to_string id =
      match List.find_opt (fun tv -> tv.tv_index = id) types with
      | Some tv -> type_var_to_string tv
      | None -> failwith "Unreachable"
    in
    let fmt = { r_to_string; type_var_id_to_string; type_def_id_to_string } in
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
    | Struct fields ->
        let fields = FieldId.vector_to_list fields in
        if List.length fields > 0 then
          let fields =
            String.concat ","
              (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
          in
          "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
        else "struct" ^ name ^ params ^ "{}"
    | Enum variants ->
        let variants = VariantId.vector_to_list variants in
        let variants =
          List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
        in
        let variants = String.concat "\n" variants in
        "enum " ^ name ^ params ^ " =\n" ^ variants
end

(** Pretty-printing for values *)

open Values
module PT = Types (* local module *)

module Values = struct
  type value_formatter = {
    r_to_string : RegionVarId.id -> string;
    type_var_id_to_string : TypeVarId.id -> string;
    type_def_id_to_string : TypeDefId.id -> string;
    type_def_id_variant_id_to_string : TypeDefId.id -> VariantId.id -> string;
    var_id_to_string : VarId.id -> string;
  }

  let value_to_etype_formatter (fmt : value_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let value_to_rtype_formatter (fmt : value_formatter) : PT.rtype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.r_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let var_id_to_string (id : VarId.id) : string = "var@" ^ VarId.to_string id

  let var_to_string (v : var) : string =
    let id = var_id_to_string v.index in
    match v.name with None -> id | Some name -> name ^ "(" ^ id ^ ")"

  let big_int_to_string (bi : big_int) : string = Z.to_string bi

  let scalar_value_to_string (sv : scalar_value) : string =
    big_int_to_string sv.value ^ ": " ^ PT.integer_type_to_string sv.int_ty

  let constant_value_to_string (cv : constant_value) : string =
    match cv with
    | Scalar sv -> scalar_value_to_string sv
    | Bool b -> Bool.to_string b
    | Char c -> String.make 1 c
    | String s -> s

  let symbolic_value_id_to_string (id : SymbolicValueId.id) : string =
    "s@" ^ SymbolicValueId.to_string id

  let symbolic_value_to_string (fmt : PT.rtype_formatter) (sv : symbolic_value)
      : string =
    symbolic_value_id_to_string sv.sv_id ^ " : " ^ PT.ty_to_string fmt sv.sv_ty

  let region_id_to_string (rid : RegionId.id) : string =
    "r@" ^ RegionId.to_string rid

  let symbolic_proj_comp_to_string (fmt : PT.rtype_formatter)
      (sp : symbolic_proj_comp) : string =
    let regions = RegionId.set_to_string sp.rset_ended in
    "proj_comp " ^ regions ^ " (" ^ symbolic_value_to_string fmt sp.svalue ^ ")"

  let rec typed_value_to_string (fmt : value_formatter) (v : typed_value) :
      string =
    match v.value with
    | Concrete cv -> constant_value_to_string cv
    | Adt av ->
        let adt_ident =
          match av.variant_id with
          | Some vid -> fmt.type_def_id_variant_id_to_string av.def_id vid
          | None -> fmt.type_def_id_to_string av.def_id
        in
        let field_values = FieldId.vector_to_list av.field_values in
        if List.length field_values > 0 then
          let field_values =
            String.concat " "
              (List.map (typed_value_to_string fmt) field_values)
          in
          adt_ident ^ " " ^ field_values
        else adt_ident
    | Tuple values ->
        let values = FieldId.vector_to_list values in
        let values =
          String.concat ", " (List.map (typed_value_to_string fmt) values)
        in
        "(" ^ values ^ ")"
    | Bottom -> "⊥"
    | Assumed av -> (
        match av with Box bv -> "@Box(" ^ typed_value_to_string fmt bv ^ ")")
    | Borrow bc -> borrow_content_to_string fmt bc
    | Loan lc -> loan_content_to_string fmt lc
    | Symbolic sp ->
        symbolic_proj_comp_to_string (value_to_rtype_formatter fmt) sp

  and borrow_content_to_string (fmt : value_formatter) (bc : borrow_content) :
      string =
    match bc with
    | SharedBorrow bid -> "⌊shared@" ^ BorrowId.to_string bid ^ "⌋"
    | MutBorrow (bid, tv) ->
        "&mut@" ^ BorrowId.to_string bid ^ " ("
        ^ typed_value_to_string fmt tv
        ^ ")"
    | InactivatedMutBorrow bid ->
        "⌊inactivated_mut@" ^ BorrowId.to_string bid ^ "⌋"

  and loan_content_to_string (fmt : value_formatter) (lc : loan_content) :
      string =
    match lc with
    | SharedLoan (loans, v) ->
        let loans = BorrowId.set_to_string loans in
        "@shared_loan(" ^ loans ^ ", " ^ typed_value_to_string fmt v ^ ")"
    | MutLoan bid -> "⌊mut@" ^ BorrowId.to_string bid ^ "⌋"

  let symbolic_value_proj_to_string (fmt : value_formatter)
      (sv : symbolic_value) (rty : rty) : string =
    symbolic_value_id_to_string sv.sv_id
    ^ " : "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) sv.sv_ty
    ^ " <: "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) rty

  let rec abstract_shared_borrows_to_string (fmt : value_formatter)
      (abs : abstract_shared_borrows) : string =
    match abs with
    | AsbSet bs -> BorrowId.set_to_string bs
    | AsbProjReborrows (sv, rty) ->
        "{" ^ symbolic_value_proj_to_string fmt sv rty ^ "}"
    | AsbUnion (asb1, asb2) ->
        abstract_shared_borrows_to_string fmt asb1
        ^ " U "
        ^ abstract_shared_borrows_to_string fmt asb2

  let rec typed_avalue_to_string (fmt : value_formatter) (v : typed_avalue) :
      string =
    match v.avalue with
    | AConcrete cv -> constant_value_to_string cv
    | AAdt av ->
        let adt_ident =
          match av.avariant_id with
          | Some vid -> fmt.type_def_id_variant_id_to_string av.adef_id vid
          | None -> fmt.type_def_id_to_string av.adef_id
        in
        let field_values = FieldId.vector_to_list av.afield_values in
        if List.length field_values > 0 then
          let field_values =
            String.concat " "
              (List.map (typed_avalue_to_string fmt) field_values)
          in
          adt_ident ^ " " ^ field_values
        else adt_ident
    | ATuple values ->
        let values = FieldId.vector_to_list values in
        let values =
          String.concat ", " (List.map (typed_avalue_to_string fmt) values)
        in
        "(" ^ values ^ ")"
    | ABottom -> "⊥"
    | ALoan lc -> aloan_content_to_string fmt lc
    | ABorrow bc -> aborrow_content_to_string fmt bc
    | AAssumed av -> (
        match av with ABox bv -> "@Box(" ^ typed_avalue_to_string fmt bv ^ ")")
    | AProj pv -> aproj_to_string fmt pv

  and aloan_content_to_string (fmt : value_formatter) (lc : aloan_content) :
      string =
    match lc with
    | AMutLoan (bid, av) ->
        "⌊mut@" ^ BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ "⌋"
    | ASharedLoan (loans, v, av) ->
        let loans = BorrowId.set_to_string loans in
        "@shared_loan(" ^ loans ^ ", "
        ^ typed_value_to_string fmt v
        ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AEndedMutLoan ml ->
        "@ended_mut_loan{ given_back="
        ^ typed_value_to_string fmt ml.given_back
        ^ "; child="
        ^ typed_avalue_to_string fmt ml.child
        ^ " }"
    | AEndedSharedLoan (v, av) ->
        "@ended_shared_loan("
        ^ typed_value_to_string fmt v
        ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AIgnoredMutLoan (bid, av) ->
        "@ignored_mut_loan(" ^ BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AIgnoredSharedLoan asb ->
        "@ignored_shared_loan("
        ^ abstract_shared_borrows_to_string fmt asb
        ^ ")"

  and aborrow_content_to_string (fmt : value_formatter) (bc : aborrow_content) :
      string =
    match bc with
    | AMutBorrow (bid, av) ->
        "&mut@" ^ BorrowId.to_string bid ^ " ("
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | ASharedBorrow bid -> "⌊shared@" ^ BorrowId.to_string bid ^ "⌋"
    | AIgnoredMutBorrow av ->
        "@ignored_mut_borrow(" ^ typed_avalue_to_string fmt av ^ ")"
    | AEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_borrow{ given_back="
        ^ typed_avalue_to_string fmt ml.given_back
        ^ "; child: "
        ^ typed_avalue_to_string fmt ml.child
        ^ "}"
    | AIgnoredSharedBorrow sb ->
        "@ignored_shared_borrow("
        ^ abstract_shared_borrows_to_string fmt sb
        ^ ")"

  and aproj_to_string (fmt : value_formatter) (pv : aproj) : string =
    match pv with
    | AProjLoans sv ->
        "proj_loans ("
        ^ symbolic_value_to_string (value_to_rtype_formatter fmt) sv
        ^ ")"
    | AProjBorrows (sv, rty) ->
        "proj_borrows (" ^ symbolic_value_proj_to_string fmt sv rty ^ ")"

  let abs_to_string (fmt : value_formatter) (abs : abs) : string =
    let avs =
      List.map (fun av -> "  " ^ typed_avalue_to_string fmt av) abs.avalues
    in
    let avs = String.concat ",\n" avs in
    "abs@"
    ^ AbstractionId.to_string abs.abs_id
    ^ "{parents="
    ^ AbstractionId.set_to_string abs.parents
    ^ "}" ^ "{regions="
    ^ RegionId.set_to_string abs.regions
    ^ "}" ^ " {\n" ^ avs ^ "\n}"
end

module PV = Values (* Local module *)

open Contexts
module C = Contexts

(** Pretty-printing for contexts *)

module Contexts = struct
  open Values (* local module *)

  open Contexts

  let env_value_to_string (fmt : value_formatter) (ev : env_value) : string =
    match ev with
    | Var (var, tv) -> var_to_string var ^ " -> " ^ typed_value_to_string fmt tv
    | Abs abs -> abs_to_string fmt abs
    | Frame -> failwith "Can't print a Frame element"

  let env_to_string (fmt : value_formatter) (env : env) : string =
    "{\n"
    ^ String.concat ";\n"
        (List.map (fun ev -> "  " ^ env_value_to_string fmt ev) env)
    ^ "\n}"

  type ctx_formatter = value_formatter

  let eval_ctx_to_ctx_formatter (ctx : eval_ctx) : ctx_formatter =
    (* We shouldn't use r_to_string *)
    let r_to_string _ = failwith "Unreachable" in
    let type_var_id_to_string vid =
      let v = lookup_type_var ctx vid in
      v.tv_name
    in
    let type_def_id_to_string def_id =
      let def = TypeDefId.nth ctx.type_context def_id in
      PT.name_to_string def.name
    in
    let type_def_id_variant_id_to_string def_id variant_id =
      let def = TypeDefId.nth ctx.type_context def_id in
      match def.kind with
      | Struct _ -> failwith "Unreachable"
      | Enum variants ->
          let variant = VariantId.nth variants variant_id in
          PT.name_to_string def.name ^ "::" ^ variant.variant_name
    in
    let var_id_to_string vid =
      let var = ctx_lookup_var ctx vid in
      var_to_string var
    in
    {
      r_to_string;
      type_var_id_to_string;
      type_def_id_to_string;
      type_def_id_variant_id_to_string;
      var_id_to_string;
    }

  (** Split an [env] at every occurrence of [Frame], eliminating those elements.
          Also reorders the frames and the values in the frames according to the
          following order:
          * frames: from the first pushed (oldest) to the last pushed (current frame)
          * values: from the first pushed (oldest) to the last pushed
       *)
  let split_env_according_to_frames (env : env) : env list =
    let rec split_aux (frames : env list) (curr_frame : env) (env : env) =
      match env with
      | [] -> frames
      | Frame :: env' -> split_aux (curr_frame :: frames) [] env'
      | ev :: env' -> split_aux frames (ev :: curr_frame) env'
    in
    let frames = split_aux [] [] env in
    List.rev frames

  let eval_ctx_to_string (ctx : eval_ctx) : string =
    let fmt = eval_ctx_to_ctx_formatter ctx in
    let frames = split_env_according_to_frames ctx.env in
    let num_frames = List.length frames in
    let frames =
      List.mapi
        (fun i f ->
          "\n# Frame " ^ string_of_int i ^ ":\n" ^ env_to_string fmt f ^ "\n")
        frames
    in
    "# " ^ string_of_int num_frames ^ " frame(s)\n" ^ String.concat "" frames
end

module PC = Contexts

module CfimAst = struct
  type ast_formatter = {
    r_to_string : RegionVarId.id -> string;
    type_var_id_to_string : TypeVarId.id -> string;
    type_def_id_to_string : TypeDefId.id -> string;
    (* TODO: rename to something like adt_variant_to_string *)
    type_def_id_variant_id_to_string : TypeDefId.id -> VariantId.id -> string;
    adt_field_to_string :
      TypeDefId.id -> VariantId.id option -> FieldId.id -> string;
    var_id_to_string : VarId.id -> string;
    fun_def_id_to_string : A.FunDefId.id -> string;
  }

  let ast_to_ctx_formatter (fmt : ast_formatter) : PC.ctx_formatter =
    {
      PV.r_to_string = fmt.r_to_string;
      PV.type_var_id_to_string = fmt.type_var_id_to_string;
      PV.type_def_id_to_string = fmt.type_def_id_to_string;
      PV.type_def_id_variant_id_to_string = fmt.type_def_id_variant_id_to_string;
      PV.var_id_to_string = fmt.var_id_to_string;
    }

  let ast_to_etype_formatter (fmt : ast_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_def_id_to_string = fmt.type_def_id_to_string;
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
        | E.Field (E.ProjTuple _, fid) -> "(" ^ s ^ ")." ^ FieldId.to_string fid
        | E.Field (E.ProjAdt (adt_id, opt_variant_id), fid) -> (
            let field_name =
              fmt.adt_field_to_string adt_id opt_variant_id fid
            in
            match opt_variant_id with
            | None -> "(" ^ s ^ ")." ^ field_name
            | Some variant_id ->
                let variant_name =
                  fmt.type_def_id_variant_id_to_string adt_id variant_id
                in
                "(" ^ s ^ " as " ^ variant_name ^ ")." ^ field_name))

  let place_to_string (fmt : ast_formatter) (p : E.place) : string =
    let var = fmt.var_id_to_string p.E.var_id in
    projection_to_string fmt var p.E.projection

  let unop_to_string (unop : E.unop) : string =
    match unop with E.Not -> "¬" | E.Neg -> "-"

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

  let operand_constant_value_to_string (fmt : ast_formatter)
      (cv : E.operand_constant_value) : string =
    match cv with
    | E.ConstantValue cv -> PV.constant_value_to_string cv
    | E.ConstantAdt def_id -> fmt.type_def_id_to_string def_id
    | E.Unit -> "()"

  let operand_to_string (fmt : ast_formatter) (op : E.operand) : string =
    match op with
    | E.Copy p -> "copy " ^ place_to_string fmt p
    | E.Move p -> "move " ^ place_to_string fmt p
    | E.Constant (_ty, cv) -> operand_constant_value_to_string fmt cv

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
        | E.AggregatedAdt (def_id, opt_variant_id, _regions, _types) -> (
            let adt_name = fmt.type_def_id_to_string def_id in
            match opt_variant_id with
            | None -> adt_name ^ "{ " ^ String.concat ", " ops ^ " }"
            | Some variant_id ->
                let variant_name =
                  fmt.type_def_id_variant_id_to_string def_id variant_id
                in
                adt_name ^ "::" ^ variant_name ^ "(" ^ String.concat ", " ops
                ^ ")"))

  let statement_to_string (fmt : ast_formatter) (st : A.statement) : string =
    match st with
    | A.Assign (p, rv) ->
        place_to_string fmt p ^ " := " ^ rvalue_to_string fmt rv
    | A.FakeRead p -> "fake_read " ^ place_to_string fmt p
    | A.SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        "set_discriminant(" ^ place_to_string fmt p ^ ", "
        ^ T.VariantId.to_string variant_id
        ^ ")"
    | A.Drop p -> "drop(" ^ place_to_string fmt p ^ ")"
    | A.Assert a ->
        let cond = operand_to_string fmt a.A.cond in
        if a.A.expected then "assert(" ^ cond ^ ")"
        else "assert(¬" ^ cond ^ ")"
    | A.Call call -> (
        let ty_fmt = ast_to_etype_formatter fmt in
        let params =
          if List.length call.A.type_params > 0 then
            "<"
            ^ String.concat ","
                (List.map (PT.ty_to_string ty_fmt) call.A.type_params)
            ^ ">"
          else ""
        in
        match call.A.func with
        | A.Local fid -> fmt.fun_def_id_to_string fid ^ params
        | A.Assumed fid -> (
            match fid with
            | A.BoxNew -> "alloc::boxed::Box" ^ params ^ "::new"
            | A.BoxDeref -> "core::ops::deref::Deref<Box" ^ params ^ ">::deref"
            | A.BoxDerefMut ->
                "core::ops::deref::DerefMut<Box" ^ params ^ ">::deref_mut"
            | A.BoxFree -> "alloc::alloc::box_free<" ^ params ^ ">"))
    | A.Panic -> "panic"
    | A.Return -> "return"
    | A.Break i -> "break " ^ string_of_int i
    | A.Continue i -> "continue " ^ string_of_int i
    | A.Nop -> "nop"
end
