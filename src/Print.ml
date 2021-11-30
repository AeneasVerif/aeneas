(* TODO: use one letter abbreviations for modules *)

open Identifiers
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module C = Contexts
module M = Modules

(** Pretty-printing for types *)
module Types = struct
  let type_var_to_string (tv : T.type_var) : string = tv.tv_name

  let region_var_to_string (rv : T.region_var) : string =
    match rv.rv_name with
    | Some name -> name
    | None -> T.RegionVarId.to_string rv.rv_index

  let region_to_string (rid_to_string : 'rid -> string) (r : 'rid T.region) :
      string =
    match r with Static -> "'static" | Var rid -> rid_to_string rid

  let erased_region_to_string (_ : T.erased_region) : string = "'_"

  let ref_kind_to_string (rk : T.ref_kind) : string =
    match rk with Mut -> "Mut" | Shared -> "Shared"

  let assumed_ty_to_string (_ : T.assumed_ty) : string = "Box"

  (* TODO: This is probably not the most OCaml-like way of doing this *)
  type 'r type_formatter = {
    r_to_string : 'r -> string;
    (* TODO: remove this and put the name everywhere instead? *)
    type_var_id_to_string : T.TypeVarId.id -> string;
    (* TODO: remove this and put the name everywhere instead? *)
    type_def_id_to_string : T.TypeDefId.id -> string;
  }

  type etype_formatter = T.erased_region type_formatter

  type rtype_formatter = T.RegionVarId.id T.region type_formatter

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

  let rec ty_to_string (fmt : 'r type_formatter) (ty : 'r T.ty) : string =
    match ty with
    | T.Adt (id, regions, tys) ->
        let params = params_to_string fmt regions tys in
        fmt.type_def_id_to_string id ^ params
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
    | T.Tuple tys ->
        "(" ^ String.concat ",  " (List.map (ty_to_string fmt) tys) ^ ")"
    | T.Assumed (aty, regions, tys) -> (
        let params = params_to_string fmt regions tys in
        match aty with Box -> "std::boxed::Box" ^ params)

  and params_to_string (fmt : 'r type_formatter) (regions : 'r list)
      (types : 'r T.ty list) : string =
    if List.length regions + List.length types > 0 then
      let regions = List.map fmt.r_to_string regions in
      let types = List.map (ty_to_string fmt) types in
      let params = String.concat ", " (List.append regions types) in
      "<" ^ params ^ ">"
    else ""

  let rty_to_string fmt (ty : T.rty) : string = ty_to_string fmt ty

  let ety_to_string fmt (ty : T.ety) : string = ty_to_string fmt ty

  let field_to_string fmt (f : T.field) : string =
    f.field_name ^ " : " ^ ty_to_string fmt f.field_ty

  let variant_to_string fmt (v : T.variant) : string =
    v.variant_name ^ "("
    ^ String.concat ", "
        (List.map (field_to_string fmt) (T.FieldId.vector_to_list v.fields))
    ^ ")"

  let name_to_string (name : name) : string = String.concat "::" name

  let type_def_to_string (type_def_id_to_string : T.TypeDefId.id -> string)
      (def : T.type_def) : string =
    let regions : T.region_var list =
      T.RegionVarId.vector_to_list def.region_params
    in
    let types : T.type_var list = T.TypeVarId.vector_to_list def.type_params in
    let rid_to_string rid =
      match List.find_opt (fun rv -> rv.T.rv_index = rid) regions with
      | Some rv -> region_var_to_string rv
      | None -> failwith "Unreachable"
    in
    let r_to_string = region_to_string rid_to_string in
    let type_var_id_to_string id =
      match List.find_opt (fun tv -> tv.T.tv_index = id) types with
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
    | T.Struct fields ->
        let fields = T.FieldId.vector_to_list fields in
        if List.length fields > 0 then
          let fields =
            String.concat ","
              (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
          in
          "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
        else "struct " ^ name ^ params ^ "{}"
    | T.Enum variants ->
        let variants = T.VariantId.vector_to_list variants in
        let variants =
          List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
        in
        let variants = String.concat "\n" variants in
        "enum " ^ name ^ params ^ " =\n" ^ variants
end

module PT = Types (* local module *)

(** Pretty-printing for values *)
module Values = struct
  type value_formatter = {
    r_to_string : T.RegionVarId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_def_id_to_string : T.TypeDefId.id -> string;
    adt_variant_to_string : T.TypeDefId.id -> T.VariantId.id -> string;
    var_id_to_string : V.VarId.id -> string;
    adt_field_names :
      T.TypeDefId.id -> T.VariantId.id option -> string list option;
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

  let var_id_to_string (id : V.VarId.id) : string =
    "var@" ^ V.VarId.to_string id

  let var_to_string (v : V.var) : string =
    match v.name with None -> var_id_to_string v.index | Some name -> name

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
    symbolic_value_id_to_string sv.sv_id ^ " : " ^ PT.ty_to_string fmt sv.sv_ty

  let region_id_to_string (rid : V.RegionId.id) : string =
    "r@" ^ V.RegionId.to_string rid

  let symbolic_proj_comp_to_string (fmt : PT.rtype_formatter)
      (sp : V.symbolic_proj_comp) : string =
    let regions = V.RegionId.set_to_string sp.rset_ended in
    "proj_comp " ^ regions ^ " (" ^ symbolic_value_to_string fmt sp.svalue ^ ")"

  let rec typed_value_to_string (fmt : value_formatter) (v : V.typed_value) :
      string =
    let ety_fmt = value_to_etype_formatter fmt in
    match v.value with
    | Concrete cv -> constant_value_to_string cv
    | Adt av ->
        let adt_ident =
          match av.variant_id with
          | Some vid -> fmt.adt_variant_to_string av.def_id vid
          | None -> fmt.type_def_id_to_string av.def_id
        in
        let field_values = T.FieldId.vector_to_list av.field_values in
        let field_values = List.map (typed_value_to_string fmt) field_values in
        if List.length field_values > 0 then
          match fmt.adt_field_names av.V.def_id av.V.variant_id with
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
              let field_values = String.concat "; " field_values in
              adt_ident ^ " { " ^ field_values ^ " }"
        else adt_ident
    | Tuple values ->
        let values = T.FieldId.vector_to_list values in
        let values =
          String.concat ", " (List.map (typed_value_to_string fmt) values)
        in
        "(" ^ values ^ ")"
    | Bottom -> "⊥ : " ^ PT.ety_to_string ety_fmt v.ty
    | Assumed av -> (
        match av with Box bv -> "@Box(" ^ typed_value_to_string fmt bv ^ ")")
    | Borrow bc -> borrow_content_to_string fmt bc
    | Loan lc -> loan_content_to_string fmt lc
    | Symbolic sp ->
        symbolic_proj_comp_to_string (value_to_rtype_formatter fmt) sp

  and borrow_content_to_string (fmt : value_formatter) (bc : V.borrow_content) :
      string =
    match bc with
    | SharedBorrow bid -> "⌊shared@" ^ V.BorrowId.to_string bid ^ "⌋"
    | MutBorrow (bid, tv) ->
        "&mut@" ^ V.BorrowId.to_string bid ^ " ("
        ^ typed_value_to_string fmt tv
        ^ ")"
    | InactivatedMutBorrow bid ->
        "⌊inactivated_mut@" ^ V.BorrowId.to_string bid ^ "⌋"

  and loan_content_to_string (fmt : value_formatter) (lc : V.loan_content) :
      string =
    match lc with
    | SharedLoan (loans, v) ->
        let loans = V.BorrowId.set_to_string loans in
        "@shared_loan(" ^ loans ^ ", " ^ typed_value_to_string fmt v ^ ")"
    | MutLoan bid -> "⌊mut@" ^ V.BorrowId.to_string bid ^ "⌋"

  let symbolic_value_proj_to_string (fmt : value_formatter)
      (sv : V.symbolic_value) (rty : T.rty) : string =
    symbolic_value_id_to_string sv.sv_id
    ^ " : "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) sv.sv_ty
    ^ " <: "
    ^ PT.ty_to_string (value_to_rtype_formatter fmt) rty

  let rec abstract_shared_borrows_to_string (fmt : value_formatter)
      (abs : V.abstract_shared_borrows) : string =
    match abs with
    | AsbSet bs -> V.BorrowId.set_to_string bs
    | AsbProjReborrows (sv, rty) ->
        "{" ^ symbolic_value_proj_to_string fmt sv rty ^ "}"
    | AsbUnion (asb1, asb2) ->
        abstract_shared_borrows_to_string fmt asb1
        ^ " U "
        ^ abstract_shared_borrows_to_string fmt asb2

  let rec typed_avalue_to_string (fmt : value_formatter) (v : V.typed_avalue) :
      string =
    let rty_fmt = value_to_rtype_formatter fmt in
    match v.avalue with
    | AConcrete cv -> constant_value_to_string cv
    | AAdt av ->
        let adt_ident =
          match av.avariant_id with
          | Some vid -> fmt.adt_variant_to_string av.adef_id vid
          | None -> fmt.type_def_id_to_string av.adef_id
        in
        let field_values = T.FieldId.vector_to_list av.afield_values in
        if List.length field_values > 0 then
          let field_values =
            String.concat " "
              (List.map (typed_avalue_to_string fmt) field_values)
          in
          adt_ident ^ " " ^ field_values
        else adt_ident
    | ATuple values ->
        let values = T.FieldId.vector_to_list values in
        let values =
          String.concat ", " (List.map (typed_avalue_to_string fmt) values)
        in
        "(" ^ values ^ ")"
    | ABottom -> "⊥ : " ^ PT.rty_to_string rty_fmt v.aty
    | ALoan lc -> aloan_content_to_string fmt lc
    | ABorrow bc -> aborrow_content_to_string fmt bc
    | AAssumed av -> (
        match av with ABox bv -> "@Box(" ^ typed_avalue_to_string fmt bv ^ ")")
    | AProj pv -> aproj_to_string fmt pv

  and aloan_content_to_string (fmt : value_formatter) (lc : V.aloan_content) :
      string =
    match lc with
    | AMutLoan (bid, av) ->
        "⌊mut@" ^ V.BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ "⌋"
    | ASharedLoan (loans, v, av) ->
        let loans = V.BorrowId.set_to_string loans in
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
        "@ignored_mut_loan(" ^ V.BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | AIgnoredSharedLoan asb ->
        "@ignored_shared_loan("
        ^ abstract_shared_borrows_to_string fmt asb
        ^ ")"

  and aborrow_content_to_string (fmt : value_formatter) (bc : V.aborrow_content)
      : string =
    match bc with
    | AMutBorrow (bid, av) ->
        "&mut@" ^ V.BorrowId.to_string bid ^ " ("
        ^ typed_avalue_to_string fmt av
        ^ ")"
    | ASharedBorrow bid -> "⌊shared@" ^ V.BorrowId.to_string bid ^ "⌋"
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

  and aproj_to_string (fmt : value_formatter) (pv : V.aproj) : string =
    match pv with
    | AProjLoans sv ->
        "proj_loans ("
        ^ symbolic_value_to_string (value_to_rtype_formatter fmt) sv
        ^ ")"
    | AProjBorrows (sv, rty) ->
        "proj_borrows (" ^ symbolic_value_proj_to_string fmt sv rty ^ ")"

  let abs_to_string (fmt : value_formatter) (abs : V.abs) : string =
    let avs =
      List.map (fun av -> "  " ^ typed_avalue_to_string fmt av) abs.avalues
    in
    let avs = String.concat ",\n" avs in
    "abs@"
    ^ V.AbstractionId.to_string abs.abs_id
    ^ "{parents="
    ^ V.AbstractionId.set_to_string abs.parents
    ^ "}" ^ "{regions="
    ^ V.RegionId.set_to_string abs.regions
    ^ "}" ^ " {\n" ^ avs ^ "\n}"
end

module PV = Values (* local module *)

(** Pretty-printing for contexts *)
module Contexts = struct
  let env_value_to_string (fmt : PV.value_formatter) (ev : C.env_value) : string
      =
    match ev with
    | Var (var, tv) ->
        PV.var_to_string var ^ " -> " ^ PV.typed_value_to_string fmt tv ^ " ;"
    | Abs abs -> PV.abs_to_string fmt abs
    | Frame -> failwith "Can't print a Frame element"

  let env_to_string (fmt : PV.value_formatter) (env : C.env) : string =
    "{\n"
    ^ String.concat "\n"
        (List.map (fun ev -> "  " ^ env_value_to_string fmt ev) env)
    ^ "\n}"

  type ctx_formatter = PV.value_formatter

  let ctx_to_etype_formatter (fmt : ctx_formatter) : PT.etype_formatter =
    PV.value_to_etype_formatter fmt

  let ctx_to_rtype_formatter (fmt : ctx_formatter) : PT.rtype_formatter =
    PV.value_to_rtype_formatter fmt

  let type_ctx_to_adt_variant_to_string_fun
      (ctx : T.type_def T.TypeDefId.vector) :
      T.TypeDefId.id -> T.VariantId.id -> string =
   fun def_id variant_id ->
    let def = T.TypeDefId.nth ctx def_id in
    match def.kind with
    | Struct _ -> failwith "Unreachable"
    | Enum variants ->
        let variant = T.VariantId.nth variants variant_id in
        PT.name_to_string def.name ^ "::" ^ variant.variant_name

  let type_ctx_to_adt_field_names_fun (ctx : T.type_def T.TypeDefId.vector) :
      T.TypeDefId.id -> T.VariantId.id option -> string list option =
   fun def_id opt_variant_id ->
    let def = T.TypeDefId.nth ctx def_id in
    let fields = T.type_def_get_fields def opt_variant_id in
    (* TODO: the field name should be optional?? *)
    let fields = T.FieldId.map (fun f -> f.T.field_name) fields in
    Some (T.FieldId.vector_to_list fields)

  let eval_ctx_to_ctx_formatter (ctx : C.eval_ctx) : ctx_formatter =
    (* We shouldn't use r_to_string *)
    let r_to_string _ = failwith "Unexpected use of r_to_string" in
    let type_var_id_to_string vid =
      let v = C.lookup_type_var ctx vid in
      v.tv_name
    in
    let type_def_id_to_string def_id =
      let def = T.TypeDefId.nth ctx.type_context def_id in
      PT.name_to_string def.name
    in
    let adt_variant_to_string =
      type_ctx_to_adt_variant_to_string_fun ctx.type_context
    in
    let var_id_to_string vid =
      let var = C.ctx_lookup_var ctx vid in
      PV.var_to_string var
    in
    let adt_field_names = type_ctx_to_adt_field_names_fun ctx.C.type_context in
    {
      r_to_string;
      type_var_id_to_string;
      type_def_id_to_string;
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

module PC = Contexts (* local module *)

(** Pretty-printing for contexts (generic functions) *)
module CfimAst = struct
  type ast_formatter = {
    r_to_string : T.RegionVarId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_def_id_to_string : T.TypeDefId.id -> string;
    adt_variant_to_string : T.TypeDefId.id -> T.VariantId.id -> string;
    adt_field_to_string :
      T.TypeDefId.id -> T.VariantId.id option -> T.FieldId.id -> string;
    var_id_to_string : V.VarId.id -> string;
    adt_field_names :
      T.TypeDefId.id -> T.VariantId.id option -> string list option;
    fun_def_id_to_string : A.FunDefId.id -> string;
  }

  let ast_to_ctx_formatter (fmt : ast_formatter) : PC.ctx_formatter =
    {
      PV.r_to_string = fmt.r_to_string;
      PV.type_var_id_to_string = fmt.type_var_id_to_string;
      PV.type_def_id_to_string = fmt.type_def_id_to_string;
      PV.adt_variant_to_string = fmt.adt_variant_to_string;
      PV.var_id_to_string = fmt.var_id_to_string;
      PV.adt_field_names = fmt.adt_field_names;
    }

  let ast_to_etype_formatter (fmt : ast_formatter) : PT.etype_formatter =
    {
      PT.r_to_string = PT.erased_region_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let ast_to_rtype_formatter (fmt : ast_formatter) : PT.rtype_formatter =
    {
      PT.r_to_string = PT.region_to_string fmt.r_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let type_ctx_to_adt_field_to_string_fun (ctx : T.type_def T.TypeDefId.vector)
      : T.TypeDefId.id -> T.VariantId.id option -> T.FieldId.id -> string =
   fun def_id opt_variant_id field_id ->
    let def = T.TypeDefId.nth ctx def_id in
    let fields = T.type_def_get_fields def opt_variant_id in
    let field = T.FieldId.nth fields field_id in
    field.T.field_name

  let eval_ctx_to_ast_formatter (ctx : C.eval_ctx) : ast_formatter =
    let ctx_fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let adt_field_to_string =
      type_ctx_to_adt_field_to_string_fun ctx.type_context
    in
    let fun_def_id_to_string def_id =
      let def = A.FunDefId.nth ctx.fun_context def_id in
      PT.name_to_string def.name
    in
    {
      r_to_string = ctx_fmt.PV.r_to_string;
      type_var_id_to_string = ctx_fmt.PV.type_var_id_to_string;
      type_def_id_to_string = ctx_fmt.PV.type_def_id_to_string;
      adt_variant_to_string = ctx_fmt.PV.adt_variant_to_string;
      var_id_to_string = ctx_fmt.PV.var_id_to_string;
      adt_field_names = ctx_fmt.PV.adt_field_names;
      adt_field_to_string;
      fun_def_id_to_string;
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
        | E.Field (E.ProjTuple _, fid) ->
            "(" ^ s ^ ")." ^ T.FieldId.to_string fid
        | E.Field (E.ProjAdt (adt_id, opt_variant_id), fid) -> (
            let field_name =
              fmt.adt_field_to_string adt_id opt_variant_id fid
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
        | E.AggregatedAdt (def_id, opt_variant_id, _regions, _types) ->
            let adt_name = fmt.type_def_id_to_string def_id in
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
    | A.Call call ->
        let ty_fmt = ast_to_etype_formatter fmt in
        let params =
          if List.length call.A.type_params > 0 then
            "<"
            ^ String.concat ","
                (List.map (PT.ty_to_string ty_fmt) call.A.type_params)
            ^ ">"
          else ""
        in
        let args = List.map (operand_to_string fmt) call.A.args in
        let args = "(" ^ String.concat ", " args ^ ")" in
        let name_params =
          match call.A.func with
          | A.Local fid -> fmt.fun_def_id_to_string fid ^ params
          | A.Assumed fid -> (
              match fid with
              | A.BoxNew -> "alloc::boxed::Box" ^ params ^ "::new"
              | A.BoxDeref ->
                  "core::ops::deref::Deref<Box" ^ params ^ ">::deref"
              | A.BoxDerefMut ->
                  "core::ops::deref::DerefMut" ^ params ^ "::deref_mut"
              | A.BoxFree -> "alloc::alloc::box_free" ^ params)
        in
        name_params ^ args
    | A.Panic -> "panic"
    | A.Return -> "return"
    | A.Break i -> "break " ^ string_of_int i
    | A.Continue i -> "continue " ^ string_of_int i
    | A.Nop -> "nop"

  let rec expression_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (e : A.expression) : string =
    match e with
    | A.Statement st -> indent ^ statement_to_string fmt st ^ ";"
    | A.Sequence (e1, e2) ->
        expression_to_string fmt indent indent_incr e1
        ^ "\n"
        ^ expression_to_string fmt indent indent_incr e2
    | A.Switch (op, tgts) -> (
        let op = operand_to_string fmt op in
        match tgts with
        | A.If (true_e, false_e) ->
            let inner_indent = indent ^ indent_incr in
            let inner_to_string =
              expression_to_string fmt inner_indent indent_incr
            in
            let true_e = inner_to_string true_e in
            let false_e = inner_to_string false_e in
            indent ^ "if (" ^ op ^ ") {\n" ^ true_e ^ "\n" ^ indent ^ "}\n"
            ^ indent ^ "else {\n" ^ false_e ^ "\n" ^ indent ^ "}"
        | A.SwitchInt (_ty, branches, otherwise) ->
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 =
              expression_to_string fmt indent2 indent_incr
            in
            let branches =
              List.map
                (fun (sv, be) ->
                  indent1
                  ^ PV.scalar_value_to_string sv
                  ^ " => {\n" ^ inner_to_string2 be ^ "\n" ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              branches ^ "\n" ^ indent1 ^ "_ => {\n"
              ^ inner_to_string2 otherwise ^ "\n" ^ indent1 ^ "}"
            in
            indent ^ "switch (" ^ op ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | A.Loop loop_e ->
        indent ^ "loop {\n"
        ^ expression_to_string fmt (indent ^ indent_incr) indent_incr loop_e
        ^ "\n" ^ indent ^ "}"

  let fun_def_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.fun_def) : string =
    let rty_fmt = ast_to_rtype_formatter fmt in
    let rty_to_string = PT.rty_to_string rty_fmt in
    let ety_fmt = ast_to_etype_formatter fmt in
    let ety_to_string = PT.ety_to_string ety_fmt in
    let sg = def.signature in

    (* Function name *)
    let name = PT.name_to_string def.A.name in

    (* Region/type parameters *)
    let regions = T.RegionVarId.vector_to_list sg.region_params in
    let types = T.TypeVarId.vector_to_list sg.type_params in
    let params =
      if List.length regions + List.length types = 0 then ""
      else
        let regions = List.map PT.region_var_to_string regions in
        let types = List.map PT.type_var_to_string types in
        "<" ^ String.concat "," (List.append regions types) ^ ">"
    in

    (* Arguments *)
    let inputs = V.VarId.vector_to_list def.locals in
    let ret_var, inputs =
      match inputs with
      | [] -> failwith "Inconsistent signature"
      | ret_var :: inputs -> (ret_var, inputs)
    in
    let inputs, _aux_locals = Utilities.list_split_at inputs def.arg_count in
    let args = List.combine inputs (V.VarId.vector_to_list sg.inputs) in
    let args =
      List.map
        (fun (var, rty) -> PV.var_to_string var ^ " : " ^ rty_to_string rty)
        args
    in
    let args = String.concat ", " args in

    (* Return type *)
    let ret_ty = sg.output in
    let ret_ty =
      if T.ty_is_unit ret_ty then "" else " -> " ^ rty_to_string ret_ty
    in

    (* All the locals (with erased regions) *)
    let locals =
      List.map
        (fun var ->
          indent ^ indent_incr ^ PV.var_to_string var ^ " : "
          ^ ety_to_string var.var_ty ^ ";")
        (V.VarId.vector_to_list def.locals)
    in
    let locals = String.concat "\n" locals in

    (* Body *)
    let body =
      expression_to_string fmt (indent ^ indent_incr) indent_incr def.body
    in

    (* Put everything together *)
    indent ^ "fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ " {\n" ^ locals
    ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"
end

module PA = CfimAst (* local module *)

(** Pretty-printing for ASTs (functions based on a definition context) *)
module Module = struct
  (** This function pretty-prints a type definition by using a definition
      context *)
  let type_def_to_string (type_context : T.type_def T.TypeDefId.vector)
      (def : T.type_def) : string =
    let type_def_id_to_string (id : T.TypeDefId.id) : string =
      let def = T.TypeDefId.nth type_context id in
      PT.name_to_string def.name
    in
    PT.type_def_to_string type_def_id_to_string def

  (** Generate an [ast_formatter] by using a definition context in combination
      with the variables local to a function's definition *)
  let def_ctx_to_ast_formatter (type_context : T.type_def T.TypeDefId.vector)
      (fun_context : A.fun_def A.FunDefId.vector) (def : A.fun_def) :
      PA.ast_formatter =
    let r_to_string vid =
      let var = T.RegionVarId.nth def.signature.region_params vid in
      PT.region_var_to_string var
    in
    let type_var_id_to_string vid =
      let var = T.TypeVarId.nth def.signature.type_params vid in
      PT.type_var_to_string var
    in
    let type_def_id_to_string def_id =
      let def = T.TypeDefId.nth type_context def_id in
      PT.name_to_string def.name
    in
    let fun_def_id_to_string def_id =
      let def = A.FunDefId.nth fun_context def_id in
      PT.name_to_string def.name
    in
    let var_id_to_string vid =
      let var = V.VarId.nth def.locals vid in
      PV.var_to_string var
    in
    let adt_variant_to_string =
      PC.type_ctx_to_adt_variant_to_string_fun type_context
    in
    let adt_field_to_string =
      PA.type_ctx_to_adt_field_to_string_fun type_context
    in
    let adt_field_names = PC.type_ctx_to_adt_field_names_fun type_context in
    {
      r_to_string;
      type_var_id_to_string;
      type_def_id_to_string;
      adt_variant_to_string;
      adt_field_to_string;
      var_id_to_string;
      adt_field_names;
      fun_def_id_to_string;
    }

  (** This function pretty-prints a function definition by using a definition
      context *)
  let fun_def_to_string (type_context : T.type_def T.TypeDefId.vector)
      (fun_context : A.fun_def A.FunDefId.vector) (def : A.fun_def) : string =
    let fmt = def_ctx_to_ast_formatter type_context fun_context def in
    PA.fun_def_to_string fmt "" "  " def

  let module_to_string (m : M.cfim_module) : string =
    (* The types *)
    let type_defs =
      List.map
        (type_def_to_string m.M.types)
        (T.TypeDefId.vector_to_list m.M.types)
    in

    (* The functions *)
    let fun_defs =
      List.map
        (fun_def_to_string m.M.types m.M.functions)
        (A.FunDefId.vector_to_list m.M.functions)
    in

    (* Put everything together *)
    let all_defs = List.append type_defs fun_defs in
    String.concat "\n\n" all_defs
end

(** Pretty-printing for ASTs (functions based on an evaluation context) *)
module EvalCtxCfimAst = struct
  let ety_to_string (ctx : C.eval_ctx) (t : T.ety) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_etype_formatter fmt in
    PT.ety_to_string fmt t

  let rty_to_string (ctx : C.eval_ctx) (t : T.rty) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_rtype_formatter fmt in
    PT.rty_to_string fmt t

  let typed_value_to_string (ctx : C.eval_ctx) (v : V.typed_value) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.typed_value_to_string fmt v

  let operand_to_string (ctx : C.eval_ctx) (op : E.operand) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.operand_to_string fmt op

  let statement_to_string (ctx : C.eval_ctx) (s : A.statement) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.statement_to_string fmt s

  let expression_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (e : A.expression) : string =
    let fmt = PA.eval_ctx_to_ast_formatter ctx in
    PA.expression_to_string fmt indent indent_incr e
end
