open Errors
open Identifiers

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
    type_var_id_to_string : TypeVarId.id -> string;
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

  and params_to_string fmt (regions : 'r list) (types : 'r ty list) : string =
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
      | None -> unreachable __LOC__
    in
    let r_to_string = region_to_string rid_to_string in
    let type_var_id_to_string id =
      match List.find_opt (fun tv -> tv.tv_index = id) types with
      | Some tv -> type_var_to_string tv
      | None -> unreachable __LOC__
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

module Values = struct
  open Types

  type value_formatter = {
    r_to_string : RegionVarId.id -> string;
    type_var_id_to_string : TypeVarId.id -> string;
    type_def_id_to_string : TypeDefId.id -> string;
    type_def_id_variant_id_to_string : TypeDefId.id -> VariantId.id -> string;
    var_id_to_string : VarId.id -> string;
  }

  let value_to_etype_formatter (fmt : value_formatter) : etype_formatter =
    {
      Types.r_to_string = erased_region_to_string;
      Types.type_var_id_to_string = fmt.type_var_id_to_string;
      Types.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let value_to_rtype_formatter (fmt : value_formatter) : rtype_formatter =
    {
      Types.r_to_string = region_to_string fmt.r_to_string;
      Types.type_var_id_to_string = fmt.type_var_id_to_string;
      Types.type_def_id_to_string = fmt.type_def_id_to_string;
    }

  let var_id_to_string (id : VarId.id) : string = "var@" ^ VarId.to_string id

  let var_to_string (v : var) : string =
    let id = var_id_to_string v.index in
    match v.name with None -> id | Some name -> name ^ "(" ^ id ^ ")"

  let big_int_to_string (bi : big_int) : string = Z.to_string bi

  let scalar_value_to_string (sv : scalar_value) : string =
    match sv with
    | Isize bi -> big_int_to_string bi ^ ": isize"
    | I8 bi -> big_int_to_string bi ^ ": i8"
    | I16 bi -> big_int_to_string bi ^ ": i16"
    | I32 bi -> big_int_to_string bi ^ ": i32"
    | I64 bi -> big_int_to_string bi ^ ": i64"
    | I128 bi -> big_int_to_string bi ^ ": i128"
    | Usize bi -> big_int_to_string bi ^ ": usize"
    | U8 bi -> big_int_to_string bi ^ ": u8"
    | U16 bi -> big_int_to_string bi ^ ": u16"
    | U32 bi -> big_int_to_string bi ^ ": u32"
    | U64 bi -> big_int_to_string bi ^ ": u64"
    | U128 bi -> big_int_to_string bi ^ ": u128"

  let constant_value_to_string (cv : constant_value) : string =
    match cv with
    | Scalar sv -> scalar_value_to_string sv
    | Bool b -> Bool.to_string b
    | Char c -> String.make 1 c
    | String s -> s

  let symbolic_value_id_to_string (id : SymbolicValueId.id) : string =
    "s@" ^ SymbolicValueId.to_string id

  let symbolic_value_to_string (fmt : rtype_formatter) (sv : symbolic_value) :
      string =
    symbolic_value_id_to_string sv.sv_id ^ " : " ^ ty_to_string fmt sv.sv_ty

  let region_id_to_string (rid : RegionId.id) : string =
    "r@" ^ RegionId.to_string rid

  let symbolic_proj_comp_to_string (fmt : rtype_formatter)
      (sp : symbolic_proj_comp) : string =
    let regions =
      RegionId.Set.fold
        (fun id ids -> region_id_to_string id :: ids)
        sp.rset_ended []
    in
    let regions = String.concat "," (List.rev regions) in
    "proj_comp {" ^ regions ^ "} ("
    ^ symbolic_value_to_string fmt sp.svalue
    ^ ")"

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
    | Borrow bc -> "" (* TODO *)
    | Loan lc -> "" (* TODO *)
    | Symbolic sp ->
        symbolic_proj_comp_to_string (value_to_rtype_formatter fmt) sp
end
