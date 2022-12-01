include Charon.PrintUtils
include Charon.PrintLlbcAst
module V = Values
module VU = ValuesUtils
module C = Contexts
module PrimitiveValues = Charon.PrintPrimitiveValues
module Types = Charon.PrintTypes
module Expressions = Charon.PrintExpressions

(** Pretty-printing for values *)
module Values = struct
  type value_formatter = {
    rvar_to_string : T.RegionVarId.id -> string;
    r_to_string : T.RegionId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
    adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
    var_id_to_string : E.VarId.id -> string;
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

  let var_id_to_string (id : E.VarId.id) : string =
    "var@" ^ E.VarId.to_string id

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
    | Primitive cv -> PPV.primitive_value_to_string cv
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
                else raise (Failure "Unreachable")
            | Vec, _ -> "@Vec[" ^ String.concat ", " field_values ^ "]"
            | _ -> raise (Failure "Inconsistent value"))
        | _ -> raise (Failure "Inconsistent typed value"))
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
    | ReservedMutBorrow (_, bid) ->
        "⌊reserved_mut@" ^ V.BorrowId.to_string bid ^ "⌋"

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
    | APrimitive cv -> PPV.primitive_value_to_string cv
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
            | _ -> raise (Failure "Inconsistent value"))
        | _ -> raise (Failure "Inconsistent typed value"))
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
    | AIgnoredMutLoan (opt_bid, av) ->
        "@ignored_mut_loan("
        ^ option_to_string V.BorrowId.to_string opt_bid
        ^ ", "
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
  let var_binder_to_string (bv : C.var_binder) : string =
    match bv.name with
    | None -> PV.var_id_to_string bv.index
    | Some name -> name

  let dummy_var_id_to_string (bid : C.DummyVarId.id) : string =
    "_@" ^ C.DummyVarId.to_string bid

  let binder_to_string (bv : C.binder) : string =
    match bv with
    | VarBinder b -> var_binder_to_string b
    | DummyBinder bid -> dummy_var_id_to_string bid

  let env_elem_to_string (fmt : PV.value_formatter) (indent : string)
      (indent_incr : string) (ev : C.env_elem) : string =
    match ev with
    | Var (var, tv) ->
        let bv = binder_to_string var in
        indent ^ bv ^ " -> " ^ PV.typed_value_to_string fmt tv ^ " ;"
    | Abs abs -> PV.abs_to_string fmt indent indent_incr abs
    | Frame -> raise (Failure "Can't print a Frame element")

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
      | Var (VarBinder _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if VU.is_bottom tv.value then None else Some ev
      | Var (DummyBinder _, tv) ->
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

  let ast_to_ctx_formatter (fmt : PA.ast_formatter) : ctx_formatter =
    {
      PV.rvar_to_string = fmt.rvar_to_string;
      PV.r_to_string = fmt.r_to_string;
      PV.type_var_id_to_string = fmt.type_var_id_to_string;
      PV.type_decl_id_to_string = fmt.type_decl_id_to_string;
      PV.adt_variant_to_string = fmt.adt_variant_to_string;
      PV.var_id_to_string = fmt.var_id_to_string;
      PV.adt_field_names = fmt.adt_field_names;
    }

  let ast_to_value_formatter (fmt : PA.ast_formatter) : PV.value_formatter =
    ast_to_ctx_formatter fmt

  let ctx_to_etype_formatter (fmt : ctx_formatter) : PT.etype_formatter =
    PV.value_to_etype_formatter fmt

  let ctx_to_rtype_formatter (fmt : ctx_formatter) : PT.rtype_formatter =
    PV.value_to_rtype_formatter fmt

  let eval_ctx_to_ctx_formatter (ctx : C.eval_ctx) : ctx_formatter =
    (* We shouldn't use rvar_to_string *)
    let rvar_to_string _r =
      raise (Failure "Unexpected use of rvar_to_string")
    in
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
      PT.type_ctx_to_adt_variant_to_string_fun ctx.type_context.type_decls
    in
    let var_id_to_string vid =
      let bv = C.ctx_lookup_var_binder ctx vid in
      var_binder_to_string bv
    in
    let adt_field_names =
      PT.type_ctx_to_adt_field_names_fun ctx.type_context.type_decls
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

  let eval_ctx_to_ast_formatter (ctx : C.eval_ctx) : PA.ast_formatter =
    let ctx_fmt = eval_ctx_to_ctx_formatter ctx in
    let adt_field_to_string =
      PT.type_ctx_to_adt_field_to_string_fun ctx.type_context.type_decls
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

  let eval_ctx_to_string_gen (filter : bool) (ctx : C.eval_ctx) : string =
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
              | C.Var (DummyBinder _, _) -> num_dummies := !num_abs + 1
              | C.Var (VarBinder _, _) -> num_bindings := !num_bindings + 1
              | C.Abs _ -> num_abs := !num_abs + 1
              | _ -> raise (Failure "Unreachable"))
            f;
          "\n# Frame " ^ string_of_int i ^ ":" ^ "\n- locals: "
          ^ string_of_int !num_bindings
          ^ "\n- dummy bindings: " ^ string_of_int !num_dummies
          ^ "\n- abstractions: " ^ string_of_int !num_abs ^ "\n"
          ^ env_to_string filter fmt f ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames

  let eval_ctx_to_string (ctx : C.eval_ctx) : string =
    eval_ctx_to_string_gen true ctx

  let eval_ctx_to_string_no_filter (ctx : C.eval_ctx) : string =
    eval_ctx_to_string_gen false ctx
end

module PC = Contexts (* local module *)

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
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PE.place_to_string fmt op

  let operand_to_string (ctx : C.eval_ctx) (op : E.operand) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PE.operand_to_string fmt op

  let statement_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (e : A.statement) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.statement_to_string fmt indent indent_incr e

  let env_elem_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (ev : C.env_elem) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PC.env_elem_to_string fmt indent indent_incr ev

  let abs_to_string (ctx : C.eval_ctx) (indent : string) (indent_incr : string)
      (abs : V.abs) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.abs_to_string fmt indent indent_incr abs
end
