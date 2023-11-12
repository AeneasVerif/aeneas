include Charon.PrintUtils
include Charon.PrintLlbcAst
module V = Values
module VU = ValuesUtils
module C = Contexts
module PrimitiveValues = Charon.PrintPrimitiveValues
module Types = Charon.PrintTypes
module Expressions = Charon.PrintExpressions

let list_to_string (to_string : 'a -> string) (ls : 'a list) : string =
  "[" ^ String.concat "; " (List.map to_string ls) ^ "]"

let bool_to_string (b : bool) : string = if b then "true" else "false"

(** Pretty-printing for values *)
module Values = struct
  type value_formatter = {
    region_id_to_string : T.RegionId.id -> string;
    type_var_id_to_string : T.TypeVarId.id -> string;
    type_decl_id_to_string : T.TypeDeclId.id -> string;
    const_generic_var_id_to_string : T.ConstGenericVarId.id -> string;
    global_decl_id_to_string : T.GlobalDeclId.id -> string;
    trait_decl_id_to_string : T.TraitDeclId.id -> string;
    trait_impl_id_to_string : T.TraitImplId.id -> string;
    trait_clause_id_to_string : T.TraitClauseId.id -> string;
    adt_variant_to_string : T.TypeDeclId.id -> T.VariantId.id -> string;
    var_id_to_string : E.VarId.id -> string;
    adt_field_names :
      T.TypeDeclId.id -> T.VariantId.id option -> string list option;
  }

  let value_to_type_formatter (fmt : value_formatter) : PT.type_formatter =
    {
      PT.region_id_to_string = fmt.region_id_to_string;
      PT.type_var_id_to_string = fmt.type_var_id_to_string;
      PT.type_decl_id_to_string = fmt.type_decl_id_to_string;
      PT.const_generic_var_id_to_string = fmt.const_generic_var_id_to_string;
      PT.global_decl_id_to_string = fmt.global_decl_id_to_string;
      PT.trait_decl_id_to_string = fmt.trait_decl_id_to_string;
      PT.trait_impl_id_to_string = fmt.trait_impl_id_to_string;
      PT.trait_clause_id_to_string = fmt.trait_clause_id_to_string;
    }

  let var_id_to_string (id : E.VarId.id) : string =
    "var@" ^ E.VarId.to_string id

  let symbolic_value_id_to_string (id : V.SymbolicValueId.id) : string =
    "s@" ^ V.SymbolicValueId.to_string id

  let symbolic_value_to_string (fmt : PT.type_formatter) (sv : V.symbolic_value)
      : string =
    symbolic_value_id_to_string sv.sv_id ^ " : " ^ PT.ty_to_string fmt sv.sv_ty

  let symbolic_value_proj_to_string (fmt : value_formatter)
      (sv : V.symbolic_value) (rty : T.ty) : string =
    let ty_fmt = value_to_type_formatter fmt in
    symbolic_value_id_to_string sv.sv_id
    ^ " : "
    ^ PT.ty_to_string ty_fmt sv.sv_ty
    ^ " <: " ^ PT.ty_to_string ty_fmt rty

  (* TODO: it may be a good idea to try to factorize this function with
   * typed_avalue_to_string. At some point we had done it, because [typed_value]
   * and [typed_avalue] were instances of the same general type [g_typed_value],
   * but then we removed this general type because it proved to be a bad idea. *)
  let rec typed_value_to_string (fmt : value_formatter) (v : V.typed_value) :
      string =
    let ty_fmt : PT.type_formatter = value_to_type_formatter fmt in
    match v.value with
    | VLiteral cv -> PPV.literal_to_string cv
    | VAdt av -> (
        let field_values =
          List.map (typed_value_to_string fmt) av.field_values
        in
        match v.ty with
        | T.TAdt (T.Tuple, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | T.TAdt (T.AdtId def_id, _) ->
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
        | T.TAdt (T.TAssumed aty, _) -> (
            (* Assumed type *)
            match (aty, field_values) with
            | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
            | TArray, _ ->
                (* Happens when we aggregate values *)
                "@Array[" ^ String.concat ", " field_values ^ "]"
            | _ ->
                raise (Failure ("Inconsistent value: " ^ V.show_typed_value v)))
        | _ -> raise (Failure "Inconsistent typed value"))
    | Bottom -> "⊥ : " ^ PT.ty_to_string ty_fmt v.ty
    | Borrow bc -> borrow_content_to_string fmt bc
    | Loan lc -> loan_content_to_string fmt lc
    | Symbolic s -> symbolic_value_to_string ty_fmt s

  and borrow_content_to_string (fmt : value_formatter) (bc : V.borrow_content) :
      string =
    match bc with
    | SharedBorrow bid -> "⌊shared@" ^ V.BorrowId.to_string bid ^ "⌋"
    | MutBorrow (bid, tv) ->
        "&mut@" ^ V.BorrowId.to_string bid ^ " ("
        ^ typed_value_to_string fmt tv
        ^ ")"
    | ReservedMutBorrow bid -> "⌊reserved_mut@" ^ V.BorrowId.to_string bid ^ "⌋"

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
        ^ symbolic_value_to_string (value_to_type_formatter fmt) sv
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
    let ty_fmt : PT.type_formatter = value_to_type_formatter fmt in
    match v.value with
    | AAdt av -> (
        let field_values =
          List.map (typed_avalue_to_string fmt) av.field_values
        in
        match v.ty with
        | T.TAdt (T.Tuple, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | T.TAdt (T.AdtId def_id, _) ->
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
        | T.TAdt (T.TAssumed aty, _) -> (
            (* Assumed type *)
            match (aty, field_values) with
            | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
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
    | AMutBorrow (bid, av) ->
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
    | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
        "@ended_ignored_mut_borrow{ "
        ^ typed_avalue_to_string fmt child
        ^ "; "
        ^ typed_avalue_to_string fmt given_back
        ^ ")"
    | AEndedSharedBorrow -> "@ended_shared_borrow"
    | AProjSharedBorrow sb ->
        "@ignored_shared_borrow("
        ^ abstract_shared_borrows_to_string fmt sb
        ^ ")"

  let loop_abs_kind_to_string (kind : V.loop_abs_kind) : string =
    match kind with
    | LoopSynthInput -> "LoopSynthInput"
    | LoopCall -> "LoopCall"

  let abs_kind_to_string (kind : V.abs_kind) : string =
    match kind with
    | V.FunCall (fid, rg_id) ->
        "FunCall(fid:" ^ V.FunCallId.to_string fid ^ ", rg_id:"
        ^ T.RegionGroupId.to_string rg_id
        ^ ")"
    | SynthInput rg_id ->
        "SynthInput(rg_id:" ^ T.RegionGroupId.to_string rg_id ^ ")"
    | SynthRet rg_id ->
        "SynthRet(rg_id:" ^ T.RegionGroupId.to_string rg_id ^ ")"
    | Loop (lp_id, rg_id, abs_kind) ->
        "Loop(loop_id:" ^ V.LoopId.to_string lp_id ^ ", rg_id:"
        ^ option_to_string T.RegionGroupId.to_string rg_id
        ^ ", loop abs kind: "
        ^ loop_abs_kind_to_string abs_kind
        ^ ")"
    | Identity -> "Identity"

  let abs_to_string (fmt : value_formatter) (verbose : bool) (indent : string)
      (indent_incr : string) (abs : V.abs) : string =
    let indent2 = indent ^ indent_incr in
    let avs =
      List.map (fun av -> indent2 ^ typed_avalue_to_string fmt av) abs.avalues
    in
    let avs = String.concat ",\n" avs in
    let kind =
      if verbose then "[kind:" ^ abs_kind_to_string abs.kind ^ "]" else ""
    in
    indent ^ "abs@"
    ^ V.AbstractionId.to_string abs.abs_id
    ^ kind ^ "{parents="
    ^ V.AbstractionId.Set.to_string None abs.parents
    ^ "}" ^ "{regions="
    ^ T.RegionId.Set.to_string None abs.regions
    ^ "}" ^ " {\n" ^ avs ^ "\n" ^ indent ^ "}"

  let inst_fun_sig_to_string (fmt : value_formatter) (sg : LlbcAst.inst_fun_sig)
      : string =
    (* TODO: print the trait type constraints? *)
    let ty_fmt = value_to_type_formatter fmt in
    let ty_to_string = PT.ty_to_string ty_fmt in

    let inputs =
      "(" ^ String.concat ", " (List.map ty_to_string sg.inputs) ^ ")"
    in
    let output = ty_to_string sg.output in
    inputs ^ " -> " ^ output
end

module PV = Values (* local module *)

(** Pretty-printing for contexts *)
module Contexts = struct
  let var_binder_to_string (bv : C.var_binder) : string =
    match bv.name with
    | None -> PV.var_id_to_string bv.index
    | Some name -> name ^ "^" ^ E.VarId.to_string bv.index

  let dummy_var_id_to_string (bid : C.DummyVarId.id) : string =
    "_@" ^ C.DummyVarId.to_string bid

  let binder_to_string (bv : C.binder) : string =
    match bv with
    | BVar b -> var_binder_to_string b
    | BDummy bid -> dummy_var_id_to_string bid

  let env_elem_to_string (fmt : PV.value_formatter) (verbose : bool)
      (with_var_types : bool) (indent : string) (indent_incr : string)
      (ev : C.env_elem) : string =
    match ev with
    | EBinding (var, tv) ->
        let bv = binder_to_string var in
        let ty =
          if with_var_types then
            " : " ^ PT.ty_to_string (PV.value_to_type_formatter fmt) tv.V.ty
          else ""
        in
        indent ^ bv ^ ty ^ " -> " ^ PV.typed_value_to_string fmt tv ^ " ;"
    | EAbs abs -> PV.abs_to_string fmt verbose indent indent_incr abs
    | EFrame -> raise (Failure "Can't print a Frame element")

  let opt_env_elem_to_string (fmt : PV.value_formatter) (verbose : bool)
      (with_var_types : bool) (indent : string) (indent_incr : string)
      (ev : C.env_elem option) : string =
    match ev with
    | None -> indent ^ "..."
    | Some ev ->
        env_elem_to_string fmt verbose with_var_types indent indent_incr ev

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
      | EBinding (BVar _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if VU.is_bottom tv.value then None else Some ev
      | EBinding (BDummy _, tv) ->
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
      [with_var_types]: if true, print the type of the variables
   *)
  let env_to_string (filter : bool) (fmt : PV.value_formatter) (verbose : bool)
      (with_var_types : bool) (env : C.env) : string =
    let env =
      if filter then filter_env env else List.map (fun ev -> Some ev) env
    in
    "{\n"
    ^ String.concat "\n"
        (List.map
           (fun ev ->
             opt_env_elem_to_string fmt verbose with_var_types "  " "  " ev)
           env)
    ^ "\n}"

  type ctx_formatter = PV.value_formatter

  let ast_to_ctx_formatter (fmt : PA.ast_formatter) : ctx_formatter =
    {
      PV.region_id_to_string = fmt.region_id_to_string;
      PV.type_var_id_to_string = fmt.type_var_id_to_string;
      PV.type_decl_id_to_string = fmt.type_decl_id_to_string;
      PV.const_generic_var_id_to_string = fmt.const_generic_var_id_to_string;
      PV.global_decl_id_to_string = fmt.global_decl_id_to_string;
      PV.adt_variant_to_string = fmt.adt_variant_to_string;
      PV.var_id_to_string = fmt.var_id_to_string;
      PV.adt_field_names = fmt.adt_field_names;
      PV.trait_decl_id_to_string = fmt.trait_decl_id_to_string;
      PV.trait_impl_id_to_string = fmt.trait_impl_id_to_string;
      PV.trait_clause_id_to_string = fmt.trait_clause_id_to_string;
    }

  let ast_to_value_formatter (fmt : PA.ast_formatter) : PV.value_formatter =
    ast_to_ctx_formatter fmt

  let ctx_to_type_formatter (fmt : ctx_formatter) : PT.type_formatter =
    PV.value_to_type_formatter fmt

  let eval_ctx_to_ctx_formatter (ctx : C.eval_ctx) : ctx_formatter =
    let region_id_to_string r = PT.region_id_to_string r in

    let type_var_id_to_string vid =
      (* The context may be invalid *)
      match C.lookup_type_var_opt ctx vid with
      | None -> T.TypeVarId.to_string vid
      | Some v -> v.name
    in
    let const_generic_var_id_to_string vid =
      match C.lookup_const_generic_var_opt ctx vid with
      | None -> T.ConstGenericVarId.to_string vid
      | Some v -> v.name
    in
    let type_decl_id_to_string def_id =
      let def = C.ctx_lookup_type_decl ctx def_id in
      name_to_string def.name
    in
    let global_decl_id_to_string def_id =
      let def = C.ctx_lookup_global_decl ctx def_id in
      name_to_string def.name
    in
    let trait_decl_id_to_string def_id =
      let def = C.ctx_lookup_trait_decl ctx def_id in
      name_to_string def.name
    in
    let trait_impl_id_to_string def_id =
      let def = C.ctx_lookup_trait_impl ctx def_id in
      name_to_string def.name
    in
    let trait_clause_id_to_string id = PT.trait_clause_id_to_pretty_string id in
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
      region_id_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      const_generic_var_id_to_string;
      global_decl_id_to_string;
      adt_variant_to_string;
      var_id_to_string;
      adt_field_names;
      trait_decl_id_to_string;
      trait_impl_id_to_string;
      trait_clause_id_to_string;
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
    let trait_decl_id_to_string def_id =
      let def = C.ctx_lookup_trait_decl ctx def_id in
      name_to_string def.name
    in
    let trait_impl_id_to_string def_id =
      let def = C.ctx_lookup_trait_impl ctx def_id in
      name_to_string def.name
    in
    let trait_clause_id_to_string id = PT.trait_clause_id_to_pretty_string id in
    {
      region_id_to_string = ctx_fmt.PV.region_id_to_string;
      type_var_id_to_string = ctx_fmt.PV.type_var_id_to_string;
      type_decl_id_to_string = ctx_fmt.PV.type_decl_id_to_string;
      const_generic_var_id_to_string = ctx_fmt.PV.const_generic_var_id_to_string;
      adt_variant_to_string = ctx_fmt.PV.adt_variant_to_string;
      var_id_to_string = ctx_fmt.PV.var_id_to_string;
      adt_field_names = ctx_fmt.PV.adt_field_names;
      adt_field_to_string;
      fun_decl_id_to_string;
      global_decl_id_to_string;
      trait_decl_id_to_string;
      trait_impl_id_to_string;
      trait_clause_id_to_string;
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
      | EFrame :: env' -> split_aux (curr_frame :: frames) [] env'
      | ev :: env' -> split_aux frames (ev :: curr_frame) env'
    in
    let frames = split_aux [] [] env in
    frames

  let fmt_eval_ctx_to_string_gen (fmt : ctx_formatter) (verbose : bool)
      (filter : bool) (with_var_types : bool) (ctx : C.eval_ctx) : string =
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
              | C.EBinding (BDummy _, _) -> num_dummies := !num_abs + 1
              | C.EBinding (BVar _, _) -> num_bindings := !num_bindings + 1
              | C.EAbs _ -> num_abs := !num_abs + 1
              | _ -> raise (Failure "Unreachable"))
            f;
          "\n# Frame " ^ string_of_int i ^ ":" ^ "\n- locals: "
          ^ string_of_int !num_bindings
          ^ "\n- dummy bindings: " ^ string_of_int !num_dummies
          ^ "\n- abstractions: " ^ string_of_int !num_abs ^ "\n"
          ^ env_to_string filter fmt verbose with_var_types f
          ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames

  let eval_ctx_to_string_gen (verbose : bool) (filter : bool)
      (with_var_types : bool) (ctx : C.eval_ctx) : string =
    let fmt = eval_ctx_to_ctx_formatter ctx in
    fmt_eval_ctx_to_string_gen fmt verbose filter with_var_types ctx

  let eval_ctx_to_string (ctx : C.eval_ctx) : string =
    eval_ctx_to_string_gen false true true ctx

  let eval_ctx_to_string_no_filter (ctx : C.eval_ctx) : string =
    eval_ctx_to_string_gen false false true ctx
end

module PC = Contexts (* local module *)

(** Pretty-printing for LLBC ASTs (functions based on an evaluation context) *)
module EvalCtxLlbcAst = struct
  let ty_to_string (ctx : C.eval_ctx) (t : T.ty) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_type_formatter fmt in
    PT.ty_to_string fmt t

  let generic_params_to_strings (ctx : C.eval_ctx) (x : T.generic_params) :
      string list * string list =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_type_formatter fmt in
    PT.generic_params_to_strings fmt x

  let generic_args_to_string (ctx : C.eval_ctx) (x : T.generic_args) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_type_formatter fmt in
    PT.generic_args_to_string fmt x

  let trait_ref_to_string (ctx : C.eval_ctx) (x : T.trait_ref) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_type_formatter fmt in
    PT.trait_ref_to_string fmt x

  let trait_instance_id_to_string (ctx : C.eval_ctx) (x : T.trait_instance_id) :
      string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    let fmt = PC.ctx_to_type_formatter fmt in
    PT.trait_instance_id_to_string fmt x

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
    let fmt = PC.ctx_to_type_formatter fmt in
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

  let call_to_string (ctx : C.eval_ctx) (call : A.call) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.call_to_string fmt "" call

  let fun_decl_to_string (ctx : C.eval_ctx) (f : A.fun_decl) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.fun_decl_to_string fmt "" "  " f

  let fun_sig_to_string (ctx : C.eval_ctx) (x : A.fun_sig) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.fun_sig_to_string fmt "" "  " x

  let inst_fun_sig_to_string (ctx : C.eval_ctx) (x : LlbcAst.inst_fun_sig) :
      string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    let fmt = PC.ast_to_value_formatter fmt in
    PV.inst_fun_sig_to_string fmt x

  let fun_id_or_trait_method_ref_to_string (ctx : C.eval_ctx)
      (x : E.fun_id_or_trait_method_ref) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PE.fun_id_or_trait_method_ref_to_string fmt x "..."

  let statement_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (e : A.statement) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.statement_to_string fmt indent indent_incr e

  let trait_impl_to_string (ctx : C.eval_ctx) (timpl : A.trait_impl) : string =
    let fmt = PC.eval_ctx_to_ast_formatter ctx in
    PA.trait_impl_to_string fmt "  " "  " timpl

  let env_elem_to_string (ctx : C.eval_ctx) (indent : string)
      (indent_incr : string) (ev : C.env_elem) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PC.env_elem_to_string fmt false true indent indent_incr ev

  let abs_to_string (ctx : C.eval_ctx) (indent : string) (indent_incr : string)
      (abs : V.abs) : string =
    let fmt = PC.eval_ctx_to_ctx_formatter ctx in
    PV.abs_to_string fmt false indent indent_incr abs
end
