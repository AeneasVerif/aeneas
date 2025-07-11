include Charon.PrintUtils
include Charon.PrintTypes
include Charon.PrintLlbcAst
open Charon.PrintTypes
open Charon.PrintExpressions
open Charon.PrintLlbcAst.Ast
open Types
open Values
open ValuesUtils
open Expressions
open LlbcAst
open Contexts
open Errors
module Types = Charon.PrintTypes
module Expressions = Charon.PrintExpressions

let list_to_string (to_string : 'a -> string) (ls : 'a list) : string =
  "[" ^ String.concat "; " (List.map to_string ls) ^ "]"

let pair_to_string (to_string0 : 'a -> string) (to_string1 : 'b -> string)
    ((x, y) : 'a * 'b) : string =
  "(" ^ to_string0 x ^ ", " ^ to_string1 y ^ ")"

let bool_to_string (b : bool) : string = if b then "true" else "false"

(** Pretty-printing for values *)
module Values = struct
  include Charon.PrintValues

  let symbolic_value_id_to_pretty_string (id : SymbolicValueId.id) : string =
    "s@" ^ SymbolicValueId.to_string id

  let symbolic_value_to_string (env : fmt_env) (sv : symbolic_value) : string =
    symbolic_value_id_to_pretty_string sv.sv_id
    ^ " : " ^ ty_to_string env sv.sv_ty

  let symbolic_value_proj_to_string (env : fmt_env) (sv_id : symbolic_value_id)
      (rty : ty) : string =
    symbolic_value_id_to_pretty_string sv_id ^ " <: " ^ ty_to_string env rty

  (* TODO: it may be a good idea to try to factorize this function with
   * typed_avalue_to_string. At some point we had done it, because [typed_value]
   * and [typed_avalue] were instances of the same general type [g_typed_value],
   * but then we removed this general type because it proved to be a bad idea. *)
  let rec typed_value_to_string ?(span : Meta.span option = None)
      (env : fmt_env) (v : typed_value) : string =
    match v.value with
    | VLiteral cv -> literal_to_string cv
    | VAdt av -> (
        let field_values =
          List.map (typed_value_to_string ~span env) av.field_values
        in
        match v.ty with
        | TAdt { id = TTuple; _ } ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | TAdt { id = TAdtId def_id; _ } ->
            (* "Regular" ADT *)
            let adt_ident =
              match av.variant_id with
              | Some vid -> adt_variant_to_string env def_id vid
              | None -> type_decl_id_to_string env def_id
            in
            if List.length field_values > 0 then
              match adt_field_names env def_id av.variant_id with
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
        | TAdt { id = TBuiltin aty; _ } -> (
            (* Builtin type *)
            match (aty, field_values) with
            | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
            | TArray, _ ->
                (* Happens when we aggregate values *)
                "@Array[" ^ String.concat ", " field_values ^ "]"
            | _ ->
                craise_opt_span __FILE__ __LINE__ span
                  ("Inconsistent value: " ^ show_typed_value v))
        | _ -> craise_opt_span __FILE__ __LINE__ span "Inconsistent typed value"
        )
    | VBottom -> "⊥ : " ^ ty_to_string env v.ty
    | VBorrow bc -> borrow_content_to_string ~span env bc
    | VLoan lc -> loan_content_to_string ~span env lc
    | VSymbolic s -> symbolic_value_to_string env s

  and borrow_content_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (bc : borrow_content) : string =
    match bc with
    | VSharedBorrow bid -> "shared_borrow@" ^ BorrowId.to_string bid
    | VMutBorrow (bid, tv) ->
        "mut_borrow@" ^ BorrowId.to_string bid ^ " ("
        ^ typed_value_to_string ~span env tv
        ^ ")"
    | VReservedMutBorrow bid -> "reserved_borrow@" ^ BorrowId.to_string bid

  and loan_content_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (lc : loan_content) : string =
    match lc with
    | VSharedLoan (loans, v) ->
        let loans = BorrowId.Set.to_string None loans in
        "@shared_loan(" ^ loans ^ ", " ^ typed_value_to_string ~span env v ^ ")"
    | VMutLoan bid -> "ml@" ^ BorrowId.to_string bid

  let abstract_shared_borrow_to_string (env : fmt_env)
      (abs : abstract_shared_borrow) : string =
    match abs with
    | AsbBorrow bid -> BorrowId.to_string bid
    | AsbProjReborrows (sv_id, rty) ->
        "{" ^ symbolic_value_proj_to_string env sv_id rty ^ "}"

  let abstract_shared_borrows_to_string (env : fmt_env)
      (abs : abstract_shared_borrows) : string =
    "{"
    ^ String.concat "," (List.map (abstract_shared_borrow_to_string env) abs)
    ^ "}"

  let rec aproj_to_string ?(with_ended : bool = false) (env : fmt_env)
      (pv : aproj) : string =
    match pv with
    | AProjLoans (sv, rty, given_back) ->
        let given_back =
          if given_back = [] then ""
          else
            let given_back = List.map snd given_back in
            let given_back =
              List.map (aproj_to_string ~with_ended env) given_back
            in
            " [" ^ String.concat "," given_back ^ "]"
        in
        "⌊" ^ symbolic_value_proj_to_string env sv rty ^ given_back ^ "⌋"
    | AProjBorrows (sv, rty, given_back) ->
        let given_back =
          if given_back = [] then ""
          else
            let given_back = List.map snd given_back in
            let given_back =
              List.map (aproj_to_string ~with_ended env) given_back
            in
            " [" ^ String.concat "," given_back ^ "]"
        in
        "(" ^ symbolic_value_proj_to_string env sv rty ^ given_back ^ ")"
    | AEndedProjLoans (msv, given_back) ->
        let msv =
          if with_ended then
            "original_loan = " ^ symbolic_value_id_to_pretty_string msv
          else "_"
        in
        let given_back = List.map snd given_back in
        let given_back =
          List.map (aproj_to_string ~with_ended env) given_back
        in
        "ended_aproj_loans (" ^ msv ^ ", ["
        ^ String.concat "," given_back
        ^ "])"
    | AEndedProjBorrows (meta, given_back) ->
        let meta =
          if with_ended then
            "original_borrow = "
            ^ symbolic_value_id_to_pretty_string meta.consumed
            ^ ", given_back = "
            ^ symbolic_value_to_string env meta.given_back
          else "_"
        in
        let given_back = List.map snd given_back in
        let given_back =
          List.map (aproj_to_string ~with_ended env) given_back
        in
        "ended_aproj_borrows (" ^ meta ^ ", ["
        ^ String.concat "," given_back
        ^ "])"
    | AEmpty -> "_"

  (** Wrap a value inside its marker, if there is one *)
  let add_proj_marker (pm : proj_marker) (s : string) : string =
    match pm with
    | PNone -> s
    | PLeft -> "|" ^ s ^ "|"
    | PRight -> "︙" ^ s ^ "︙"

  let ended_mut_borrow_meta_to_string (env : fmt_env)
      (mv : ended_mut_borrow_meta) : string =
    let { bid; given_back } = mv in
    "{ bid = " ^ BorrowId.to_string bid ^ "; given_back = "
    ^ symbolic_value_to_string env given_back
    ^ " }"

  let rec typed_avalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (v : typed_avalue) : string =
    match v.value with
    | AAdt av -> (
        let field_values =
          List.map
            (typed_avalue_to_string ~span ~with_ended env)
            av.field_values
        in
        match v.ty with
        | TAdt { id = TTuple; _ } ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | TAdt { id = TAdtId def_id; _ } ->
            (* "Regular" ADT *)
            let adt_ident =
              match av.variant_id with
              | Some vid -> adt_variant_to_string env def_id vid
              | None -> type_decl_id_to_string env def_id
            in
            if List.length field_values > 0 then
              match adt_field_names env def_id av.variant_id with
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
        | TAdt { id = TBuiltin aty; _ } -> (
            (* Builtin type *)
            match (aty, field_values) with
            | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
            | _ -> craise_opt_span __FILE__ __LINE__ span "Inconsistent value")
        | _ -> craise_opt_span __FILE__ __LINE__ span "Inconsistent typed value"
        )
    | ABottom -> "⊥ : " ^ ty_to_string env v.ty
    | ABorrow bc -> aborrow_content_to_string ~span ~with_ended env bc
    | ALoan lc -> aloan_content_to_string ~span ~with_ended env lc
    | ASymbolic (pm, proj) ->
        aproj_to_string ~with_ended env proj |> add_proj_marker pm
    | AIgnored _ -> "_"

  and aloan_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (lc : aloan_content) : string
      =
    match lc with
    | AMutLoan (pm, bid, av) ->
        "@mut_loan(" ^ BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedLoan (pm, loans, v, av) ->
        let loans = BorrowId.Set.to_string None loans in
        "@shared_loan(" ^ loans ^ ", "
        ^ typed_value_to_string ~span env v
        ^ ", "
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | AEndedMutLoan ml ->
        let consumed =
          if with_ended then
            "consumed = " ^ typed_value_to_string env ml.given_back_meta ^ ", "
          else ""
        in
        "@ended_mut_loan{" ^ consumed
        ^ typed_avalue_to_string ~span ~with_ended env ml.child
        ^ "; "
        ^ typed_avalue_to_string ~span ~with_ended env ml.given_back
        ^ " }"
    | AEndedSharedLoan (v, av) ->
        "@ended_shared_loan("
        ^ typed_value_to_string ~span env v
        ^ ", "
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
    | AIgnoredMutLoan (opt_bid, av) ->
        "@ignored_mut_loan("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
    | AEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_loan{ "
        ^ typed_avalue_to_string ~span ~with_ended env ml.child
        ^ "; "
        ^ typed_avalue_to_string ~span ~with_ended env ml.given_back
        ^ "}"
    | AIgnoredSharedLoan sl ->
        "@ignored_shared_loan("
        ^ typed_avalue_to_string ~span ~with_ended env sl
        ^ ")"

  and aborrow_content_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (env : fmt_env) (bc : aborrow_content) :
      string =
    match bc with
    | AMutBorrow (pm, bid, av) ->
        "mb@" ^ BorrowId.to_string bid ^ " ("
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedBorrow (pm, bid) ->
        "sb@" ^ BorrowId.to_string bid |> add_proj_marker pm
    | AIgnoredMutBorrow (opt_bid, av) ->
        "@ignored_mut_borrow("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ typed_avalue_to_string ~span ~with_ended env av
        ^ ")"
    | AEndedMutBorrow (mv, child) ->
        "@ended_mut_borrow("
        ^
        if with_ended then
          "given_back= " ^ ended_mut_borrow_meta_to_string env mv
        else "" ^ typed_avalue_to_string ~span ~with_ended env child ^ ")"
    | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
        "@ended_ignored_mut_borrow{ "
        ^ typed_avalue_to_string ~span ~with_ended env child
        ^ "; "
        ^ typed_avalue_to_string ~span ~with_ended env given_back
        ^ ")"
    | AEndedSharedBorrow -> "@ended_shared_borrow"
    | AProjSharedBorrow sb ->
        "@ignored_shared_borrow("
        ^ abstract_shared_borrows_to_string env sb
        ^ ")"

  let loop_abs_kind_to_string (kind : loop_abs_kind) : string =
    match kind with
    | LoopSynthInput -> "LoopSynthInput"
    | LoopCall -> "LoopCall"

  let abs_kind_to_string (kind : abs_kind) : string =
    match kind with
    | FunCall (fid, rg_id) ->
        "FunCall(fid:" ^ FunCallId.to_string fid ^ ", rg_id:"
        ^ RegionGroupId.to_string rg_id
        ^ ")"
    | SynthInput rg_id ->
        "SynthInput(rg_id:" ^ RegionGroupId.to_string rg_id ^ ")"
    | SynthRet rg_id -> "SynthRet(rg_id:" ^ RegionGroupId.to_string rg_id ^ ")"
    | Loop (lp_id, rg_id, abs_kind) ->
        "Loop(loop_id:" ^ LoopId.to_string lp_id ^ ", rg_id:"
        ^ option_to_string RegionGroupId.to_string rg_id
        ^ ", loop abs kind: "
        ^ loop_abs_kind_to_string abs_kind
        ^ ")"
    | Identity -> "Identity"
    | CopySymbolicValue -> "CopySymbolicValue"

  let abs_to_string ?(span : Meta.span option = None) (env : fmt_env)
      ?(with_ended : bool = false) (verbose : bool) (indent : string)
      (indent_incr : string) (abs : abs) : string =
    let indent2 = indent ^ indent_incr in
    let avs =
      List.map
        (fun av -> indent2 ^ typed_avalue_to_string ~span ~with_ended env av)
        abs.avalues
    in
    let avs = String.concat ",\n" avs in
    let kind =
      if verbose then "kind:" ^ abs_kind_to_string abs.kind ^ "," else ""
    in
    let can_end = if abs.can_end then "endable" else "frozen" in
    indent ^ "abs@"
    ^ AbstractionId.to_string abs.abs_id
    ^ "{" ^ kind ^ "parents="
    ^ AbstractionId.Set.to_string None abs.parents
    ^ ",regions="
    ^ RegionId.Set.to_string None abs.regions.owned
    ^ "," ^ can_end ^ "} {\n" ^ avs ^ "\n" ^ indent ^ "}"

  let abs_region_group_to_string (gr : abs_region_group) : string =
    g_region_group_to_string RegionId.to_string AbstractionId.to_string gr

  let abs_region_groups_to_string (gl : abs_region_groups) : string =
    String.concat "\n" (List.map abs_region_group_to_string gl)

  let inst_fun_sig_to_string (env : fmt_env) (sg : LlbcAst.inst_fun_sig) :
      string =
    (* TODO: print the trait type constraints? *)
    let ty_to_string = ty_to_string env in

    let inputs =
      "(" ^ String.concat ", " (List.map ty_to_string sg.inputs) ^ ")"
    in
    let output = ty_to_string sg.output in
    inputs ^ " -> " ^ output ^ "\n- regions_hierarchy:\n"
    ^ region_var_groups_to_string sg.regions_hierarchy
    ^ "\n- abs_regions_hierarchy:\n"
    ^ abs_region_groups_to_string sg.abs_regions_hierarchy

  let symbolic_expansion_to_string (env : fmt_env) (ty : ty)
      (se : symbolic_expansion) : string =
    match se with
    | SeLiteral lit -> literal_to_string lit
    | SeAdt (variant_id, svl) ->
        let field_values =
          List.map ValuesUtils.mk_typed_value_from_symbolic_value svl
        in
        let v : typed_value =
          { value = VAdt { variant_id; field_values }; ty }
        in
        typed_value_to_string env v
    | SeMutRef (bid, sv) ->
        "MB " ^ BorrowId.to_string bid ^ " " ^ symbolic_value_to_string env sv
    | SeSharedRef (bid, sv) ->
        "SB {"
        ^ BorrowId.Set.to_string None bid
        ^ "} "
        ^ symbolic_value_to_string env sv
end

(** Pretty-printing for contexts *)
module Contexts = struct
  open Values

  let real_var_binder_to_string (env : fmt_env) (bv : real_var_binder) : string
      =
    match bv.name with
    | None -> local_id_to_string env bv.index
    | Some name -> name ^ "^" ^ LocalId.to_string bv.index

  let dummy_var_id_to_string (bid : DummyVarId.id) : string =
    "_@" ^ DummyVarId.to_string bid

  let var_binder_to_string (env : fmt_env) (bv : var_binder) : string =
    match bv with
    | BVar b -> real_var_binder_to_string env b
    | BDummy bid -> dummy_var_id_to_string bid

  let env_elem_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (with_var_types : bool) (indent : string)
      (indent_incr : string) (ev : env_elem) : string =
    match ev with
    | EBinding (var, tv) ->
        let bv = var_binder_to_string env var in
        let ty =
          if with_var_types then " : " ^ ty_to_string env tv.ty else ""
        in
        indent ^ bv ^ ty ^ " -> " ^ typed_value_to_string ~span env tv ^ " ;"
    | EAbs abs -> abs_to_string ~span env verbose indent indent_incr abs
    | EFrame ->
        craise_opt_span __FILE__ __LINE__ span "Can't print a Frame element"

  let opt_env_elem_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (with_var_types : bool) (indent : string)
      (indent_incr : string) (ev : env_elem option) : string =
    match ev with
    | None -> indent ^ "..."
    | Some ev ->
        env_elem_to_string ~span env verbose with_var_types indent indent_incr
          ev

  (** Filters "dummy" bindings from an environment, to gain space and clarity/
      See [env_to_string]. *)
  let filter_env (ended_regions : RegionId.Set.t) (env : env) :
      env_elem option list =
    (* We filter:
       - non-dummy bindings which point to ⊥
       - dummy bindings which don't contain loans nor borrows
       Note that the first case can sometimes be confusing: we may try to improve
       it...
    *)
    let filter_elem (ev : env_elem) : env_elem option =
      match ev with
      | EBinding (BVar _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if is_bottom tv.value then None else Some ev
      | EBinding (BDummy _, tv) ->
          (* Dummy binding: check if the value contains borrows or loans *)
          if value_has_non_ended_borrows_or_loans ended_regions tv.value then
            Some ev
          else None
      | _ -> Some ev
    in
    let env = List.map filter_elem env in
    (* We collapse groups of filtered values - so that we can print one
     * single "..." for a whole group of filtered values *)
    let rec group_filtered (env : env_elem option list) : env_elem option list =
      match env with
      | [] -> []
      | None :: None :: env -> group_filtered (None :: env)
      | x :: env -> x :: group_filtered env
    in
    group_filtered env

  (** Environments can have a lot of dummy or uninitialized values: [filter]
      allows to filter them when printing, replacing groups of such bindings
      with "..." to gain space and clarity. [with_var_types]: if true, print the
      type of the variables *)
  let env_to_string ?(span : Meta.span option = None) (filter : bool)
      (fmt_env : fmt_env) (verbose : bool) (with_var_types : bool)
      (ended_regions : RegionId.Set.t) (env : env) : string =
    let env =
      if filter then filter_env ended_regions env
      else List.map (fun ev -> Some ev) env
    in
    "{\n"
    ^ String.concat "\n"
        (List.map
           (fun ev ->
             opt_env_elem_to_string ~span fmt_env verbose with_var_types "  "
               "  " ev)
           env)
    ^ "\n}"

  let decls_ctx_to_fmt_env (ctx : decls_ctx) : fmt_env =
    Crate.crate_to_fmt_env ctx.crate

  let eval_ctx_to_fmt_env (ctx : eval_ctx) : fmt_env =
    (* Below: it is always safe to omit fields - if an id can't be found at
       printing time, we print the id (in raw form) instead of the name it
       designates. *)
    (* For the locals: we retrieve the information from the environment.
       Note that the locals don't need to be ordered based on their indices.
    *)
    let rec env_to_locals (env : env) : (LocalId.id * string option) list =
      match env with
      | [] | EFrame :: _ -> []
      | EAbs _ :: env -> env_to_locals env
      | EBinding (BVar b, _) :: env -> (b.index, b.name) :: env_to_locals env
      | EBinding (BDummy _, _) :: env -> env_to_locals env
    in
    let locals = env_to_locals ctx.env in
    {
      crate = ctx.crate;
      generics =
        [
          {
            TypesUtils.empty_generic_params with
            types = ctx.type_vars;
            const_generics = ctx.const_generic_vars;
            (* The regions have been transformed to region groups *)
            regions = [];
            (* We don't need the trait clauses so we initialize them to empty *)
            trait_clauses = [];
          };
        ];
      locals;
    }

  (** Split an [env] at every occurrence of [Frame], eliminating those elements.
      Also reorders the frames and the values in the frames according to the
      following order: * frames: from the current frame to the first pushed
      (oldest frame) * values: from the first pushed (oldest) to the last pushed
  *)
  let split_env_according_to_frames (env : env) : env list =
    let rec split_aux (frames : env list) (curr_frame : env) (env : env) =
      match env with
      | [] ->
          if List.length curr_frame > 0 then curr_frame :: frames else frames
      | EFrame :: env' -> split_aux (curr_frame :: frames) [] env'
      | ev :: env' -> split_aux frames (ev :: curr_frame) env'
    in
    let frames = split_aux [] [] env in
    frames

  let eval_ctx_to_string ?(span : Meta.span option = None)
      ?(verbose : bool = false) ?(filter : bool = true)
      ?(with_var_types : bool = true) (ctx : eval_ctx) : string =
    let fmt_env = eval_ctx_to_fmt_env ctx in
    let ended_regions = RegionId.Set.to_string None ctx.ended_regions in
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
              | EBinding (BDummy _, _) -> num_dummies := !num_abs + 1
              | EBinding (BVar _, _) -> num_bindings := !num_bindings + 1
              | EAbs _ -> num_abs := !num_abs + 1
              | _ -> craise_opt_span __FILE__ __LINE__ span "Unreachable")
            f;
          "\n# Frame " ^ string_of_int i ^ ":" ^ "\n- locals: "
          ^ string_of_int !num_bindings
          ^ "\n- dummy bindings: " ^ string_of_int !num_dummies
          ^ "\n- abstractions: " ^ string_of_int !num_abs ^ "\n"
          ^ env_to_string ~span filter fmt_env verbose with_var_types
              ctx.ended_regions f
          ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames
end

(** Pretty-printing for LLBC ASTs (functions based on an evaluation context) *)
module EvalCtx = struct
  open Values
  open Contexts

  let name_to_string (ctx : eval_ctx) (n : name) : string =
    let env = eval_ctx_to_fmt_env ctx in
    name_to_string env n

  let ty_to_string (ctx : eval_ctx) (t : ty) : string =
    let env = eval_ctx_to_fmt_env ctx in
    ty_to_string env t

  let constant_expr_to_string (ctx : eval_ctx) (c : constant_expr) : string =
    let env = eval_ctx_to_fmt_env ctx in
    constant_expr_to_string env c

  let generic_params_to_strings (ctx : eval_ctx) (x : generic_params) :
      string list * string list =
    let env = eval_ctx_to_fmt_env ctx in
    generic_params_to_strings env x

  let generic_args_to_string (ctx : eval_ctx) (x : generic_args) : string =
    let env = eval_ctx_to_fmt_env ctx in
    generic_args_to_string env x

  let trait_ref_to_string (ctx : eval_ctx) (x : trait_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_ref_to_string env x

  let trait_decl_ref_region_binder_to_string (ctx : eval_ctx)
      (x : trait_decl_ref region_binder) : string =
    let env = eval_ctx_to_fmt_env ctx in
    region_binder_to_string trait_decl_ref_to_string env x

  let trait_decl_ref_to_string (ctx : eval_ctx) (x : trait_decl_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_decl_ref_to_string env x

  let trait_instance_id_to_string (ctx : eval_ctx) (x : trait_instance_id) :
      string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_instance_id_to_string env x

  let borrow_content_to_string ?(span : Meta.span option = None)
      (ctx : eval_ctx) (bc : borrow_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    borrow_content_to_string ~span env bc

  let loan_content_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (lc : loan_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    loan_content_to_string ~span env lc

  let aborrow_content_to_string ?(span : Meta.span option = None)
      (ctx : eval_ctx) (bc : aborrow_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aborrow_content_to_string ~span env bc

  let aloan_content_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (lc : aloan_content) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aloan_content_to_string ~span env lc

  let aproj_to_string (ctx : eval_ctx) (p : aproj) : string =
    let env = eval_ctx_to_fmt_env ctx in
    aproj_to_string env p

  let symbolic_value_to_string (ctx : eval_ctx) (sv : symbolic_value) : string =
    let env = eval_ctx_to_fmt_env ctx in
    symbolic_value_to_string env sv

  let typed_value_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (v : typed_value) : string =
    let env = eval_ctx_to_fmt_env ctx in
    typed_value_to_string ~span env v

  let typed_avalue_to_string ?(span : Meta.span option = None)
      ?(with_ended : bool = false) (ctx : eval_ctx) (v : typed_avalue) : string
      =
    let env = eval_ctx_to_fmt_env ctx in
    typed_avalue_to_string ~span ~with_ended env v

  let place_to_string (ctx : eval_ctx) (op : place) : string =
    let env = eval_ctx_to_fmt_env ctx in
    place_to_string env op

  let unop_to_string (ctx : eval_ctx) (op : unop) : string =
    let env = eval_ctx_to_fmt_env ctx in
    unop_to_string env op

  let operand_to_string (ctx : eval_ctx) (op : operand) : string =
    let env = eval_ctx_to_fmt_env ctx in
    operand_to_string env op

  let rvalue_to_string (ctx : eval_ctx) (rval : rvalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    rvalue_to_string env rval

  let call_to_string (ctx : eval_ctx) (call : call) : string =
    let env = eval_ctx_to_fmt_env ctx in
    call_to_string env "" call

  let fun_decl_to_string (ctx : eval_ctx) (f : fun_decl) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fun_decl_to_string env "" "  " f

  let fun_sig_to_string (ctx : eval_ctx) (x : fun_sig) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fun_sig_to_string env "" "  " x

  let inst_fun_sig_to_string (ctx : eval_ctx) (x : LlbcAst.inst_fun_sig) :
      string =
    let env = eval_ctx_to_fmt_env ctx in
    inst_fun_sig_to_string env x

  let fun_id_or_trait_method_ref_to_string (ctx : eval_ctx)
      (x : fun_id_or_trait_method_ref) : string =
    let env = eval_ctx_to_fmt_env ctx in
    fun_id_or_trait_method_ref_to_string env x

  let statement_to_string (ctx : eval_ctx) (indent : string)
      (indent_incr : string) (e : statement) : string =
    let env = eval_ctx_to_fmt_env ctx in
    statement_to_string env indent indent_incr e

  let trait_impl_to_string (ctx : eval_ctx) (timpl : trait_impl) : string =
    let env = eval_ctx_to_fmt_env ctx in
    trait_impl_to_string env "  " "  " timpl

  let env_elem_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (indent : string) (indent_incr : string) (ev : env_elem) : string =
    let env = eval_ctx_to_fmt_env ctx in
    env_elem_to_string ~span env false true indent indent_incr ev

  let abs_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      ?(with_ended : bool = false) (indent : string) (indent_incr : string)
      (abs : abs) : string =
    let env = eval_ctx_to_fmt_env ctx in
    abs_to_string ~span env ~with_ended false indent indent_incr abs
end
