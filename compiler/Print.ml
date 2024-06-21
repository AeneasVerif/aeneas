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

  let symbolic_value_proj_to_string (env : fmt_env) (sv : symbolic_value)
      (rty : ty) : string =
    symbolic_value_id_to_pretty_string sv.sv_id
    ^ " : " ^ ty_to_string env sv.sv_ty ^ " <: " ^ ty_to_string env rty

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
        | TAdt (TTuple, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | TAdt (TAdtId def_id, _) ->
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
        | TAdt (TAssumed aty, _) -> (
            (* Assumed type *)
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
    | AsbProjReborrows (sv, rty) ->
        "{" ^ symbolic_value_proj_to_string env sv rty ^ "}"

  let abstract_shared_borrows_to_string (env : fmt_env)
      (abs : abstract_shared_borrows) : string =
    "{"
    ^ String.concat "," (List.map (abstract_shared_borrow_to_string env) abs)
    ^ "}"

  let rec aproj_to_string (env : fmt_env) (pv : aproj) : string =
    match pv with
    | AProjLoans (sv, given_back) ->
        let given_back =
          if given_back = [] then ""
          else
            let given_back = List.map snd given_back in
            let given_back = List.map (aproj_to_string env) given_back in
            " (" ^ String.concat "," given_back ^ ") "
        in
        "⌊" ^ symbolic_value_to_string env sv ^ given_back ^ "⌋"
    | AProjBorrows (sv, rty) ->
        "(" ^ symbolic_value_proj_to_string env sv rty ^ ")"
    | AEndedProjLoans (_, given_back) ->
        if given_back = [] then "_"
        else
          let given_back = List.map snd given_back in
          let given_back = List.map (aproj_to_string env) given_back in
          "ended_aproj_loans (" ^ String.concat "," given_back ^ ")"
    | AEndedProjBorrows _mv -> "_"
    | AIgnoredProjBorrows -> "_"

  (** Wrap a value inside its marker, if there is one *)
  let add_proj_marker (pm : proj_marker) (s : string) : string =
    match pm with
    | PNone -> s
    | PLeft -> "|" ^ s ^ "|"
    | PRight -> "︙" ^ s ^ "︙"

  let rec typed_avalue_to_string ?(span : Meta.span option = None)
      (env : fmt_env) (v : typed_avalue) : string =
    match v.value with
    | AAdt av -> (
        let field_values =
          List.map (typed_avalue_to_string ~span env) av.field_values
        in
        match v.ty with
        | TAdt (TTuple, _) ->
            (* Tuple *)
            "(" ^ String.concat ", " field_values ^ ")"
        | TAdt (TAdtId def_id, _) ->
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
        | TAdt (TAssumed aty, _) -> (
            (* Assumed type *)
            match (aty, field_values) with
            | TBox, [ bv ] -> "@Box(" ^ bv ^ ")"
            | _ -> craise_opt_span __FILE__ __LINE__ span "Inconsistent value")
        | _ -> craise_opt_span __FILE__ __LINE__ span "Inconsistent typed value"
        )
    | ABottom -> "⊥ : " ^ ty_to_string env v.ty
    | ABorrow bc -> aborrow_content_to_string ~span env bc
    | ALoan lc -> aloan_content_to_string ~span env lc
    | ASymbolic s -> aproj_to_string env s
    | AIgnored -> "_"

  and aloan_content_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (lc : aloan_content) : string =
    match lc with
    | AMutLoan (pm, bid, av) ->
        "@mut_loan(" ^ BorrowId.to_string bid ^ ", "
        ^ typed_avalue_to_string ~span env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedLoan (pm, loans, v, av) ->
        let loans = BorrowId.Set.to_string None loans in
        "@shared_loan(" ^ loans ^ ", "
        ^ typed_value_to_string ~span env v
        ^ ", "
        ^ typed_avalue_to_string ~span env av
        ^ ")"
        |> add_proj_marker pm
    | AEndedMutLoan ml ->
        "@ended_mut_loan{"
        ^ typed_avalue_to_string ~span env ml.child
        ^ "; "
        ^ typed_avalue_to_string ~span env ml.given_back
        ^ " }"
    | AEndedSharedLoan (v, av) ->
        "@ended_shared_loan("
        ^ typed_value_to_string ~span env v
        ^ ", "
        ^ typed_avalue_to_string ~span env av
        ^ ")"
    | AIgnoredMutLoan (opt_bid, av) ->
        "@ignored_mut_loan("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ typed_avalue_to_string ~span env av
        ^ ")"
    | AEndedIgnoredMutLoan ml ->
        "@ended_ignored_mut_loan{ "
        ^ typed_avalue_to_string ~span env ml.child
        ^ "; "
        ^ typed_avalue_to_string ~span env ml.given_back
        ^ "}"
    | AIgnoredSharedLoan sl ->
        "@ignored_shared_loan(" ^ typed_avalue_to_string ~span env sl ^ ")"

  and aborrow_content_to_string ?(span : Meta.span option = None)
      (env : fmt_env) (bc : aborrow_content) : string =
    match bc with
    | AMutBorrow (pm, bid, av) ->
        "mb@" ^ BorrowId.to_string bid ^ " ("
        ^ typed_avalue_to_string ~span env av
        ^ ")"
        |> add_proj_marker pm
    | ASharedBorrow (pm, bid) ->
        "sb@" ^ BorrowId.to_string bid |> add_proj_marker pm
    | AIgnoredMutBorrow (opt_bid, av) ->
        "@ignored_mut_borrow("
        ^ option_to_string BorrowId.to_string opt_bid
        ^ ", "
        ^ typed_avalue_to_string ~span env av
        ^ ")"
    | AEndedMutBorrow (_mv, child) ->
        "@ended_mut_borrow(" ^ typed_avalue_to_string ~span env child ^ ")"
    | AEndedIgnoredMutBorrow { child; given_back; given_back_span = _ } ->
        "@ended_ignored_mut_borrow{ "
        ^ typed_avalue_to_string ~span env child
        ^ "; "
        ^ typed_avalue_to_string ~span env given_back
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

  let abs_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (indent : string) (indent_incr : string) (abs : abs) :
      string =
    let indent2 = indent ^ indent_incr in
    let avs =
      List.map
        (fun av -> indent2 ^ typed_avalue_to_string ~span env av)
        abs.avalues
    in
    let avs = String.concat ",\n" avs in
    let kind =
      if verbose then "[kind:" ^ abs_kind_to_string abs.kind ^ "]" else ""
    in
    let can_end = if abs.can_end then "{endable}" else "{frozen}" in
    indent ^ "abs@"
    ^ AbstractionId.to_string abs.abs_id
    ^ kind ^ "{parents="
    ^ AbstractionId.Set.to_string None abs.parents
    ^ "}" ^ "{regions="
    ^ RegionId.Set.to_string None abs.regions
    ^ "}" ^ can_end ^ " {\n" ^ avs ^ "\n" ^ indent ^ "}"

  let inst_fun_sig_to_string (env : fmt_env) (sg : LlbcAst.inst_fun_sig) :
      string =
    (* TODO: print the trait type constraints? *)
    let ty_to_string = ty_to_string env in

    let inputs =
      "(" ^ String.concat ", " (List.map ty_to_string sg.inputs) ^ ")"
    in
    let output = ty_to_string sg.output in
    inputs ^ " -> " ^ output
end

(** Pretty-printing for contexts *)
module Contexts = struct
  open Values

  let var_binder_to_string (env : fmt_env) (bv : var_binder) : string =
    match bv.name with
    | None -> var_id_to_string env bv.index
    | Some name -> name ^ "^" ^ VarId.to_string bv.index

  let dummy_var_id_to_string (bid : DummyVarId.id) : string =
    "_@" ^ DummyVarId.to_string bid

  let binder_to_string (env : fmt_env) (bv : binder) : string =
    match bv with
    | BVar b -> var_binder_to_string env b
    | BDummy bid -> dummy_var_id_to_string bid

  let env_elem_to_string ?(span : Meta.span option = None) (env : fmt_env)
      (verbose : bool) (with_var_types : bool) (indent : string)
      (indent_incr : string) (ev : env_elem) : string =
    match ev with
    | EBinding (var, tv) ->
        let bv = binder_to_string env var in
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
  let filter_env (env : env) : env_elem option list =
    (* We filter:
     * - non-dummy bindings which point to ⊥
     * - dummy bindings which don't contain loans nor borrows
     * Note that the first case can sometimes be confusing: we may try to improve
     * it...
     *)
    let filter_elem (ev : env_elem) : env_elem option =
      match ev with
      | EBinding (BVar _, tv) ->
          (* Not a dummy binding: check if the value is ⊥ *)
          if is_bottom tv.value then None else Some ev
      | EBinding (BDummy _, tv) ->
          (* Dummy binding: check if the value contains borrows or loans *)
          if borrows_in_value tv || loans_in_value tv then Some ev else None
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
      allows to filter them when printing, replacing groups of such bindings with
      "..." to gain space and clarity.
      [with_var_types]: if true, print the type of the variables
   *)
  let env_to_string ?(span : Meta.span option = None) (filter : bool)
      (fmt_env : fmt_env) (verbose : bool) (with_var_types : bool) (env : env) :
      string =
    let env =
      if filter then filter_env env else List.map (fun ev -> Some ev) env
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
    let type_decls = ctx.type_ctx.type_decls in
    let fun_decls = ctx.fun_ctx.fun_decls in
    let global_decls = ctx.global_ctx.global_decls in
    let trait_decls = ctx.trait_decls_ctx.trait_decls in
    let trait_impls = ctx.trait_impls_ctx.trait_impls in
    {
      type_decls;
      fun_decls;
      global_decls;
      trait_decls;
      trait_impls;
      regions = [];
      generics = TypesUtils.empty_generic_params;
      locals = [];
    }

  let eval_ctx_to_fmt_env (ctx : eval_ctx) : fmt_env =
    let type_decls = ctx.type_ctx.type_decls in
    let fun_decls = ctx.fun_ctx.fun_decls in
    let global_decls = ctx.global_ctx.global_decls in
    let trait_decls = ctx.trait_decls_ctx.trait_decls in
    let trait_impls = ctx.trait_impls_ctx.trait_impls in
    (* Below: it is always safe to omit fields - if an id can't be found at
       printing time, we print the id (in raw form) instead of the name it
       designates. *)
    (* For the locals: we retrieve the information from the environment.
       Note that the locals don't need to be ordered based on their indices.
    *)
    let rec env_to_locals (env : env) : (VarId.id * string option) list =
      match env with
      | [] | EFrame :: _ -> []
      | EAbs _ :: env -> env_to_locals env
      | EBinding (BVar b, _) :: env -> (b.index, b.name) :: env_to_locals env
      | EBinding (BDummy _, _) :: env -> env_to_locals env
    in
    let locals = env_to_locals ctx.env in
    {
      type_decls;
      fun_decls;
      global_decls;
      trait_decls;
      trait_impls;
      (* The regions have been transformed to region groups *)
      regions = [];
      generics =
        {
          TypesUtils.empty_generic_params with
          types = ctx.type_vars;
          const_generics = ctx.const_generic_vars;
          (* We don't need the trait clauses so we initialize them to empty *)
          trait_clauses = [];
        };
      locals;
    }

  (** Split an [env] at every occurrence of [Frame], eliminating those elements.
          Also reorders the frames and the values in the frames according to the
          following order:
          * frames: from the current frame to the first pushed (oldest frame)
          * values: from the first pushed (oldest) to the last pushed
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

  let eval_ctx_to_string_gen ?(span : Meta.span option = None) (verbose : bool)
      (filter : bool) (with_var_types : bool) (ctx : eval_ctx) : string =
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
          ^ env_to_string ~span filter fmt_env verbose with_var_types f
          ^ "\n")
        frames
    in
    "# Ended regions: " ^ ended_regions ^ "\n" ^ "# " ^ string_of_int num_frames
    ^ " frame(s)\n" ^ String.concat "" frames

  let eval_ctx_to_string ?(span : Meta.span option = None) (ctx : eval_ctx) :
      string =
    eval_ctx_to_string_gen ~span false true true ctx

  let eval_ctx_to_string_no_filter ?(span : Meta.span option = None)
      (ctx : eval_ctx) : string =
    eval_ctx_to_string_gen ~span false false true ctx
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

  let typed_avalue_to_string ?(span : Meta.span option = None) (ctx : eval_ctx)
      (v : typed_avalue) : string =
    let env = eval_ctx_to_fmt_env ctx in
    typed_avalue_to_string ~span env v

  let place_to_string (ctx : eval_ctx) (op : place) : string =
    let env = eval_ctx_to_fmt_env ctx in
    place_to_string env op

  let operand_to_string (ctx : eval_ctx) (op : operand) : string =
    let env = eval_ctx_to_fmt_env ctx in
    operand_to_string env op

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
      (indent : string) (indent_incr : string) (abs : abs) : string =
    let env = eval_ctx_to_fmt_env ctx in
    abs_to_string ~span env false indent indent_incr abs
end
