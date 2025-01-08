open Types
open Values
open Print
open SymbolicAst

type fmt_env = Print.fmt_env

let call_id_to_string (env : fmt_env) (call_id : call_id) : string =
  match call_id with
  | Fun (fid, call_id) ->
      Expressions.fun_id_or_trait_method_ref_to_string env fid
      ^ "@"
      ^ FunCallId.to_string call_id
  | Unop unop -> Expressions.unop_to_string env unop
  | Binop binop -> Expressions.binop_to_string binop

let call_to_string (env : fmt_env) (indent : string) (call : call) : string =
  let dest = Values.symbolic_value_to_string env call.dest in
  let call_id = call_id_to_string env call.call_id in
  let generics = Types.generic_args_to_string env call.generics in
  let args =
    if call.args = [] then ""
    else
      "("
      ^ String.concat ", "
          (List.map (Values.typed_value_to_string env) call.args)
      ^ ")"
  in
  indent ^ dest ^ " = " ^ call_id ^ generics ^ args

let value_aggregate_to_string (env : fmt_env) (v : value_aggregate) : string =
  match v with
  | VaSingleValue v -> Values.typed_value_to_string env v
  | VaArray vl ->
      "["
      ^ String.concat ", " (List.map (Values.typed_value_to_string env) vl)
      ^ "]"
  | VaCgValue cg_id -> const_generic_db_var_to_string env (Free cg_id)
  | VaTraitConstValue (trait_ref, item) ->
      trait_ref_to_string env trait_ref ^ "." ^ item

let rec expression_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (e : expression) : string =
  match e with
  | Return (_ctx, ret) ->
      let ret =
        match ret with
        | None -> ""
        | Some ret -> " " ^ Values.typed_value_to_string env ret
      in
      indent ^ "return" ^ ret
  | Panic -> indent ^ "panic"
  | FunCall (call, next) ->
      let call = call_to_string env indent call in
      let next = expression_to_string env indent indent_incr next in
      call ^ "\n" ^ next
  | EndAbstraction (_, abs, next) ->
      let indent1 = indent ^ indent_incr in
      let verbose = false in
      let abs =
        Values.abs_to_string env ~with_ended:true verbose indent1 indent_incr
          abs
      in
      let next = expression_to_string env indent indent_incr next in
      indent ^ "end\n" ^ abs ^ "\n" ^ next
  | EvalGlobal (global_id, global_generics, sv, next) ->
      let sv = Values.symbolic_value_to_string env sv in
      let global =
        global_decl_ref_to_string env { global_id; global_generics }
      in
      let next = expression_to_string env indent indent_incr next in
      indent ^ "let " ^ sv ^ " = " ^ global ^ " in\n" ^ next
  | Assertion (_, b, next) ->
      let b = Values.typed_value_to_string env b in
      let next = expression_to_string env indent indent_incr next in
      indent ^ "assert " ^ b ^ ";\n" ^ next
  | Expansion (_, sv, exp) -> expansion_to_string env indent indent_incr sv exp
  | IntroSymbolic (_, _, sv, v, next) ->
      let sv = Values.symbolic_value_to_string env sv in
      let v = value_aggregate_to_string env v in
      let next = expression_to_string env indent indent_incr next in
      indent ^ "let " ^ sv ^ " = " ^ v ^ "in\n" ^ next
  | ForwardEnd (ret, _, loop_sid_maps, fwd_end, backs) ->
      let indent1 = indent ^ indent_incr in
      let indent2 = indent1 ^ indent_incr in
      let indent3 = indent2 ^ indent_incr in
      let ret =
        match ret with
        | None -> "None"
        | Some (_, ret) -> "Some " ^ Values.typed_value_to_string env ret
      in
      let ret = "ret = " ^ ret in
      let sid_to_value, refreshed_sids =
        match loop_sid_maps with
        | None -> ("None", "None")
        | Some (sid_to_value, refreshed_sids) ->
            ( SymbolicValueId.Map.to_string None
                (Values.typed_value_to_string env)
                sid_to_value,
              SymbolicValueId.Map.to_string None SymbolicValueId.to_string
                refreshed_sids )
      in
      let sid_to_value = "sid_to_value = " ^ sid_to_value in
      let refreshed_sids = "refreshed_sids = " ^ refreshed_sids in

      let fwd_end = expression_to_string env indent2 indent_incr fwd_end in
      let backs =
        RegionGroupId.Map.to_string (Some indent2)
          (fun e -> "\n" ^ expression_to_string env indent3 indent_incr e)
          backs
      in
      indent ^ "forward_end {\n" ^ indent1 ^ ret ^ "\n" ^ indent1 ^ sid_to_value
      ^ "\n" ^ indent1 ^ refreshed_sids ^ "\n" ^ indent1 ^ "fwd_end =\n"
      ^ fwd_end ^ "\n" ^ indent1 ^ "backs =\n" ^ indent1 ^ backs ^ "\n" ^ indent
      ^ "}"
  | Loop loop -> loop_to_string env indent indent_incr loop
  | ReturnWithLoop (loop_id, is_continue) ->
      indent ^ "return_with_loop (" ^ LoopId.to_string loop_id
      ^ ", is_continue: " ^ bool_to_string is_continue ^ ")"
  | Meta (_, next) -> expression_to_string env indent indent_incr next
  | Error (_, error) -> indent ^ "ERROR(" ^ error ^ ")"

and expansion_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (scrut : symbolic_value) (e : expansion) : string =
  let ty = scrut.sv_ty in
  let scrut = Values.symbolic_value_to_string env scrut in
  let indent1 = indent ^ indent_incr in
  match e with
  | ExpandNoBranch (se, next) ->
      let next = expression_to_string env indent indent_incr next in
      indent ^ "let "
      ^ Values.symbolic_expansion_to_string env ty se
      ^ " = " ^ scrut ^ "in\n" ^ next
  | ExpandAdt branches ->
      let branch_to_string
          ((variant_id, svl, branch) :
            variant_id option * symbolic_value list * expression) : string =
        let field_values =
          List.map ValuesUtils.mk_typed_value_from_symbolic_value svl
        in
        let v : typed_value =
          { value = VAdt { variant_id; field_values }; ty }
        in
        indent ^ "| "
        ^ Values.typed_value_to_string env v
        ^ " ->\n"
        ^ expression_to_string env indent1 indent_incr branch
      in
      indent ^ "match " ^ scrut ^ " with\n"
      ^ String.concat "\n" (List.map branch_to_string branches)
  | ExpandBool (e0, e1) ->
      let e0 = expression_to_string env indent1 indent_incr e0 in
      let e1 = expression_to_string env indent1 indent_incr e1 in
      indent ^ "if " ^ scrut ^ " then\n" ^ e0 ^ "\n" ^ indent ^ "else\n" ^ e1
  | ExpandInt (_, branches, otherwise) ->
      let branch_to_string ((sv, branch) : scalar_value * expression) : string =
        indent ^ "| "
        ^ Values.scalar_value_to_string sv
        ^ " ->\n"
        ^ expression_to_string env indent1 indent_incr branch
      in
      let otherwise = expression_to_string env indent1 indent_incr otherwise in
      indent ^ "match " ^ scrut ^ " with\n"
      ^ String.concat "\n" (List.map branch_to_string branches)
      ^ "\n" ^ indent ^ "| _ ->\n" ^ otherwise

and loop_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (loop : loop) : string =
  let indent1 = indent ^ indent_incr in
  let loop_id = LoopId.to_string loop.loop_id in
  let fresh_svalues = SymbolicValueId.Set.to_string None loop.fresh_svalues in
  let end_expr = expression_to_string env indent1 indent_incr loop.end_expr in
  let loop_expr = expression_to_string env indent1 indent_incr loop.loop_expr in
  "loop@" ^ loop_id ^ " {\n\n" ^ indent1 ^ "fresh_svalues = " ^ fresh_svalues
  ^ "\n\n" ^ indent1 ^ "end_expr=\n" ^ end_expr ^ "\n\n" ^ indent1
  ^ "loop_expr=\n" ^ loop_expr ^ "\n" ^ indent ^ "}"
