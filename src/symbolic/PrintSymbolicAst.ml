open Types
open Values
open Print
open SymbolicAst

type fmt_env = Print.fmt_env

let call_id_to_string (env : fmt_env) (call_id : call_id) : string =
  match call_id with
  | Fun (fid, call_id) ->
      Types.fn_ptr_kind_to_string env fid ^ "@" ^ FunCallId.to_string call_id
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
      ^ String.concat ", " (List.map (Values.tvalue_to_string env) call.args)
      ^ ")"
  in
  indent ^ dest ^ " = " ^ call_id ^ generics ^ args

let value_aggregate_to_string (env : fmt_env) (v : value_aggregate) : string =
  match v with
  | VaSingleValue v -> Values.tvalue_to_string env v
  | VaArray vl ->
      "[" ^ String.concat ", " (List.map (Values.tvalue_to_string env) vl) ^ "]"
  | VaCgValue cg_id -> const_generic_db_var_to_string env (Free cg_id)
  | VaTraitConstValue (trait_ref, item) ->
      trait_ref_to_string env trait_ref ^ "." ^ item

let rec expr_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (e : expr) : string =
  match e with
  | Return (_ctx, ret) ->
      let ret =
        match ret with
        | None -> ""
        | Some ret -> " " ^ Values.tvalue_to_string env ret
      in
      indent ^ "return" ^ ret
  | Panic -> indent ^ "panic"
  | FunCall (call, next) ->
      let call = call_to_string env indent call in
      let next = expr_to_string env indent indent_incr next in
      call ^ "\n" ^ next
  | EndAbs (_, abs, next) ->
      let indent1 = indent ^ indent_incr in
      let verbose = false in
      let abs =
        Values.abs_to_string env ~with_ended:true verbose indent1 indent_incr
          abs
      in
      let next = expr_to_string env indent indent_incr next in
      indent ^ "end\n" ^ abs ^ "\n" ^ next
  | EvalGlobal (id, generics, sv, next) ->
      let sv = Values.symbolic_value_to_string env sv in
      let global = global_decl_ref_to_string env { id; generics } in
      let next = expr_to_string env indent indent_incr next in
      indent ^ "let " ^ sv ^ " = " ^ global ^ " in\n" ^ next
  | Assertion (_, b, next) ->
      let b = Values.tvalue_to_string env b in
      let next = expr_to_string env indent indent_incr next in
      indent ^ "assert " ^ b ^ ";\n" ^ next
  | Expansion (_, sv, exp) -> expansion_to_string env indent indent_incr sv exp
  | IntroSymbolic (_, _, sv, v, next) ->
      let sv = Values.symbolic_value_to_string env sv in
      let v = value_aggregate_to_string env v in
      let next = expr_to_string env indent indent_incr next in
      indent ^ "let " ^ sv ^ " = " ^ v ^ "in\n" ^ next
  | SubstituteAbsIds (aids, next) ->
      let aids = AbsId.Map.to_string None AbsId.to_string aids in
      let next = expr_to_string env indent indent_incr next in
      indent ^ "subst " ^ aids ^ " in\n" ^ next
  | ForwardEnd (ret, _, fwd_end, backs) ->
      let indent1 = indent ^ indent_incr in
      let indent2 = indent1 ^ indent_incr in
      let indent3 = indent2 ^ indent_incr in
      let ret =
        match ret with
        | None -> "None"
        | Some (_, ret) -> "Some " ^ Values.tvalue_to_string env ret
      in
      let ret = "ret = " ^ ret in
      let fwd_end = expr_to_string env indent2 indent_incr fwd_end in
      let backs =
        RegionGroupId.Map.to_string (Some indent2)
          (fun e -> "\n" ^ expr_to_string env indent3 indent_incr e)
          backs
      in
      indent ^ "forward_end {\n" ^ indent1 ^ ret ^ "\n" ^ indent1
      ^ "fwd_end =\n" ^ fwd_end ^ "\n" ^ indent1 ^ "backs =\n" ^ indent1 ^ backs
      ^ "\n" ^ indent ^ "}"
  | Loop loop -> loop_to_string env indent indent_incr loop
  | LoopContinue (ectx, loop_id, values, abs) ->
      loop_continue_break_to_string env indent indent_incr ~is_continue:true
        ectx loop_id values abs
  | LoopBreak (ectx, loop_id, values, abs) ->
      loop_continue_break_to_string env indent indent_incr ~is_continue:false
        ectx loop_id values abs
  | Join (ectx, values, abs) ->
      join_to_string env indent indent_incr ectx values abs
  | Let lete -> let_expr_to_string env indent indent_incr lete
  | Meta (_, next) -> expr_to_string env indent indent_incr next
  | Error (_, error) -> indent ^ "ERROR(" ^ error ^ ")"

and loop_continue_break_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) ~(is_continue : bool) _ctx (loop_id : loop_id)
    (values : tvalue list) (abs : abs list) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let keyword = if is_continue then "@continue" else "@break" in
  let loop_id = "loop_id@" ^ LoopId.to_string loop_id in
  let values =
    List.map
      (fun v -> indent2 ^ Print.Values.tvalue_to_string env v ^ ",\n")
      values
  in
  let abs =
    List.map
      (fun a ->
        Print.Values.abs_to_string ~with_ended:true env true indent2 indent_incr
          a
        ^ ",\n")
      abs
  in
  indent ^ keyword ^ " {\n" ^ indent1 ^ loop_id ^ ",\n" ^ indent1
  ^ "values = [\n" ^ String.concat "" values ^ indent1 ^ "]\n\n" ^ indent1
  ^ "abs = [\n" ^ String.concat "" abs ^ indent1 ^ "]\n" ^ indent ^ "}"

and join_to_string (env : fmt_env) (indent : string) (indent_incr : string) _ctx
    (values : tvalue list) (abs : abs list) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let values =
    List.map
      (fun v -> indent2 ^ Print.Values.tvalue_to_string env v ^ ",\n")
      values
  in
  let abs =
    List.map
      (fun a ->
        Print.Values.abs_to_string ~with_ended:true env true indent2 indent_incr
          a
        ^ ",\n")
      abs
  in
  indent ^ "@join" ^ " {\n" ^ indent1 ^ "values = [\n" ^ String.concat "" values
  ^ indent1 ^ "]\n\n" ^ indent1 ^ "abs = [\n" ^ String.concat "" abs ^ indent1
  ^ "]\n" ^ indent ^ "}"

and expansion_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (scrut : symbolic_value) (e : expansion) : string =
  let ty = scrut.sv_ty in
  let scrut = Values.symbolic_value_to_string env scrut in
  let indent1 = indent ^ indent_incr in
  match e with
  | ExpandNoBranch (se, next) ->
      let next = expr_to_string env indent indent_incr next in
      indent ^ "let "
      ^ Values.symbolic_expansion_to_string env ty se
      ^ " = " ^ scrut ^ "in\n" ^ next
  | ExpandAdt branches ->
      let branch_to_string
          ((variant_id, svl, branch) :
            variant_id option * symbolic_value list * expr) : string =
        let fields = List.map ValuesUtils.mk_tvalue_from_symbolic_value svl in
        let v : tvalue = { value = VAdt { variant_id; fields }; ty } in
        indent ^ "| "
        ^ Values.tvalue_to_string env v
        ^ " ->\n"
        ^ expr_to_string env indent1 indent_incr branch
      in
      indent ^ "match " ^ scrut ^ " with\n"
      ^ String.concat "\n" (List.map branch_to_string branches)
  | ExpandBool (e0, e1) ->
      let e0 = expr_to_string env indent1 indent_incr e0 in
      let e1 = expr_to_string env indent1 indent_incr e1 in
      indent ^ "if " ^ scrut ^ " then\n" ^ e0 ^ "\n" ^ indent ^ "else\n" ^ e1
  | ExpandInt (_, branches, otherwise) ->
      let branch_to_string ((sv, branch) : scalar_value * expr) : string =
        indent ^ "| "
        ^ Values.scalar_value_to_string sv
        ^ " ->\n"
        ^ expr_to_string env indent1 indent_incr branch
      in
      let otherwise = expr_to_string env indent1 indent_incr otherwise in
      indent ^ "match " ^ scrut ^ " with\n"
      ^ String.concat "\n" (List.map branch_to_string branches)
      ^ "\n" ^ indent ^ "| _ ->\n" ^ otherwise

and loop_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (loop : loop) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let loop_id = LoopId.to_string loop.loop_id in
  let next_expr = expr_to_string env indent2 indent_incr loop.next_expr in
  let loop_expr = expr_to_string env indent2 indent_incr loop.loop_expr in
  indent ^ "loop@" ^ loop_id ^ " {\n" ^ indent1 ^ "input_svalues= "
  ^ Print.list_to_string ~sep:", "
      (fun (v : symbolic_value) -> SymbolicValueId.to_string v.sv_id)
      loop.input_svalues
  ^ "\n" ^ indent1 ^ "input_abs= "
  ^ Print.list_to_string ~sep:", "
      (fun (a : abs) -> AbsId.to_string a.abs_id)
      loop.input_abs
  ^ "\n" ^ indent1 ^ "break_svalues= "
  ^ Print.list_to_string ~sep:", "
      (fun (v : symbolic_value) -> SymbolicValueId.to_string v.sv_id)
      loop.break_svalues
  ^ "\n" ^ indent1 ^ "break_abs= "
  ^ Print.list_to_string ~sep:", "
      (fun (a : abs) -> AbsId.to_string a.abs_id)
      loop.break_abs
  ^ "\n" ^ indent1 ^ "loop_expr=\n" ^ loop_expr ^ "\n\n" ^ indent1
  ^ "next_expr=\n" ^ next_expr ^ "\n" ^ indent ^ "}"

and let_expr_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (lete : let_expr) : string =
  let indent1 = indent ^ indent_incr in
  let indent2 = indent1 ^ indent_incr in
  let next_expr = expr_to_string env indent2 indent_incr lete.next_expr in
  let bound_expr = expr_to_string env indent2 indent_incr lete.bound_expr in
  indent ^ "@let {" ^ "\n" ^ indent1 ^ "out_svalues= "
  ^ Print.list_to_string ~sep:", "
      (fun (v : symbolic_value) -> SymbolicValueId.to_string v.sv_id)
      lete.out_svalues
  ^ "\n" ^ indent1 ^ "out_abs= "
  ^ Print.list_to_string ~sep:", "
      (fun (a : abs) -> AbsId.to_string a.abs_id)
      lete.out_abs
  ^ "\n" ^ indent1 ^ "bound_expr=\n" ^ bound_expr ^ "\n\n" ^ indent1
  ^ "next_expr=\n" ^ next_expr ^ "\n" ^ indent ^ "}"
