module C = Collections
module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module A = LlbcAst
open SymbolicAst

let mk_mplace (p : E.place) (ctx : Contexts.eval_ctx) : mplace =
  let bv = Contexts.ctx_lookup_var_binder ctx p.var_id in
  { bv; projection = p.projection }

let mk_opt_mplace (p : E.place option) (ctx : Contexts.eval_ctx) : mplace option
    =
  Option.map (fun p -> mk_mplace p ctx) p

let mk_opt_place_from_op (op : E.operand) (ctx : Contexts.eval_ctx) :
    mplace option =
  match op with
  | E.Copy p | E.Move p -> Some (mk_mplace p ctx)
  | E.Constant _ -> None

let mk_meta (m : meta) (e : expression) : expression = Meta (m, e)

let synthesize_symbolic_expansion (sv : V.symbolic_value)
    (place : mplace option) (seel : V.symbolic_expansion option list)
    (el : expression list option) : expression option =
  match el with
  | None -> None
  | Some el ->
      let ls = List.combine seel el in
      (* Match on the symbolic value type to know which can of expansion happened *)
      let expansion =
        match sv.V.sv_ty with
        | T.Literal PV.Bool -> (
            (* Boolean expansion: there should be two branches *)
            match ls with
            | [
             (Some (V.SeLiteral (PV.Bool true)), true_exp);
             (Some (V.SeLiteral (PV.Bool false)), false_exp);
            ] ->
                ExpandBool (true_exp, false_exp)
            | _ -> raise (Failure "Ill-formed boolean expansion"))
        | T.Literal (PV.Integer int_ty) ->
            (* Switch over an integer: split between the "regular" branches
               and the "otherwise" branch (which should be the last branch) *)
            let branches, otherwise = C.List.pop_last ls in
            (* For all the regular branches, the symbolic value should have
             * been expanded to a constant *)
            let get_scalar (see : V.symbolic_expansion option) : V.scalar_value
                =
              match see with
              | Some (V.SeLiteral (PV.Scalar cv)) ->
                  assert (cv.PV.int_ty = int_ty);
                  cv
              | _ -> raise (Failure "Unreachable")
            in
            let branches =
              List.map (fun (see, exp) -> (get_scalar see, exp)) branches
            in
            (* For the otherwise branch, the symbolic value should have been left
             * unchanged *)
            let otherwise_see, otherwise = otherwise in
            assert (otherwise_see = None);
            (* Return *)
            ExpandInt (int_ty, branches, otherwise)
        | T.Adt (_, _, _, _) ->
            (* Branching: it is necessarily an enumeration expansion *)
            let get_variant (see : V.symbolic_expansion option) :
                T.VariantId.id option * V.symbolic_value list =
              match see with
              | Some (V.SeAdt (vid, fields)) -> (vid, fields)
              | _ -> raise (Failure "Ill-formed branching ADT expansion")
            in
            let exp =
              List.map
                (fun (see, exp) ->
                  let vid, fields = get_variant see in
                  (vid, fields, exp))
                ls
            in
            ExpandAdt exp
        | T.Ref (_, _, _) -> (
            (* Reference expansion: there should be one branch *)
            match ls with
            | [ (Some see, exp) ] -> ExpandNoBranch (see, exp)
            | _ -> raise (Failure "Ill-formed borrow expansion"))
        | T.TypeVar _ | T.Literal Char | Never ->
            raise (Failure "Ill-formed symbolic expansion")
      in
      Some (Expansion (place, sv, expansion))

let synthesize_symbolic_expansion_no_branching (sv : V.symbolic_value)
    (place : mplace option) (see : V.symbolic_expansion) (e : expression option)
    : expression option =
  let el = Option.map (fun e -> [ e ]) e in
  synthesize_symbolic_expansion sv place [ Some see ] el

let synthesize_function_call (call_id : call_id) (ctx : Contexts.eval_ctx)
    (abstractions : V.AbstractionId.id list) (type_params : T.ety list)
    (args : V.typed_value list) (args_places : mplace option list)
    (dest : V.symbolic_value) (dest_place : mplace option)
    (e : expression option) : expression option =
  Option.map
    (fun e ->
      let call =
        {
          call_id;
          ctx;
          abstractions;
          type_params;
          args;
          dest;
          args_places;
          dest_place;
        }
      in
      FunCall (call, e))
    e

let synthesize_global_eval (gid : A.GlobalDeclId.id) (dest : V.symbolic_value)
    (e : expression option) : expression option =
  Option.map (fun e -> EvalGlobal (gid, dest, e)) e

let synthesize_regular_function_call (fun_id : A.fun_id)
    (call_id : V.FunCallId.id) (ctx : Contexts.eval_ctx)
    (abstractions : V.AbstractionId.id list) (type_params : T.ety list)
    (args : V.typed_value list) (args_places : mplace option list)
    (dest : V.symbolic_value) (dest_place : mplace option)
    (e : expression option) : expression option =
  synthesize_function_call
    (Fun (fun_id, call_id))
    ctx abstractions type_params args args_places dest dest_place e

let synthesize_unary_op (ctx : Contexts.eval_ctx) (unop : E.unop)
    (arg : V.typed_value) (arg_place : mplace option) (dest : V.symbolic_value)
    (dest_place : mplace option) (e : expression option) : expression option =
  synthesize_function_call (Unop unop) ctx [] [] [ arg ] [ arg_place ] dest
    dest_place e

let synthesize_binary_op (ctx : Contexts.eval_ctx) (binop : E.binop)
    (arg0 : V.typed_value) (arg0_place : mplace option) (arg1 : V.typed_value)
    (arg1_place : mplace option) (dest : V.symbolic_value)
    (dest_place : mplace option) (e : expression option) : expression option =
  synthesize_function_call (Binop binop) ctx [] [] [ arg0; arg1 ]
    [ arg0_place; arg1_place ] dest dest_place e

let synthesize_end_abstraction (ctx : Contexts.eval_ctx) (abs : V.abs)
    (e : expression option) : expression option =
  Option.map (fun e -> EndAbstraction (ctx, abs, e)) e

let synthesize_assignment (ctx : Contexts.eval_ctx) (lplace : mplace)
    (rvalue : V.typed_value) (rplace : mplace option) (e : expression option) :
    expression option =
  Option.map (fun e -> Meta (Assignment (ctx, lplace, rvalue, rplace), e)) e

let synthesize_assertion (ctx : Contexts.eval_ctx) (v : V.typed_value)
    (e : expression option) =
  Option.map (fun e -> Assertion (ctx, v, e)) e

let synthesize_forward_end (ctx : Contexts.eval_ctx)
    (loop_input_values : V.typed_value V.SymbolicValueId.Map.t option)
    (e : expression) (el : expression T.RegionGroupId.Map.t) =
  Some (ForwardEnd (ctx, loop_input_values, e, el))

let synthesize_loop (loop_id : V.LoopId.id)
    (input_svalues : V.symbolic_value list)
    (fresh_svalues : V.SymbolicValueId.Set.t)
    (rg_to_given_back_tys :
      (T.RegionId.Set.t * T.rty list) T.RegionGroupId.Map.t)
    (end_expr : expression option) (loop_expr : expression option) :
    expression option =
  match (end_expr, loop_expr) with
  | None, None -> None
  | Some end_expr, Some loop_expr ->
      Some
        (Loop
           {
             loop_id;
             input_svalues;
             fresh_svalues;
             rg_to_given_back_tys;
             end_expr;
             loop_expr;
           })
  | _ -> raise (Failure "Unreachable")
