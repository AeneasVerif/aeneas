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
        | T.Bool -> (
            (* Boolean expansion: there should be two branches *)
            match ls with
            | [
             (Some (V.SePrimitive (PV.Bool true)), true_exp);
             (Some (V.SePrimitive (PV.Bool false)), false_exp);
            ] ->
                ExpandBool (true_exp, false_exp)
            | _ -> raise (Failure "Ill-formed boolean expansion"))
        | T.Integer int_ty ->
            (* Switch over an integer: split between the "regular" branches
               and the "otherwise" branch (which should be the last branch) *)
            let branches, otherwise = C.List.pop_last ls in
            (* For all the regular branches, the symbolic value should have
             * been expanded to a constant *)
            let get_scalar (see : V.symbolic_expansion option) : V.scalar_value
                =
              match see with
              | Some (V.SePrimitive (PV.Scalar cv)) ->
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
        | T.Adt (_, _, _) ->
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
        | T.TypeVar _ | Char | Never | Str | Array _ | Slice _ ->
            raise (Failure "Ill-formed symbolic expansion")
      in
      Some (Expansion (place, sv, expansion))

let synthesize_symbolic_expansion_no_branching (sv : V.symbolic_value)
    (place : mplace option) (see : V.symbolic_expansion) (e : expression option)
    : expression option =
  let el = Option.map (fun e -> [ e ]) e in
  synthesize_symbolic_expansion sv place [ Some see ] el

let synthesize_function_call (call_id : call_id)
    (abstractions : V.AbstractionId.id list) (type_params : T.ety list)
    (args : V.typed_value list) (args_places : mplace option list)
    (dest : V.symbolic_value) (dest_place : mplace option)
    (e : expression option) : expression option =
  Option.map
    (fun e ->
      let call =
        {
          call_id;
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
    (call_id : V.FunCallId.id) (abstractions : V.AbstractionId.id list)
    (type_params : T.ety list) (args : V.typed_value list)
    (args_places : mplace option list) (dest : V.symbolic_value)
    (dest_place : mplace option) (e : expression option) : expression option =
  synthesize_function_call
    (Fun (fun_id, call_id))
    abstractions type_params args args_places dest dest_place e

let synthesize_unary_op (unop : E.unop) (arg : V.typed_value)
    (arg_place : mplace option) (dest : V.symbolic_value)
    (dest_place : mplace option) (e : expression option) : expression option =
  synthesize_function_call (Unop unop) [] [] [ arg ] [ arg_place ] dest
    dest_place e

let synthesize_binary_op (binop : E.binop) (arg0 : V.typed_value)
    (arg0_place : mplace option) (arg1 : V.typed_value)
    (arg1_place : mplace option) (dest : V.symbolic_value)
    (dest_place : mplace option) (e : expression option) : expression option =
  synthesize_function_call (Binop binop) [] [] [ arg0; arg1 ]
    [ arg0_place; arg1_place ] dest dest_place e

let synthesize_end_abstraction (abs : V.abs) (e : expression option) :
    expression option =
  Option.map (fun e -> EndAbstraction (abs, e)) e

let synthesize_assignment (lplace : mplace) (rvalue : V.typed_value)
    (rplace : mplace option) (e : expression option) : expression option =
  Option.map (fun e -> Meta (Assignment (lplace, rvalue, rplace), e)) e

let synthesize_assertion (v : V.typed_value) (e : expression option) =
  Option.map (fun e -> Assertion (v, e)) e

let synthesize_forward_end (e : expression)
    (el : expression T.RegionGroupId.Map.t) =
  Some (ForwardEnd (e, el))
