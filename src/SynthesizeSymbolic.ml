module C = Collections
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
open SymbolicAst

let synthesize_symbolic_expansion (sv : V.symbolic_value)
    (seel : V.symbolic_expansion option list) (exprl : expression list option) :
    expression option =
  match exprl with
  | None -> None
  | Some exprl ->
      let ls = List.combine seel exprl in
      (* Match on the symbolic value type to know which can of expansion happened *)
      let expansion =
        match sv.V.sv_ty with
        | T.Bool -> (
            (* Boolean expansion: there should be two branches *)
            match ls with
            | [
             (Some (V.SeConcrete (V.Bool true)), true_exp);
             (Some (V.SeConcrete (V.Bool false)), false_exp);
            ] ->
                ExpandBool (true_exp, false_exp)
            | _ -> failwith "Ill-formed boolean expansion")
        | T.Integer int_ty ->
            (* Switch over an integer: split between the "regular" branches
               and the "otherwise" branch (which should be the last branch) *)
            let branches, otherwise = C.List.pop_last ls in
            (* For all the regular branches, the symbolic value should have
             * been expanded to a constant *)
            let get_scalar (see : V.symbolic_expansion option) : V.scalar_value
                =
              match see with
              | Some (V.SeConcrete (V.Scalar cv)) ->
                  assert (cv.V.int_ty = int_ty);
                  cv
              | _ -> failwith "Unreachable"
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
              | _ -> failwith "Ill-formed branching ADT expansion"
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
            | _ -> failwith "Ill-formed borrow expansion")
        | T.TypeVar _ | Char | Never | Str | Array _ | Slice _ ->
            failwith "Ill-formed symbolic expansion"
      in
      Some (Expansion (sv, expansion))

let synthesize_symbolic_expansion_no_branching (sv : V.symbolic_value)
    (see : V.symbolic_expansion) (expr : expression option) : expression option
    =
  let exprl = match expr with None -> None | Some expr -> Some [ expr ] in
  synthesize_symbolic_expansion sv [ Some see ] exprl

let synthesize_function_call (call_id : call_id)
    (abstractions : V.AbstractionId.id list) (type_params : T.ety list)
    (args : V.typed_value list) (dest : V.symbolic_value)
    (expr : expression option) : expression option =
  match expr with
  | None -> None
  | Some expr ->
      let call = { call_id; abstractions; type_params; args; dest } in
      Some (FunCall (call, expr))

let synthesize_regular_function_call (fun_id : A.fun_id)
    (call_id : V.FunCallId.id) (abstractions : V.AbstractionId.id list)
    (type_params : T.ety list) (args : V.typed_value list)
    (dest : V.symbolic_value) (expr : expression option) : expression option =
  synthesize_function_call
    (Fun (fun_id, call_id))
    abstractions type_params args dest expr

let synthesize_unary_op (unop : E.unop) (arg : V.typed_value)
    (dest : V.symbolic_value) (expr : expression option) : expression option =
  synthesize_function_call (Unop unop) [] [] [ arg ] dest expr

let synthesize_binary_op (binop : E.binop) (arg0 : V.typed_value)
    (arg1 : V.typed_value) (dest : V.symbolic_value) (expr : expression option)
    : expression option =
  synthesize_function_call (Binop binop) [] [] [ arg0; arg1 ] dest expr

let synthesize_aggregated_value (aggr_v : V.typed_value)
    (expr : expression option) : expression option =
  match expr with
  | None -> None
  | Some expr -> Some (Meta (Aggregate aggr_v, expr))

let synthesize_end_abstraction (abs : V.abs) (expr : expression option) :
    expression option =
  match expr with
  | None -> None
  | Some expr -> Some (EndAbstraction (abs, expr))
