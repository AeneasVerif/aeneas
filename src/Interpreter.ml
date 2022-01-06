module L = Logging
open InterpreterExpressions
open InterpreterStatements

(* TODO: check that the value types are correct when evaluating *)
(* TODO: for debugging purposes, we might want to put use eval_ctx everywhere
   (rather than only env) *)

(* TODO: it would be good to find a "core", which implements the rules (like
   "end_borrow") and on top of which we build more complex functions which
   chose in which order to apply the rules, etc. This way we would make very
   explicit where we need to insert sanity checks, what the preconditions are,
   where invariants might be broken, etc.
*)

(* TODO: intensively test with PLT-redex *)

(* TODO: remove the config parameters when they are useless *)

module Test = struct
  (** Test a unit function (taking no arguments) by evaluating it in an empty
    environment
 *)
  let test_unit_function (type_context : C.type_context)
      (fun_defs : A.fun_def list) (fid : A.FunDefId.id) : unit eval_result =
    (* Retrieve the function declaration *)
    let fdef = A.FunDefId.nth fun_defs fid in

    (* Debug *)
    L.log#ldebug
      (lazy ("test_unit_function: " ^ Print.Types.name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (List.length fdef.A.signature.region_params = 0);
    assert (List.length fdef.A.signature.type_params = 0);
    assert (fdef.A.arg_count = 0);

    (* Create the evaluation context *)
    let ctx =
      {
        C.type_context;
        C.fun_context = fun_defs;
        C.type_vars = [];
        C.env = [];
        C.symbolic_counter = V.SymbolicValueId.generator_zero;
        C.borrow_counter = V.BorrowId.generator_zero;
        C.region_counter = T.RegionId.generator_zero;
        C.abstraction_counter = V.AbstractionId.generator_zero;
      }
    in

    (* Put the (uninitialized) local variables *)
    let ctx = C.ctx_push_uninitialized_vars ctx fdef.A.locals in

    (* Evaluate the function *)
    let config = { C.mode = C.ConcreteMode; C.check_invariants = true } in
    match eval_function_body config ctx fdef.A.body with
    | [ Ok _ ] -> Ok ()
    | [ Error err ] -> Error err
    | _ ->
        (* We execute the concrete interpreter: there shouldn't be any branching *)
        failwith "Unreachable"

  (** Small helper: return true if the function is a unit function (no parameters,
    no arguments) - TODO: move *)
  let fun_def_is_unit (def : A.fun_def) : bool =
    def.A.arg_count = 0
    && List.length def.A.signature.region_params = 0
    && List.length def.A.signature.type_params = 0
    && List.length def.A.signature.inputs = 0

  (** Test all the unit functions in a list of function definitions *)
  let test_all_unit_functions (type_defs : T.type_def list)
      (fun_defs : A.fun_def list) : unit =
    let test_fun (def : A.fun_def) : unit =
      if fun_def_is_unit def then
        let type_ctx = { C.type_defs } in
        match test_unit_function type_ctx fun_defs def.A.def_id with
        | Error _ -> failwith "Unit test failed"
        | Ok _ -> ()
      else ()
    in
    List.iter test_fun fun_defs
end
