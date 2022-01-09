module L = Logging
module T = Types
module A = CfimAst
open Utils
open InterpreterUtils
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

(** The local logger *)
let log = L.interpreter_log

module Test = struct
  let initialize_context (type_context : C.type_context)
      (fun_defs : A.fun_def list) (type_vars : T.type_var list) : C.eval_ctx =
    C.reset_global_counters ();
    {
      C.type_context;
      C.fun_context = fun_defs;
      C.type_vars;
      C.env = [];
      C.ended_regions = T.RegionId.Set.empty;
    }

  (** Initialize an evaluation context to execute a function.

      Introduces local variables initialized in the following manner:
      - input arguments are initialized as symbolic values
      - the remaining locals are initialized as ⊥
      "Dummy" abstractions are introduced for the regions present in the
      function signature.
   *)
  let initialize_symbolic_context_for_fun (type_context : C.type_context)
      (fun_defs : A.fun_def list) (fdef : A.fun_def) : C.eval_ctx =
    (* The abstractions are not initialized the same way as for function
     * calls: they contain *loan* projectors, because they "provide" us
     * with the input values (which behave as if they had been returned
     * by some function calls...).
     * Also, note that we properly set the set of parents of every abstraction:
     * this should not be necessary, as those abstractions should never be
     * *automatically* ended (because ending some borrows requires to end
     * one of them), but rather selectively ended when generating code
     * for each of the backward functions. We do it only because we can
     * do it, and because it gives a bit of sanity.
     * *)
    let sg = fdef.signature in
    (* Create the context *)
    let ctx = initialize_context type_context fun_defs sg.type_params in
    (* Instantiate the signature *)
    let type_params =
      List.map (fun tv -> T.TypeVar tv.T.index) sg.type_params
    in
    let ctx, inst_sg = instantiate_fun_sig type_params sg ctx in
    (* Create fresh symbolic values for the inputs *)
    let input_svs =
      List.map (fun ty -> mk_fresh_symbolic_value ty) inst_sg.inputs
    in
    (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
    let empty_absl =
      create_empty_abstractions_from_abs_region_groups
        inst_sg.A.regions_hierarchy
    in
    (* Add the avalues to the abstractions and insert them in the context *)
    let insert_abs (ctx : C.eval_ctx) (abs : V.abs) : C.eval_ctx =
      (* Project over the values - we use *loan* projectors, as explained above *)
      let project_all_loans = false in
      let avalues =
        List.map
          (mk_aproj_loans_from_symbolic_value project_all_loans)
          input_svs
      in
      (* Insert the avalues in the abstraction *)
      let abs = { abs with avalues } in
      (* Insert the abstraction in the context *)
      let ctx = { ctx with env = Abs abs :: ctx.env } in
      (* Return *)
      ctx
    in
    let ctx = List.fold_left insert_abs ctx empty_absl in
    (* Split the variables between return var, inputs and remaining locals *)
    let ret_var = List.hd fdef.locals in
    let input_vars, local_vars =
      list_split_at (List.tl fdef.locals) fdef.arg_count
    in
    (* Push the return variable (initialized with ⊥) *)
    let ctx = C.ctx_push_uninitialized_var ctx ret_var in
    (* Push the input variables (initialized with symbolic values) *)
    let input_values = List.map mk_typed_value_from_symbolic_value input_svs in
    let ctx = C.ctx_push_vars ctx (List.combine input_vars input_values) in
    (* Push the remaining local variables (initialized with ⊥) *)
    let ctx = C.ctx_push_uninitialized_vars ctx local_vars in
    (* Return *)
    ctx

  (** Test a unit function (taking no arguments) by evaluating it in an empty
      environment.
   *)
  let test_unit_function (type_context : C.type_context)
      (fun_defs : A.fun_def list) (fid : A.FunDefId.id) : unit eval_result =
    (* Retrieve the function declaration *)
    let fdef = A.FunDefId.nth fun_defs fid in

    (* Debug *)
    log#ldebug
      (lazy ("test_unit_function: " ^ Print.Types.name_to_string fdef.A.name));

    (* Sanity check - *)
    assert (List.length fdef.A.signature.region_params = 0);
    assert (List.length fdef.A.signature.type_params = 0);
    assert (fdef.A.arg_count = 0);

    (* Create the evaluation context *)
    let ctx = initialize_context type_context fun_defs [] in

    (* Insert the (uninitialized) local variables *)
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
  let test_unit_functions (type_defs : T.type_def list)
      (fun_defs : A.fun_def list) : unit =
    let unit_funs = List.filter fun_def_is_unit fun_defs in
    let test_unit_fun (def : A.fun_def) : unit =
      let type_ctx = { C.type_defs } in
      match test_unit_function type_ctx fun_defs def.A.def_id with
      | Error _ -> failwith "Unit test failed (concrete execution)"
      | Ok _ -> ()
    in
    List.iter test_unit_fun unit_funs

  (** Execute the symbolic interpreter on a function. *)
  let test_function_symbolic (type_context : C.type_context)
      (fun_defs : A.fun_def list) (fid : A.FunDefId.id) :
      C.eval_ctx eval_result list =
    (* Retrieve the function declaration *)
    let fdef = A.FunDefId.nth fun_defs fid in

    (* Debug *)
    log#ldebug
      (lazy
        ("test_function_symbolic: " ^ Print.Types.name_to_string fdef.A.name));

    (* Create the evaluation context *)
    let ctx = initialize_symbolic_context_for_fun type_context fun_defs fdef in

    (* Evaluate the function *)
    let config = { C.mode = C.SymbolicMode; C.check_invariants = true } in
    eval_function_body config ctx fdef.A.body

  (** Execute the symbolic interpreter on a list of functions.

      TODO: for now we ignore the functions which contain loops, because
      they are not supported by the symbolic interpreter.
   *)
  let test_functions_symbolic (type_defs : T.type_def list)
      (fun_defs : A.fun_def list) : unit =
    let no_loop_funs =
      List.filter (fun f -> not (CfimAstUtils.fun_def_has_loops f)) fun_defs
    in
    let test_fun (def : A.fun_def) : unit =
      let type_ctx = { C.type_defs } in
      (* Execute the function - note that as the symbolic interpreter explores
       * all the path, some executions are expected to "panic": we thus don't
       * check the return value *)
      let _ = test_function_symbolic type_ctx fun_defs def.A.def_id in
      ()
    in
    List.iter test_fun no_loop_funs
end
