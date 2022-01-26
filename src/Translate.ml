module L = Logging
module T = Types
module A = CfimAst
module M = Modules
module SA = SymbolicAst
open Cps
open InterpreterUtils
open InterpreterStatements

(** The local logger *)
let log = L.translate_log

(** Execute the symbolic interpreter on a function to generate a pure AST.
    
    We don't apply any micro pass.
 *)
let translate_function_to_pure (config : C.partial_config) (m : M.cfim_module)
    (fid : A.FunDefId.id) : unit =
  (* Retrieve the function declaration *)
  let fdef = A.FunDefId.nth m.functions fid in

  (* Debug *)
  log#ldebug
    (lazy ("translate_function_to_pure: " ^ Print.name_to_string fdef.A.name));

  (* Create the evaluation context *)
  let ctx = initialize_symbolic_context_for_fun m fdef in

  (* Create the continuation to check the function's result *)
  let cf_check res _ =
    match res with
    | Return -> if synthesize then raise Errors.Unimplemented else None
    | Panic ->
        (* Note that as we explore all the execution branches, one of
         * the executions can lead to a panic *)
        if synthesize then Some SA.Panic else None
    | _ ->
        failwith
          ("Unit test failed (symbolic execution) on: "
          ^ Print.name_to_string fdef.A.name)
  in

  (* Evaluate the function *)
  let config = C.config_of_partial C.SymbolicMode config in
  let _ = eval_function_body config fdef.A.body cf_check ctx in
  ()
