module L = Logging
module T = Types
module A = CfimAst
module M = Modules
module SA = SymbolicAst
open Errors
open Cps
open InterpreterUtils
open InterpreterStatements

(** The local logger *)
let log = L.translate_log

(** Execute the symbolic interpreter on a function to generate a list of symbolic ASTs,
    for the forward function and the backward functions. *)
let translate_function_to_symbolics (config : C.partial_config)
    (m : M.cfim_module) (fid : A.FunDefId.id) :
    SA.expression * SA.expression list =
  (* Retrieve the function declaration *)
  let fdef = A.FunDefId.nth m.functions fid in

  (* Debug *)
  log#ldebug
    (lazy
      ("translate_function_to_symbolics: " ^ Print.name_to_string fdef.A.name));

  (* Evaluate *)
  let evaluate = evaluate_function_symbolic config synthesize m fid in
  (* Execute the forward function *)
  let forward = evaluate None in
  (* Execute the backward functions *)
  let backwards =
    T.RegionGroupId.mapi
      (fun gid _ -> evaluate (Some gid))
      fdef.signature.regions_hierarchy
  in

  (* Return *)
  (forward, backwards)

(*let translate (config : C.partial_config) (m : M.cfim_module) : unit =
    (* Translate all the type definitions *)
    let type_defs = SymbolicToPure.translate_type_defs m.type_defs in

    (* Translate all the function signatures *)
    let fun_defs = SymbolicToPure.translate_fun_signatures types_infos
  raise Unimplemented*)
