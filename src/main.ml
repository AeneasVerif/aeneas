open CfimOfJson
open Logging
open Print
module T = Types
module A = CfimAst

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work *)
let () = Printexc.record_backtrace true

let () =
  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> log#error "error: %s\n" s
  | Ok m ->
      (* Print the module *)
      log#ldebug (lazy ("\n" ^ Print.Module.module_to_string m))
