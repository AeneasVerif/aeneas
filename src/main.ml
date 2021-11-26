open CfimOfJson
open Interpreter
open Print

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work *)
let () = Printexc.record_backtrace true

let () =
  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "Ok"
