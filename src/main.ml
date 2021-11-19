open CfimOfJson

(*open Interpreter*)
open Print

let () =
  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "Ok"
