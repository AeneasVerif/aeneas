open CfimOfJson
open Logging
open Print
module T = Types
module A = CfimAst
module I = Interpreter
module EL = Easy_logging.Logging

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work.
 * JP: are you running with OCAMLRUNPARAM=b=1? *)
let () = Printexc.record_backtrace true

let usage =
  Printf.sprintf
    {|Aenaes: verification of Rust programs by translation

Usage: %s [OPTIONS] FILE
|}
    Sys.argv.(0)

let () =
  (* Read the command line arguments *)
  let spec = [] in
  let spec = Arg.align spec in
  let filename = ref "" in
  let fail () =
    print_string usage;
    exit 1
  in
  Arg.parse spec
    (fun f ->
      if not (Filename.check_suffix f ".cfim") then (
        print_string "Unrecognized file extension";
        fail ())
      else if not (Sys.file_exists f) then (
        print_string "File not found";
        fail ())
      else filename := f)
    usage;
  if !filename = "" then (
    print_string usage;
    exit 1);
  (* Set up the logging - for now we use default values - TODO: use the
   * command-line arguments *)
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  main_log#set_level EL.Debug;
  interpreter_log#set_level EL.Debug;
  statements_log#set_level EL.Debug;
  expressions_log#set_level EL.Warning;
  expansion_log#set_level EL.Debug;
  borrows_log#set_level EL.Debug;
  invariants_log#set_level EL.Warning;
  (* Load the module *)
  let json = Yojson.Basic.from_file !filename in
  match cfim_module_of_json json with
  | Error s -> main_log#error "error: %s\n" s
  | Ok m ->
      (* Print the module *)
      main_log#ldebug (lazy ("\n" ^ Print.Module.module_to_string m ^ "\n"));

      (* Test the unit functions with the concrete interpreter *)
      I.Test.test_unit_functions m.types m.functions;

      (* Evaluate the symbolic interpreter on the functions *)
      I.Test.test_functions_symbolic m.types m.functions
