open CfimOfJson
open Logging
open Print
module T = Types
module A = CfimAst
module I = Interpreter

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work *)
let () = Printexc.record_backtrace true

let usage =
  Printf.sprintf
    {|Aenaes: verification of Rust programs by translation

Usage: %s [OPTIONS] FILE
|}
    Sys.argv.(0)

let () =
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
  let json = Yojson.Basic.from_file !filename in
  match cfim_module_of_json json with
  | Error s -> log#error "error: %s\n" s
  | Ok m ->
      (* Print the module *)
      log#ldebug (lazy ("\n" ^ Print.Module.module_to_string m ^ "\n"));

      (* Test the unit functions *)
      I.Test.test_unit_functions m.types m.functions
