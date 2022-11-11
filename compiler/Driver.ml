open Aeneas.LlbcOfJson
open Aeneas.Logging
module T = Aeneas.Types
module A = Aeneas.LlbcAst
module I = Aeneas.Interpreter
module EL = Easy_logging.Logging
module TA = Aeneas.TypesAnalysis
module Micro = Aeneas.PureMicroPasses
module Print = Aeneas.Print
module PrePasses = Aeneas.PrePasses
module Translate = Aeneas.Translate
open Aeneas.Config

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work.
 * TODO: run with OCAMLRUNPARAM=b=1? *)
let () = Printexc.record_backtrace true

let usage =
  Printf.sprintf
    {|Aeneas: verification of Rust programs by translation to pure lambda calculus

Usage: %s [OPTIONS] FILE
|}
    Sys.argv.(0)

let () =
  (* Measure start time *)
  let start_time = Unix.gettimeofday () in

  (* Read the command line arguments *)
  let dest_dir = ref "" in

  let spec =
    [
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
      ( "-decompose-monads",
        Arg.Set decompose_monadic_let_bindings,
        " Decompose the monadic let-bindings.\n\n\
        \         Introduces a temporary variable which is later decomposed,\n\
        \         when the pattern on the left of the monadic let is not a \n\
        \         variable.\n\
        \         \n\
        \         Example:\n\
        \         `(x, y) <-- f (); ...` ~~>\n\
        \         `tmp <-- f (); let (x, y) = tmp in ...`\n\
        \        " );
      ( "-unfold-monads",
        Arg.Set unfold_monadic_let_bindings,
        " Unfold the monadic let-bindings to matches" );
      ( "-no-filter-useless-calls",
        Arg.Clear filter_useless_monadic_calls,
        " Do not filter the useless function calls, when possible" );
      ( "-no-filter-useless-funs",
        Arg.Clear filter_useless_functions,
        " Do not filter the useless forward/backward functions" );
      ( "-test-units",
        Arg.Set test_unit_functions,
        " Test the unit functions with the concrete interpreter" );
      ( "-test-trans-units",
        Arg.Set test_trans_unit_functions,
        " Test the translated unit functions with the target theorem\n\
        \                         prover's normalizer" );
      ( "-no-decreases-clauses",
        Arg.Clear extract_decreases_clauses,
        " Do not add decrease clauses to the recursive definitions" );
      ( "-no-state",
        Arg.Clear use_state,
        " Do not use state-error monads, simply use error monads" );
      ( "-backward-no-state-update",
        Arg.Set backward_no_state_update,
        " Forbid backward functions from updating the state" );
      ( "-template-clauses",
        Arg.Set extract_template_decreases_clauses,
        " Generate templates for the required decreases clauses, in a\n\
        \                         dedicated file. Incompatible with \
         -no-decreases-clauses" );
      ( "-no-split-files",
        Arg.Clear split_files,
        " Don't split the definitions between different files for types,\n\
        \                         functions, etc." );
      ( "-no-check-inv",
        Arg.Clear check_invariants,
        " Deactivate the invariant sanity checks performed at every step of\n\
        \                         evaluation. Dramatically saves speed." );
    ]
  in
  (* Sanity check: -template-clauses ==> not -no-decrease-clauses *)
  assert (!extract_decreases_clauses || not !extract_template_decreases_clauses);
  (* Sanity check: -backward-no-state-update ==> not -no-state *)
  assert ((not !backward_no_state_update) || !use_state);

  let spec = Arg.align spec in
  let filenames = ref [] in
  let add_filename f = filenames := f :: !filenames in
  Arg.parse spec add_filename usage;
  let fail () =
    print_string usage;
    exit 1
  in
  (* Retrieve and check the filename *)
  let filename =
    match !filenames with
    | [ f ] ->
        (* TODO: update the extension *)
        if not (Filename.check_suffix f ".llbc") then (
          print_string ("Unrecognized file extension: " ^ f ^ "\n");
          fail ())
        else if not (Sys.file_exists f) then (
          print_string ("File not found: " ^ f ^ "\n");
          fail ())
        else f
    | _ ->
        (* For now, we only process one file at a time *)
        print_string usage;
        exit 1
  in
  (* Check the destination directory *)
  let dest_dir =
    if !dest_dir = "" then Filename.dirname filename else !dest_dir
  in

  (* Set up the logging - for now we use default values - TODO: use the
   * command-line arguments *)
  (* By setting a level for the main_logger_handler, we filter everything *)
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  main_log#set_level EL.Info;
  llbc_of_json_logger#set_level EL.Info;
  pre_passes_log#set_level EL.Info;
  interpreter_log#set_level EL.Info;
  statements_log#set_level EL.Info;
  paths_log#set_level EL.Info;
  expressions_log#set_level EL.Info;
  expansion_log#set_level EL.Info;
  projectors_log#set_level EL.Info;
  borrows_log#set_level EL.Info;
  invariants_log#set_level EL.Info;
  pure_utils_log#set_level EL.Info;
  symbolic_to_pure_log#set_level EL.Info;
  pure_micro_passes_log#set_level EL.Info;
  pure_to_extract_log#set_level EL.Info;
  translate_log#set_level EL.Info;
  let log = main_log in

  (* Load the module *)
  let json = Yojson.Basic.from_file filename in
  match crate_of_json json with
  | Error s ->
      log#error "error: %s\n" s;
      exit 1
  | Ok m ->
      (* Logging *)
      log#linfo (lazy ("Imported: " ^ filename));
      log#ldebug (lazy ("\n" ^ Print.Crate.crate_to_string m ^ "\n"));

      (* Apply the pre-passes *)
      let m = PrePasses.apply_passes m in

      (* Some options for the execution *)

      (* Test the unit functions with the concrete interpreter *)
      if !test_unit_functions then I.Test.test_unit_functions m;

      (* Evaluate the symbolic interpreter on the functions, ignoring the
       * functions which contain loops - TODO: remove *)
      let synthesize = true in
      I.Test.test_functions_symbolic synthesize m;

      (* Translate the functions *)
      Translate.translate_module filename dest_dir m;

      (* Print total elapsed time *)
      log#linfo
        (lazy
          (Printf.sprintf "Total execution time: %f seconds"
             (Unix.gettimeofday () -. start_time)))
