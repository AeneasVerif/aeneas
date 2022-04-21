open LlbcOfJson
open Logging
open Print
module T = Types
module A = LlbcAst
module I = Interpreter
module EL = Easy_logging.Logging
module TA = TypesAnalysis
module Micro = PureMicroPasses

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
  (* Read the command line arguments *)
  let dest_dir = ref "" in
  let decompose_monads = ref false in
  let unfold_monads = ref true in
  let filter_useless_calls = ref true in
  let filter_useless_functions = ref true in
  let test_units = ref false in
  let test_trans_units = ref false in
  let no_decreases_clauses = ref false in
  let no_state = ref false in
  let template_decreases_clauses = ref false in
  let no_split_files = ref false in
  let no_check_inv = ref false in

  let spec =
    [
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
      ( "-decompose-monads",
        Arg.Set decompose_monads,
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
        Arg.Set unfold_monads,
        " Unfold the monadic let-bindings to matches" );
      ( "-filter-useless-calls",
        Arg.Set filter_useless_calls,
        " Filter the useless function calls, when possible" );
      ( "-filter-useless-funs",
        Arg.Set filter_useless_functions,
        " Filter the useless forward/backward functions" );
      ( "-test-units",
        Arg.Set test_units,
        " Test the unit functions with the concrete interpreter" );
      ( "-test-trans-units",
        Arg.Set test_trans_units,
        " Test the translated unit functions with the target theorem\n\
        \                         prover's normalizer" );
      ( "-no-decreases-clauses",
        Arg.Set no_decreases_clauses,
        " Do not add decrease clauses to the recursive definitions" );
      ( "-no-state",
        Arg.Set no_state,
        " Do not use state-error monads, simply use error monads" );
      ( "-template-clauses",
        Arg.Set template_decreases_clauses,
        " Generate templates for the required decreases clauses, in a\n\
        \                         dedicated file. Incompatible with \
         -no-decreases-clauses" );
      ( "-no-split-files",
        Arg.Set no_split_files,
        " Don't split the definitions between different files for types,\n\
        \                         functions, etc." );
      ( "-no-check-inv",
        Arg.Set no_check_inv,
        " Deactivate the invariant sanity checks performed at every step of\n\
        \                         evaluation. Dramatically saves speed." );
    ]
  in
  (* Sanity check: -template-clauses ==> not -no-decrease-clauses *)
  assert ((not !no_decreases_clauses) || not !template_decreases_clauses);

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
          print_string "Unrecognized file extension";
          fail ())
        else if not (Sys.file_exists f) then (
          print_string "File not found";
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
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  main_log#set_level EL.Debug;
  llbc_of_json_logger#set_level EL.Debug;
  pre_passes_log#set_level EL.Debug;
  interpreter_log#set_level EL.Debug;
  statements_log#set_level EL.Debug;
  paths_log#set_level EL.Debug;
  expressions_log#set_level EL.Debug;
  expansion_log#set_level EL.Debug;
  borrows_log#set_level EL.Debug;
  invariants_log#set_level EL.Debug;
  pure_utils_log#set_level EL.Debug;
  symbolic_to_pure_log#set_level EL.Debug;
  pure_micro_passes_log#set_level EL.Debug;
  pure_to_extract_log#set_level EL.Debug;
  translate_log#set_level EL.Debug;
  (* Load the module *)
  let json = Yojson.Basic.from_file filename in
  match llbc_module_of_json json with
  | Error s ->
      main_log#error "error: %s\n" s;
      exit 1
  | Ok m ->
      (* Logging *)
      main_log#linfo (lazy ("Imported: " ^ filename));
      main_log#ldebug (lazy ("\n" ^ Print.Module.module_to_string m ^ "\n"));

      (* Apply the pre-passes *)
      let m = PrePasses.apply_passes m in

      (* Some options for the execution *)
      let eval_config =
        {
          C.check_invariants = not !no_check_inv;
          greedy_expand_symbolics_with_borrows = true;
          allow_bottom_below_borrow = true;
        }
      in

      (* Test the unit functions with the concrete interpreter *)
      if !test_units then I.Test.test_unit_functions eval_config m;

      (* Evaluate the symbolic interpreter on the functions, ignoring the
       * functions which contain loops - TODO: remove *)
      let synthesize = true in
      I.Test.test_functions_symbolic eval_config synthesize m;

      (* Translate the functions *)
      let test_unit_functions = !test_trans_units in
      let micro_passes_config =
        {
          Micro.decompose_monadic_let_bindings = !decompose_monads;
          unfold_monadic_let_bindings = !unfold_monads;
          filter_useless_monadic_calls = !filter_useless_calls;
          filter_useless_functions = !filter_useless_functions;
          add_unit_args = false;
          use_state_monad = not !no_state;
        }
      in
      (* Small issue: the monadic `bind` only works for the error-monad, not
       * the state-error monad (there are definitions to write and piping to do) *)
      assert (
        (not micro_passes_config.use_state_monad)
        || micro_passes_config.unfold_monadic_let_bindings);
      let trans_config =
        {
          Translate.eval_config;
          mp_config = micro_passes_config;
          split_files = not !no_split_files;
          test_unit_functions;
          extract_decreases_clauses = not !no_decreases_clauses;
          extract_template_decreases_clauses = !template_decreases_clauses;
        }
      in
      Translate.translate_module filename dest_dir trans_config m
