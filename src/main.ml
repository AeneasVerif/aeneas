open CfimOfJson
open Logging
open Print
module T = Types
module A = CfimAst
module I = Interpreter
module EL = Easy_logging.Logging
module TA = TypesAnalysis
module Micro = PureMicroPasses

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work.
 * JP: are you running with OCAMLRUNPARAM=b=1? *)
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
  let no_decrease_clauses = ref false in
  let template_decrease_clauses = ref false in

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
        \                        prover's normalizer" );
      ( "-no-decrease-clauses",
        Arg.Set no_decrease_clauses,
        " Do not add decrease clauses to the recursive definitions" );
      ( "-template-clauses",
        Arg.Set template_decrease_clauses,
        " Generate templates for the required decrease clauses, in a\n\
         `\n\
        \                                dedicated file. Incompatible with \
         -no-decrease-clauses" );
    ]
  in
  (* Sanity check: -template-clauses ==> not -no-decrease-clauses *)
  assert ((not !no_decrease_clauses) || not !template_decrease_clauses);

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
        if not (Filename.check_suffix f ".cfim") then (
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
  Easy_logging.Handlers.set_level main_logger_handler EL.Info;
  main_log#set_level EL.Info;
  pre_passes_log#set_level EL.Info;
  interpreter_log#set_level EL.Info;
  statements_log#set_level EL.Info;
  paths_log#set_level EL.Info;
  expressions_log#set_level EL.Info;
  expansion_log#set_level EL.Info;
  borrows_log#set_level EL.Info;
  invariants_log#set_level EL.Info;
  pure_utils_log#set_level EL.Info;
  symbolic_to_pure_log#set_level EL.Info;
  pure_micro_passes_log#set_level EL.Info;
  pure_to_extract_log#set_level EL.Info;
  translate_log#set_level EL.Info;
  (* Load the module *)
  let json = Yojson.Basic.from_file filename in
  match cfim_module_of_json json with
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
          C.check_invariants = true;
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
        }
      in
      let trans_config =
        {
          Translate.eval_config;
          mp_config = micro_passes_config;
          test_unit_functions;
          extract_decrease_clauses = not !no_decrease_clauses;
          extract_template_decrease_clauses = !template_decrease_clauses;
        }
      in
      Translate.translate_module filename dest_dir trans_config m
