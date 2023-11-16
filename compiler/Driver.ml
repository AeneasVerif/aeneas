open Aeneas.LlbcOfJson
open Aeneas.Logging
open Aeneas.LlbcAst
open Aeneas.Interpreter
module EL = Easy_logging.Logging
open Aeneas.Config
open Aeneas

(** The local logger *)
let log = main_log

let _ =
  (* Set up the logging - for now we use default values - TODO: use the
   * command-line arguments *)
  (* By setting a level for the main_logger_handler, we filter everything.
     To have a good trace: one should switch between Info and Debug.
  *)
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  main_log#set_level EL.Info;
  llbc_of_json_logger#set_level EL.Info;
  regions_hierarchy_log#set_level EL.Info;
  pre_passes_log#set_level EL.Info;
  associated_types_log#set_level EL.Info;
  contexts_log#set_level EL.Info;
  interpreter_log#set_level EL.Info;
  statements_log#set_level EL.Info;
  loops_match_ctxs_log#set_level EL.Info;
  loops_join_ctxs_log#set_level EL.Info;
  loops_fixed_point_log#set_level EL.Info;
  loops_log#set_level EL.Info;
  paths_log#set_level EL.Info;
  expressions_log#set_level EL.Info;
  expansion_log#set_level EL.Info;
  projectors_log#set_level EL.Info;
  borrows_log#set_level EL.Info;
  invariants_log#set_level EL.Info;
  pure_utils_log#set_level EL.Info;
  symbolic_to_pure_log#set_level EL.Info;
  pure_micro_passes_log#set_level EL.Info;
  extract_log#set_level EL.Info;
  translate_log#set_level EL.Info;
  scc_log#set_level EL.Info;
  reorder_decls_log#set_level EL.Info

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

  (* Print the imported llbc *)
  let print_llbc = ref false in

  let spec =
    [
      ( "-backend",
        Arg.Symbol (backend_names, set_backend),
        " Specify the target backend" );
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
      ( "-no-filter-useless-calls",
        Arg.Clear filter_useless_monadic_calls,
        " Do not filter the useless function calls" );
      ( "-no-filter-useless-funs",
        Arg.Clear filter_useless_functions,
        " Do not filter the useless forward/backward functions" );
      ( "-test-units",
        Arg.Set test_unit_functions,
        " Test the unit functions with the concrete (i.e., not symbolic) \
         interpreter" );
      ( "-test-trans-units",
        Arg.Set test_trans_unit_functions,
        " Test the translated unit functions with the target theorem prover's \
         normalizer" );
      ( "-decreases-clauses",
        Arg.Set extract_decreases_clauses,
        " Use decreases clauses/termination measures for the recursive \
         definitions" );
      ( "-state",
        Arg.Set use_state,
        " Use a *state*-error monads, instead of an error monads" );
      ( "-use-fuel",
        Arg.Set use_fuel,
        " Use a fuel parameter to control divergence" );
      ( "-backward-no-state-update",
        Arg.Set backward_no_state_update,
        " Forbid backward functions from updating the state" );
      ( "-template-clauses",
        Arg.Set extract_template_decreases_clauses,
        " Generate templates for the required decreases clauses/termination \
         measures, in a dedicated file. Implies -decreases-clauses" );
      ( "-split-files",
        Arg.Set split_files,
        " Split the definitions between different files for types, functions, \
         etc." );
      ( "-no-check-inv",
        Arg.Clear check_invariants,
        " Deactivate the invariant sanity checks performed at every evaluation \
         step. Dramatically increases speed." );
      ( "-no-gen-lib-entry",
        Arg.Clear generate_lib_entry_point,
        " Do not generate the entry point file for the generated library (only \
         valid if the crate is split between different files)" );
      ( "-lean-default-lakefile",
        Arg.Clear lean_gen_lakefile,
        " Generate a default lakefile.lean (Lean only)" );
      ("-print-llbc", Arg.Set print_llbc, " Print the imported LLBC");
      ("-k", Arg.Clear fail_hard, " Do not fail hard in case of error");
    ]
  in

  let spec = Arg.align spec in
  let filenames = ref [] in
  let add_filename f = filenames := f :: !filenames in
  Arg.parse spec add_filename usage;
  let fail () =
    print_string usage;
    exit 1
  in

  if !extract_template_decreases_clauses then extract_decreases_clauses := true;
  if !print_llbc then main_log#set_level EL.Debug;

  (* Sanity check (now that the arguments are parsed!): -template-clauses ==> decrease-clauses *)
  assert (!extract_decreases_clauses || not !extract_template_decreases_clauses);
  (* Sanity check: -backward-no-state-update ==> -state *)
  assert ((not !backward_no_state_update) || !use_state);
  (* Sanity check: the use of decrease clauses is not compatible with the use of fuel *)
  assert (
    (not !use_fuel)
    || (not !extract_decreases_clauses)
       && not !extract_template_decreases_clauses);
  (* We have: not generate_lib_entry_point ==> split_files *)
  assert (!split_files || !generate_lib_entry_point);
  if !lean_gen_lakefile && not (!backend = Lean) then
    log#error
      "The -lean-default-lakefile option is valid only for the Lean backend";

  (* Check that the user specified a backend *)
  let _ =
    match !opt_backend with
    | Some b -> backend := b
    | None ->
        log#error "Backend not specified (use the `-backend` argument)";
        fail ()
  in

  (* Set some options depending on the backend *)
  let _ =
    match !backend with
    | FStar ->
        (* Some patterns are not supported *)
        decompose_monadic_let_bindings := false;
        decompose_nested_let_patterns := false;
        (* F* can disambiguate the field names *)
        record_fields_short_names := true
    | Coq ->
        (* Some patterns are not supported *)
        decompose_monadic_let_bindings := true;
        decompose_nested_let_patterns := true
    | Lean ->
        (* We don't support fuel for the Lean backend *)
        if !use_fuel then (
          log#error "The Lean backend doesn't support the -use-fuel option";
          fail ());
        (* Lean can disambiguate the field names *)
        record_fields_short_names := true
    | HOL4 ->
        (* We don't support fuel for the HOL4 backend *)
        if !use_fuel then (
          log#error "The HOL4 backend doesn't support the -use-fuel option";
          fail ())
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

      (* We don't support mutually recursive definitions with decreases clauses in Lean *)
      if
        !backend = Lean && !extract_decreases_clauses
        && List.exists
             (function
               | Aeneas.LlbcAst.FunGroup (RecGroup (_ :: _)) -> true
               | _ -> false)
             m.declarations
      then (
        log#error
          "The Lean backend doesn't support the use of \
           decreasing_by/termination_by clauses with mutually recursive \
           definitions";
        fail ());

      (* Apply the pre-passes *)
      let m = Aeneas.PrePasses.apply_passes m in

      (* Some options for the execution *)

      (* Test the unit functions with the concrete interpreter *)
      if !test_unit_functions then Test.test_unit_functions m;

      (* Translate the functions *)
      Aeneas.Translate.translate_crate filename dest_dir m;

      (* Print total elapsed time *)
      log#linfo
        (lazy
          (Printf.sprintf "Total execution time: %f seconds"
             (Unix.gettimeofday () -. start_time)))
