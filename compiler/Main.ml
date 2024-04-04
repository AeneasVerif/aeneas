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
  builtin_log#set_level EL.Info;
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

  let spec_ls =
    [
      ( "-backend",
        Arg.Symbol (backend_names, set_backend),
        " Specify the target backend" );
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
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
      ( "-checks",
        Arg.Set sanity_checks,
        " Activate extensive sanity checks (warning: causes a ~100 times slow \
         down)." );
      ( "-no-gen-lib-entry",
        Arg.Clear generate_lib_entry_point,
        " Do not generate the entry point file for the generated library (only \
         valid if the crate is split between different files)" );
      ( "-lean-default-lakefile",
        Arg.Clear lean_gen_lakefile,
        " Generate a default lakefile.lean (Lean only)" );
      ("-print-llbc", Arg.Set print_llbc, " Print the imported LLBC");
      ( "-abort-on-error",
        Arg.Set fail_hard,
        "Abort on the first encountered error" );
      ( "-tuple-nested-proj",
        Arg.Set use_nested_tuple_projectors,
        " Use nested projectors for tuples (e.g., (0, 1).snd.fst instead of \
         (0, 1).1)." );
    ]
  in

  let spec = Arg.align spec_ls in
  let filenames = ref [] in
  let add_filename f = filenames := f :: !filenames in
  Arg.parse spec add_filename usage;
  let fail () =
    print_string usage;
    exit 1
  in

  (* Small helper to check the validity of the input arguments and print
     an error if necessary *)
  let check_arg_name name =
    assert (List.exists (fun (n, _, _) -> n = name) spec_ls)
  in
  let check_arg_implies (arg0 : bool) (name0 : string) (arg1 : bool)
      (name1 : string) : unit =
    check_arg_name name0;
    check_arg_name name1;
    if (not arg0) || arg1 then ()
    else (
      log#error "Invalid command-line arguments: the use of %s requires %s"
        name0 name1;
      fail ())
  in

  let check_arg_not (arg0 : bool) (name0 : string) (arg1 : bool)
      (name1 : string) : unit =
    check_arg_name name0;
    check_arg_name name1;
    if (not arg0) || not arg1 then ()
    else (
      log#error
        "Invalid command-line arguments: the use of %s is incompatible with %s"
        name0 name1;
      fail ())
  in

  if !print_llbc then main_log#set_level EL.Debug;

  (* Sanity check (now that the arguments are parsed!): -template-clauses ==> decrease-clauses *)
  check_arg_implies
    !extract_template_decreases_clauses
    "-template-clauses" !extract_decreases_clauses "-decreases-clauses";
  (* Sanity check: -backward-no-state-update ==> -state *)
  check_arg_implies !backward_no_state_update "-backward-no-state-update"
    !use_state "-state";
  (* Sanity check: the use of decrease clauses is not compatible with the use of fuel *)
  check_arg_not !use_fuel "-use-fuel" !extract_decreases_clauses
    "-decreases-clauses";
  (* We have: not generate_lib_entry_point ==> split_files *)
  check_arg_implies
    (not !generate_lib_entry_point)
    "-no-gen-lib-entry" !split_files "-split-files";
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
        record_fields_short_names := true;
        (* We exploit the fact that the variant name should always be
           prefixed with the type name to prevent collisions *)
        variant_concatenate_type_name := false
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

      (* There may be exceptions to catch *)
      (try
         (* Apply the pre-passes *)
         let m = Aeneas.PrePasses.apply_passes m in

         (* Test the unit functions with the concrete interpreter *)
         if !test_unit_functions then Test.test_unit_functions m;

         (* Translate the functions *)
         Aeneas.Translate.translate_crate filename dest_dir m
       with Errors.CFailure (_, _) ->
         (* In theory it shouldn't happen, but there may be uncaught errors -
            note that we let the [Failure] exceptions go through (they are
            send if we use the option [-abort-on-error] *)
         if not (List.is_empty !Errors.error_list) then (
           let errors = Errors.error_list_to_string !Errors.error_list in
           log#serror errors;
           exit 1));

      (* Print total elapsed time *)
      log#linfo
        (lazy
          (Printf.sprintf "Total execution time: %f seconds"
             (Unix.gettimeofday () -. start_time)))
