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
     TODO: remove
  *)
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  main_log#set_level EL.Info;
  llbc_of_json_logger#set_level EL.Info;
  regions_hierarchy_log#set_level EL.Info;
  pre_passes_log#set_level EL.Info;
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
  symbolic_to_pure_types_log#set_level EL.Info;
  symbolic_to_pure_values_log#set_level EL.Info;
  symbolic_to_pure_expressions_log#set_level EL.Info;
  symbolic_to_pure_log#set_level EL.Info;
  pure_micro_passes_log#set_level EL.Info;
  simplify_aggregates_unchanged_fields_log#set_level EL.Info;
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

let matches_name (c : crate) (name : Types.name)
    (m : 'a ExtractName.NameMatcherMap.t) : bool =
  let mctx = Charon.NameMatcher.ctx_from_crate c in
  let open ExtractBuiltin in
  NameMatcherMap.mem mctx name m

let matches_name_with_generics (c : crate) (name : Types.name)
    (generics : Types.generic_args) (m : 'a ExtractName.NameMatcherMap.t) : bool
    =
  let mctx = Charon.NameMatcher.ctx_from_crate c in
  let open ExtractBuiltin in
  Option.is_some (NameMatcherMap.find_with_generics_opt mctx name generics m)

let activated_loggers : (EL.level * string) list ref = ref []

let add_activated_loggers level (name_list : string) =
  let names = String.split_on_char ',' name_list in
  activated_loggers := List.map (fun n -> (level, n)) names @ !activated_loggers

let marked_ids : string list ref = ref []

let add_marked_ids (ids : string) =
  let ids = String.split_on_char ',' ids in
  marked_ids := ids @ !marked_ids

let () =
  (* Measure start time *)
  let start_time = Unix.gettimeofday () in

  (* Read the command line arguments *)
  let dest_dir = ref "" in

  (* Print the imported llbc *)
  let print_llbc = ref false in

  let spec_ls =
    [
      ( "-print-error-emitters",
        Arg.Set print_error_emitters,
        " Whenever reporting an error, print the span of the source code of \
         Aeneas which emitted the error" );
      ( "-borrow-check",
        Arg.Set borrow_check,
        " Only borrow-check the program and do not generate any translation" );
      ( "-backend",
        Arg.Symbol (backend_names, set_backend),
        " Specify the target backend (" ^ String.concat ", " backend_names ^ ")"
      );
      ( "-namespace",
        Arg.String set_namespace,
        " Set the namespace of the definitions in the pure model" );
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
      ( "-subdir",
        Arg.String set_subdir,
        " Extract the files in a sub-folder; this option has an impact on the \
         import paths of the generated files" );
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
      ( "-backward-state-update",
        Arg.Set backward_state_update,
        " Generate backward functions which update the state. THIS OPTION IS \
         DEPRECATED." );
      ( "-no-template-clauses",
        Arg.Clear extract_template_decreases_clauses,
        " Do not generate templates for the required decreases \
         clauses/termination measures, in a dedicated file, if you also put \
         the option -decreases-clauses" );
      ( "-split-files",
        Arg.Set split_files,
        " Split the definitions between different files for types, functions, \
         etc." );
      ( "-checks",
        Arg.Set sanity_checks,
        " Activate extensive sanity checks (warning: causes a ~100 times slow \
         down)." );
      ( "-gen-lib-entry",
        Arg.Set generate_lib_entry_point,
        " Add an entry point file to the generated library (only valid if the \
         crate is split between different files)" );
      ( "-lean-default-lakefile",
        Arg.Clear lean_gen_lakefile,
        " Generate a default lakefile.lean (Lean only)" );
      ("-print-llbc", Arg.Set print_llbc, " Print the imported LLBC");
      ( "-abort-on-error",
        Arg.Set fail_hard,
        " Abort on the first encountered error" );
      ( "-soft-warnings",
        Arg.Clear warnings_as_errors,
        " Do not treat warnings as errors" );
      ( "-tuple-nested-proj",
        Arg.Set use_nested_tuple_projectors,
        " Use nested projectors for tuples (e.g., (0, 1, 2).snd.fst instead of \
         (0, 1, 2).1)." );
      ( "-print-unknown-externals",
        Arg.Set print_unknown_externals,
        " Print all the external definitions which are not listed in the \
         builtin functions" );
      ( "-log",
        Arg.String (add_activated_loggers EL.Trace),
        " Activate trace log for a given logger designated by its name. It is \
         possible to specifiy a list of names if they are separated by commas \
         without spaces; for instance: '-log Interpreter,SymbolicToPure'. The \
         existing loggers are: {"
        ^ String.concat ", " (Collections.StringMap.keys !loggers)
        ^ "}" );
      ( "-log-debug",
        Arg.String (add_activated_loggers EL.Debug),
        " Same as '-log' but sets the level to the more verbose 'debug' rather \
         than 'trace'" );
      ( "-mark-ids",
        Arg.String add_marked_ids,
        " For developers: mark some identifiers to throw an exception if we \
         generate them; this is useful to insert breakpoints when debugging by \
         using the log. For example, one can mark the symbolic value ids 1 and \
         2 with '-mark-ids s1,s2', or '-mark-ids s@1, s@2. The supported \
         prefixes are: 's' (symbolic value id), 'b' (borrow id), 'a' \
         (abstraction id), 'r' (region id), 'f' (pure free variable id)." );
    ]
  in

  let spec = Arg.align spec_ls in
  let filenames = ref [] in
  let add_filename f = filenames := f :: !filenames in
  Arg.parse spec add_filename usage;
  let fail (print_doc : bool) =
    if print_doc then print_string usage;
    exit 1
  in

  (* Small helper to check the validity of the input arguments and print
     an error if necessary *)
  let check_arg_name name =
    assert (List.exists (fun (n, _, _) -> n = name) spec_ls)
  in

  let fail_with_error (msg : string) =
    log#serror msg;
    fail true
  in
  let fail_with_error_no_doc (msg : string) =
    log#serror msg;
    fail false
  in

  let check_arg_implies (arg0 : bool) (name0 : string) (arg1 : bool)
      (name1 : string) : unit =
    check_arg_name name0;
    check_arg_name name1;
    if (not arg0) || arg1 then ()
    else (
      log#error "Invalid command-line arguments: the use of %s requires %s"
        name0 name1;
      fail true)
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
      fail true)
  in

  let check (cond : bool) (msg : string) =
    if not cond then fail_with_error msg
  in
  let check_no_doc (cond : bool) (msg : string) =
    if not cond then fail_with_error_no_doc msg
  in

  let check_not (cond : bool) (msg : string) =
    if cond then fail_with_error msg
  in

  (* Activate the loggers *)
  let activated_loggers_set = ref Collections.StringSet.empty in
  List.iter
    (fun (level, name) ->
      match Collections.StringMap.find_opt name !loggers with
      | None ->
          log#serror
            ("The logger '" ^ name
           ^ "' does not exist. The existing loggers are: {"
            ^ String.concat ", " (Collections.StringMap.keys !loggers)
            ^ "}");
          fail false
      | Some logger ->
          (* Check that we haven't activated the logger twice *)
          if Collections.StringSet.mem name !activated_loggers_set then begin
            log#serror
              ("The logger '" ^ name
             ^ "' is used twice in the '-log' and/or '-log-debug' option(s)");
            fail false
          end
          else begin
            activated_loggers_set :=
              Collections.StringSet.add name !activated_loggers_set;
            logger#set_level level
          end)
    !activated_loggers;

  (* Properly register the marked ids *)
  List.iter
    (fun id ->
      let i = if String.length id >= 2 && String.get id 1 = '@' then 2 else 1 in
      let sub = String.sub id i (String.length id - i) in
      match int_of_string_opt sub with
      | None ->
          log#serror
            ("Invalid identifier provided to option `-mark-ids`: '" ^ id
           ^ "': '" ^ sub ^ "' can't be parsed as an int");
          fail false
      | Some i -> (
          let open ContextsBase in
          match String.get id 0 with
          | 's' -> marked_symbolic_value_ids_insert_from_int i
          | 'b' -> marked_borrow_ids_insert_from_int i
          | 'a' -> marked_abstraction_ids_insert_from_int i
          | 'r' -> marked_region_ids_insert_from_int i
          | 'f' -> Pure.marked_fvar_ids_insert_from_int i
          | _ ->
              log#serror
                ("Invalid identifier provided to option: '" ^ id
               ^ "': the first character should be in {'s', 'b', 'a', 'r'}");
              fail false))
    !marked_ids;

  (* Sanity check (now that the arguments are parsed!) *)
  check_arg_implies
    (not !extract_template_decreases_clauses)
    "-no-template-clauses" !extract_decreases_clauses "-decreases-clauses";
  if not !extract_decreases_clauses then
    extract_template_decreases_clauses := false;
  (* Sanity check: -backward-state-update ==> -state *)
  check_arg_implies !backward_state_update "-backward-state-update" !use_state
    "-state";
  (* Sanity check: the use of decrease clauses is not compatible with the use of fuel *)
  check_arg_not !use_fuel "-use-fuel" !extract_decreases_clauses
    "-decreases-clauses";
  check_arg_implies !generate_lib_entry_point "-gen-lib-entry" !split_files
    "-split-files";
  check_arg_not !generate_lib_entry_point "-gen-lib-entry"
    (Option.is_some !subdir) "-subdir";
  if !lean_gen_lakefile && not (backend () = Lean) then
    fail_with_error
      "The -lean-default-lakefile option is valid only for the Lean backend";
  if !borrow_check then (
    check (!dest_dir = "") "Options -borrow-check and -dest are not compatible";
    check_not !split_files
      "Options -borrow-check and -split-files are not compatible";
    check_not !test_unit_functions
      "Options -borrow-check and -test-unit-functions are not compatible";
    check_not !test_trans_unit_functions
      "Options -borrow-check and -test-trans-units are not compatible";
    check_not !extract_decreases_clauses
      "Options -borrow-check and -decreases-clauses are not compatible";
    check_not !use_state
      "Options -borrow-check and -use-state are not compatible";
    check_not !use_fuel "Options -borrow-check and -use-fuel are not compatible";
    check_not !split_files
      "Options -borrow-check and -split-files are not compatible");

  (* Check that the user specified a backend *)
  let _ =
    match !opt_backend with
    | Some _ ->
        check_not !borrow_check
          "Arguments `-backend` and `-borrow-check` are not compatible"
    | None ->
        check !borrow_check "Missing `-backend` or `-borrow-check` argument"
  in

  (* Set some options depending on the backend *)
  let _ =
    match !opt_backend with
    | None -> ()
    | Some backend -> (
        match backend with
        | FStar ->
            (* F* can disambiguate the field names *)
            record_fields_short_names := true;
            (* Introducing [massert] leads to type inferencing issues *)
            intro_massert := false
        | Coq ->
            (* Some patterns are not supported *)
            decompose_monadic_let_bindings := true;
            decompose_nested_let_patterns := true
        | Lean ->
            (* We don't support fuel for the Lean backend *)
            check_not !use_fuel
              "The Lean backend doesn't support the -use-fuel option";
            (* Lean can disambiguate the field names *)
            record_fields_short_names := true;
            (* We exploit the fact that the variant name should always be
               prefixed with the type name to prevent collisions *)
            variant_concatenate_type_name := false;
            (* *) merge_let_app_decompose_tuple := true;
            lift_pure_function_calls := true
        | HOL4 ->
            (* We don't support fuel for the HOL4 backend *)
            if !use_fuel then (
              log#error "The HOL4 backend doesn't support the -use-fuel option";
              fail true))
  in

  (* Retrieve and check the filename *)
  let filename =
    match !filenames with
    | [ f ] ->
        (* TODO: update the extension *)
        if not (Filename.check_suffix f ".llbc") then (
          print_string ("Unrecognized file extension: " ^ f ^ "\n");
          fail true)
        else if not (Sys.file_exists f) then (
          print_string ("File not found: " ^ f ^ "\n");
          fail true)
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
      if !print_llbc then
        log#linfo (lazy ("\n" ^ Print.Crate.crate_to_string m ^ "\n"))
      else log#ldebug (lazy ("\n" ^ Print.Crate.crate_to_string m ^ "\n"));

      (* Check that Charon was called with the `--preset=aeneas` option *)
      check_no_doc
        (m.options.preset = Some Aeneas)
        "Invalid option detected: the serialized crate was generated by Charon \
         without the `--preset=aeneas` option. Please regenerate the crate by \
         calling Charon with `--preset=aeneas`.\n";

      (* We don't support mutually recursive definitions with decreases clauses in Lean *)
      if
        !opt_backend = Some Lean && !extract_decreases_clauses
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
        fail true);

      (* Print the external definitions which are not listed in the builtin functions *)
      if !print_unknown_externals then (
        let open TranslateCore in
        let { type_decls; fun_decls; global_decls; trait_decls; trait_impls; _ }
            =
          m
        in
        (* Filter the definitions *)
        let type_decls =
          Types.TypeDeclId.Map.filter
            (fun _ (d : Types.type_decl) ->
              let names_map = ExtractBuiltin.builtin_types_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name names_map))
            type_decls
        in
        let fun_decls =
          LlbcAst.FunDeclId.Map.filter
            (fun _ (d : LlbcAst.fun_decl) ->
              let names_map = ExtractBuiltin.builtin_funs_map () in
              (not d.item_meta.is_local)
              && (not (matches_name m d.item_meta.name names_map))
              (* We also ignore the trait method declarations *)
              &&
              match d.kind with
              | TraitDeclItem _ -> false
              | _ -> true)
            fun_decls
        in
        let global_decls =
          LlbcAst.GlobalDeclId.Map.filter
            (fun _ (d : LlbcAst.global_decl) ->
              let globals_map = ExtractBuiltin.builtin_globals_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name globals_map))
            global_decls
        in
        let trait_decls =
          LlbcAst.TraitDeclId.Map.filter
            (fun _ (d : LlbcAst.trait_decl) ->
              let names_map = ExtractBuiltin.builtin_trait_decls_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name names_map))
            trait_decls
        in
        let trait_impls =
          List.filter_map
            (fun (d : LlbcAst.trait_impl) ->
              let names_map = ExtractBuiltin.builtin_trait_impls_map () in
              match
                LlbcAst.TraitDeclId.Map.find_opt d.impl_trait.id m.trait_decls
              with
              | None -> None (* Just ignore it *)
              | Some trait_decl ->
                  if
                    (not d.item_meta.is_local)
                    && not
                         (matches_name_with_generics m trait_decl.item_meta.name
                            d.impl_trait.generics names_map)
                  then Some (d, trait_decl)
                  else None)
            (LlbcAst.TraitImplId.Map.values trait_impls)
        in
        (* Print *)
        let fmt_env = Print.Crate.crate_to_fmt_env m in
        let type_decls =
          List.map
            (fun (d : Types.type_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Type decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.type_decl_to_string fmt_env d)
            (Types.TypeDeclId.Map.values type_decls)
        in
        let fun_decls =
          List.map
            (fun (d : LlbcAst.fun_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              let d =
                (* FIXME: there is a bug in the formatter when splitting the predicates
                   and trait clauses between the inherited ones and the others (the
                   index is sometimes out of bounds).
                   See: https://github.com/AeneasVerif/charon/issues/482
                *)
                try Print.Ast.fun_decl_to_string fmt_env "" "  " d
                with _ -> "UNKNOWN"
              in
              "Fun decl (pattern: [" ^ pattern ^ "]]):\n" ^ d)
            (LlbcAst.FunDeclId.Map.values fun_decls)
        in
        let global_decls =
          List.map
            (fun (d : LlbcAst.global_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Global decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.Ast.global_decl_to_string fmt_env "" "  " d)
            (LlbcAst.GlobalDeclId.Map.values global_decls)
        in
        let trait_decls =
          List.map
            (fun (d : LlbcAst.trait_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Trait decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.Ast.trait_decl_to_string fmt_env "" "  " d)
            (LlbcAst.TraitDeclId.Map.values trait_decls)
        in
        let trait_impls =
          List.map
            (fun ((d, trait_decl) : LlbcAst.trait_impl * LlbcAst.trait_decl) ->
              let pattern =
                LlbcAstUtils.trait_impl_with_crate_to_pattern_string
                  (Some d.item_meta.span) m trait_decl d
              in
              "Trait impl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.Ast.trait_impl_to_string fmt_env "" "  " d)
            trait_impls
        in

        log#linfo
          (lazy
            (String.concat "\n\n"
               (type_decls @ fun_decls @ global_decls @ trait_decls
              @ trait_impls)));
        ());

      (* Apply the pre-passes *)
      let m = Aeneas.PrePasses.apply_passes m in

      (* Test the unit functions with the concrete interpreter *)
      if !test_unit_functions then Test.test_unit_functions m;

      (* Translate or borrow-check the crate *)
      if !borrow_check then Aeneas.BorrowCheck.borrow_check_crate m
      else Aeneas.Translate.translate_crate filename dest_dir !Config.subdir m;

      if !Errors.error_list <> [] then (
        List.iter
          (fun (file, line, span, msg) ->
            if !print_error_emitters then
              log#serror
                (Errors.format_error_message_with_file_line file line span msg)
            else log#serror (Errors.format_error_message span msg))
          (* Reverse the list of error messages so that we print them from the
             earliest to the latest. *)
          (List.rev !Errors.error_list);
        exit 1)
      else if !borrow_check then
        log#linfo (lazy "Crate successfully borrow-checked");

      (* Print total elapsed time *)
      log#linfo
        (lazy
          (Printf.sprintf "Total execution time: %f seconds"
             (Unix.gettimeofday () -. start_time)))
