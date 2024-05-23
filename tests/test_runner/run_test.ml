(* Paths to use for tests *)
type aeneas_env = { aeneas_path : string; llbc_dir : string }

type charon_env = {
  charon_path : string;
  inputs_dir : string;
  llbc_dir : string;
}

(* The data for a specific test to run aeneas on *)
type aeneas_test_case = {
  name : string;
  backend : string;
  subdir : string;
  extra_aeneas_options : string list;
}

(* The data for a specific test to generate llbc for *)
type charon_test_case = { name : string; extra_charon_options : string list }

let concat_path = List.fold_left Filename.concat ""

let run_command args =
  (* Debug arguments *)
  print_string "[test_runner] Running: ";
  Array.iter
    (fun x ->
      print_string x;
      print_string " ")
    args;
  print_endline "";

  (* Run the command *)
  let pid =
    Unix.create_process args.(0) args Unix.stdin Unix.stdout Unix.stderr
  in
  let _ = Unix.waitpid [] pid in
  ()

(* Run Aeneas on a specific input with the given options *)
let run_aeneas (env : aeneas_env) (case : aeneas_test_case) =
  let input_file = concat_path [ env.llbc_dir; case.name ] ^ ".llbc" in
  let dest_dir = concat_path [ "tests"; case.backend; case.subdir ] in
  let args =
    [|
      env.aeneas_path; input_file; "-dest"; dest_dir; "-backend"; case.backend;
    |]
  in
  let args = Array.append args (Array.of_list case.extra_aeneas_options) in
  (* Run Aeneas *)
  run_command args

(* Run Charon on a specific input with the given options *)
let run_charon (env : charon_env) (case : charon_test_case) =
  let input_crate = concat_path [ env.inputs_dir; case.name ] in
  let input_file = input_crate ^ ".rs" in
  if Sys.file_exists input_file then
    let args =
      [|
        env.charon_path;
        "--no-cargo";
        "--input";
        input_file;
        "--crate";
        case.name;
        "--dest";
        env.llbc_dir;
      |]
    in
    let args = Array.append args (Array.of_list case.extra_charon_options) in
    (* Run Charon on the rust file *)
    run_command args
  else if Sys.file_exists input_crate then
    match Sys.getenv_opt "IN_CI" with
    | None ->
        let args = [| env.charon_path; "--dest"; env.llbc_dir |] in
        let args =
          Array.append args (Array.of_list case.extra_charon_options)
        in
        (* Run Charon inside the crate *)
        Unix.chdir input_crate;
        run_command args
    | Some _ ->
        (* Crates with dependencies must be generated separately in CI. We skip
           here and trust that CI takes care to generate the necessary llbc
           file. *)
        print_endline
          "Warn: IN_CI is set; we skip generating llbc files for whole crates"
  else failwith ("Neither " ^ input_file ^ " nor " ^ input_crate ^ " exist.")

(* File-specific options *)
let aeneas_options_for_test backend test_name =
  (* TODO: reactivate -test-trans-units for hashmap and hashmap_main *)
  let use_fuel =
    match (backend, test_name) with
    | ( "coq",
        ( "arrays" | "betree_main" | "demo" | "hashmap" | "hashmap_main"
        | "loops" ) ) ->
        true
    | "fstar", "demo" -> true
    | _ -> false
  in
  let options = if use_fuel then "-use-fuel" :: [] else [] in

  let decrease_template_clauses =
    backend = "fstar"
    &&
    match test_name with
    | "arrays" | "betree_main" | "hashmap" | "hashmap_main" | "loops" | "traits"
      ->
        true
    | _ -> false
  in
  let options =
    if decrease_template_clauses then
      "-decreases-clauses" :: "-template-clauses" :: options
    else options
  in

  let extra_options =
    match (backend, test_name) with
    | _, "betree_main" ->
        [
          "-backward-no-state-update";
          "-test-trans-units";
          "-state";
          "-split-files";
        ]
    | _, "bitwise" -> [ "-test-trans-units" ]
    | _, "constants" -> [ "-test-trans-units" ]
    | _, "external" -> [ "-test-trans-units"; "-state"; "-split-files" ]
    | _, "hashmap_main" -> [ "-state"; "-split-files" ]
    | _, "no_nested_borrows" -> [ "-test-trans-units" ]
    | _, "paper" -> [ "-test-trans-units" ]
    | _, "polonius_list" -> [ "-test-trans-units" ]
    | "fstar", "arrays" -> [ "-split-files" ]
    | "fstar", "loops" -> [ "-split-files" ]
    (* We add a custom import in the Hashmap.lean file: we do not want to overwrite it *)
    | "lean", "hashmap" -> [ "-split-files"; "-no-gen-lib-entry" ]
    | _, "hashmap" -> [ "-split-files" ]
    | _ -> []
  in
  let options = List.append extra_options options in
  options

(* File-specific options *)
let charon_options_for_test test_name =
  (* Possible to add `--no-code-duplication` for `hashmap_main` if we use the optimized MIR *)
  let no_code_dup =
    match test_name with
    | "constants" | "external" | "nested_borrows" | "no_nested_borrows"
    | "paper" ->
        [ "--no-code-duplication" ]
    | _ -> []
  in
  let extra_options =
    (* $(LLBC_DIR)/betree_main.llbc: CHARON_OPTIONS += --polonius --opaque=betree_utils --crate betree_main *)
    match test_name with
    | "betree_main" ->
        [ "--polonius"; "--opaque=betree_utils"; "--crate"; "betree_main" ]
    | "hashmap_main" -> [ "--opaque=hashmap_utils" ]
    | "polonius_list" -> [ "--polonius" ]
    | _ -> []
  in
  List.append no_code_dup extra_options

(* The subdirectory in which to store the outputs. *)
(* This reproduces the file layout that was set by the old Makefile. FIXME: cleanup *)
let test_subdir backend test_name =
  match (backend, test_name) with
  | "lean", "demo" -> "Demo"
  | "lean", _ -> "."
  | _, ("arrays" | "demo" | "hashmap" | "traits") -> test_name
  | _, "betree_main" -> "betree"
  | _, "hashmap_main" -> "hashmap_on_disk"
  | "hol4", _ -> "misc-" ^ test_name
  | ( _,
      ( "bitwise" | "constants" | "external" | "loops" | "no_nested_borrows"
      | "paper" | "polonius_list" ) ) ->
      "misc"
  | _ -> test_name

let () =
  match Array.to_list Sys.argv with
  (* Ad-hoc argument passing for now. *)
  | _exe_path :: "aeneas" :: aeneas_path :: llbc_dir :: test_name :: options ->
      let tests_env = { aeneas_path; llbc_dir } in
      (* TODO: reactivate HOL4 once traits are parameterized by their associated types *)
      let backends = [ "coq"; "lean"; "fstar" ] in
      List.iter
        (fun backend ->
          let subdir = test_subdir backend test_name in
          let extra_aeneas_options =
            List.append (aeneas_options_for_test backend test_name) options
          in
          let test_case =
            { name = test_name; backend; subdir; extra_aeneas_options }
          in
          run_aeneas tests_env test_case)
        backends
  | _exe_path :: "charon" :: charon_path :: inputs_dir :: llbc_dir :: test_name
    :: options ->
      let tests_env = { charon_path; inputs_dir; llbc_dir } in
      let extra_charon_options =
        List.append (charon_options_for_test test_name) options
      in
      (* FIXME: remove this special case *)
      let test_name =
        if test_name = "betree_main" then "betree" else test_name
      in
      let test_case = { name = test_name; extra_charon_options } in
      run_charon tests_env test_case
  | _ -> failwith "Incorrect options passed to test runner"
