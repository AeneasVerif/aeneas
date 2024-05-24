(* Paths to use for tests *)
type runner_env = {
  charon_path : string;
  aeneas_path : string;
  llbc_dir : string;
}

(* The data for a specific test to run aeneas on *)
type aeneas_test_case = {
  name : string;
  backend : string;
  subdir : string;
  extra_aeneas_options : string list;
}

type input_kind = SingleFile | Crate

(* The data for a specific test to generate llbc for *)
type charon_test_case = {
  kind : input_kind;
  name : string;
  path : string;
  extra_charon_options : string list;
}

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
let run_aeneas (env : runner_env) (case : aeneas_test_case) =
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
let run_charon (env : runner_env) (case : charon_test_case) =
  match case.kind with
  | SingleFile ->
      let args =
        [|
          env.charon_path;
          "--no-cargo";
          "--input";
          case.path;
          "--crate";
          case.name;
          "--dest";
          env.llbc_dir;
        |]
      in
      let args = Array.append args (Array.of_list case.extra_charon_options) in
      (* Run Charon on the rust file *)
      run_command args
  | Crate -> (
      match Sys.getenv_opt "IN_CI" with
      | None ->
          let args = [| env.charon_path; "--dest"; env.llbc_dir |] in
          let args =
            Array.append args (Array.of_list case.extra_charon_options)
          in
          (* Run Charon inside the crate *)
          let old_pwd = Unix.getcwd () in
          Unix.chdir case.path;
          run_command args;
          Unix.chdir old_pwd
      | Some _ ->
          (* Crates with dependencies must be generated separately in CI. We skip
             here and trust that CI takes care to generate the necessary llbc
             file. *)
          print_endline
            "Warn: IN_CI is set; we skip generating llbc files for whole crates"
      )

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
    match test_name with
    | "betree" ->
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
  | _exe_path :: charon_path :: aeneas_path :: llbc_dir :: test_path
    :: aeneas_options ->
      let runner_env = { charon_path; aeneas_path; llbc_dir } in
      let test_name = Filename.remove_extension (Filename.basename test_path) in

      let charon_kind =
        if Sys_unix.is_file_exn test_path then SingleFile
        else if Sys_unix.is_directory_exn test_path then Crate
        else failwith ("`" ^ test_path ^ "` is not a file or a directory.")
      in
      let extra_charon_options = charon_options_for_test test_name in
      let charon_case =
        {
          path = test_path;
          name = test_name;
          kind = charon_kind;
          extra_charon_options;
        }
      in
      (* Generate the llbc file *)
      run_charon runner_env charon_case;

      (* FIXME: remove this special case *)
      let test_name =
        if test_name = "betree" then "betree_main" else test_name
      in
      (* TODO: reactivate HOL4 once traits are parameterized by their associated types *)
      let backends = [ "coq"; "lean"; "fstar" ] in
      List.iter
        (fun backend ->
          let subdir = test_subdir backend test_name in
          let extra_aeneas_options =
            List.append
              (aeneas_options_for_test backend test_name)
              aeneas_options
          in
          let aeneas_case =
            { name = test_name; backend; subdir; extra_aeneas_options }
          in
          (* Process the llbc file for the current backend *)
          run_aeneas runner_env aeneas_case)
        backends
  | _ -> failwith "Incorrect options passed to test runner"
