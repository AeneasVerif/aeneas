(* Paths to use for tests *)
type test_env = { aeneas_path : string; llbc_dir : string }

(* The data for a specific test to run *)
type test_case = {
  name : string;
  backend : string;
  subdir : string;
  extra_aeneas_options : string list;
}

(* Run Aeneas on a specific input with the given options *)
let run_test env case =
  let concat_path = List.fold_left Filename.concat "" in
  let input_file = concat_path [ env.llbc_dir; case.name ] ^ ".llbc" in
  let dest_dir = concat_path [ "tests"; case.backend; case.subdir ] in
  let args =
    [|
      env.aeneas_path; input_file; "-dest"; dest_dir; "-backend"; case.backend;
    |]
  in
  let args = Array.append args (Array.of_list case.extra_aeneas_options) in

  (* Debug arguments *)
  print_string "[test_runner] Running: ";
  Array.iter
    (fun x ->
      print_string x;
      print_string " ")
    args;
  print_endline "";

  (* Run Aeneas *)
  let pid =
    Unix.create_process env.aeneas_path args Unix.stdin Unix.stdout Unix.stderr
  in
  let _ = Unix.waitpid [] pid in
  ()

(* File-specific options *)
let test_options backend test_name =
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
  | _exe_path :: aeneas_path :: llbc_dir :: test_name :: options ->
      let tests_env = { aeneas_path; llbc_dir } in
      (* TODO: reactivate HOL4 once traits are parameterized by their associated types *)
      let backends = [ "coq"; "lean"; "fstar" ] in
      List.iter
        (fun backend ->
          let subdir = test_subdir backend test_name in
          let extra_aeneas_options =
            List.append (test_options backend test_name) options
          in
          let test_case =
            { name = test_name; backend; subdir; extra_aeneas_options }
          in
          run_test tests_env test_case)
        backends
  | _ -> failwith "Incorrect options passed to test runner"
