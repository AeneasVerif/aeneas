(* Paths to use for tests *)
type runner_env = {
  charon_path : string;
  aeneas_path : string;
  llbc_dir : string;
}

module Backend = struct
  type t = Coq | Lean | FStar | HOL4 [@@deriving ord, sexp]

  (* TODO: reactivate HOL4 once traits are parameterized by their associated types *)
  let all = [ Coq; Lean; FStar ]

  let of_string = function
    | "coq" -> Coq
    | "lean" -> Lean
    | "fstar" -> FStar
    | "hol4" -> HOL4
    | backend -> failwith ("Unknown backend: `" ^ backend ^ "`")

  let to_string = function
    | Coq -> "coq"
    | Lean -> "lean"
    | FStar -> "fstar"
    | HOL4 -> "hol4"
end

module BackendMap = Map.Make (Backend)

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

(* File-specific options *)
let aeneas_options_for_test backend test_name =
  let backend = Backend.to_string backend in
  (* TODO: reactivate -test-trans-units for hashmap and hashmap_main *)
  let use_fuel =
    match (backend, test_name) with
    | ( "coq",
        ("arrays" | "betree" | "demo" | "hashmap" | "hashmap_main" | "loops") )
      ->
        true
    | "fstar", "demo" -> true
    | _ -> false
  in
  let options = if use_fuel then "-use-fuel" :: [] else [] in

  let decrease_template_clauses =
    backend = "fstar"
    &&
    match test_name with
    | "arrays" | "betree" | "hashmap" | "hashmap_main" | "loops" | "traits" ->
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
    | _, "betree" ->
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
  let backend = Backend.to_string backend in
  match (backend, test_name) with
  | "lean", "demo" -> "Demo"
  | "lean", _ -> "."
  | _, ("arrays" | "demo" | "hashmap" | "traits") -> test_name
  | _, "betree" -> "betree"
  | _, "hashmap_main" -> "hashmap_on_disk"
  | "hol4", _ -> "misc-" ^ test_name
  | ( _,
      ( "bitwise" | "constants" | "external" | "loops" | "no_nested_borrows"
      | "paper" | "polonius_list" ) ) ->
      "misc"
  | _ -> test_name

(* The data for a specific test input *)
module Input = struct
  type kind = SingleFile | Crate

  type t = {
    name : string;
    path : string;
    kind : kind;
    charon_options : string list;
    aeneas_options : string list BackendMap.t;
    subdir : string BackendMap.t;
  }

  let build (path : string) : t =
    let name = Filename.remove_extension (Filename.basename path) in
    let kind =
      if Sys_unix.is_file_exn path then SingleFile
      else if Sys_unix.is_directory_exn path then Crate
      else failwith ("`" ^ path ^ "` is not a file or a directory.")
    in
    let charon_options = charon_options_for_test name in
    let subdir =
      List.fold_left
        (fun map backend ->
          let subdir = test_subdir backend name in
          BackendMap.add backend subdir map)
        BackendMap.empty Backend.all
    in
    let aeneas_options =
      List.fold_left
        (fun map backend ->
          let opts = aeneas_options_for_test backend name in
          BackendMap.add backend opts map)
        BackendMap.empty Backend.all
    in
    { path; name; kind; charon_options; subdir; aeneas_options }
end

(* Run Aeneas on a specific input with the given options *)
let run_aeneas (env : runner_env) (case : Input.t) (backend : Backend.t) =
  (* FIXME: remove this special case *)
  let test_name = if case.name = "betree" then "betree_main" else case.name in
  let input_file = concat_path [ env.llbc_dir; test_name ] ^ ".llbc" in
  let subdir = BackendMap.find backend case.subdir in
  let aeneas_options = BackendMap.find backend case.aeneas_options in
  let backend_str = Backend.to_string backend in
  let dest_dir = concat_path [ "tests"; backend_str; subdir ] in
  let args =
    [|
      env.aeneas_path; input_file; "-dest"; dest_dir; "-backend"; backend_str;
    |]
  in
  let args = Array.append args (Array.of_list aeneas_options) in
  (* Run Aeneas *)
  run_command args

(* Run Charon on a specific input with the given options *)
let run_charon (env : runner_env) (case : Input.t) =
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
      let args = Array.append args (Array.of_list case.charon_options) in
      (* Run Charon on the rust file *)
      run_command args
  | Crate -> (
      match Sys.getenv_opt "IN_CI" with
      | None ->
          let args = [| env.charon_path; "--dest"; env.llbc_dir |] in
          let args = Array.append args (Array.of_list case.charon_options) in
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

let () =
  match Array.to_list Sys.argv with
  (* Ad-hoc argument passing for now. *)
  | _exe_path :: charon_path :: aeneas_path :: llbc_dir :: test_path
    :: aeneas_options ->
      let runner_env = { charon_path; aeneas_path; llbc_dir } in
      let test_case = Input.build test_path in
      let test_case =
        {
          test_case with
          aeneas_options =
            BackendMap.map (List.append aeneas_options) test_case.aeneas_options;
        }
      in

      (* Generate the llbc file *)
      run_charon runner_env test_case;
      (* Process the llbc file for the each backend *)
      List.iter
        (fun backend -> run_aeneas runner_env test_case backend)
        Backend.all
  | _ -> failwith "Incorrect options passed to test runner"
