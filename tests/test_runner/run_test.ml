(* Paths to use for tests *)
type runner_env = {
  charon_path : string;
  aeneas_path : string;
  llbc_dir : string;
  dest_dir : string;
}

let concat_path = List.fold_left Filename.concat ""

module Command = struct
  type t = { args : string array; redirect_out : Unix.file_descr option }
  type status = Success | Failure

  let make (args : string list) : t =
    { args = Array.of_list args; redirect_out = None }

  let to_string (cmd : t) = Core.String.concat_array ~sep:" " cmd.args

  (* Run the command and returns its exit status. *)
  let run (cmd : t) : status =
    let command_str = to_string cmd in
    print_endline ("[test_runner] Running: " ^ command_str);

    (* Run the command *)
    let out = Option.value cmd.redirect_out ~default:Unix.stdout in
    let pid =
      Unix.create_process cmd.args.(0) cmd.args Unix.stdin out Unix.stderr
    in
    let status = Core_unix.waitpid (Core.Pid.of_int pid) in
    match status with
    | Ok () -> Success
    | Error (`Exit_non_zero _) -> Failure
    | Error (`Signal _) ->
        failwith ("Command `" ^ command_str ^ "` exited incorrectly.")

  (* Run the command and aborts the program if the command failed. *)
  let run_command_expecting_success cmd =
    match run cmd with
    | Success -> ()
    | Failure -> failwith ("Command `" ^ to_string cmd ^ "` failed.")

  (* Run the command and aborts the program if the command succeeded. *)
  let run_command_expecting_failure cmd =
    match run cmd with
    | Success ->
        failwith
          ("Command `" ^ to_string cmd ^ "` succeeded but was expected to fail.")
    | Failure -> ()
end

(* Run Aeneas on a specific input with the given options *)
let run_aeneas (env : runner_env) (case : Input.t) (backend : Backend.t) =
  let backend_str = Backend.to_string backend in
  let backend_command = Backend.to_command backend in
  let input_file = concat_path [ env.llbc_dir; case.name ] ^ ".llbc" in
  let output_file =
    Filename.remove_extension case.path ^ "." ^ backend_str ^ ".out"
  in

  let per_backend = Backend.Map.find backend case.per_backend in
  let subdir = per_backend.subdir in
  let check_output = per_backend.check_output in
  let aeneas_options = per_backend.aeneas_options in
  let action = per_backend.action in
  (* No destination directory if we borrow-check *)
  let dest_command =
    match backend with
    | Backend.BorrowCheck -> []
    | _ ->
        let subdir =
          match subdir with
          | None -> []
          | Some x -> [ x ]
        in
        [ "-dest"; concat_path ([ env.dest_dir; backend_str ] @ subdir) ]
  in

  (* Build the command *)
  let args = [ env.aeneas_path; input_file ] @ dest_command @ backend_command in
  (* Abort on error to help debugging, except for borrow-check failure cases
     where that would be too noisy. *)
  let abort_on_error =
    match action with
    | KnownFailure when backend = Backend.BorrowCheck -> []
    | _ -> [ "-abort-on-error" ]
  in
  let args = List.concat [ args; aeneas_options; abort_on_error ] in
  let cmd = Command.make args in
  (* Remove leftover files if they're not needed anymore *)
  if
    Sys.file_exists output_file
    &&
    match action with
    | Skip | Normal -> true
    | KnownFailure when not check_output -> true
    | _ -> false
  then Sys.remove output_file;
  (* Run Aeneas *)
  match action with
  | Skip -> ()
  | Normal -> Command.run_command_expecting_success cmd
  | KnownFailure ->
      let out =
        if check_output then
          Core_unix.openfile ~mode:[ O_CREAT; O_TRUNC; O_WRONLY ] output_file
        else Core_unix.openfile ~mode:[ O_WRONLY ] "/dev/null"
      in
      let cmd = { cmd with redirect_out = Some out } in
      Command.run_command_expecting_failure cmd;
      Unix.close out

(* Run Charon on a specific input with the given options *)
let run_charon (env : runner_env) (case : Input.t) =
  (* Create the folder for the .llbc files, if it doesn't exist yet *)
  (if not (Sys.file_exists env.llbc_dir) then
     (* Note that the [full_perm] argument is ignored on Windows *)
     let full_perm = 0o777 in
     Sys.mkdir env.llbc_dir full_perm);
  let llbc_name =
    Filename_unix.realpath env.llbc_dir ^ "/" ^ case.name ^ ".llbc"
  in
  match case.kind with
  | SingleFile ->
      let args =
        [
          env.charon_path; "rustc"; "--dest-file"; llbc_name; "--preset=aeneas";
        ]
        @ case.charon_options
        @ [
            "--";
            case.path;
            "--crate-name=" ^ case.name;
            "--crate-type=rlib";
            "--allow=unused";
            "--allow=non_snake_case";
          ]
      in
      (* Run Charon on the rust file *)
      Command.run_command_expecting_success (Command.make args)
  | Crate ->
      (* Because some tests have dependencies which force us to implement custom
         treatment in the flake.nix, when in CI, we regenerate files for the crates
         only if the .llbc doesn't exist (if it exists, it means it was generated
         via a custom derivation in the flake.nix) *)
      let generate =
        match Sys.getenv_opt "IN_CI" with
        | None -> true
        | Some _ -> not (Sys.file_exists llbc_name)
        (* Check if the llbc file already exists *)
      in
      if generate then (
        let args =
          [
            env.charon_path;
            "cargo";
            "--preset=aeneas";
            "--rustc-flag=--allow=unused";
            "--dest-file";
            llbc_name;
          ]
        in
        let args = List.append args case.charon_options in
        (* Run Charon inside the crate *)
        let old_pwd = Unix.getcwd () in
        Unix.chdir case.path;
        Command.run_command_expecting_success (Command.make args);
        Unix.chdir old_pwd)
      else
        print_endline
          ("Warn: crate test \"" ^ case.name
         ^ "\": IN_CI is set and the llbc file already exists; we do not \
            regenerate the llbc file for the crate")

let () =
  match Array.to_list Sys.argv with
  (* Ad-hoc argument passing for now. *)
  | _exe_path :: charon_path :: aeneas_path :: llbc_dir :: test_path
    :: aeneas_options ->
      let runner_env =
        { charon_path; aeneas_path; llbc_dir; dest_dir = "tests" }
      in
      let test_case = Input.build test_path in
      let test_case =
        {
          test_case with
          per_backend =
            Backend.Map.map
              (fun x ->
                {
                  x with
                  Input.aeneas_options =
                    List.append aeneas_options x.Input.aeneas_options;
                })
              test_case.per_backend;
        }
      in
      let skip_all =
        List.for_all
          (fun backend ->
            (Backend.Map.find backend test_case.per_backend).action = Input.Skip)
          Backend.all
      in
      if skip_all then ()
      else (
        (* Generate the llbc file *)
        run_charon runner_env test_case;
        (* Process the llbc file for the each backend *)
        List.iter (run_aeneas runner_env test_case) Backend.all)
  | _ -> failwith "Incorrect options passed to test runner"
