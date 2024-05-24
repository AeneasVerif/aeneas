(* Convenience functions *)
let map_while (f : 'a -> 'b option) (input : 'a list) : 'b list =
  let _, result =
    List.fold_left
      (fun (continue, out) a ->
        if continue then
          match f a with None -> (false, out) | Some b -> (true, b :: out)
        else (continue, out))
      (true, []) input
  in
  List.rev result

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

module BackendMap = struct
  include Map.Make (Backend)

  (* Make a new map with one entry per backend, given by `f` *)
  let make (f : Backend.t -> 'a) : 'a t =
    List.fold_left
      (fun map backend -> add backend (f backend) map)
      empty Backend.all

  (* Set this value for all the backends in `backends` *)
  let add_each (backends : Backend.t list) (v : 'a) (map : 'a t) : 'a t =
    List.fold_left (fun map backend -> add backend v map) map backends

  (* Updates all the backends in `backends` with `f` *)
  let update_each (backends : Backend.t list) (f : 'a -> 'a) (map : 'a t) : 'a t
      =
    List.fold_left
      (fun map backend -> update backend (Option.map f) map)
      map backends
end

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
  if test_name = "betree" then
    let options =
      [
        "-backward-no-state-update";
        "-test-trans-units";
        "-state";
        "-split-files";
      ]
    in
    let extra_options =
      match backend with
      | Backend.Coq -> [ "-use-fuel" ]
      | Backend.FStar -> [ "-decreases-clauses"; "-template-clauses" ]
      | _ -> []
    in
    List.append extra_options options
  else []

(* File-specific options *)
let charon_options_for_test test_name =
  match test_name with
  | "betree" ->
      [ "--polonius"; "--opaque=betree_utils"; "--crate"; "betree_main" ]
  | _ -> []

(* The data for a specific test input *)
module Input = struct
  type kind = SingleFile | Crate
  type action = Normal | Skip | KnownFailure

  type t = {
    name : string;
    path : string;
    kind : kind;
    actions : action BackendMap.t;
    charon_options : string list;
    aeneas_options : string list BackendMap.t;
    subdirs : string BackendMap.t;
  }

  (* The default subdirectory in which to store the outputs. *)
  let default_subdir backend test_name =
    match backend with Backend.Lean -> "." | _ -> test_name

  (* Parse lines that start `//@`. Each of them modifies the options we use for the test.
     Supported comments:
       - `skip`: don't process the file;
       - `known-failure`: TODO;
       - `subdir=...: set the subdirectory in which to store the outputs.
            Defaults to nothing for lean and to the test name for other backends;
       - `charon-args=...`: extra arguments to pass to charon;
       - `aeneas-args=...`: extra arguments to pass to aeneas;
       - `[backend,..]...`: where each `backend` is the name of a backend supported by
            aeneas; this sets options for these backends only.
  *)
  let apply_special_comment comment input =
    let comment = String.trim comment in
    (* Parse the backends if any *)
    let re = Re.compile (Re.Pcre.re "^\\[([a-zA-Z,]+)\\](.*)$") in
    let comment, (backends : Backend.t list) =
      match Re.exec_opt re comment with
      | Some groups ->
          let backends = Re.Group.get groups 1 in
          let backends = String.split_on_char ',' backends in
          let backends = List.map Backend.of_string backends in
          let rest = Re.Group.get groups 2 in
          (String.trim rest, backends)
      | None -> (comment, Backend.all)
    in
    (* Parse the other options *)
    let charon_args = Core.String.chop_prefix comment ~prefix:"charon-args=" in
    let aeneas_args = Core.String.chop_prefix comment ~prefix:"aeneas-args=" in
    let subdir = Core.String.chop_prefix comment ~prefix:"subdir=" in

    if comment = "skip" then
      { input with actions = BackendMap.add_each backends Skip input.actions }
    else if comment = "known-failure" then
      {
        input with
        actions = BackendMap.add_each backends KnownFailure input.actions;
      }
    else if Option.is_some charon_args then
      let args = Option.get charon_args in
      let args = String.split_on_char ' ' args in
      if backends != Backend.all then
        failwith "Cannot set per-backend charon-args"
      else { input with charon_options = List.append input.charon_options args }
    else if Option.is_some aeneas_args then
      let args = Option.get aeneas_args in
      let args = String.split_on_char ' ' args in
      let add_args opts = List.append opts args in
      {
        input with
        aeneas_options =
          BackendMap.update_each backends add_args input.aeneas_options;
      }
    else if Option.is_some subdir then
      let subdir = Option.get subdir in
      { input with subdirs = BackendMap.add_each backends subdir input.subdirs }
    else failwith ("Unrecognized special comment: `" ^ comment ^ "`")

  (* Given a path to a rust file or crate, gather the details and options about how to build the test. *)
  let build (path : string) : t =
    let name = Filename.remove_extension (Filename.basename path) in
    let name = Str.global_replace (Str.regexp "-") "_" name in
    let kind =
      if Sys_unix.is_file_exn path then SingleFile
      else if Sys_unix.is_directory_exn path then Crate
      else failwith ("`" ^ path ^ "` is not a file or a directory.")
    in
    let actions = BackendMap.make (fun _ -> Normal) in
    let charon_options = charon_options_for_test name in
    let subdirs =
      BackendMap.make (fun backend -> default_subdir backend name)
    in
    let aeneas_options =
      BackendMap.make (fun backend -> aeneas_options_for_test backend name)
    in
    let input =
      { path; name; kind; actions; charon_options; subdirs; aeneas_options }
    in
    match kind with
    | SingleFile ->
        let file_lines = Core.In_channel.read_lines path in
        (* Extract the special lines. Stop at the first non-special line. *)
        let special_comments =
          map_while
            (fun line -> Core.String.chop_prefix line ~prefix:"//@")
            file_lines
        in
        (* Apply the changes from the special lines to our input. *)
        List.fold_left
          (fun input comment -> apply_special_comment comment input)
          input special_comments
    | Crate -> input
end

(* Run Aeneas on a specific input with the given options *)
let run_aeneas (env : runner_env) (case : Input.t) (backend : Backend.t) =
  (* FIXME: remove this special case *)
  let test_name = if case.name = "betree" then "betree_main" else case.name in
  let input_file = concat_path [ env.llbc_dir; test_name ] ^ ".llbc" in
  let subdir = BackendMap.find backend case.subdirs in
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
      let skip_all =
        List.for_all
          (fun backend ->
            BackendMap.find backend test_case.actions = Input.Skip)
          Backend.all
      in
      if skip_all then ()
      else (
        (* Generate the llbc file *)
        run_charon runner_env test_case;
        (* Process the llbc file for the each backend *)
        List.iter
          (fun backend ->
            match BackendMap.find backend test_case.actions with
            | Skip -> ()
            | Normal -> run_aeneas runner_env test_case backend
            | KnownFailure -> failwith "KnownFailure is unimplemented")
          Backend.all)
  | _ -> failwith "Incorrect options passed to test runner"
