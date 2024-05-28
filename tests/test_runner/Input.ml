(*** The data for a specific test input *)

type kind = SingleFile | Crate
type action = Normal | Skip | KnownFailure

type t = {
  name : string;
  path : string;
  kind : kind;
  actions : action Backend.Map.t;
  charon_options : string list;
  aeneas_options : string list Backend.Map.t;
  subdirs : string Backend.Map.t;
  (* Whether to store the command output to a file. Only available for known-failure tests. *)
  check_output : bool Backend.Map.t;
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
    { input with actions = Backend.Map.add_each backends Skip input.actions }
  else if comment = "known-failure" then
    {
      input with
      actions = Backend.Map.add_each backends KnownFailure input.actions;
    }
  else if comment = "no-check-output" then
    {
      input with
      check_output = Backend.Map.add_each backends false input.check_output;
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
        Backend.Map.update_each backends add_args input.aeneas_options;
    }
  else if Option.is_some subdir then
    let subdir = Option.get subdir in
    { input with subdirs = Backend.Map.add_each backends subdir input.subdirs }
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
  let actions = Backend.Map.make (fun _ -> Normal) in
  let subdirs = Backend.Map.make (fun backend -> default_subdir backend name) in
  let aeneas_options = Backend.Map.make (fun _ -> []) in
  let check_output = Backend.Map.make (fun _ -> true) in
  let input =
    {
      path;
      name;
      kind;
      actions;
      charon_options = [];
      subdirs;
      aeneas_options;
      check_output;
    }
  in
  (* For crates, we store the special comments in a separate file. *)
  let crate_config_file = Filename.concat path "aeneas-test-options" in
  match kind with
  | SingleFile ->
      let file_lines = Core.In_channel.read_lines path in
      (* Extract the special lines. Stop at the first non-special line. *)
      let special_comments =
        Utils.map_while
          (fun line -> Core.String.chop_prefix line ~prefix:"//@")
          file_lines
      in
      (* Apply the changes from the special lines to our input. *)
      List.fold_left
        (fun input comment -> apply_special_comment comment input)
        input special_comments
  | Crate when Sys.file_exists crate_config_file ->
      let special_comments = Core.In_channel.read_lines crate_config_file in
      List.fold_left
        (fun input comment -> apply_special_comment comment input)
        input special_comments
  | Crate -> input
