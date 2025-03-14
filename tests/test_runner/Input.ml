(*** The data for a specific test input *)

type kind = SingleFile | Crate
type action = Normal | Skip | KnownFailure

(* Options that can be set for a specific backend *)
type per_backend = {
  action : action;
  aeneas_options : string list;
  subdir : string option;
  (* Whether to store the command output to a file. Only available for known-failure tests. *)
  check_output : bool;
}

(* The data for a specific test input *)
type t = {
  name : string;
  path : string;
  kind : kind;
  charon_options : string list;
  per_backend : per_backend Backend.Map.t;
}

(* The default subdirectory in which to store the outputs. *)
let default_subdir (kind : kind) backend test_name : string option =
  match kind with
  | SingleFile -> None
  | Crate -> (
      match backend with
      | Backend.Lean ->
          let elems = String.split_on_char '_' test_name in
          let elems = List.map String.capitalize_ascii elems in
          Some (String.concat "" elems)
      | Backend.BorrowCheck -> None
      | _ -> Some test_name)

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
  let re = Re.compile (Re.Pcre.re "^\\[(!)?([a-zA-Z,-]+)\\](.*)$") in
  let (comment, (backends : Backend.t list)) =
    match Re.exec_opt re comment with
    | Some groups ->
        let exclude = Re.Group.get_opt groups 1 <> None in
        let backends = Re.Group.get groups 2 in
        let backends = String.split_on_char ',' backends in
        let backends = List.map Backend.of_string backends in
        let rest = Re.Group.get groups 3 in
        (* If [exclude]: we take all the backends *but* the list provided. *)
        let backends =
          if exclude then
            List.filter (fun x -> not (List.mem x backends)) Backend.all
          else backends
        in
        (String.trim rest, backends)
    | None -> (comment, Backend.all)
  in
  (* Apply `f` to the selected backends *)
  let per_backend f =
    {
      input with
      per_backend = Backend.Map.update_each backends f input.per_backend;
    }
  in
  (* Assert that this option is not available to be set per-backend *)
  let assert_no_backend option_name =
    if backends != Backend.all then
      failwith ("Cannot set the `" ^ option_name ^ "` option per-backend")
  in

  (* Parse the other options *)
  let charon_args = Core.String.chop_prefix comment ~prefix:"charon-args=" in
  let aeneas_args = Core.String.chop_prefix comment ~prefix:"aeneas-args=" in
  let subdir = Core.String.chop_prefix comment ~prefix:"subdir=" in

  if comment = "skip" then per_backend (fun x -> { x with action = Skip })
  else if comment = "known-failure" then
    per_backend (fun x -> { x with action = KnownFailure })
  else if comment = "no-check-output" then
    per_backend (fun x -> { x with check_output = false })
  else if Option.is_some charon_args then (
    let args = Option.get charon_args in
    let args = String.split_on_char ' ' args in
    assert_no_backend "charon-args";
    { input with charon_options = List.append input.charon_options args })
  else if Option.is_some aeneas_args then
    let args = Option.get aeneas_args in
    let args = String.split_on_char ' ' args in
    per_backend (fun x ->
        { x with aeneas_options = List.append x.aeneas_options args })
  else if Option.is_some subdir then (
    assert (not (List.mem Backend.BorrowCheck backends));
    per_backend (fun x -> { x with subdir }))
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
  let per_backend =
    Backend.Map.make (fun backend ->
        {
          action = Normal;
          subdir = default_subdir kind backend name;
          aeneas_options = [];
          check_output = true;
        })
  in
  let input = { path; name; kind; charon_options = []; per_backend } in
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
