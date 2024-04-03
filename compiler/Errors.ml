let log = Logging.errors_log

let meta_to_string (meta : Meta.meta) =
  let span = meta.span in
  let file = match span.file with Virtual s | Local s -> s in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
  "Source: '" ^ file ^ "', lines " ^ loc_to_string span.beg_loc ^ "-"
  ^ loc_to_string span.end_loc

let format_error_message (meta : Meta.meta option) (msg : string) =
  let meta =
    match meta with None -> "" | Some meta -> "\n" ^ meta_to_string meta
  in
  msg ^ meta

let format_error_message_with_file_line (file : string) (line : int)
    (meta : Meta.meta option) (msg : string) =
  "In file " ^ file ^ ", line " ^ string_of_int line ^ ":\n"
  ^ format_error_message meta msg

exception CFailure of (Meta.meta option * string)

let error_list : (Meta.meta option * string) list ref = ref []

let push_error (meta : Meta.meta option) (msg : string) =
  error_list := (meta, msg) :: !error_list

(** Register an error, and throw an exception if [throw] is true *)
let save_error (file : string) (line : int) ?(throw : bool = false)
    (meta : Meta.meta option) (msg : string) =
  push_error meta msg;
  if !Config.fail_hard && throw then (
    let msg = format_error_message_with_file_line file line meta msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let craise_opt_meta (file : string) (line : int) (meta : Meta.meta option)
    (msg : string) =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line meta msg in
    log#serror (msg ^ "\n");
    raise (Failure (format_error_message_with_file_line file line meta msg)))
  else
    let () = push_error meta msg in
    raise (CFailure (meta, msg))

let craise (file : string) (line : int) (meta : Meta.meta) (msg : string) =
  craise_opt_meta file line (Some meta) msg

let cassert_opt_meta (file : string) (line : int) (b : bool)
    (meta : Meta.meta option) (msg : string) =
  if not b then craise_opt_meta file line meta msg

let cassert (file : string) (line : int) (b : bool) (meta : Meta.meta)
    (msg : string) =
  cassert_opt_meta file line b (Some meta) msg

let sanity_check (file : string) (line : int) b meta =
  cassert file line b meta "Internal error, please file an issue"

let sanity_check_opt_meta (file : string) (line : int) b meta =
  cassert_opt_meta file line b meta "Internal error, please file an issue"

let internal_error (file : string) (line : int) meta =
  craise file line meta "Internal error, please file an issue"

let exec_raise = craise
let exec_assert = cassert
