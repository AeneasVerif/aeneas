let log = Logging.errors_log

let raw_span_to_string (raw_span : Meta.raw_span) =
  let file =
    match raw_span.file with
    | Virtual s | Local s -> s
  in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
  "Source: '" ^ file ^ "', lines "
  ^ loc_to_string raw_span.beg_loc
  ^ "-"
  ^ loc_to_string raw_span.end_loc

let span_to_string (span : Meta.span) = raw_span_to_string span.span

let format_error_message (span : Meta.span option) (msg : string) =
  let span =
    match span with
    | None -> ""
    | Some span -> "\n" ^ span_to_string span
  in
  msg ^ span

let format_error_message_with_file_line (file : string) (line : int)
    (span : Meta.span option) (msg : string) =
  "In file " ^ file ^ ", line " ^ string_of_int line ^ ":\n"
  ^ format_error_message span msg

exception CFailure of (Meta.span option * string)

let error_list : (Meta.span option * string) list ref = ref []

let push_error (span : Meta.span option) (msg : string) =
  error_list := (span, msg) :: !error_list

(** Register an error, and throw an exception if [throw] is true *)
let save_error (file : string) (line : int) ?(throw : bool = false)
    (span : Meta.span option) (msg : string) =
  push_error span msg;
  if !Config.fail_hard && throw then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let craise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure (format_error_message_with_file_line file line span msg)))
  else
    let () = push_error span msg in
    raise (CFailure (span, msg))

let craise (file : string) (line : int) (span : Meta.span) (msg : string) =
  craise_opt_span file line (Some span) msg

let cassert_opt_span (file : string) (line : int) (b : bool)
    (span : Meta.span option) (msg : string) =
  if not b then craise_opt_span file line span msg

let cassert (file : string) (line : int) (b : bool) (span : Meta.span)
    (msg : string) =
  cassert_opt_span file line b (Some span) msg

let sanity_check (file : string) (line : int) b span =
  cassert file line b span "Internal error, please file an issue"

let sanity_check_opt_span (file : string) (line : int) b span =
  cassert_opt_span file line b span "Internal error, please file an issue"

let internal_error (file : string) (line : int) span =
  craise file line span "Internal error, please file an issue"

let exec_raise = craise
let exec_assert = cassert
