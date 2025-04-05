let log = Logging.errors_log

let raw_span_to_string (raw_span : Meta.raw_span) =
  let file =
    match raw_span.file.name with
    | Virtual s | Local s -> s
  in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
  "'" ^ file ^ "', lines "
  ^ loc_to_string raw_span.beg_loc
  ^ "-"
  ^ loc_to_string raw_span.end_loc

let span_to_string (span : Meta.span) =
  let generated_from =
    match span.generated_from_span with
    | None -> ""
    | Some span ->
        "; this code is generated from a macro invocation at: "
        ^ raw_span_to_string span
  in
  "Source: " ^ raw_span_to_string span.span ^ generated_from

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

type cfailure = {
  span : Meta.span option;
  file : string;
  line : int;
  msg : string;
}
[@@deriving show]

exception CFailure of cfailure

let error_list : (string * int * Meta.span option * string) list ref = ref []

let push_error (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  error_list := (file, line, span, msg) :: !error_list

(** Register an error, and throw an exception if [throw] is true *)
let save_error_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  push_error file line span msg;
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let save_error (file : string) (line : int) (span : Meta.span) (msg : string) =
  save_error_opt_span file line (Some span) msg

let craise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))
  else
    let () = push_error file line span msg in
    raise (CFailure { span; file; line; msg })

let craise (file : string) (line : int) (span : Meta.span) (msg : string) =
  craise_opt_span file line (Some span) msg

(** Throw an exception, but do not register an error *)
let craise_opt_span_silent (file : string) (line : int)
    (span : Meta.span option) (msg : string) =
  if !Config.fail_hard then
    let msg = format_error_message_with_file_line file line span msg in
    raise (Failure msg)
  else raise (CFailure { span; file; line; msg })

let craise_silent (file : string) (line : int) (span : Meta.span) (msg : string)
    =
  craise_opt_span_silent file line (Some span) msg

(** Lazy assert *)
let classert_opt_span (file : string) (line : int) (b : bool)
    (span : Meta.span option) (msg : string Lazy.t) =
  if not b then craise_opt_span file line span (Lazy.force msg)

(** Lazy assert *)
let classert (file : string) (line : int) (b : bool) (span : Meta.span)
    (msg : string Lazy.t) =
  classert_opt_span file line b (Some span) msg

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

let internal_error_opt_span (file : string) (line : int)
    (span : Meta.span option) =
  craise_opt_span file line span "Internal error, please file an issue"

let internal_error (file : string) (line : int) (span : Meta.span) =
  internal_error_opt_span file line (Some span)

let warn_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  if !Config.warnings_as_errors then
    craise_opt_span file line span
      (msg ^ "\nYou can deactivate this error with the option -soft-warnings")
  else
    let msg = format_error_message_with_file_line file line span msg in
    log#swarning (msg ^ "\n")

let cassert_warn_opt_span (file : string) (line : int) (b : bool)
    (span : Meta.span option) (msg : string) =
  if not b then warn_opt_span file line span msg

let cassert_warn (file : string) (line : int) (b : bool) (span : Meta.span)
    (msg : string) =
  if not b then warn_opt_span file line (Some span) msg

let exec_raise = craise
let exec_assert = cassert

let unwrap_opt_span (file : string) (line : int) (span : Meta.span option)
    (x : 'a option) (msg : string) : 'a =
  match x with
  | Some x -> x
  | None -> craise_opt_span_silent file line span msg

let silent_unwrap_opt_span (file : string) (line : int)
    (span : Meta.span option) (x : 'a option) : 'a =
  unwrap_opt_span file line span x "Internal error: please file an issue"

let silent_unwrap (file : string) (line : int) (span : Meta.span)
    (x : 'a option) : 'a =
  silent_unwrap_opt_span file line (Some span) x

let opt_raise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) : unit =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let opt_raise (file : string) (line : int) (span : Meta.span) (msg : string) :
    unit =
  opt_raise_opt_span file line (Some span) msg
