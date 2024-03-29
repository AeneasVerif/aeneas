let meta_to_string (span : Meta.span) =
  let file = match span.file with Virtual s | Local s -> s in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
  "Source: '" ^ file ^ "', lines " ^ loc_to_string span.beg_loc ^ "-"
  ^ loc_to_string span.end_loc

let format_error_message (meta : Meta.meta) msg =
  msg ^ "\n" ^ meta_to_string meta.span

exception CFailure of string

let error_list : (Meta.meta option * string) list ref = ref []

let push_error (file : string) (line : int) (meta : Meta.meta option)
    (msg : string) =
  error_list :=
    (meta, msg ^ "\n In file:" ^ file ^ "\n Line:" ^ string_of_int line)
    :: !error_list

let save_error (file : string) (line : int) ?(b : bool = true)
    (meta : Meta.meta option) (msg : string) =
  push_error file line meta msg;
  match meta with
  | Some m ->
      if !Config.fail_hard && not b then
        raise
          (Failure
             (format_error_message m
                (msg ^ "\n In file:" ^ file ^ "\n Line:" ^ string_of_int line)))
  | None -> if !Config.fail_hard && not b then raise (Failure msg)

let craise_opt_meta (file : string) (line : int) (meta : Meta.meta option)
    (msg : string) =
  match meta with
  | Some m ->
      if !Config.fail_hard then
        raise
          (Failure
             (format_error_message m
                (msg ^ "\n In file:" ^ file ^ "\n Line:" ^ string_of_int line)))
      else
        let () = push_error file line (Some m) msg in
        raise (CFailure msg)
  | None ->
      if !Config.fail_hard then
        raise
          (Failure (msg ^ "\n In file:" ^ file ^ "\n Line:" ^ string_of_int line))
      else
        let () = push_error file line None msg in
        raise (CFailure msg)

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
  craise file line meta "Internal error, please report an issue"

let exec_raise = craise
let exec_assert = cassert
