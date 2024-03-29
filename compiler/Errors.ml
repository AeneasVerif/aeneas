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

let push_error (meta : Meta.meta option) (msg : string) =
  error_list := (meta, msg) :: !error_list

let save_error ?(b : bool = true) (meta : Meta.meta option) (msg : string) =
  push_error meta msg;
  match meta with
  | Some m ->
      if !Config.fail_hard && b then
        raise (Failure (format_error_message m msg))
  | None -> if !Config.fail_hard && b then raise (Failure msg)

let craise_opt_meta (meta : Meta.meta option) (msg : string) =
  match meta with
  | Some m ->
      if !Config.fail_hard then raise (Failure (format_error_message m msg))
      else
        let () = push_error (Some m) msg in
        raise (CFailure msg)
  | None ->
      if !Config.fail_hard then raise (Failure msg)
      else
        let () = push_error None msg in
        raise (CFailure msg)

let craise (meta : Meta.meta) (msg : string) = craise_opt_meta (Some meta) msg

let cassert_opt_meta (b : bool) (meta : Meta.meta option) (msg : string) =
  if not b then craise_opt_meta meta msg

let cassert (b : bool) (meta : Meta.meta) (msg : string) =
  cassert_opt_meta b (Some meta) msg

let sanity_check b meta = cassert b meta "Internal error, please file an issue"

let sanity_check_opt_meta b meta =
  cassert_opt_meta b meta "Internal error, please file an issue"

let internal_error meta = craise meta "Internal error, please report an issue"
let exec_raise = craise
let exec_assert = cassert
