let meta_to_string (span : Meta.span ) = 
  let file = match span.file with Virtual s | Local s -> s in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
    "Source: '" ^ file ^ "', lines " ^ loc_to_string span.beg_loc ^ "-"
    ^ loc_to_string span.end_loc

let format_error_message (meta : Meta.meta) msg =
  msg ^ ":" ^ meta_to_string meta.span

exception CFailure of string


let error_list : (Meta.meta option * string) list ref = ref []
let save_error (meta : Meta.meta option) (msg : string) = error_list := (meta, msg)::(!error_list)

let craise (meta : Meta.meta) (msg : string) =
  if !Config.fail_hard then
    raise (Failure (format_error_message meta msg))
  else
    let () = save_error (Some meta) msg in  
    raise (CFailure msg)

let cassert (b : bool) (meta : Meta.meta) (msg : string) =
  if b then
    craise meta msg

let craise_opt_meta (meta : Meta.meta option) (msg : string) =
  match meta with 
  | Some m -> craise m msg
  | None -> 
      let () = save_error (None) msg in  
      raise (CFailure msg)

let cassert_opt_meta (b : bool) (meta : Meta.meta option) (msg : string) =
  match meta with 
  | Some m -> cassert b m msg
  | None -> 
    if b then 
      let () = save_error (None) msg in  
      raise (CFailure msg)