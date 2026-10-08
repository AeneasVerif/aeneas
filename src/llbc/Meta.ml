include Charon.Meta

(** The path string carried by a Charon [file_name], ignoring the
    local/virtual/non-real constructor. *)
let path_of_file_name (n : file_name) : string =
  match n with
  | Virtual s | Local s | NotReal s -> s
