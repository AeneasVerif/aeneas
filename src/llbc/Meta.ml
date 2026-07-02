include Charon.Meta

(** The raw path carried by a [file_name], irrespective of the constructor
    (local/virtual/not-real) wrapping it. *)
let path_of_file_name (n : file_name) : string =
  match n with
  | Virtual s | Local s | NotReal s -> s
