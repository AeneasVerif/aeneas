(** The available file layouts (see {!FileLayout}). *)

(** All the layouts. *)
val all : FileLayout.t list

(** The layout the CLI options ask for: [-split-files], [-split-files-legacy],
    or a single file by default. *)
val of_config : unit -> FileLayout.t
