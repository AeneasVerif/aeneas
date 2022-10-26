(** Meta data like code spans *)

(** A line location *)
type loc = {
  line : int;  (** The (1-based) line number. *)
  col : int;  (** The (0-based) column offset. *)
}
[@@deriving show]

type file_name =
  | Virtual of string  (** A remapped path (namely paths into stdlib) *)
  | Local of string
      (** A local path (a file coming from the current crate for instance) *)
[@@deriving show]

(** Span data *)
type span = { file : file_name; beg_loc : loc; end_loc : loc } [@@deriving show]

type meta = {
  span : span;
      (** The source code span.

          If this meta information is for a statement/terminator coming from a macro
          expansion/inlining/etc., this span is (in case of macros) for the macro
          before expansion (i.e., the location the code where the user wrote the call
          to the macro).

          Ex:
          {[
            // Below, we consider the spans for the statements inside `test`

            //   the statement we consider, which gets inlined in `test`
                                     VV
            macro_rules! macro { ... st ... } // `generated_from_span` refers to this location

            fn test() {
                macro!(); // <-- `span` refers to this location
            }
          ]}
       *)
  generated_from_span : span option;
      (** Where the code actually comes from, in case of macro expansion/inlining/etc. *)
}
[@@deriving show]
