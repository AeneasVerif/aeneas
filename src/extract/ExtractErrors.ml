(** Error utilities for the extraction *)
(*
   The easiest way of using the helpers below is to use the PPX macros that are
   introduced in the [aeneas-ppx] library. For example, [[%extract_raise]] expands to
   [extract_raise __FILE__ __LINE__].

   The convention is simple: if a function has name [NAME], then [[%NAME]]
   expands to [NAME __FILE__ __LINE__].
 *)

open Errors

let extract_raise_opt_span (file : string) (line : int)
    (span : Meta.span option) (msg : string) (fmt : Format.formatter)
    (extract : string) : unit =
  (* Save the error *)
  save_error_opt_span file line span msg;
  (* If we did not raise an exception above, generate an output *)
  Format.pp_print_string fmt extract

let extract_raise (file : string) (line : int) (span : Meta.span) (msg : string)
    (fmt : Format.formatter) (extract : string) : unit =
  extract_raise_opt_span file line (Some span) msg fmt extract

let admit () =
  match Config.backend () with
  | Coq | FStar | HOL4 -> "admit"
  | Lean -> "sorry"

let admit_raise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) (fmt : Format.formatter) : unit =
  extract_raise_opt_span file line span msg fmt (admit ())

let admit_raise (file : string) (line : int) (span : Meta.span) (msg : string)
    (fmt : Format.formatter) : unit =
  admit_raise_opt_span file line (Some span) msg fmt

let admit_string_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) : string =
  (* Save the error *)
  save_error_opt_span file line span msg;
  (* *)
  admit ()

let admit_string (file : string) (line : int) (span : Meta.span) (msg : string)
    : string =
  admit_string_opt_span file line (Some span) msg

let extract_admit (fmt : Format.formatter) : unit =
  Format.pp_print_string fmt (admit ())
