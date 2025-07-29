include Charon.ExpressionsUtils
open Charon.Expressions
open Charon.Utils

(** Return [true] if a place accesses a global *)
let rec place_accesses_global (p : place) : bool =
  match p.kind with
  | PlaceLocal _ -> false
  | PlaceGlobal _ -> true
  | PlaceProjection (p, _) -> place_accesses_global p

(** Return [true] if an rvalue accesses a global *)
let rvalue_accesses_global (rv : rvalue) : bool =
  let visitor =
    object
      inherit [_] iter_rvalue

      method! visit_place _ p =
        if place_accesses_global p then raise Found else ()
    end
  in
  try
    visitor#visit_rvalue () rv;
    false
  with Found -> true
