(* Split a list at a given index [i] (the first list contains all the elements
   up to element of index [i], not included, the second one contains the remaining
   elements. Note that the first returned list has length [i].
*)
let rec list_split_at (ls : 'a list) (i : int) =
  if i < 0 then raise (Invalid_argument "list_split_at take positive integers")
  else if i = 0 then ([], ls)
  else
    match ls with
    | [] ->
        raise
          (Failure
             "The int given to list_split_at should be <= the list's length")
    | x :: ls' ->
        let ls1, ls2 = list_split_at ls' (i - 1) in
        (x :: ls1, ls2)

exception Found
(** Utility exception

    When looking for something while exploring a term, it can be easier to
    just throw an exception to signal we found what we were looking for.
 *)
