(* Split a list at a given index i (the first list contains all the elements
   up to element of index i, not included, the second one contains the remaining
   elements *)
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
