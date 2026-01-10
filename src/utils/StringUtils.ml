include Charon.StringUtils

(** Compute the Levenshtein distance between two strings.

    This is a direct implementation of the algorithm described in the Wikipedia
    article: https://en.wikipedia.org/wiki/Levenshtein_distance *)
let levenshtein_distance (s : string) (t : string) : int =
  let m = String.length s in
  let n = String.length t in
  let v0 = Array.make (n + 1) 0 in
  let v1 = Array.make (n + 1) 0 in

  for i = 0 to n do
    Array.set v0 i i
  done;

  let rv0 = ref v0 in
  let rv1 = ref v1 in

  for i = 0 to m - 1 do
    let v0 = !rv0 in
    let v1 = !rv1 in
    Array.set v1 0 (i + 1);
    for j = 0 to n - 1 do
      let deletion_cost = Array.get v0 (j + 1) + 1 in
      let insertion_cost = Array.get v1 j + 1 in
      let subst_cost =
        if String.get s i = String.get t j then Array.get v0 j
        else Array.get v0 j + 1
      in
      let v =
        if deletion_cost < insertion_cost then deletion_cost else insertion_cost
      in
      let v = if v < subst_cost then v else subst_cost in
      Array.set v1 (j + 1) v
    done;
    let tmp = !rv0 in
    rv0 := !rv1;
    rv1 := tmp
  done;
  Array.get !rv0 n
