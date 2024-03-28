include Charon.Utils

let option_to_list (x : 'a option) : 'a list =
  match x with None -> [] | Some x -> [ x ]
