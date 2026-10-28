(*** Convenience functions *)

let chop_prefix (s : string) ~(prefix : string) : string option =
  if String.starts_with ~prefix s then
    let n = String.length prefix in
    Some (String.sub s n (String.length s - n))
  else None

let read_lines (path : string) : string list =
  In_channel.with_open_text path In_channel.input_lines

let map_while (f : 'a -> 'b option) (input : 'a list) : 'b list =
  let (_, result) =
    List.fold_left
      (fun (continue, out) a ->
        if continue then
          match f a with
          | None -> (false, out)
          | Some b -> (true, b :: out)
        else (continue, out))
      (true, []) input
  in
  List.rev result
