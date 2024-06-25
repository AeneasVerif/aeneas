(*** Convenience functions *)

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
