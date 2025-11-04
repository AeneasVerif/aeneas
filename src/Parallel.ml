open Domain

(** Run a map in parallel.

    We allocate the maximum number of recommended domains. *)
let parallel_map (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    (* Decompose the list into chunks and spawn a domain for each chunk *)
    let num_domains = recommended_domain_count () in
    let elems_per_domain = List.length ls / num_domains in
    let chunks = Collections.List.chunks elems_per_domain ls in
    let domains =
      List.map (fun chunk -> spawn (fun () -> List.map f chunk)) chunks
    in
    (* Join *)
    let ll = List.map join domains in
    List.flatten ll
  else List.map f ls

(** Run a filter_map in parallel.

    We allocate the maximum number of recommended domains. *)
let parallel_filter_map (f : 'a -> 'b option) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    (* Decompose the list into chunks and spawn a domain for each chunk *)
    let num_domains = recommended_domain_count () in
    let elems_per_domain = List.length ls / num_domains in
    let chunks = Collections.List.chunks elems_per_domain ls in
    let domains =
      List.map (fun chunk -> spawn (fun () -> List.filter_map f chunk)) chunks
    in
    (* Join *)
    let ll = List.map join domains in
    List.flatten ll
  else List.filter_map f ls
