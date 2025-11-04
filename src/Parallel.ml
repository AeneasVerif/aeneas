open Domain

(** Run a map in parallel.

    We divide the list in chunks and use one domain to compute the map on a
    chunk. We allocate the maximum number of recommended domains. *)
let parallel_map_chunks (f : 'a -> 'b) (ls : 'a list) : 'b list =
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

    We divide the list in chunks and use one domain to compute the filter map on
    a chunk. We allocate the maximum number of recommended domains. *)
let parallel_filter_map_chunks (f : 'a -> 'b option) (ls : 'a list) : 'b list =
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

(** Run a map in parallel.

    We allocate the maximum number of recommended domains. This is a variant of
    [parallel_map_chunks] where we use a thread pool together with asynchronous
    tasks. *)
let parallel_map_pool (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then (
    let module T = Domainslib.Task in
    (* Create the pool *)
    let num_domains = recommended_domain_count () in
    let pool = T.setup_pool ~num_domains () in
    (* Run the tasks asynchronously *)
    let run (x : 'a) () = f x in
    let tasks = List.map (fun x -> T.async pool (run x)) ls in
    (* Wait *)
    let ls = T.run pool (fun _ -> List.map (T.await pool) tasks) in
    T.teardown_pool pool;
    ls)
  else List.map f ls

(** Run a filter_map in parallel.

    We allocate the maximum number of recommended domains. This is a variant of
    [parallel_filter_map_chunks] where we use a thread pool together with
    asynchronous tasks. *)
let parallel_filter_map_pool (f : 'a -> 'b option) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then (
    let module T = Domainslib.Task in
    (* Create the pool *)
    let num_domains = recommended_domain_count () in
    let pool = T.setup_pool ~num_domains () in
    (* Run the tasks asynchronously *)
    let run (x : 'a) () = f x in
    let tasks = List.map (fun x -> T.async pool (run x)) ls in
    (* Wait *)
    let ls = T.run pool (fun _ -> List.filter_map (T.await pool) tasks) in
    T.teardown_pool pool;
    ls)
  else List.filter_map f ls

let parallel_map = parallel_map_pool
let parallel_filter_map = parallel_filter_map_pool
