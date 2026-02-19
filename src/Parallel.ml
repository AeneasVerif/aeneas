open Domain

exception Stop of exn * Printexc.raw_backtrace

(** Exceptions are not properly propagated through domain boundaries with the
    consequence that we lose precious backtraces when they are not properly
    caught.

    This helper wraps a function call inside a try with to catch uncaught
    exceptions and save their backtrace. *)
let run_with_backtrace (f : 'a -> 'b) (x : 'a) : 'b =
  (* We have to activate the backtrace for the domain - it is not activated by default! *)
  Printexc.record_backtrace true;
  try f x with exn -> raise (Stop (exn, Printexc.get_raw_backtrace ()))

let catch_reraise (f : 'a -> 'b) (x : 'a) : 'b =
  try f x with Stop (e, bt) -> Printexc.raise_with_backtrace e bt

(** Run a map in parallel.

    We divide the list in chunks and use one domain to compute the map on a
    chunk. We allocate the maximum number of recommended domains. *)
let parallel_map_chunks_aux (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
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

let parallel_map_chunks f ls = catch_reraise (parallel_map_chunks_aux f) ls

(** Run a filter_map in parallel.

    We divide the list in chunks and use one domain to compute the filter map on
    a chunk. We allocate the maximum number of recommended domains. *)
let parallel_filter_map_chunks_aux (f : 'a -> 'b option) (ls : 'a list) :
    'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then
    let f = run_with_backtrace f in
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

let parallel_filter_map_chunks f ls =
  catch_reraise (parallel_filter_map_chunks_aux f) ls

(** Run a map in parallel.

    We allocate the maximum number of recommended domains. This is a variant of
    [parallel_map_chunks] where we use a thread pool together with asynchronous
    tasks. *)
let parallel_map_pool_aux (f : 'a -> 'b) (ls : 'a list) : 'b list =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then (
    let f = run_with_backtrace f in
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

let parallel_map_pool f ls = catch_reraise (parallel_map_pool_aux f) ls

(** Run a filter_map in parallel.

    We allocate the maximum number of recommended domains. This is a variant of
    [parallel_filter_map_chunks] where we use a thread pool together with
    asynchronous tasks. *)
let parallel_filter_map_pool_aux (f : 'a -> 'b option) (ls : 'a list) : 'b list
    =
  (* Only run in parallel if the option is activated *)
  if !Config.parallel then (
    let f = run_with_backtrace f in
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

let parallel_filter_map_pool f ls =
  catch_reraise (parallel_filter_map_pool_aux f) ls

let parallel_map = parallel_map_pool
let parallel_filter_map = parallel_filter_map_pool
