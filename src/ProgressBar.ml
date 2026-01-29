let with_reporter (total : int) (msg : string) (f : (int -> unit) -> 'a) : 'a =
  if !Config.progress_bar then
    let bar =
      let open Progress.Line in
      list [ const msg; bar total; count_to total; spinner () ]
    in
    Progress.with_reporter bar f
  else f (fun _ -> ())

let with_parallel_reporter (total : int) (msg : string)
    (f : (int -> unit) -> 'a) : 'a =
  if !Config.progress_bar then
    let mutex = Mutex.create () in
    let bar =
      let open Progress.Line in
      list [ const msg; bar total; count_to total; spinner () ]
    in
    Progress.with_reporter bar (fun report ->
        let report i = Mutex.protect mutex (fun _ -> report i) in
        f report)
  else f (fun _ -> ())
