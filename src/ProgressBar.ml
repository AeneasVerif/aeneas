let with_reporter (total : int) (msg : string) (f : (int -> unit) -> 'a) : 'a =
  let bar =
    let open Progress.Line in
    list [ const msg; bar total; count_to total; spinner () ]
  in
  Progress.with_reporter bar f

let with_parallel_reporter (total : int) (msg : string)
    (f : (int -> unit) -> 'a) : 'a =
  let bar =
    let open Progress.Line in
    list [ const msg; bar total; count_to total; spinner () ]
  in
  Progress.with_reporter bar f
