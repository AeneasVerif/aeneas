let single : FileLayout.t = (module FileLayoutSingle)
let by_kind : FileLayout.t = (module FileLayoutByKind)
let all : FileLayout.t list = [ single; by_kind ]

let of_config () : FileLayout.t =
  if !Config.split_files then by_kind else single
