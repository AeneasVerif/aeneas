let single : FileLayout.t = (module FileLayoutSingle)
let by_kind : FileLayout.t = (module FileLayoutByKind)
let by_module : FileLayout.t = (module FileLayoutByModule)
let all : FileLayout.t list = [ single; by_kind; by_module ]

let of_config () : FileLayout.t =
  if !Config.split_files then by_module
  else if !Config.split_files_legacy then by_kind
  else single
