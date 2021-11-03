open Identifiers
open CfimAst

module Id0 = IdGen ()

module Id1 = IdGen ()

let x0 = Id0.zero

let x1 = Id0.incr x0

let () =
  let _ = print_endline "Hello, world!" in
  let _ = print_endline (Id0.to_string x1) in
  ()
