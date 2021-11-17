open Identifiers
(*open CfimAst*)

module Id0 = IdGen ()

module Id1 = IdGen ()

let x0 = Id0.zero

let x1 = Id0.incr x0

let () =
  let _ = print_endline "Hello, world!" in
  let _ = print_endline (Id0.to_string x1) in
  ()

type 'a test_struct = { x : 'a } [@@deriving of_yojson]

type id0_t = Id0.id [@@deriving of_yojson]

let id0_t_test_struct_of_yojson = test_struct_of_yojson id0_t_of_yojson

type ty1 = int Id0.vector [@@deriving of_yojson]

let () =
  (*  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in *)
  let _json = Yojson.Safe.from_file "../charon/charon/tests/test1.cfim" in
  let _test = ty1_of_yojson _json in
  ()
