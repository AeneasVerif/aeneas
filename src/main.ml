open Types
open CfimAst

type declaration =
  | Type of TypeDefId.id
  | Fun of FunDefId.id
  | RecTypes of TypeDefId.id list
  | RecFuns of FunDefId.id list
[@@deriving of_yojson]

type rust_module = {
  declarations : declaration list;
  types : type_def TypeDefId.vector;
  functions : fun_def FunDefId.vector;
}
[@@deriving of_yojson]

let () =
  (*  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in *)
  let _json1 = Yojson.Safe.from_file "../charon/charon/tests/test1.cfim" in
  let json2 = Yojson.Safe.from_file "../charon/charon/tests/test4.cfim" in
  match statement_of_yojson json2 with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "ast"
(*  match rust_module_of_yojson json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "ast"*)
