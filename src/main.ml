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
  let json = Yojson.Safe.from_file "../charon/charon/tests/test1.cfim" in
  match rust_module_of_yojson json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "ast"
