open Types
open CfimAst
open CfimOfJson

type declaration =
  | Type of TypeDefId.id
  | Fun of FunDefId.id
  | RecTypes of TypeDefId.id list
  | RecFuns of FunDefId.id list

type rust_module = {
  declarations : declaration list;
  types : type_def TypeDefId.vector;
  functions : fun_def FunDefId.vector;
}

let () =
  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "Ok"
