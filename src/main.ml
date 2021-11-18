open Types
open CfimAst
open CfimOfJson

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
  (* let json = Yojson.Basic.from_string "{\"Return\"}" in
     print_endline (Yojson.Basic.show json)*)
  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "Ok"
(*  let json = Yojson.Basic.from_string "{\"Statement\":\"Return\"}" in
  print_endline (Yojson.Basic.show json)*)

(*  let json = Yojson.Safe.from_file "../charon/charon/tests/test1.cfim" in
  match cfim_module_of_json json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "Ok"*)

(*  let json = Yojson.Basic.from_file "../charon/charon/tests/test1.cfim" in *)
(*  let _json1 = Yojson.Safe.from_file "../charon/charon/tests/test1.cfim" in
  let st1 = Return in
  let json1 = statement_to_yojson st1 in
  print_endline (Yojson.Safe.to_string json1);
  let e1 = Statement Return in
  let e1_json = expression_to_yojson e1 in
  print_endline (Yojson.Safe.to_string e1_json);
  let int_ty = Isize in
  let int_ty_json = integer_type_to_yojson int_ty in
  print_endline (Yojson.Safe.to_string int_ty_json);
  let json2 = Yojson.Safe.from_string "[\"Return\"]" in
  match statement_of_yojson json2 with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "ast"*)
(*  match rust_module_of_yojson json with
  | Error s -> Printf.printf "error: %s\n" s
  | Ok _ast -> print_endline "ast"*)
