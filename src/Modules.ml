open Yojson.Basic
open Identifiers
open Types
open OfJsonBasic
open Scalars
open Values
open CfimAst

(** Module declaration *)
type declaration =
  | Type of TypeDefId.id
  | Fun of FunDefId.id
  | RecTypes of TypeDefId.id list
  | RecFuns of FunDefId.id list

type cfim_module = {
  declarations : declaration list;
  types : type_def TypeDefId.vector;
  functions : fun_def FunDefId.vector;
}
(** CFIM module *)
