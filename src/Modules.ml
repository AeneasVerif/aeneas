open Types
open CfimAst

(** Module declaration *)
type declaration =
  | Type of TypeDefId.id
  | Fun of FunDefId.id
  | RecTypes of TypeDefId.id list
  | RecFuns of FunDefId.id list

type cfim_module = {
  declarations : declaration list;
  types : type_def list;
  functions : fun_def list;
}
(** CFIM module *)
