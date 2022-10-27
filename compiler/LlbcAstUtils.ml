open LlbcAst
include Charon.LlbcAstUtils

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    fun_sig =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).signature
  | Assumed aid -> Assumed.get_assumed_sig aid

let lookup_fun_name (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    Names.fun_name =
  match fun_id with
  | Regular id -> (FunDeclId.Map.find id fun_decls).name
  | Assumed aid -> Assumed.get_assumed_name aid
