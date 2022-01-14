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

type 'id decl_group = NonRec of 'id | Rec of 'id list [@@deriving show]

type types_decl_group = TypeDefId.id decl_group [@@deriving show]

type funs_decl_group = FunDefId.id decl_group [@@deriving show]

(** Split a module's declarations between types and functions *)
let split_declarations (decls : declaration list) :
    types_decl_group list * funs_decl_group list =
  let rec split decls =
    match decls with
    | [] -> ([], [])
    | d :: decls' -> (
        let types, funs = split decls' in
        match d with
        | Type id -> (NonRec id :: types, funs)
        | Fun id -> (types, NonRec id :: funs)
        | RecTypes ids -> (Rec ids :: types, funs)
        | RecFuns ids -> (types, Rec ids :: funs))
  in
  split decls

(** Split a module's declarations into two maps from type/fun ids to
    declaration groups.
 *)
let split_declarations_to_group_maps (decls : declaration list) :
    types_decl_group TypeDefId.Map.t * funs_decl_group FunDefId.Map.t =
  let module G (M : Map.S) = struct
    let add_group (map : M.key decl_group M.t) (group : M.key decl_group) :
        M.key decl_group M.t =
      match group with
      | NonRec id -> M.add id group map
      | Rec ids -> List.fold_left (fun map id -> M.add id group map) map ids

    let create_map (groups : M.key decl_group list) : M.key decl_group M.t =
      List.fold_left add_group M.empty groups
  end in
  let types, funs = split_declarations decls in
  let module TG = G (TypeDefId.Map) in
  let types = TG.create_map types in
  let module FG = G (FunDefId.Map) in
  let funs = FG.create_map funs in
  (types, funs)
