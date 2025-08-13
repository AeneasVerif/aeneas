open Collections
open SCC
open Pure

(** The local logger *)
let log = Logging.reorder_decls_log

type fun_id = { def_id : FunDeclId.id; lp_id : LoopId.id option }
[@@deriving show, ord]

module FunIdOrderedType : OrderedType with type t = fun_id = struct
  type t = fun_id

  let compare = compare_fun_id
  let to_string = show_fun_id
  let pp_t = pp_fun_id
  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

(** Compute the dependencies of a function body, taking only into account the
    *custom* (i.e., not builtin) functions ids (ignoring operations, types,
    globals, etc.). *)
let compute_body_fun_deps (e : texpr) : FunIdSet.t =
  let ids = ref FunIdSet.empty in

  let visitor =
    object
      inherit [_] iter_expr

      method! visit_qualif _ id =
        match id.id with
        | FunOrOp (Unop _ | Binop _)
        | Global _ | AdtCons _ | Proj _ | TraitConst _ -> ()
        | FunOrOp (Fun fid) -> (
            match fid with
            | Pure _ -> ()
            | FromLlbc (fid, lp_id) -> (
                match fid with
                | FunId (FBuiltin _) -> ()
                | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
                    let id = { def_id = fid; lp_id } in
                    ids := FunIdSet.add id !ids))
    end
  in

  visitor#visit_texpr () e;
  !ids

type function_group = {
  is_rec : bool;
      (** [true] if (mutually) recursive. Useful only if there is exactly one
          declaration in the group. *)
  decls : fun_decl list;
}

(** Group mutually recursive functions together and reorder the groups so that
    if a group B depends on a group A then A comes before B, while trying to
    respect the original order as much as possible. *)
let group_reorder_fun_decls (decls : fun_decl list) :
    (bool * fun_decl list) list =
  let module IntMap = MakeMap (OrderedInt) in
  let get_fun_id (decl : fun_decl) : fun_id =
    { def_id = decl.def_id; lp_id = decl.loop_id }
  in
  (* Compute the list/set of identifiers *)
  let idl = List.map get_fun_id decls in
  let ids = FunIdSet.of_list idl in

  log#ltrace
    (lazy
      ("group_reorder_fun_decls: ids:\n"
      ^ (Print.list_to_string FunIdOrderedType.show_t) idl));

  (* Explore the bodies to compute the dependencies - we ignore the ids
     which refer to declarations not in the group we want to reorder *)
  let deps : (fun_id * FunIdSet.t) list =
    List.map
      (fun decl ->
        let id = get_fun_id decl in
        match decl.body with
        | None -> (id, FunIdSet.empty)
        | Some body ->
            let deps = compute_body_fun_deps body.body in
            (* Restrict the set dependencies *)
            let deps = FunIdSet.inter deps ids in
            (id, deps))
      decls
  in

  (* Compute the ordered SCCs *)
  let module Scc = SCC.Make (FunIdOrderedType) in
  let sccs = Scc.compute deps in

  (* Group the declarations *)
  let deps = FunIdMap.of_list deps in
  let decls = FunIdMap.of_list (List.map (fun d -> (get_fun_id d, d)) decls) in
  List.map
    (fun (_, ids) ->
      (* is_rec is useful only if there is exactly one declaration *)
      let is_rec =
        match ids with
        | [] -> raise (Failure "Unreachable")
        | [ id ] ->
            let dep_ids = FunIdMap.find id deps in
            FunIdSet.mem id dep_ids
        | _ -> true
      in
      let decls = List.map (fun id -> FunIdMap.find id decls) ids in
      (is_rec, decls))
    (SccId.Map.bindings sccs.sccs)
