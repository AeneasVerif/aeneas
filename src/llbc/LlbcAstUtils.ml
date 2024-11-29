open Types
open LlbcAst
include Charon.LlbcAstUtils
open Collections
open Utils
open Meta

module FunIdOrderedType : OrderedType with type t = fun_id = struct
  type t = fun_id

  let compare = compare_fun_id
  let to_string = show_fun_id
  let pp_t = pp_fun_id
  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

let lookup_fun_sig (fun_id : fun_id) (fun_decls : fun_decl FunDeclId.Map.t) :
    fun_sig =
  match fun_id with
  | FRegular id -> (FunDeclId.Map.find id fun_decls).signature
  | FBuiltin aid -> Builtin.get_builtin_fun_sig aid

(** Return the opaque declarations found in the crate, which are also *not builtin*.

    [filter_builtin]: if [true], do not consider as opaque the external definitions
    that we will map to definitions from the standard library.

    Remark: the list of functions also contains the list of opaque global bodies.
 *)
let crate_get_opaque_non_builtin_decls (k : crate) (filter_builtin : bool) :
    type_decl list * fun_decl list =
  let open ExtractBuiltin in
  let ctx : Charon.NameMatcher.ctx =
    {
      type_decls = k.type_decls;
      global_decls = k.global_decls;
      fun_decls = k.fun_decls;
      trait_decls = k.trait_decls;
      trait_impls = k.trait_impls;
    }
  in
  let is_opaque_fun (d : fun_decl) : bool =
    d.body = None
    (* Something to pay attention to: we must ignore trait method *declarations*
       (which don't have a body but must not be considered as opaque) *)
    && (match d.kind with
       | TraitDeclItem (_, _, false) -> false
       | _ -> true)
    && ((not filter_builtin)
       || (not (NameMatcherMap.mem ctx d.item_meta.name builtin_globals_map))
          && not (NameMatcherMap.mem ctx d.item_meta.name (builtin_funs_map ()))
       )
  in
  let is_opaque_type (d : type_decl) : bool =
    d.kind = Opaque
    && ((not filter_builtin)
       || not (NameMatcherMap.mem ctx d.item_meta.name (builtin_types_map ())))
  in
  (* Note that by checking the function bodies we also the globals *)
  ( List.filter is_opaque_type (TypeDeclId.Map.values k.type_decls),
    List.filter is_opaque_fun (FunDeclId.Map.values k.fun_decls) )

(** Return true if the crate contains opaque declarations, ignoring the builtin
    definitions. *)
let crate_has_opaque_non_builtin_decls (k : crate) (filter_builtin : bool) :
    bool =
  crate_get_opaque_non_builtin_decls k filter_builtin <> ([], [])

(** For error reporting: compute which local definitions (transitively) depend
    on a set of external definitions. This allows us to pinpoint to the user
    which parts of the code are responsible for an error stemming from a
    dependency. *)
let find_local_transitive_dep (m : crate) (marked_externals : AnyDeclIdSet.t) :
    span list =
  (* Compute the edges from: (decl_id, span) to (decl_id) *)
  let edges = ref [] in
  let visitor =
    object
      inherit [_] iter_statement as super

      method! visit_statement decl_span_info st =
        let decl_span_info =
          Option.map (fun (decl_id, _) -> (decl_id, st.span)) decl_span_info
        in
        super#visit_statement decl_span_info st

      method! visit_type_decl_id decl_span_info id =
        Option.iter
          (fun info -> edges := (info, IdType id) :: !edges)
          decl_span_info

      method! visit_fun_decl_id decl_span_info id =
        Option.iter
          (fun info -> edges := (info, IdFun id) :: !edges)
          decl_span_info

      method! visit_global_decl_id decl_span_info id =
        Option.iter
          (fun info -> edges := (info, IdGlobal id) :: !edges)
          decl_span_info

      method! visit_trait_decl_id decl_span_info id =
        Option.iter
          (fun info -> edges := (info, IdTraitDecl id) :: !edges)
          decl_span_info

      method! visit_trait_impl_id decl_span_info id =
        Option.iter
          (fun info -> edges := (info, IdTraitImpl id) :: !edges)
          decl_span_info
    end
  in
  (* Visit each kind of definition *)
  TypeDeclId.Map.iter
    (fun _ (d : type_decl) ->
      let decl_span_info = Some (IdType d.def_id, d.item_meta.span) in
      visitor#visit_type_decl decl_span_info d)
    m.type_decls;
  FunDeclId.Map.iter
    (fun _ (d : fun_decl) ->
      let decl_span_info = Some (IdFun d.def_id, d.item_meta.span) in
      visitor#visit_fun_sig decl_span_info d.signature;
      Option.iter
        (fun (body : expr_body) ->
          visitor#visit_statement decl_span_info body.body)
        d.body)
    m.fun_decls;
  (* We don't need to visit the globals (it is redundant with visiting the functions) *)
  TraitDeclId.Map.iter
    (fun _ (d : trait_decl) ->
      let decl_span_info = Some (IdTraitDecl d.def_id, d.item_meta.span) in
      visitor#visit_trait_decl decl_span_info d)
    m.trait_decls;
  TraitImplId.Map.iter
    (fun _ (d : trait_impl) ->
      let decl_span_info = Some (IdTraitImpl d.def_id, d.item_meta.span) in
      visitor#visit_trait_impl decl_span_info d)
    m.trait_impls;
  (* We're using a union-find data-structure.

     All external dependencies which are in the set [external] or which
     transitively depend on declarations in this set are put in the same
     equivalence class.
  *)
  let ids =
    List.map (fun id -> IdType id) (TypeDeclId.Map.keys m.type_decls)
    @ List.map (fun id -> IdFun id) (FunDeclId.Map.keys m.fun_decls)
    @ List.map (fun id -> IdGlobal id) (GlobalDeclId.Map.keys m.global_decls)
    @ List.map (fun id -> IdTraitDecl id) (TraitDeclId.Map.keys m.trait_decls)
    @ List.map (fun id -> IdTraitImpl id) (TraitImplId.Map.keys m.trait_impls)
  in
  let uf_store = UF.new_store () in
  let external_ids =
    AnyDeclIdMap.of_list
      (List.filter_map
         (fun id ->
           let meta = crate_get_item_meta m id in
           match meta with
           | None -> None
           | Some meta ->
               if meta.is_local then None else Some (id, UF.make uf_store id))
         ids)
  in
  (* Merge the classes of the marked externals *)
  let marked_class =
    match AnyDeclIdSet.elements marked_externals with
    | id0 :: ids ->
        let c0 = AnyDeclIdMap.find id0 external_ids in
        List.iter
          (fun id ->
            let c = AnyDeclIdMap.find id external_ids in
            let _ = UF.union uf_store c0 c in
            ())
          ids;
        c0
    | _ -> raise (Failure "Unreachable")
  in
  (* Merge the classes by using the edges *)
  List.iter
    (fun ((id0, _), id1) ->
      match (crate_get_item_meta m id0, crate_get_item_meta m id1) with
      | Some meta0, Some meta1 ->
          if (not meta0.is_local) && not meta1.is_local then
            let c0 = AnyDeclIdMap.find id0 external_ids in
            let c1 = AnyDeclIdMap.find id1 external_ids in
            let _ = UF.union uf_store c0 c1 in
            ()
          else ()
      | _ -> ())
    !edges;
  (* We now compute a map from external id in the set to set of local
     declarations (and spans) which depend on this external id *)
  List.iter
    (fun ((id0, _), id1) ->
      match (crate_get_item_meta m id0, crate_get_item_meta m id1) with
      | Some meta0, Some meta1 ->
          if (not meta0.is_local) && not meta1.is_local then
            let c0 = AnyDeclIdMap.find id0 external_ids in
            let c1 = AnyDeclIdMap.find id1 external_ids in
            let _ = UF.union uf_store c0 c1 in
            ()
          else ()
      | _ -> ())
    !edges;
  (* The spans at which we transitively refer to a marked external definition *)
  let spans = ref Charon.MetaUtils.SpanSet.empty in
  List.iter
    (fun ((id0, span), id1) ->
      match (crate_get_item_meta m id0, crate_get_item_meta m id1) with
      | Some meta0, Some meta1 ->
          if meta0.is_local && not meta1.is_local then
            let c1 = AnyDeclIdMap.find id1 external_ids in
            if UF.eq uf_store marked_class c1 then
              spans := Charon.MetaUtils.SpanSet.add span !spans
            else ()
      | _ -> ())
    !edges;
  (* Return the spans *)
  Charon.MetaUtils.SpanSet.elements !spans
