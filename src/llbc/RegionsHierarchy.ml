(** This module analyzes function signatures to compute the hierarchy between
    regions.

    Note that we don't need to analyze the types: when there is a non-trivial
    relation between lifetimes in a type definition, the Rust compiler will
    automatically introduce the relevant where clauses. For instance, in the
    definition below:

    {[
      struct Wrapper<'a, 'b, T> {
        x : &'a mut &'b mut T,
      }
    ]}

    the Rust compiler will introduce the where clauses:
    {[
      'b : 'a
      T : 'b
    ]}

    However, it doesn't do so for the function signatures, which means we have
    to compute the constraints between the lifetimes ourselves, then that we
    have to compute the SCCs of the lifetimes (two lifetimes 'a and 'b may
    satisfy 'a : 'b and 'b : 'a, meaning they are actually equal and should be
    grouped together).

    TODO: we don't handle locally bound regions yet. *)

open Types
open TypesUtils
open LlbcAst
open LlbcAstUtils
open Builtin
open SCC
open Errors
module Subst = Substitute

(** The local logger *)
let log = Logging.regions_hierarchy_log

let compute_regions_hierarchy_for_sig (span : Meta.span option) (crate : crate)
    (fun_name : string) (sg : fun_sig) : region_var_groups =
  log#ltrace (lazy (__FUNCTION__ ^ ": " ^ fun_name));
  (* Initialize a normalization context (we may need to normalize some
     associated types) *)
  let norm_ctx : AssociatedTypes.norm_ctx =
    let norm_trait_types =
      AssociatedTypes.compute_norm_trait_types_from_preds span
        sg.generics.trait_type_constraints
    in
    {
      span;
      norm_trait_types;
      crate;
      type_vars = sg.generics.types;
      const_generic_vars = sg.generics.const_generics;
    }
  in

  (* Create the dependency graph.

     An edge from 'short to 'long means that 'long outlives 'short (that is
     we have 'long : 'short,  using Rust notations).
  *)
  (* First initialize the regions map.

     We add:
     - the region variables
     - the static region
     - edges from the region variables to the static region

     Note that we only consider the regions bound at the
     level of the signature (this excludes the regions locally bound inside
     the types, for instance at the level of an arrow type).
  *)
  let g : RegionSet.t RegionMap.t ref =
    let s_set = RegionSet.singleton RStatic in
    let m =
      List.map
        (fun (r : region_var) -> (RVar (Free r.index), s_set))
        sg.generics.regions
    in
    let s = (RStatic, RegionSet.empty) in
    ref (RegionMap.of_list (s :: m))
  in

  let add_edge ~(short : region) ~(long : region) =
    (* Sanity checks *)
    sanity_check_opt_span __FILE__ __LINE__ (short <> RErased) span;
    sanity_check_opt_span __FILE__ __LINE__ (long <> RErased) span;
    (* Ignore the locally bound regions (at the level of arrow types for instance *)
    match (short, long) with
    | RVar (Bound _), _ | _, RVar (Bound _) -> ()
    | _, _ ->
        let m = !g in
        let s = RegionMap.find short !g in
        let s = RegionSet.add long s in
        g := RegionMap.add short s m
  in

  let add_edges_from_region_binder :
      'a. ('a -> unit) -> 'a region_binder -> unit =
   fun visit c ->
    sanity_check_opt_span __FILE__ __LINE__ (c.binder_regions = []) span;
    visit c.binder_value
  in

  let add_edge_from_region_constraint ((long, short) : region_outlives) =
    add_edge ~short ~long
  in

  let add_edges ~(long : region) ~(shorts : region list) =
    List.iter (fun short -> add_edge ~short ~long) shorts
  in

  (* Explore the clauses - we only explore the "region outlives" clause,
     not the "type outlives" clauses *)
  List.iter
    (add_edges_from_region_binder add_edge_from_region_constraint)
    sg.generics.regions_outlive;

  (* Explore the types in the signature to add the edges *)
  let rec explore_ty (outer : region list) (ty : ty) =
    match ty with
    | TAdt { id; generics } ->
        (* Add constraints coming from the type clauses *)
        (match id with
        | TAdtId id ->
            (* Lookup the type declaration *)
            let decl =
              silent_unwrap_opt_span __FILE__ __LINE__ span
                (TypeDeclId.Map.find_opt id crate.type_decls)
            in
            (* Instantiate the predicates *)
            let subst = Subst.make_subst_from_generics decl.generics generics in
            let predicates = Subst.predicates_substitute subst decl.generics in
            (* Note that because we also explore the generics below, we may
               explore several times the same type - this is ok *)
            let add_edges_from_regions_outlive (long, short) =
              add_edges ~long ~shorts:(short :: outer)
            in
            List.iter
              (add_edges_from_region_binder add_edges_from_regions_outlive)
              predicates.regions_outlive;
            let add_edges_from_types_outlive (ty, short) =
              explore_ty (short :: outer) ty
            in
            List.iter
              (add_edges_from_region_binder add_edges_from_types_outlive)
              predicates.types_outlive
        | TTuple -> (* No clauses for tuples *) ()
        | TBuiltin aid -> (
            match aid with
            | TBox | TArray | TSlice | TStr -> (* No clauses for those *) ()));
        (* Explore the generics *)
        explore_generics outer generics
    | TVar _ | TLiteral _ | TNever -> ()
    | TRef (r, ty, _) ->
        (* Add the constraints for r *)
        add_edges ~long:r ~shorts:outer;
        (* Add r to the outer regions *)
        let outer = r :: outer in
        (* Continue *)
        explore_ty outer ty
    | TRawPtr (ty, _) -> explore_ty outer ty
    | TTraitType (trait_ref, _) ->
        (* The trait should reference a clause, and not an implementation
           (otherwise it should have been normalized), or a special builtin
           trait (in particular, [core::marker::DiscriminantKind]) *)
        sanity_check_opt_span __FILE__ __LINE__
          (AssociatedTypes.check_non_normalizable_trait_instance_id
             trait_ref.trait_id)
          span;
        (* We have nothing to do *)
        ()
    | TFnPtr binder ->
        (* TODO: *)
        cassert_opt_span __FILE__ __LINE__
          (binder.binder_regions = [])
          span "We don't support arrow types with locally quantified regions";
        (* We can ignore the outer regions *)
        let inputs, output = binder.binder_value in
        List.iter (explore_ty []) (output :: inputs)
    | TFnDef _ -> craise_opt_span __FILE__ __LINE__ span "unsupported: FnDef"
    | TDynTrait _ ->
        craise_opt_span __FILE__ __LINE__ span
          "Dynamic trait types are not supported yet"
    | TError _ ->
        craise_opt_span __FILE__ __LINE__ span
          "Found type error in the output of charon"
  and explore_generics (outer : region list) (generics : generic_args) =
    let { regions; types; const_generics = _; trait_refs = _ } = generics in
    List.iter (fun long -> add_edges ~long ~shorts:outer) regions;
    List.iter (explore_ty outer) types
  in

  (* Substitute the regions in a type, then explore *)
  let explore_ty_subst ty = explore_ty [] ty in

  (* Normalize the types then explore *)
  let tys =
    List.map
      (AssociatedTypes.norm_ctx_normalize_ty norm_ctx)
      (sg.output :: sg.inputs)
  in
  List.iter explore_ty_subst tys;

  (* Compute the ordered SCCs *)
  let module Scc = SCC.Make (RegionOrderedType) in
  let sccs = Scc.compute (RegionMap.bindings !g) in

  (* Remove the SCC containing the static region.

     For now, we don't handle cases where regions different from 'static
     can live as long as 'static, so we check that if the group contains
     'static then it is the only region it contains, and then we filter
     the group.
     TODO: general support for 'static
  *)
  let sccs =
    (* Find the SCC which contains the static region *)
    let static_gr_id, static_scc =
      List.find
        (fun (_, scc) -> List.mem RStatic scc)
        (SccId.Map.bindings sccs.sccs)
    in
    (* The SCC should only contain the 'static *)
    sanity_check_opt_span __FILE__ __LINE__ (static_scc = [ RStatic ]) span;
    (* Remove the group as well as references to this group from the
       other SCCs *)
    let { sccs; scc_deps } = sccs in
    (* We have to change the indexing:
       - if id < static_gr_id: we leave the id as it is
       - if id = static_gr_id: we remove id
       - if id > static_gr_id: we decrement it by one
    *)
    let static_i = SccId.to_int static_gr_id in
    let convert_id (id : SccId.id) : SccId.id option =
      let i = SccId.to_int id in
      if i < static_i then Some id
      else if i = static_i then None
      else Some (SccId.of_int (i - 1))
    in
    let sccs =
      SccId.Map.of_list
        (List.filter_map
           (fun (id, rg_ids) ->
             match convert_id id with
             | None -> None
             | Some id -> Some (id, rg_ids))
           (SccId.Map.bindings sccs))
    in

    let scc_deps =
      List.filter_map
        (fun (id, deps) ->
          match convert_id id with
          | None -> None
          | Some id ->
              let deps = List.filter_map convert_id (SccId.Set.elements deps) in
              Some (id, SccId.Set.of_list deps))
        (SccId.Map.bindings scc_deps)
    in
    let scc_deps = SccId.Map.of_list scc_deps in

    { sccs; scc_deps }
  in

  (*
   * Compute the regions hierarchy
   *)
  List.filter_map
    (fun (scc_id, scc) ->
      (* The region id *)
      let i = SccId.to_int scc_id in
      let id = RegionGroupId.of_int i in

      (* Retrieve the set of regions in the group *)
      let regions : RegionId.id list =
        List.map
          (fun r ->
            match r with
            | RVar (Free rid) -> rid
            | _ -> craise __FILE__ __LINE__ (Option.get span) "Unreachable")
          scc
      in

      (* Compute the set of parent region groups *)
      let parents =
        List.map
          (fun id -> RegionGroupId.of_int (SccId.to_int id))
          (SccId.Set.elements (SccId.Map.find scc_id sccs.scc_deps))
      in

      (* Put together *)
      Some { id; regions; parents })
    (SccId.Map.bindings sccs.sccs)

(** Compute the region hierarchies for a set of function declarations.Aeneas

    Remark: in case we do not abort on error, this function will ignore the
    signatures which trigger errors. *)
let compute_regions_hierarchies (crate : crate) : region_var_groups FunIdMap.t =
  let open Print in
  let env : fmt_env = Charon.PrintLlbcAst.Crate.crate_to_fmt_env crate in
  let regular =
    List.map
      (fun ((fid, d) : FunDeclId.id * fun_decl) ->
        ( FRegular fid,
          ( Types.name_to_string env d.item_meta.name,
            d.signature,
            Some d.item_meta.span ) ))
      (FunDeclId.Map.bindings crate.fun_decls)
  in
  let builtin =
    List.map
      (fun (info : builtin_fun_info) ->
        (FBuiltin info.fun_id, (info.name, info.fun_sig, None)))
      (BuiltinFunIdMap.values builtin_fun_infos)
  in
  FunIdMap.of_list
    (List.filter_map
       (fun (fid, (name, sg, span)) ->
         try Some (fid, compute_regions_hierarchy_for_sig span crate name sg)
         with CFailure error ->
           let pattern =
             (* The conversion from name to pattern may fail, hence the [try with] *)
             try
               match fid with
               | FRegular fid -> (
                   match FunDeclId.Map.find_opt fid crate.fun_decls with
                   | None -> ""
                   | Some decl ->
                       "\nName pattern: '"
                       ^ LlbcAstUtils.name_with_crate_to_pattern_string
                           error.span crate decl.item_meta.name
                       ^ "'")
               | _ -> ""
             with CFailure _ ->
               " (Could not compute the name pattern due to an additional \
                error)"
           in
           save_error_opt_span __FILE__ __LINE__ error.span
             ("Could not compute the region hierarchies for function '" ^ name
            ^ " because of previous error." ^ pattern);
           None)
       (regular @ builtin))
