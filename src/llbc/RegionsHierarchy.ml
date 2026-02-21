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
open SCC
module Subst = Substitute

(** The local logger *)
let log = Logging.regions_hierarchy_log

type regions_hierarchy = region_var_groups [@@deriving show]

let compute_regions_hierarchy_for_sig (span : Meta.span option) (crate : crate)
    (sg : bound_fun_sig) : region_var_groups =
  (* Create the dependency graph.

     An edge from 'long to 'short means that 'long outlives 'short (that is
     we have 'long : 'short,  using Rust notations).
  *)
  (* First initialize the regions map.

     We add:
     - the region variables
     - the static region
     - edges from the static region to the region variables

     Note that we only consider the regions bound at the
     level of the signature (this excludes the regions locally bound inside
     the types, for instance at the level of an arrow type).
  *)
  let g : RegionSet.t RegionMap.t ref =
    let rvars =
      List.map
        (fun (r : region_param) -> RVar (Free r.index))
        sg.item_binder_params.regions
    in
    let s = (RStatic, RegionSet.of_list rvars) in
    let rsets = List.map (fun r -> (r, RegionSet.empty)) rvars in
    ref (RegionMap.of_list (s :: rsets))
  in

  let add_edge ~(long : region) ~(short : region) =
    (* Sanity checks *)
    [%sanity_check_opt_span] span (short <> RErased);
    [%sanity_check_opt_span] span (long <> RErased);
    (* Ignore the locally bound regions (at the level of arrow types for instance *)
    match (short, long) with
    | RVar (Bound _), _ | _, RVar (Bound _) -> ()
    | _, _ ->
        let m = !g in
        let s = RegionMap.find long !g in
        let s = RegionSet.add short s in
        g := RegionMap.add long s m
  in

  let add_edges_from_region_binder :
      'a. ('a -> unit) -> 'a region_binder -> unit =
   fun visit c ->
    [%sanity_check_opt_span] span (c.binder_regions = []);
    visit c.binder_value
  in

  let add_edge_from_region_constraint ((long, short) : region_outlives) =
    add_edge ~long ~short
  in

  let add_edges ~(long : region) ~(shorts : region list) =
    (* TODO: shouldn't have to use List.iter *)
    List.iter (fun short -> add_edge ~long ~short) shorts
  in

  (* Explore the clauses - we only explore the "region outlives" clause,
     not the "type outlives" clauses *)
  List.iter
    (add_edges_from_region_binder add_edge_from_region_constraint)
    sg.item_binder_params.regions_outlive;

  (* Explore the types in the signature to add the edges *)
  let rec explore_ty (outer : region list) (ty : ty) =
    match ty with
    | TAdt { id; generics } ->
        (* Add constraints coming from the type clauses *)
        (match id with
        | TAdtId id ->
            (* Lookup the type declaration *)
            let decl = TypeDeclId.Map.find_opt id crate.type_decls in
            let decl =
              [%unwrap_opt_span] span decl
                "A type declaration used here is missing from the crate \
                 (probably because of a previous error, or because of the use \
                 of --exclude)"
            in

            (* Instantiate the predicates *)
            let subst =
              [%add_loc] Subst.make_subst_from_generics span decl.generics
                generics Self
            in
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
            | TBox | TStr -> (* No clauses for those *) ()));
        (* Explore the generics *)
        explore_generics outer generics
    | TArray _ | TSlice _ -> (* No clauses for those *) ()
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
        [%sanity_check_opt_span] span
          (check_non_normalizable_trait_ref_kind trait_ref.kind);
        (* We have nothing to do *)
        ()
    | TFnPtr binder ->
        (* TODO: *)
        [%cassert_opt_span] span
          (binder.binder_regions = [])
          "We don't support arrow types with locally quantified regions";
        (* We can ignore the outer regions *)
        let { Types.inputs; output; _ } = binder.binder_value in
        List.iter (explore_ty []) (output :: inputs)
    | TFnDef { binder_regions; binder_value = { kind = _; generics } } ->
        (* For now we check that there are no regions anywhere.

           TODO: the best would be to open all binders and then do a sanity
           check (probably that no region bound at the level of the signature
           is outlived by a locally bound region).
         *)
        [%cassert_opt_span] span (binder_regions = []) "Unimplemented";
        let visitor =
          object
            inherit [_] iter_ty
            method! visit_region _ _ = raise Utils.Found
          end
        in
        let has_regions =
          try
            visitor#visit_generic_args () generics;
            false
          with Utils.Found -> true
        in
        [%cassert_opt_span] span (not has_regions) "Unimplemented";
        ()
    | TDynTrait _ ->
        [%cassert_opt_span] span Config.type_analysis_ignore_dyn "Unimplemented"
    | TPtrMetadata _ -> [%craise_opt_span] span "unsupported: PtrMetadata"
    | TError _ ->
        [%craise_opt_span] span "Found type error in the output of charon"
  and explore_generics (outer : region list) (generics : generic_args) =
    let { regions; types; const_generics = _; trait_refs = _ } = generics in
    List.iter (fun long -> add_edges ~long ~shorts:outer) regions;
    List.iter (explore_ty outer) types
  in

  (* Substitute the regions in a type, then explore *)
  let explore_ty_subst ty = explore_ty [] ty in
  List.iter explore_ty_subst
    (sg.item_binder_value.output :: sg.item_binder_value.inputs);

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
    [%sanity_check_opt_span] span (static_scc = [ RStatic ]);
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
            | _ -> [%craise] (Option.get span) "Unreachable")
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
