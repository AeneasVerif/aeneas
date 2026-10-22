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

type regions_hierarchy = region_groups [@@deriving show]

(** Check whether the static region is used in a signature (in the input and
    output types, or in the region outlives constraints).

    Note that we can't simply explore the types to look for the static region: a
    borrow with lifetime 'static may be hidden inside an ADT (for instance:
    [struct S { x : &'static u32 }]), in which case the static region doesn't
    appear in the signature. We thus use the type information. *)
let sig_uses_static (span : Meta.span option)
    (type_infos : TypesAnalysis.type_infos) (sg : bound_fun_sig) : bool =
  let ty_uses_static (ty : ty) : bool =
    (TypesAnalysis.analyze_ty span type_infos ty).contains_static
  in
  List.exists ty_uses_static
    (sg.item_binder_value.output :: sg.item_binder_value.inputs)
  || List.exists
       (fun (c : region_outlives region_binder) ->
         let long, short = c.binder_value in
         long = RStatic || short = RStatic)
       sg.item_binder_params.regions_outlive

(** Check whether the static region may interact with other regions in a
    signature (in the input and output types), in which case the order in which
    we end the static region and the other regions matters (see
    {!compute_regions_hierarchy_for_sig}).

    This check is deliberately conservative: when it returns [false] and no
    region variable outlives the static region (i.e., the static region group
    contains only the static region - the region variables which outlive
    ['static] are handled separately by {!compute_regions_hierarchy_for_sig}),
    we deviate from the default regions hierarchy (in which the static region
    group has all the other region groups as parents), and we only want to do so
    in the cases where we know the order in which we end the regions is
    irrelevant. This is the case when the static region is only used for shared
    borrows which don't live under other borrows: nothing can then be given back
    through the static region (its backward function has no inputs and no
    outputs), and ending it doesn't require ending other regions first. This
    covers the most common use of the static region (for instance, types
    containing fields of type [&'static str]). In all the other cases we return
    [true], even if the order might actually not matter.

    In the examples below, we use the following definitions:
    {[
      struct S { name : &'static str } // hides a static borrow
      struct MyRef<'a, T>(&'a mut T)
    ]}

    We return [true] if one of the input/output types contains:
    {ul
     {- a mutable static borrow: values can then be given back through the
        static region, and those values may depend on the values given back by
        the other regions (because the static borrow may have been reborrowed or
        coerced into a borrow with a shorter lifetime), for instance:
        {[
          fn f(x : &'static mut u32)
          fn f(x : W<'static>) // where W<'a> contains a field of type &'a mut u32
          fn f<'a>(x : &'static mut u32, y : &'a mut u32, b : bool) -> &'a mut u32 {
            if b { x } else { y } // the value given back to x depends on 'a
          }
        ]}
     }
     {- a (shared or mutable) borrow (of any region, including the static
        region) whose type contains static borrows: the static loans may then
        live under a loan of another region, meaning that ending the static
        region may require ending this other region first, for instance:
        {[
          fn f<'a>(x : &'a mut S) -> &'a mut &'static str { &mut x.name }
          fn f<'a>(x : &'a Result<u32, S>) -> &'a Result<u32, S> { x }
        ]}
     }
     {- an ADT which has region parameters different from the static region and
        contains static borrows, either in its definition, in its region
        arguments or in its type arguments, because the static borrows may then
        live under a borrow of a different region inside the definition of the
        ADT, for instance:
        {[
          fn f<'a>(x : MyRef<'a, S>) -> &'a mut &'static str { &mut x.0.name }
        ]}
     }
    }

    We return [false] for instance for:
    {[
      fn f(x : Result<u32, S>) -> Result<u32, S>
      fn f<'a>(x : Result<&'a u8, S>) -> Result<&'a u8, S>
    ]}
    In the second example, the static borrows (in [S]) and the borrows of region
    ['a] are "side by side": the static loans don't live under loans of region
    ['a].

    As for {!sig_uses_static}, we use the type information to take into account
    the borrows hidden in ADTs. *)
let sig_static_interacts_with_other_regions (span : Meta.span option)
    (type_infos : TypesAnalysis.type_infos) (sg : bound_fun_sig) : bool =
  let static_set = RegionSet.singleton RStatic in
  let visitor =
    object
      inherit [_] iter_ty as super

      method! visit_TRef env r ty rkind =
        if ty_has_regions_in_set type_infos static_set ty then raise Utils.Found;
        super#visit_TRef env r ty rkind

      method! visit_TAdt env tref =
        (* Note that we check the instantiated ADT (the static region may be
           hidden in the type arguments, e.g., [MyRef<'a, S>] where [MyRef<'a, T>]
           contains a field of type [&'a mut T] and [S] contains a field of type
           [&'static str]) *)
        if
          List.exists (fun r -> r <> RStatic) tref.generics.regions
          && ty_has_regions_in_set type_infos static_set (TAdt tref)
        then raise Utils.Found;
        super#visit_TAdt env tref
    end
  in
  let check (ty : ty) : bool =
    (TypesAnalysis.analyze_ty span type_infos ty).contains_static_mut
    ||
    try
      visitor#visit_ty () ty;
      false
    with Utils.Found -> true
  in
  List.exists check (sg.item_binder_value.output :: sg.item_binder_value.inputs)

let compute_regions_hierarchy_for_sig (span : Meta.span option) (crate : crate)
    (type_infos : TypesAnalysis.type_infos) (sg : bound_fun_sig) : region_groups
    =
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
    | TAdt { id; generics; builtin } ->
        (* Add constraints coming from the type clauses *)
        (match builtin with
        | None ->
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
        | Some (TTuple | TBox | TStr) -> (* No clauses for those *) ());
        (* Explore the generics *)
        explore_generics outer generics
    | TArray _ | TSlice _ -> (* No clauses for those *) ()
    | TVar _ | TScalar _ | TNever -> ()
    | TRef (r, ty, _) ->
        (* Add the constraints for r *)
        add_edges ~long:r ~shorts:outer;
        (* Add r to the outer regions *)
        let outer = r :: outer in
        (* Continue *)
        explore_ty outer ty
    | TRawPtr (ty, _) -> explore_ty outer ty
    | TTraitType (trait_ref, _, _) ->
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
    | TFnDef { binder_regions; binder_value = { kind = _; generics }; _ } ->
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
    | TError _ ->
        [%craise_opt_span] span "Found type error in the output of charon"
    | _ -> [%craise_opt_span] span ("unsupported type: " ^ show_ty ty)
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

  (* Remove the SCC containing the static region: we will add it back at the
     end of the list of region groups if the static region is used in the
     signature (we put it at the end so that the identifiers of the other
     region groups don't depend on whether the static region is used or not).

     Note that this SCC may contain regions different from 'static, if they
     outlive 'static (e.g., ['a : 'static]): those regions are then merged
     with the static region (they belong to the same region group).
  *)
  let sccs, (static_scc, static_deps) =
    (* Find the SCC which contains the static region *)
    let static_gr_id, static_scc =
      List.find
        (fun (_, scc) -> List.mem RStatic scc)
        (SccId.Map.bindings sccs.sccs)
    in
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

    let convert_deps deps =
      SccId.Set.of_list (List.filter_map convert_id (SccId.Set.elements deps))
    in
    let static_deps =
      convert_deps
        ([%silent_unwrap_opt_span] span
           (SccId.Map.find_opt static_gr_id scc_deps))
    in
    let scc_deps =
      List.filter_map
        (fun (id, deps) ->
          match convert_id id with
          | None -> None
          | Some id -> Some (id, convert_deps deps))
        (SccId.Map.bindings scc_deps)
    in
    let scc_deps = SccId.Map.of_list scc_deps in

    ({ sccs; scc_deps }, (static_scc, static_deps))
  in

  (*
   * Compute the regions hierarchy
   *)
  let to_group_id (id : SccId.id) : RegionGroupId.id =
    RegionGroupId.of_int (SccId.to_int id)
  in
  let groups =
    List.map
      (fun (scc_id, scc) ->
        (* The region id *)
        let id = to_group_id scc_id in

        (* Retrieve the set of regions in the group *)
        let regions : region list =
          List.map
            (fun r ->
              match r with
              | RVar (Free _) -> r
              | _ -> [%internal_error_opt_span] span)
            scc
        in

        (* Compute the set of parent region groups *)
        let parents =
          List.map to_group_id
            (SccId.Set.elements (SccId.Map.find scc_id sccs.scc_deps))
        in

        (* Put together *)
        ({ id; regions; parents } : region_group))
      (SccId.Map.bindings sccs.sccs)
  in

  (* Add the group for the static region, if the static region is used in the
     signature or if some region variables outlive the static region (in which
     case they belong to the static region group). Note that the static region
     outlives all the other regions: its parents are thus all the other region
     groups (or, more precisely, the groups it directly outlives), meaning that
     the backward function for the static region ends all the other regions
     first.

     There is an exception: if the static region group contains only the static
     region, and the static region doesn't interact with the other regions in
     the signature (roughly: it is only used for shared borrows which neither
     live under other borrows nor inside ADTs with other region parameters;
     this check is conservative - see {!sig_static_interacts_with_other_regions}),
     nothing can be given back through the static region, and we don't need to
     force the other abstractions to end before the abstractions owning the
     static region. The symbolic execution may still have to end some of them
     when ending the static loans (for instance in
     [fn f<'b>(x: &'static str) -> &'b str { x }], ending the static loan
     requires ending the borrow of region ['b]), but the order in which we end
     the static region and the other regions is irrelevant for the translation.
     We thus don't make the static region group depend on the other region
     groups (see the comments in
     [Interp.evaluate_function_symbolic_synthesize_backward_from_return]).
     This is important because the static region is very often used (for
     instance, as soon as a type contains a field of type [&'static str]),
     while some cases involving region groups with parents are not supported
     yet (in particular when calling such functions in loops).

     We put the static region first in the list of regions of the group. *)
  let static_vars = List.filter (fun r -> r <> RStatic) static_scc in
  if static_vars <> [] || sig_uses_static span type_infos sg then
    let id = RegionGroupId.of_int (List.length groups) in
    let parents =
      if
        static_vars = []
        && not (sig_static_interacts_with_other_regions span type_infos sg)
      then []
      else List.map to_group_id (SccId.Set.elements static_deps)
    in
    groups @ [ { id; regions = RStatic :: static_vars; parents } ]
  else groups

(** List the ancestors of a region group (this list doesn't include the region
    group itself).

    This is the same as {!Charon.GAstUtils.list_ancestor_region_groups}, but for
    {!type:Types.region_groups}. *)
let rec list_ancestor_region_groups (regions_hierarchy : region_groups)
    (gid : RegionGroupId.id) : RegionGroupId.Set.t =
  let rg = RegionGroupId.nth regions_hierarchy gid in
  List.fold_left
    (fun s gid ->
      let parents = list_ancestor_region_groups regions_hierarchy gid in
      RegionGroupId.Set.union s (RegionGroupId.Set.add gid parents))
    RegionGroupId.Set.empty rg.parents
