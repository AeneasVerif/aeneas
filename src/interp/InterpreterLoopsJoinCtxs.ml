open Types
open Values
open Cps
open Contexts
open Utils
open TypesUtils
open ValuesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterBorrows
open InterpreterAbs
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs

(** The local logger *)
let log = Logging.loops_join_ctxs_log

(** Utility.

    An environment augmented with information about its
    borrows/loans/abstractions for the purpose of merging abstractions together.
    We provide functions to update this information when merging two
    abstractions together. We use it in {!reduce_ctx} and {!collapse_ctx}. *)
type ctx_with_info = { ctx : eval_ctx; info : abs_borrows_loans_maps }

let ctx_with_info_merge_into_first_abs (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : ctx_with_info)
    (abs_id0 : AbstractionId.id) (abs_id1 : AbstractionId.id) : ctx_with_info =
  (* Compute the new context and the new abstraction id *)
  let nctx, nabs_id =
    merge_into_first_abstraction span abs_kind ~can_end ~with_abs_conts
      merge_funs ctx.ctx abs_id0 abs_id1
  in
  let nabs = ctx_lookup_abs nctx nabs_id in
  (* Update the information *)
  (* We start by computing the maps for an environment which only contains
     the new region abstraction *)
  let {
    abs_to_borrows = nabs_to_borrows;
    abs_to_non_unique_borrows = nabs_to_non_unique_borrows;
    abs_to_loans = nabs_to_loans;
    borrow_to_abs = borrow_to_nabs;
    non_unique_borrow_to_abs = non_unique_borrow_to_nabs;
    loan_to_abs = loan_to_nabs;
    abs_to_borrow_projs = nabs_to_borrow_projs;
    abs_to_loan_projs = nabs_to_loan_projs;
    borrow_proj_to_abs = borrow_proj_to_nabs;
    loan_proj_to_abs = loan_proj_to_nabs;
    _;
  } =
    compute_abs_borrows_loans_maps span ctx.ctx.type_ctx.type_infos
      (fun _ -> true)
      [ EAbs nabs ]
  in
  (* Retrieve the previous maps, so that we can update them *)
  let {
    abs_ids;
    abs_to_borrows;
    abs_to_non_unique_borrows;
    abs_to_loans;
    borrow_to_abs;
    non_unique_borrow_to_abs;
    loan_to_abs;
    abs_to_borrow_projs;
    abs_to_loan_projs;
    borrow_proj_to_abs;
    loan_proj_to_abs;
  } =
    ctx.info
  in
  let abs_ids =
    List.filter_map
      (fun id ->
        if id = abs_id0 then Some nabs_id
        else if id = abs_id1 then None
        else Some id)
      abs_ids
  in
  (* Update the various maps.

     We use a functor for the maps from marked borrows/loans or symbolic value
     projections to symbolic abstractions, because we have to manipulate maps and
     sets over different types (borrow/loan ids and symbolic value projections).
  *)
  let module UpdateToAbs
      (M : Collections.Map)
      (S : Collections.Set with type elt = M.key) =
  struct
    (* Update a map from marked borrows/loans or symbolic value projections
       to region abstractions by using the old map and the information computed
       from the merged abstraction.
    *)
    let update_to_abs (abs_to : S.t AbstractionId.Map.t)
        (to_nabs : AbstractionId.Set.t M.t) (to_abs : AbstractionId.Set.t M.t) :
        AbstractionId.Set.t M.t =
      (* Remove the old bindings from borrow/loan ids to the two region
         abstractions we just merged (because those two region abstractions
         do not exist anymore). *)
      let abs0_elems = AbstractionId.Map.find abs_id0 abs_to in
      let abs1_elems = AbstractionId.Map.find abs_id1 abs_to in
      let abs01_elems = S.union abs0_elems abs1_elems in
      let to_abs = M.filter (fun id _ -> not (S.mem id abs01_elems)) to_abs in
      (* Add the new bindings from the borrows/loan ids that we find in the
         merged abstraction to this abstraction's id *)
      let merge _ _ _ =
        (* We shouldn't see the same key twice *)
        [%craise] span "Unreachable"
      in
      M.union merge to_nabs to_abs
  end in
  let module UpdateMarkedBorrowId =
    UpdateToAbs (MarkedBorrowId.Map) (MarkedBorrowId.Set)
  in
  let module UpdateMarkedUniqueBorrowId =
    UpdateToAbs (MarkedUniqueBorrowId.Map) (MarkedUniqueBorrowId.Set)
  in
  let module UpdateMarkedLoanId =
    UpdateToAbs (MarkedLoanId.Map) (MarkedLoanId.Set)
  in
  let borrow_to_abs =
    UpdateMarkedUniqueBorrowId.update_to_abs abs_to_borrows borrow_to_nabs
      borrow_to_abs
  in
  let non_unique_borrow_to_abs =
    UpdateMarkedBorrowId.update_to_abs abs_to_non_unique_borrows
      non_unique_borrow_to_nabs non_unique_borrow_to_abs
  in
  let loan_to_abs =
    UpdateMarkedLoanId.update_to_abs abs_to_loans loan_to_nabs loan_to_abs
  in
  let module UpdateSymbProj =
    UpdateToAbs (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
  in
  let borrow_proj_to_abs =
    UpdateSymbProj.update_to_abs abs_to_borrow_projs borrow_proj_to_nabs
      borrow_proj_to_abs
  in
  let loan_proj_to_abs =
    UpdateSymbProj.update_to_abs abs_to_loan_projs loan_proj_to_nabs
      loan_proj_to_abs
  in

  (* Update the maps from abstractions to marked borrows/loans or
     symbolic value projections.
  *)
  let update_abs_to nabs_to abs_to =
    (* Remove the two region abstractions we merged *)
    let m =
      AbstractionId.Map.remove abs_id0 (AbstractionId.Map.remove abs_id1 abs_to)
    in
    (* Add the merged abstraction *)
    AbstractionId.Map.add_strict nabs_id
      (AbstractionId.Map.find nabs_id nabs_to)
      m
  in
  let abs_to_borrows = update_abs_to nabs_to_borrows abs_to_borrows in
  let abs_to_non_unique_borrows =
    update_abs_to nabs_to_non_unique_borrows abs_to_non_unique_borrows
  in
  let abs_to_loans = update_abs_to nabs_to_loans abs_to_loans in
  let abs_to_borrow_projs =
    update_abs_to nabs_to_borrow_projs abs_to_borrow_projs
  in
  let abs_to_loan_projs = update_abs_to nabs_to_loan_projs abs_to_loan_projs in
  let info =
    {
      abs_ids;
      abs_to_borrows;
      abs_to_non_unique_borrows;
      abs_to_loans;
      borrow_to_abs;
      non_unique_borrow_to_abs;
      loan_to_abs;
      borrow_proj_to_abs;
      loan_proj_to_abs;
      abs_to_borrow_projs;
      abs_to_loan_projs;
    }
  in
  { ctx = nctx; info }

exception AbsToMerge of abstraction_id * abstraction_id

(** Repeatedly iterate through the borrows/loans in an environment and merge the
    abstractions that have to be merged according to a user-provided policy. *)
let repeat_iter_borrows_merge (span : Meta.span) (old_ids : ids_sets)
    (abs_kind : abs_kind) ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option)
    (iter : ctx_with_info -> ('a -> unit) -> unit)
    (policy : ctx_with_info -> 'a -> (abstraction_id * abstraction_id) option)
    (ctx : eval_ctx) : eval_ctx =
  (* Compute the information *)
  let ctx =
    let is_fresh_abs_id (id : AbstractionId.id) : bool =
      not (AbstractionId.Set.mem id old_ids.aids)
    in
    let explore (abs : abs) = is_fresh_abs_id abs.abs_id in
    let info =
      compute_abs_borrows_loans_maps span ctx.type_ctx.type_infos explore
        ctx.env
    in
    { ctx; info }
  in
  (* Explore and merge *)
  let rec explore_merge (ctx : ctx_with_info) : eval_ctx =
    try
      iter ctx (fun x ->
          (* Check if we need to merge some abstractions *)
          match policy ctx x with
          | None -> (* No *) ()
          | Some (abs_id0, abs_id1) ->
              (* Yes: raise an exception *)
              raise (AbsToMerge (abs_id0, abs_id1)));
      (* No exception raise: return the current context *)
      ctx.ctx
    with AbsToMerge (abs_id0, abs_id1) ->
      (* Merge and recurse *)
      let ctx =
        ctx_with_info_merge_into_first_abs span abs_kind ~can_end
          ~with_abs_conts merge_funs ctx abs_id0 abs_id1
      in
      explore_merge ctx
  in
  explore_merge ctx

(** Reduce an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point (this is our equivalent of Abstract Interpretation's
    **widening** operation).

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not) and convert them into abstractions
    - whenever there is a new abstraction in the context, and some of its
      borrows are associated to loans in another new abstraction, we merge them.
      We also do this with loan/borrow projectors over symbolic values. In
      effect, this allows us to merge newly introduced abstractions/borrows with
      their parent abstractions.

    For instance, looking at the [list_nth_mut] example, when evaluating the
    first loop iteration, we start in the following environment:
    {[
      abs@0 { ML l0 }
      ls -> MB l0 (s2 : loops::List<T>)
      i -> s1 : u32
    ]}

    and get the following environment upon reaching the [Continue] statement:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
      _@2 -> MB l2 (@Box (ML l4))                      // tail
      _@3 -> MB l1 (s@3 : T)                           // hd
    ]}

    In this new environment, the dummy variables [_@1], [_@2] and [_@3] are
    considered as new.

    We first convert the new dummy values to abstractions. It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@1 { MB l0, ML l1, ML l2 }
      abs@2 { MB l2, ML l4 }
      abs@3 { MB l1 }
    ]}

    We finally merge the new abstractions together (abs@1 and abs@2 because of
    l2, and abs@1 and abs@3 because of l1). It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@4 { MB l0, ML l4 }
    ]}

    - If [merge_funs] is [None], we check that there are no markers in the
      environments. This is the "reduce" operation.
    - If [merge_funs] is [Some _], when merging abstractions together, we merge
      the pairs of borrows and the pairs of loans with the same markers **if
      this marker is not** [PNone]. This is useful to reuse the reduce operation
      to implement the collapse. Note that we ignore borrows/loans with the
      [PNone] marker: the goal of the collapse operation is to *eliminate*
      markers, not to simplify the environment.

    For instance, when merging:
    {[
      abs@0 { ML l0, |MB l1| }
      abs@1 { MB l0, ︙MB l1︙ }
    ]}
    We get:
    {[
      abs@2 { MB l1 }
    ]} *)
let reduce_ctx_with_markers (merge_funs : merge_duplicates_funcs option)
    ~(with_abs_conts : bool) (span : Meta.span) (loop_id : LoopId.id)
    (old_ids : ids_sets) (ctx0 : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx0
    ^ "\n"];

  let with_markers = merge_funs <> None in

  let abs_kind : abs_kind = Loop (loop_id, None) in
  let can_end = true in
  let is_fresh_did (id : DummyVarId.id) : bool =
    not (DummyVarId.Set.mem id old_ids.dids)
  in

  let ctx = ctx0 in
  (* Convert the dummy values to abstractions (note that when we convert
     values to abstractions, the resulting abstraction should be destructured) *)
  (* Note that we preserve the order of the dummy values: we replace them with
     abstractions in place - this makes matching easier *)
  let env =
    List.concat
      (List.map
         (fun ee ->
           match ee with
           | EAbs _ | EFrame | EBinding (BVar _, _) -> [ ee ]
           | EBinding (BDummy id, v) ->
               if is_fresh_did id then (
                 let absl =
                   convert_value_to_abstractions span abs_kind ~can_end ctx v
                 in
                 Invariants.opt_type_check_absl span ctx absl;
                 List.map (fun abs -> EAbs abs) absl)
               else [ ee ])
         ctx.env)
  in
  let ctx = { ctx with env } in
  [%ltrace
    "after converting values to abstractions:\n" ^ show_ids_sets old_ids
    ^ "\n\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  [%ltrace
    "after decomposing the shared values in the abstractions:\n"
    ^ show_ids_sets old_ids ^ "\n\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (*
   * Merge all the mergeable abs.
   *)
  (* Because we need to manipulate different types for the concrete and the
     symbolic loans and borrows, we introduce a functor *)
  let module IterMerge
      (Map : Collections.Map)
      (Set : Collections.Set with type elt = Map.key)
      (Marked : sig
        val get_marker : Map.key -> proj_marker

        val get_borrow_to_abs :
          abs_borrows_loans_maps -> AbstractionId.Set.t Map.t

        val get_to_loans : abs_borrows_loans_maps -> Set.t AbstractionId.Map.t
      end) =
  struct
    (* We iterate over the *new* abstractions, then over the **loans**
       (concrete or symbolic) in the abstractions.

       We do this because we want to control the order in which abstractions
       are merged (the ids are iterated in increasing order). Otherwise, we
       could simply iterate over all the borrows in [loan_to_abs] for instance... *)
    let iterate_loans (ctx : ctx_with_info)
        (merge : abstraction_id * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Iterate over the loans *)
          let lids =
            AbstractionId.Map.find abs_id0 (Marked.get_to_loans ctx.info)
          in
          Set.iter (fun lid -> merge (abs_id0, lid)) lids)
        ctx.info.abs_ids

    (* Given a **loan**, check if there is a fresh abstraction with the corresponding borrow *)
    let merge_policy (ctx : ctx_with_info) (abs_id0, loan) =
      if not with_markers then
        [%sanity_check] span (Marked.get_marker loan = PNone);
      (* If we use markers: we are doing a collapse, which means we attempt
         to eliminate markers (and this is the only goal of the operation).
         We thus ignore the non-marked values (we merge non-marked values
         when doing a "real" reduce, to simplify the environment in order
         to converge to a fixed-point, for instance). *)
      if with_markers && Marked.get_marker loan = PNone then None
      else
        (* Find the *borrow* corresponding to the loan we want to eliminate
           (hence the use of [get_borrow_to_abs]) *)
        match Map.find_opt loan (Marked.get_borrow_to_abs ctx.info) with
        | None -> (* Nothing to to *) None
        | Some abs_ids1 -> (
            (* We need to merge *)
            match AbstractionId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                [%ltrace
                  "merging abstraction "
                  ^ AbstractionId.to_string abs_id1
                  ^ " into "
                  ^ AbstractionId.to_string abs_id0
                  ^ ":\n\n"
                  ^ eval_ctx_to_string ~span:(Some span) ctx.ctx];
                Some (abs_id0, abs_id1))

    (* Iterate over the loans and merge the abstractions *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge span old_ids abs_kind ~can_end ~with_abs_conts
        merge_funs iterate_loans merge_policy ctx
  end in
  (* Instantiate the functor for the concrete borrows and loans *)
  let module IterMergeConcrete =
    IterMerge (MarkedBorrowId.Map) (MarkedBorrowId.Set)
      (struct
        let get_marker (pm, _) = pm
        let get_borrow_to_abs info = info.non_unique_borrow_to_abs
        let get_to_loans info = info.abs_to_loans
      end)
  in
  (* Instantiate the functor for the symbolic borrows and loans *)
  let module IterMergeSymbolic =
    IterMerge (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
      (struct
        let get_marker (proj : marked_norm_symb_proj) = proj.pm
        let get_borrow_to_abs info = info.borrow_proj_to_abs
        let get_to_loans info = info.abs_to_loan_projs
      end)
  in
  (* Apply *)
  let ctx = IterMergeConcrete.iter_merge ctx in
  let ctx = IterMergeSymbolic.iter_merge ctx in

  (* Debugging *)
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids ^ "\n\n- after reduce:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers at this point. *)
  let ctx = reorder_fresh_abs span true old_ids.aids ctx in

  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids
    ^ "\n\n- after reduce and reorder borrows/loans and abstractions:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Return the new context *)
  ctx

(** reduce_ctx can only be called in a context with no markers *)
let reduce_ctx config (span : Meta.span) ~(with_abs_conts : bool)
    (loop_id : loop_id) (fixed_ids : ids_sets) (ctx : eval_ctx) : eval_ctx =
  (* Simplify the context *)
  let ctx, _ =
    InterpreterBorrows.simplify_dummy_values_useless_abs config span
      fixed_ids.aids ctx
  in
  (* Reduce *)
  reduce_ctx_with_markers None span ~with_abs_conts loop_id fixed_ids ctx

(** Auxiliary function for collapse (see below).

    We traverse all abstractions, and merge abstractions when they contain the
    same element, but with dual markers (i.e., [PLeft] and [PRight]).

    For instance, if we have the abstractions

    {[
      abs@0 { | MB l0 _ |, ML l1 }
      abs@1 { ︙MB l0 _ ︙, ML l2 }
    ]}

    We merge abs@0 and abs@1 into a new abstraction abs@2. This allows us to
    eliminate the markers used for [MB l0]:
    {[
      abs@2 { MB l0 _, ML l1, ML l2 }
    ]} *)
let collapse_ctx_collapse (span : Meta.span) (loop_id : LoopId.id)
    ~(with_abs_conts : bool) (merge_funs : merge_duplicates_funcs)
    (old_ids : ids_sets) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids ^ "\n\n- initial ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  let abs_kind : abs_kind = Loop (loop_id, None) in
  let can_end = true in

  let invert_proj_marker = function
    | PNone -> [%craise] span "Unreachable"
    | PLeft -> PRight
    | PRight -> PLeft
  in

  (* Merge all the mergeable abs where the same element in present in both abs,
     but with left and right markers respectively.

     As we have to operate over different types, with both concrete borrows and loans and
     borrow projectors and loan projectors, we implement this as a functor.
  *)
  let module IterMerge
      (Map : Collections.Map)
      (Set : Collections.Set with type elt = Map.key)
      (Marked : sig
        val get_marker : Map.key -> proj_marker

        (* Remove a marker - we need this to check whether some borrows in one
           abstraction have corresponding loans in another abstraction,
           independently of the markers, to properly choose which abstraction
           we merge into the other. *)
        val unmark : Map.key -> Map.key

        (* Invert a marker *)
        val invert_proj_marker : Map.key -> Map.key
        val get_to_borrows : abs_borrows_loans_maps -> Set.t AbstractionId.Map.t
        val get_to_loans : abs_borrows_loans_maps -> Set.t AbstractionId.Map.t

        val get_borrow_to_abs :
          abs_borrows_loans_maps -> AbstractionId.Set.t Map.t

        val get_loan_to_abs :
          abs_borrows_loans_maps -> AbstractionId.Set.t Map.t
      end) =
  struct
    (* The iter function: iterate over the abstractions, and inside an abstraction
       over the borrows (projectors) then the loan (projectors) *)
    let iter (ctx : ctx_with_info)
        (f : AbstractionId.id * bool * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Small helper *)
          let iterate is_borrow =
            let m =
              if is_borrow then Marked.get_to_borrows ctx.info
              else Marked.get_to_loans ctx.info
            in
            let ids = AbstractionId.Map.find abs_id0 m in
            Set.iter (fun id -> f (abs_id0, is_borrow, id)) ids
          in
          (* Iterate over the borrows *)
          iterate true;
          (* Iterate over the loans *)
          iterate false)
        ctx.info.abs_ids

    (* Small utility: check if we need to swap two region abstractions before
       merging them.

       We might have to swap the order to make sure that if there
       are loans in one abstraction and the corresponding borrows
       in the other they get properly merged (if we merge them in the wrong
       order, we might introduce borrowing cycles).

       Example:
       If we are merging abs0 and abs1 because of the marked value
       [MB l0]:
       {[
         abs0 { |MB l0|, MB l1 }
         abs1 { ︙MB l0︙, ML l1 }
       ]}
       we want to make sure that we swap them (abs1 goes to the
       left) to make sure [MB l1] and [ML l1] get properly eliminated.

       Remark: in case there is a borrowing cycle between the two abstractions
       (which shouldn't happen) then there isn't much we can do, and whatever
       the order in which we merge, we will preserve the cycle.
    *)
    let swap_abs (info : abs_borrows_loans_maps) (abs_id0 : abstraction_id)
        (abs_id1 : abstraction_id) =
      let abs0_borrows =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements
                (AbstractionId.Map.find abs_id0 (Marked.get_to_borrows info))))
      in
      let abs1_loans =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements
                (AbstractionId.Map.find abs_id1 (Marked.get_to_loans info))))
      in
      not (Set.disjoint abs0_borrows abs1_loans)

    (* Check if there is an abstraction with the same borrow/loan id (or the
       same projections of borrows/loans) and the dual marker, and merge them
       if it is the case. *)
    let merge_policy ctx (abs_id0, is_borrow, loan) =
      if Marked.get_marker loan = PNone then None
      else
        (* Look for an element with the dual marker *)
        match
          Map.find_opt
            (Marked.invert_proj_marker loan)
            (if is_borrow then Marked.get_borrow_to_abs ctx.info
             else Marked.get_loan_to_abs ctx.info)
        with
        | None -> (* Nothing to do *) None
        | Some abs_ids1 -> (
            (* We need to merge *)
            match AbstractionId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                (* Check if we need to swap *)
                Some
                  (if swap_abs ctx.info abs_id0 abs_id1 then (abs_id1, abs_id0)
                   else (abs_id0, abs_id1)))

    (* Iterate and merge *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge span old_ids abs_kind ~can_end ~with_abs_conts
        (Some merge_funs) iter merge_policy ctx
  end in
  (* Instantiate the functor for concrete loans and borrows *)
  let module IterMergeConcrete =
    IterMerge (MarkedBorrowId.Map) (MarkedBorrowId.Set)
      (struct
        let get_marker (v : marked_borrow_id) = fst v
        let unmark (_, bid) = (PNone, bid)
        let invert_proj_marker (pm, bid) = (invert_proj_marker pm, bid)
        let get_to_borrows info = info.abs_to_non_unique_borrows
        let get_to_loans info = info.abs_to_loans
        let get_borrow_to_abs info = info.non_unique_borrow_to_abs
        let get_loan_to_abs info = info.loan_to_abs
      end)
  in
  (* Instantiate the functor for symbolic loans and borrows *)
  let module IterMergeSymbolic =
    IterMerge (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
      (struct
        let get_marker (v : marked_norm_symb_proj) = v.pm
        let unmark v = { v with pm = PNone }
        let invert_proj_marker v = { v with pm = invert_proj_marker v.pm }
        let get_to_borrows info = info.abs_to_borrow_projs
        let get_to_loans info = info.abs_to_loan_projs
        let get_borrow_to_abs info = info.borrow_proj_to_abs
        let get_loan_to_abs info = info.loan_proj_to_abs
      end)
  in
  (* Iterate and merge *)
  let ctx = IterMergeConcrete.iter_merge ctx in
  let ctx = IterMergeSymbolic.iter_merge ctx in

  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids ^ "\n\n- after collapse:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers yet *)
  let ctx = reorder_fresh_abs span true old_ids.aids ctx in

  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets old_ids
    ^ "\n\n- after collapse and reorder borrows/loans:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Return the new context *)
  ctx

(** Small utility: check whether an environment contains markers *)
let eval_ctx_has_markers (ctx : eval_ctx) : bool =
  let visitor =
    object
      inherit [_] iter_eval_ctx

      method! visit_proj_marker _ pm =
        match pm with
        | PNone -> ()
        | PLeft | PRight -> raise Found
    end
  in
  try
    visitor#visit_eval_ctx () ctx;
    false
  with Found -> true

(** Collapse two environments containing projection markers; this function is
    called after joining environments.

    The collapse is done in two steps.

    First, we reduce the environment, merging any two pair of fresh abstractions
    which contain a loan (in one) and its corresponding borrow (in the other).
    This is our version of Abstract Interpretation's **widening** operation. For
    instance, we merge abs@0 and abs@1 below:
    {[
      abs@0 { |ML l0|, ML l1 }
      abs@1 { |MB l0 _|, ML l2 }
                ~~>
      abs@2 { ML l1, ML l2 }
    ]}
    Note that we also merge abstractions when the loan/borrow don't have the
    same markers. For instance, below:
    {[
      abs@0 { ML l0, ML l1 } // ML l0 doesn't have markers
      abs@1 { |MB l0 _|, ML l2 }
                ~~>
      abs@2 { ︙ML l0︙, ML l1, ML l2 }
    ]}

    Second, we merge abstractions containing the same element with left and
    right markers respectively. For instance:
    {[
      abs@0 { | MB l0 _ |, ML l1 }
      abs@1 { ︙MB l0 _ ︙, ML l2 }
                ~~>
      abs@2 { MB l0 _, ML l1, ML l2 }
    ]}

    At the end of the second step, all markers should have been removed from the
    resulting environment. *)
let collapse_ctx config (span : Meta.span) (loop_id : LoopId.id)
    ~(with_abs_conts : bool) (merge_funs : merge_duplicates_funcs)
    (old_ids : ids_sets) (ctx0 : eval_ctx) : eval_ctx =
  let ctx =
    reduce_ctx_with_markers (Some merge_funs) span ~with_abs_conts loop_id
      old_ids ctx0
  in
  let ctx =
    collapse_ctx_collapse span ~with_abs_conts loop_id merge_funs old_ids ctx
  in
  (* Sanity check: there are no markers remaining *)
  [%sanity_check] span (not (eval_ctx_has_markers ctx));
  (* One last cleanup *)
  let ctx, _ =
    InterpreterBorrows.simplify_dummy_values_useless_abs config span
      old_ids.aids ctx
  in
  ctx

let mk_collapse_ctx_merge_duplicate_funs (span : Meta.span)
    (loop_id : LoopId.id) (with_abs_conts : bool) (ctx : eval_ctx) :
    merge_duplicates_funcs =
  (* Rem.: the merge functions raise exceptions (that we catch). *)
  let module S : MatchJoinState = struct
    let span = span
    let loop_id = loop_id
    let nabs = ref []
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = ref SymbolicValueId.Map.empty
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  (* Functions to match avalues (see {!merge_duplicates_funcs}).

     Those functions are used to merge borrows/loans with the *same ids*.

     They will always be called on destructured avalues (whose children are
     [AIgnored] - we enforce that through sanity checks). We rely on the join
     matcher [JM] to match the concrete values (for shared loans for instance).
     Note that the join matcher doesn't implement match functions for avalues
     (see the comments in {!MakeJoinMatcher}.
  *)
  let merge_amut_borrows id ty0 _pm0 (child0 : tavalue) _ty1 _pm1
      (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);

    (* We need to pick a type for the avalue. The types on the left and on the
       right may use different regions: it doesn't really matter (here, we pick
       the one from the left), because we will merge those regions together
       anyway (see the comments for {!merge_into_first_abstraction}).
    *)
    let ty = ty0 in
    let child = child0 in
    let value = ABorrow (AMutBorrow (PNone, id, child)) in
    { value; ty }
  in

  let merge_ashared_borrows id ty0 _pm0 _ ty1 _pm1 _ : tavalue =
    (* Sanity checks *)
    let _ =
      let _, ty0, _ = ty_as_ref ty0 in
      let _, ty1, _ = ty_as_ref ty1 in
      [%sanity_check] span
        (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty0));
      [%sanity_check] span
        (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty1))
    in

    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let value =
      ABorrow (ASharedBorrow (PNone, id, fresh_shared_borrow_id ()))
    in
    { value; ty }
  in

  let merge_amut_loans id ty0 _pm0 (child0 : tavalue) _ty1 _pm1
      (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);

    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let child = child0 in
    let value = ALoan (AMutLoan (PNone, id, child)) in
    { value; ty }
  in
  let merge_ashared_loans ids ty0 _pm0 (sv0 : tvalue) (child0 : tavalue) _ty1
      _pm1 (sv1 : tvalue) (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);
    (* Same remarks as for [merge_amut_borrows].

       This time we need to also merge the shared values. We rely on the
       join matcher [JM] to do so.
    *)
    [%sanity_check] span
      (not (value_has_loans_or_borrows (Some span) ctx sv0.value));
    [%sanity_check] span
      (not (value_has_loans_or_borrows (Some span) ctx sv1.value));

    let ty = ty0 in
    let child = child0 in
    let sv = M.match_tvalues ctx ctx sv0 sv1 in
    let value = ALoan (ASharedLoan (PNone, ids, sv, child)) in
    { value; ty }
  in
  let merge_aborrow_projs ty0 _pm0 (proj0 : aproj_borrows) _ty1 _pm1
      (proj1 : aproj_borrows) : tavalue =
    let { proj = { sv_id = sv0; proj_ty = proj_ty0 }; loans = loans0 } :
        aproj_borrows =
      proj0
    in
    let { proj = { sv_id = sv1; proj_ty = proj_ty1 }; loans = loans1 } :
        aproj_borrows =
      proj1
    in
    (* Sanity checks *)
    [%sanity_check] span (loans0 = []);
    [%sanity_check] span (loans1 = []);
    [%sanity_check] span (erase_regions proj_ty0 = erase_regions proj_ty1);
    (* Same remarks as for [merge_amut_borrows]. *)
    let ty = ty0 in
    let proj_ty = proj_ty0 in
    let loans = [] in
    [%sanity_check] span (sv0 = sv1);
    let sv_id = sv0 in
    let proj : symbolic_proj = { sv_id; proj_ty } in
    let value = ASymbolic (PNone, AProjBorrows { proj; loans }) in
    { value; ty }
  in
  let merge_aloan_projs ty0 _pm0 (proj0 : aproj_loans) _ty1 _pm1
      (proj1 : aproj_loans) : tavalue =
    let {
      proj = { sv_id = sv0; proj_ty = proj_ty0 };
      consumed = consumed0;
      borrows = borrows0;
    } : aproj_loans =
      proj0
    in
    let {
      proj = { sv_id = sv1; proj_ty = proj_ty1 };
      consumed = consumed1;
      borrows = borrows1;
    } : aproj_loans =
      proj1
    in
    (* Sanity checks *)
    [%sanity_check] span (consumed0 = [] && borrows0 = []);
    [%sanity_check] span (consumed1 = [] && borrows1 = []);
    [%sanity_check] span (erase_regions proj_ty0 = erase_regions proj_ty1);
    (* Same remarks as for [merge_amut_borrows]. *)
    let ty = ty0 in
    let proj_ty = proj_ty0 in
    let consumed = [] in
    let borrows = [] in
    [%sanity_check] span (sv0 = sv1);
    let sv_id = sv0 in
    let proj : symbolic_proj = { sv_id; proj_ty } in
    let value = ASymbolic (PNone, AProjLoans { proj; consumed; borrows }) in
    { value; ty }
  in
  {
    merge_amut_borrows;
    merge_ashared_borrows;
    merge_amut_loans;
    merge_ashared_loans;
    merge_aborrow_projs;
    merge_aloan_projs;
  }

let merge_into_first_abstraction (span : Meta.span) (loop_id : LoopId.id)
    (abs_kind : abs_kind) ~(can_end : bool) ~(with_abs_conts : bool)
    (ctx : eval_ctx) (aid0 : AbstractionId.id) (aid1 : AbstractionId.id) :
    eval_ctx * AbstractionId.id =
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span loop_id with_abs_conts ctx
  in
  InterpreterAbs.merge_into_first_abstraction span abs_kind ~can_end
    ~with_abs_conts (Some merge_funs) ctx aid0 aid1

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging
    functions.

    We do this because when we join environments, we may introduce duplicated
    loans and borrows. See the explanations for {!join_ctxs}. *)
let collapse_ctx_with_merge config (span : Meta.span) (loop_id : LoopId.id)
    (old_ids : ids_sets) ~(with_abs_conts : bool) (ctx : eval_ctx) : eval_ctx =
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span loop_id with_abs_conts ctx
  in
  try collapse_ctx config span ~with_abs_conts loop_id merge_funs old_ids ctx
  with ValueMatchFailure _ -> [%internal_error] span

let join_ctxs (span : Meta.span) (loop_id : LoopId.id) (fixed_ids : ids_sets)
    ~(with_abs_conts : bool) (ctx0 : eval_ctx) (ctx1 : eval_ctx) : ctx_or_update
    =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1
    ^ "\n"];

  let env0 = List.rev ctx0.env in
  let env1 = List.rev ctx1.env in
  let nabs = ref [] in

  (* Explore the environments. *)
  let join_suffixes (env0 : env) (env1 : env) : env =
    (* Debug *)
    [%ldebug
      "join_suffixes:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
      ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx0 with env = List.rev env0 }
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx1 with env = List.rev env1 }
      ^ "\n"];

    (* Sanity check: there are no values/abstractions which should be in the prefix *)
    let check_valid (ee : env_elem) : unit =
      match ee with
      | EBinding (BVar _, _) ->
          (* Variables are necessarily in the prefix *)
          [%craise] span "Unreachable"
      | EBinding (BDummy did, _) ->
          [%sanity_check] span (not (DummyVarId.Set.mem did fixed_ids.dids))
      | EAbs abs ->
          [%sanity_check] span
            (not (AbstractionId.Set.mem abs.abs_id fixed_ids.aids))
      | EFrame ->
          (* This should have been eliminated *)
          [%craise] span "Unreachable"
    in

    (* Add projection marker to all abstractions in the left and right environments *)
    let add_marker (pm : proj_marker) (ee : env_elem) : env_elem =
      match ee with
      | EAbs abs -> EAbs (abs_add_marker span ctx0 pm abs)
      | x -> x
    in

    let env0 = List.map (add_marker PLeft) env0 in
    let env1 = List.map (add_marker PRight) env1 in

    List.iter check_valid env0;
    List.iter check_valid env1;
    (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
    let absl = List.map (fun abs -> EAbs abs) (List.rev !nabs) in
    List.concat [ env0; env1; absl ]
  in

  let symbolic_to_value = ref SymbolicValueId.Map.empty in
  let module S : MatchJoinState = struct
    let span = span
    let loop_id = loop_id
    let nabs = nabs
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = symbolic_to_value
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  (* Rem.: this function raises exceptions *)
  let rec join_prefixes (env0 : env) (env1 : env) : env =
    match (env0, env1) with
    | ( (EBinding (BDummy b0, v0) as var0) :: env0',
        (EBinding (BDummy b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        [%ldebug
          "join_prefixes: BDummys:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and we must join their values. Otherwise, it means we
           are not in the prefix anymore *)
        if DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Still in the prefix: match the values *)
          [%sanity_check] span (b0 = b1);
          let b = b0 in
          let v = M.match_tvalues ctx0 ctx1 v0 v1 in
          let var = EBinding (BDummy b, v) in
          (* Continue *)
          var :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | ( (EBinding (BVar b0, v0) as var0) :: env0',
        (EBinding (BVar b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        [%ldebug
          "join_prefixes: BVars:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        [%sanity_check] span (b0 = b1);
        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BVar b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (EAbs abs0 as abs) :: env0', EAbs abs1 :: env1' ->
        (* Debug *)
        [%ldebug
          "join_prefixes: Abs:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- abs0:\n"
          ^ abs_to_string span ctx0 abs0
          ^ "\n\n- abs1:\n"
          ^ abs_to_string span ctx1 abs1
          ^ "\n"];

        (* Same as for the dummy values: there are two cases *)
        if AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          [%sanity_check] span (abs0 = abs1);
          (* Continue *)
          abs :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | _ ->
        (* The elements don't match: we are not in the prefix anymore *)
        join_suffixes env0 env1
  in

  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> [%craise] span "Unreachable"
    in

    [%ldebug
      "- env0:\n"
      ^ env_to_string span ctx0 (List.rev env0) ~filter:false
      ^ "\n\n- env1:\n"
      ^ env_to_string span ctx1 (List.rev env1) ~filter:false
      ^ "\n"];

    let env = List.rev (EFrame :: join_prefixes env0 env1) in

    (* Construct the joined context - of course, the type, fun, etc. contexts
     * should be the same in the two contexts *)
    let {
      type_ctx;
      crate;
      fun_ctx;
      region_groups;
      type_vars;
      const_generic_vars;
      const_generic_vars_map;
      env = _;
      ended_regions = ended_regions0;
    } =
      ctx0
    in
    let {
      type_ctx = _;
      crate = _;
      fun_ctx = _;
      region_groups = _;
      type_vars = _;
      const_generic_vars = _;
      const_generic_vars_map = _;
      env = _;
      ended_regions = ended_regions1;
    } =
      ctx1
    in
    let ended_regions = RegionId.Set.union ended_regions0 ended_regions1 in
    let ctx : eval_ctx =
      {
        crate;
        type_ctx;
        fun_ctx;
        region_groups;
        type_vars;
        const_generic_vars;
        const_generic_vars_map;
        env;
        ended_regions;
      }
    in
    let join_info : ctx_join_info =
      { symbolic_to_value = !symbolic_to_value }
    in
    Ok (ctx, join_info)
  with ValueMatchFailure e -> Error e

(** Destructure all the new abstractions *)
let destructure_new_abs (span : Meta.span) (loop_id : LoopId.id)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  [%ltrace "ctx:\n\n" ^ eval_ctx_to_string ctx];
  let abs_kind : abs_kind = Loop (loop_id, None) in
  let can_end = true in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : AbstractionId.id) : bool =
    not (AbstractionId.Set.mem id old_abs_ids)
  in
  let env =
    env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs span abs_kind can_end destructure_shared_values ctx
              abs
          in
          abs
        else abs)
      ctx.env
  in
  let ctx = { ctx with env } in
  [%ltrace "resulting ctx:\n\n" ^ eval_ctx_to_string ctx];
  Invariants.check_invariants span ctx;
  ctx

(** Refresh the ids of the fresh abstractions.

    We do this because {!prepare_ashared_loans} introduces some non-fixed
    abstractions in contexts which are later joined: we have to make sure two
    contexts we join don't have non-fixed abstractions with the same ids. *)
let refresh_abs (old_abs : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let ids, _ = compute_ctx_ids ctx in
  let abs_to_refresh = AbstractionId.Set.diff ids.aids old_abs in
  let aids_subst =
    List.map
      (fun id -> (id, fresh_abstraction_id ()))
      (AbstractionId.Set.elements abs_to_refresh)
  in
  let aids_subst = AbstractionId.Map.of_list aids_subst in
  let asubst id =
    match AbstractionId.Map.find_opt id aids_subst with
    | None -> id
    | Some id -> id
  in
  let env =
    Substitute.env_subst_ids { Substitute.empty_id_subst with asubst } ctx.env
  in
  { ctx with env }

let loop_join_origin_with_continue_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_ids : ids_sets) (old_ctx : eval_ctx)
    (ctxl : eval_ctx list) : (eval_ctx * eval_ctx list) * eval_ctx =
  let with_abs_conts = false in
  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
  *)
  let joined_ctx = ref old_ctx in
  let rec join_one_aux (ctx : eval_ctx) : eval_ctx =
    match join_ctxs span loop_id fixed_ids ~with_abs_conts !joined_ctx ctx with
    | Ok (nctx, _) ->
        joined_ctx := nctx;
        ctx
    | Error err ->
        let ctx =
          (* TODO: simplify *)
          match err with
          | LoanInRight bid ->
              InterpreterBorrows.end_loan_no_synth config span bid ctx
          | LoansInRight bids ->
              InterpreterBorrows.end_loans_no_synth config span bids ctx
          | LoanInLeft bid ->
              joined_ctx :=
                InterpreterBorrows.end_loan_no_synth config span bid !joined_ctx;
              ctx
          | LoansInLeft bids ->
              joined_ctx :=
                InterpreterBorrows.end_loans_no_synth config span bids
                  !joined_ctx;
              ctx
          | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
        in
        join_one_aux ctx
  in
  let join_one (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ =
      simplify_dummy_values_useless_abs config span fixed_ids.aids ctx
    in
    [%ltrace
      "join_one: after simplify_dummy_values_useless_abs (fixed_ids.abs_ids = "
      ^ AbstractionId.Set.to_string None fixed_ids.aids
      ^ "):\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span loop_id fixed_ids.aids ctx in
    [%ltrace
      "join_one: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids ctx
    in
    [%ltrace
      "join_one: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Refresh the fresh abstractions *)
    let ctx = refresh_abs fixed_ids.aids ctx in
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Join the two contexts  *)
    let ctx1 = join_one_aux ctx in
    [%ltrace
      "join_one: after join:\n" ^ eval_ctx_to_string ~span:(Some span) ctx1];

    (* Collapse to eliminate the markers *)
    joined_ctx :=
      collapse_ctx_with_merge config span loop_id fixed_ids ~with_abs_conts
        !joined_ctx;
    [%ltrace
      "join_one: after join-collapse:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;

    (* Reduce again to reach a fixed point *)
    joined_ctx :=
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids !joined_ctx;
    [%ltrace
      "join_one: after last reduce:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;
    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  ((old_ctx, ctxl), !joined_ctx)

let loop_join_break_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_ids : ids_sets) (ctxl : eval_ctx list) :
    eval_ctx =
  (* Simplify the contexts *)
  let with_abs_conts = false in
  let prepare_ctx (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ =
      simplify_dummy_values_useless_abs config span fixed_ids.aids ctx
    in
    [%ltrace
      "join_one: after simplify_dummy_values_useless_abs (fixed_ids.abs_ids = "
      ^ AbstractionId.Set.to_string None fixed_ids.aids
      ^ "):\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span loop_id fixed_ids.aids ctx in
    [%ltrace
      "join_one: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids ctx
    in
    [%ltrace
      "join_one: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Refresh the fresh abstractions *)
    let ctx = refresh_abs fixed_ids.aids ctx in
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    ctx
  in
  let ctxl = List.map prepare_ctx ctxl in

  match ctxl with
  | [] -> [%internal_error] span
  | [ ctx ] ->
      (* Special case: simply remove the continuation expressions from the fresh abs *)
      let update (e : env_elem) : env_elem =
        match (e : env_elem) with
        | EAbs abs ->
            if AbstractionId.Set.mem abs.abs_id fixed_ids.aids then e
            else EAbs { abs with cont = None; kind = Loop (loop_id, None) }
        | EBinding _ | EFrame -> e
      in
      { ctx with env = List.map update ctx.env }
  | ctx :: ctxl ->
      let joined_ctx = ref ctx in

      (* # Join the contexts, one by one.

          For every context, we repeteadly attempt to join it with the current
          result of the join: if we fail (because we need to end loans for instance),
          we update the context and retry.
       *)
      let rec join_one_aux (ctx : eval_ctx) =
        match
          join_ctxs span loop_id fixed_ids ~with_abs_conts !joined_ctx ctx
        with
        | Ok (nctx, _) ->
            joined_ctx := nctx;
            ctx
        | Error err ->
            let ctx =
              (* TODO: simplify *)
              match err with
              | LoanInRight bid ->
                  InterpreterBorrows.end_loan_no_synth config span bid ctx
              | LoansInRight bids ->
                  InterpreterBorrows.end_loans_no_synth config span bids ctx
              | LoanInLeft bid ->
                  joined_ctx :=
                    InterpreterBorrows.end_loan_no_synth config span bid
                      !joined_ctx;
                  ctx
              | LoansInLeft bids ->
                  joined_ctx :=
                    InterpreterBorrows.end_loans_no_synth config span bids
                      !joined_ctx;
                  ctx
              | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
            in
            join_one_aux ctx
      in
      let join_one (ctx : eval_ctx) =
        (* Join the two contexts  *)
        let ctx1 = join_one_aux ctx in
        [%ltrace
          "join_one: after join:\n" ^ eval_ctx_to_string ~span:(Some span) ctx1];

        (* Collapse to eliminate the markers *)
        joined_ctx :=
          collapse_ctx_with_merge config span loop_id fixed_ids ~with_abs_conts
            !joined_ctx;
        [%ltrace
          "join_one: after join-collapse:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx;

        (* Reduce again to reach a fixed point *)
        joined_ctx :=
          reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids
            !joined_ctx;
        [%ltrace
          "join_one: after last reduce:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx
      in
      List.iter join_one ctxl;

      (* Update the fresh region abstractions *)
      !joined_ctx

let loop_match_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx
    * eval_ctx
    * tvalue SymbolicValueId.Map.t
    * abs AbstractionId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* Simplify the target context *)
  let tgt_ctx, cc =
    simplify_dummy_values_useless_abs config span fixed_ids.aids tgt_ctx
  in
  [%ltrace
    "\n- tgt_ctx after simplify_dummy_values_useless_abs:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Reduce the context *)
  let tgt_ctx =
    reduce_ctx config span ~with_abs_conts:true loop_id fixed_ids tgt_ctx
  in
  [%ltrace "\n- tgt_ctx after reduce_ctx:\n" ^ eval_ctx_to_string tgt_ctx];

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations)
  *)
  let tgt_ctx, cc =
    comp cc
      (prepare_loop_match_ctx_with_target config span loop_id fixed_ids src_ctx
         tgt_ctx)
  in
  [%ltrace
    "\nFinished preparing the match:" ^ "\n- fixed_ids: "
    ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* TODO: preparing the match might have moved some borrows to anonymous values,
     so we could call [simplify_dummy_values_useless_abs] again, but if we do so
     it would be better to call [reduce_ctx] and [prepare_loop_match_ctx_with_target]
     again (potentially within a loop). *)

  (* Join the source context with the target context *)
  let joined_ctx, join_info =
    match
      join_ctxs span loop_id fixed_ids ~with_abs_conts:true src_ctx tgt_ctx
    with
    | Ok ctx -> ctx
    | Error _ -> [%craise] span "Could not join the contexts"
  in
  [%ltrace
    "\nResult of the join:\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- join_info: "
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (Print.pair_to_string (tvalue_to_string src_ctx)
           (tvalue_to_string src_ctx))
        join_info.symbolic_to_value];

  (* Project the context to only preserve the right part, which corresponds to the
     target *)
  let joined_ctx = project_context span fixed_ids PRight joined_ctx in
  let joined_symbolic_to_tgt_value =
    SymbolicValueId.Map.map (fun (_, x) -> x) join_info.symbolic_to_value
  in
  [%ltrace
    "\nAfter projection: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value];

  (* Reduce the context *)
  let joined_ctx =
    reduce_ctx config span ~with_abs_conts:true loop_id fixed_ids joined_ctx
  in
  [%ltrace
    "\nAfter reducing the context: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  [%ltrace
    "\nAbout to match:" ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
    ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Check that the source context (i.e., the fixed-point context) matches
     the resulting target context. *)
  let src_to_joined_maps =
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : tvalue =
      match snd (lookup_loan span ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (pm, _, v, _)) ->
          [%sanity_check] span (pm = PNone);
          v
      | _ -> [%craise] span "Unreachable"
    in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_joined id = lookup_shared_loan id joined_ctx in
    (* Match *)
    match
      match_ctxs span ~check_equiv:false ~check_kind:false ~check_can_end:false
        fixed_ids lookup_in_src lookup_in_joined src_ctx joined_ctx
    with
    | Some ctx -> ctx
    | None -> [%craise] span "Could not match the contexts"
  in
  [%ltrace
    "The match was successful:" ^ "\n\n- src_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) src_ctx
    ^ "\n\n- joined_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) joined_ctx
    ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
    ^ "\n\n- src_to_joined_maps: "
    ^ ids_maps_to_string joined_ctx src_to_joined_maps];

  (* Sanity check *)
  if !Config.sanity_checks then
    Invariants.check_borrowed_values_invariant span joined_ctx;

  (* Compute the loop input values and abstractions *)
  [%ltrace
    "about to compute the input values and abstractions:"
    ^ "\n- fp_input_svalues: "
    ^ String.concat ", " (List.map SymbolicValueId.to_string fp_input_svalues)
    ^ "\n- src_to_joined_maps:\n"
    ^ ids_maps_to_string joined_ctx src_to_joined_maps
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value
    ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];
  let input_values =
    SymbolicValueId.Map.of_list
      (List.map
         (fun sid ->
           (* We retrieve the value in two steps:
               - source to joined (which *has* to be a symbolic value
               - joined to target *)
           let v =
             match
               SymbolicValueId.Map.find_opt sid
                 src_to_joined_maps.sid_to_value_map
             with
             | Some v -> v
             | None ->
                 [%craise] span
                   ("Could not find symbolic value @"
                   ^ SymbolicValueId.to_string sid
                   ^ " in src_to_joined_map")
           in
           let sid' = symbolic_tvalue_get_id span v in
           let v =
             match
               SymbolicValueId.Map.find_opt sid' joined_symbolic_to_tgt_value
             with
             | Some v -> v
             | None ->
                 [%craise] span
                   ("Could not find symbolic value @"
                   ^ SymbolicValueId.to_string sid
                   ^ " in joined_symbolic_to_tgt_map")
           in
           (sid, v))
         fp_input_svalues)
  in
  let input_abs =
    let aid_map =
      AbstractionId.Map.of_list
        (AbstractionId.InjSubst.bindings src_to_joined_maps.aid_map)
    in
    AbstractionId.Map.filter_map
      (fun src_id joined_id ->
        if AbstractionId.Set.mem src_id fixed_ids.aids then None
        else Some (ctx_lookup_abs joined_ctx joined_id))
      aid_map
  in

  [%ltrace
    "Input values:\n"
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (tvalue_to_string ~span:(Some span) src_ctx)
        input_values
    ^ "\nInput abs:\n"
    ^ AbstractionId.Map.to_string (Some "  ")
        (abs_to_string span src_ctx)
        input_abs];

  (* *)
  Invariants.check_invariants span joined_ctx;

  (* We continue with the *fixed-point* context *)
  ((src_ctx, tgt_ctx, input_values, input_abs), cc)

let loop_match_break_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx
    * eval_ctx
    * tvalue SymbolicValueId.Map.t
    * abs AbstractionId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* We have to consider the possibility that the break context is not the result
     of a join (because there was a single break in the loop): in this case there
     is no point in joining the break context with the target context, we directly
     check if they are equivalent.

     TODO: is this really useful?
  *)
  let src_to_tgt_maps =
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : tvalue =
      match snd (lookup_loan span ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (pm, _, v, _)) ->
          [%sanity_check] span (pm = PNone);
          v
      | _ -> [%craise] span "Unreachable"
    in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    (* Match *)
    match_ctxs span ~check_equiv:false ~check_kind:false ~check_can_end:false
      fixed_ids lookup_in_src lookup_in_tgt src_ctx tgt_ctx
  in

  match src_to_tgt_maps with
  | Some src_to_tgt_maps ->
      [%ltrace
        "The match was successful:" ^ "\n\n- src_ctx: "
        ^ eval_ctx_to_string ~span:(Some span) src_ctx
        ^ "\n\n- tgt_ctx: "
        ^ eval_ctx_to_string ~span:(Some span) tgt_ctx
        ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
        ^ "\n\n- src_to_tgt_maps: "
        ^ ids_maps_to_string tgt_ctx src_to_tgt_maps];

      (* Sanity check *)
      if !Config.sanity_checks then
        Invariants.check_borrowed_values_invariant span tgt_ctx;

      (* Compute the loop input values and abstractions *)
      [%ltrace
        "about to compute the input values and abstractions:"
        ^ "\n- fp_input_svalues: "
        ^ String.concat ", "
            (List.map SymbolicValueId.to_string fp_input_svalues)
        ^ "\n- src_to_tgt_maps:\n"
        ^ ids_maps_to_string tgt_ctx src_to_tgt_maps
        ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx:\n"
        ^ eval_ctx_to_string tgt_ctx];
      let input_values =
        SymbolicValueId.Map.of_list
          (List.map
             (fun sid ->
               let v =
                 SymbolicValueId.Map.find sid src_to_tgt_maps.sid_to_value_map
               in
               (sid, v))
             fp_input_svalues)
      in
      let input_abs =
        let aid_map =
          AbstractionId.Map.of_list
            (AbstractionId.InjSubst.bindings src_to_tgt_maps.aid_map)
        in
        AbstractionId.Map.filter_map
          (fun src_id tgt_id ->
            if AbstractionId.Set.mem src_id fixed_ids.aids then None
            else Some (ctx_lookup_abs tgt_ctx tgt_id))
          aid_map
      in

      [%ltrace
        "Input values:\n"
        ^ SymbolicValueId.Map.to_string (Some "  ")
            (tvalue_to_string ~span:(Some span) src_ctx)
            input_values
        ^ "\nInput abs:\n"
        ^ AbstractionId.Map.to_string (Some "  ")
            (abs_to_string span src_ctx)
            input_abs];

      (* We continue with the *break* context *)
      ((src_ctx, tgt_ctx, input_values, input_abs), fun e -> e)
  | _ ->
      [%ltrace "Match not successful"];

      loop_match_ctx_with_target config span loop_id fp_input_svalues fixed_ids
        src_ctx tgt_ctx
