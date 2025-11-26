open Values
open Types
open Contexts
open Utils
open TypesUtils
open ValuesUtils
open InterpUtils
open InterpBorrowsCore
open InterpAbs
open InterpJoinCore
open InterpMatchCtxs

(** The local logger *)
let log = Logging.reduce_collapse_log

(** Attempts to eliminate useless shared loans, in particular to get rid of
    remaining markers.

    We simply eliminate shared loans which don't have corresponding shared
    borrows.

    TODO: will not be necessary once we destructure the avalues. *)
let eliminate_shared_loans (span : Meta.span) (ctx : eval_ctx) : eval_ctx =
  (* Compute the set of shared borrows *)
  let ids, _ = compute_ctx_ids ctx in
  let shared_borrows = ids.non_unique_shared_borrow_ids in

  let update_loans =
    object (self)
      inherit [_] map_abs as super

      method! visit_ASharedLoan env pm bid sv child =
        if
          (not (BorrowId.Set.mem bid shared_borrows))
          &&
          (* We have to pay attention to markers: if there is a borrow/loan
              inside the shared value, by removing the shared loan we forget
              about the marker, which can be a problem *)
          not (value_has_loans_or_borrows (Some span) ctx sv.value)
        then self#visit_AEndedSharedLoan env sv child
        else super#visit_ASharedLoan env pm bid sv child
    end
  in
  let update_abs (abs : abs) : abs =
    (* Only update the non-frozen abstractions *)
    if not abs.can_end then update_loans#visit_abs () abs else abs
  in
  let ctx = ctx_map_abs update_abs ctx in

  (* Remove the ended shared loans, if possible *)
  let ctx = InterpBorrows.eliminate_ended_shared_loans span ctx in

  (* *)
  ctx

(** Compute the set of shared loans without markers appearing in the context *)
let get_non_marked_shared_loans (ctx : eval_ctx) : BorrowId.Set.t =
  let non_marked_loans = ref BorrowId.Set.empty in
  let collect_loans =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_ASharedLoan env pm lid sv child =
        if pm = PNone then
          non_marked_loans := BorrowId.Set.add lid !non_marked_loans;
        super#visit_ASharedLoan env pm lid sv child

      method! visit_VSharedLoan env lid sv =
        non_marked_loans := BorrowId.Set.add lid !non_marked_loans;
        super#visit_VSharedLoan env lid sv
    end
  in
  collect_loans#visit_eval_ctx () ctx;
  !non_marked_loans

(** Attempts to eliminate remaining markers over shared borrows.

    We can eliminate a marker over a shared borrow if the corresponding loan in
    the context doesn't have markers. The reason is that we are always allowed
    to introduce a shared borrow for an existing shared loan: in order to remove
    the marker, we can introduce a shared borrow in the other environment.

    For instance, the following is legal:
    {[
      x -> SL l v
      abs { |SB l| } // the left environment has a borrow, but not the right one

        ~>

      x -> SL l v
      abs { SB l } // introduce SB l in the right environment and add it to the abstraction
    ]} *)

let eliminate_shared_borrow_markers (span : Meta.span)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_id * ty) list ref option)
    (ctx : eval_ctx) : eval_ctx =
  (* Compute the set of loans without markers *)
  let non_marked_loans = get_non_marked_shared_loans ctx in

  match shared_borrows_seq with
  | None ->
      let update_borrows =
        object
          inherit [_] map_eval_ctx as super

          method! visit_ASharedBorrow env pm bid sid =
            let pm =
              if BorrowId.Set.mem bid non_marked_loans then PNone else pm
            in
            super#visit_ASharedBorrow env pm bid sid
        end
      in
      update_borrows#visit_eval_ctx () ctx
  | Some shared_borrows ->
      (* We need to register the borrows out of which we eliminate the markers.
         For now, we can't register the addition of shared borrows at arbitrary
         positions. TODO: generalize. *)
      let update_avalue (offset : int ref) (aid : abs_id) (i : int)
          (av : tavalue) : tavalue =
        match av.value with
        | ABorrow (ASharedBorrow (pm, bid, sid)) ->
            let pm =
              if pm <> PNone && BorrowId.Set.mem bid non_marked_loans then (
                (* Register the fact that we need to introduce a new shared borrow *)
                let pm' =
                  match pm with
                  | PNone -> [%internal_error] span
                  | PLeft -> PRight
                  | PRight -> PLeft
                in
                let _, ty, _ = ty_get_ref av.ty in
                shared_borrows :=
                  (aid, i + !offset, pm', bid, ty) :: !shared_borrows;
                offset := !offset + 1;
                PNone)
              else pm
            in
            { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
        | _ -> av
      in
      let update_borrows =
        object
          inherit [_] map_eval_ctx

          method! visit_abs _ abs =
            {
              abs with
              avalues = List.mapi (update_avalue (ref 0) abs.abs_id) abs.avalues;
            }
        end
      in
      update_borrows#visit_eval_ctx () ctx

(** Utility.

    An environment augmented with information about its
    borrows/loans/abstractions for the purpose of merging abstractions together.
    We provide functions to update this information when merging two
    abstractions together. We use it in {!reduce_ctx} and {!collapse_ctx}. *)
type ctx_with_info = { ctx : eval_ctx; info : abs_borrows_loans_maps }

let ctx_with_info_merge_into_first_abs (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : ctx_with_info)
    (abs_id0 : AbsId.id) (abs_id1 : AbsId.id) : ctx_with_info * abs_id =
  [%ldebug
    "Merging abstraction " ^ AbsId.to_string abs_id1 ^ " into abstraction "
    ^ AbsId.to_string abs_id0];
  (* Compute the new context and the new abstraction id *)
  let nctx, nabs_id =
    merge_into_first_abstraction span abs_kind ~can_end ~with_abs_conts
      merge_funs ctx.ctx abs_id0 abs_id1
  in
  let nabs = ctx_lookup_abs nctx nabs_id in
  [%ldebug
    "abstraction resulting from the merge:\n" ^ abs_to_string span ctx.ctx nabs];
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
    compute_abs_borrows_loans_maps span (fun _ -> true) ctx.ctx [ EAbs nabs ]
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
    let update_to_abs (key_to_string : M.key -> string)
        (abs_to : S.t AbsId.Map.t) (to_nabs : AbsId.Set.t M.t)
        (to_abs : AbsId.Set.t M.t) : AbsId.Set.t M.t =
      (* Remove the old bindings from borrow/loan ids to the two region
         abstractions we just merged (because those two region abstractions
         do not exist anymore). *)
      let abs0_elems = AbsId.Map.find abs_id0 abs_to in
      let abs1_elems = AbsId.Map.find abs_id1 abs_to in
      let abs01_elems = S.union abs0_elems abs1_elems in
      let to_abs = M.filter (fun id _ -> not (S.mem id abs01_elems)) to_abs in
      (* Add the new bindings from the borrows/loan ids that we find in the
         merged abstraction to this abstraction's id *)
      let merge (key : M.key) (abs0 : AbsId.Set.t) (abs1 : AbsId.Set.t) =
        (* We shouldn't see the same key twice *)
        [%craise] span
          ("Unreachable:\n key: " ^ key_to_string key ^ "\n- abs0: "
          ^ AbsId.Set.to_string None abs0
          ^ "\n- abs1: "
          ^ AbsId.Set.to_string None abs1)
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
  let marked_unique_borrow_id_to_string
      ((pm, bid, sid) : marked_unique_borrow_id) : string =
    let s =
      match sid with
      | None -> "MB@" ^ show_borrow_id bid
      | Some sid ->
          "SB@" ^ show_borrow_id bid ^ "(^" ^ show_shared_borrow_id sid ^ ")"
    in
    Print.Values.add_proj_marker pm s
  in
  let borrow_to_abs =
    UpdateMarkedUniqueBorrowId.update_to_abs marked_unique_borrow_id_to_string
      abs_to_borrows borrow_to_nabs borrow_to_abs
  in
  let non_unique_borrow_to_abs =
    UpdateMarkedBorrowId.update_to_abs show_marked_borrow_id
      abs_to_non_unique_borrows non_unique_borrow_to_nabs
      non_unique_borrow_to_abs
  in
  let loan_to_abs =
    UpdateMarkedLoanId.update_to_abs show_marked_borrow_id abs_to_loans
      loan_to_nabs loan_to_abs
  in
  let module UpdateSymbProj =
    UpdateToAbs (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
  in
  let borrow_proj_to_abs =
    UpdateSymbProj.update_to_abs show_marked_norm_symb_proj abs_to_borrow_projs
      borrow_proj_to_nabs borrow_proj_to_abs
  in
  let loan_proj_to_abs =
    UpdateSymbProj.update_to_abs show_marked_norm_symb_proj abs_to_loan_projs
      loan_proj_to_nabs loan_proj_to_abs
  in

  (* Update the maps from abstractions to marked borrows/loans or
     symbolic value projections.
  *)
  let update_abs_to nabs_to abs_to =
    (* Remove the two region abstractions we merged *)
    let m = AbsId.Map.remove abs_id0 (AbsId.Map.remove abs_id1 abs_to) in
    (* Add the merged abstraction *)
    AbsId.Map.add_strict nabs_id (AbsId.Map.find nabs_id nabs_to) m
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
  ({ ctx = nctx; info }, nabs_id)

exception AbsToMerge of abs_id * abs_id

(** Repeatedly iterate through the borrows/loans in an environment and merge the
    abstractions that have to be merged according to a user-provided policy.

    [sequence]: we save the sequence of merges there, in reverse order (the last
    merges are pushed at the front). *)
let repeat_iter_borrows_merge (span : Meta.span) (fixed_abs_ids : AbsId.Set.t)
    (abs_kind : abs_kind) ~(can_end : bool) ~(with_abs_conts : bool)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (merge_funs : merge_duplicates_funcs option)
    (iter : ctx_with_info -> ('a -> unit) -> unit)
    (policy : ctx_with_info -> 'a -> (abs_id * abs_id) option) (ctx : eval_ctx)
    : eval_ctx =
  (* Compute the information *)
  let ctx =
    let is_fresh_abs_id (id : AbsId.id) : bool =
      not (AbsId.Set.mem id fixed_abs_ids)
    in
    let explore (abs : abs) = is_fresh_abs_id abs.abs_id in
    let info = compute_abs_borrows_loans_maps span explore ctx ctx.env in
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
      let ctx, naid =
        ctx_with_info_merge_into_first_abs span abs_kind ~can_end
          ~with_abs_conts merge_funs ctx abs_id0 abs_id1
      in
      (* Remember the sequence of merges *)
      Option.iter
        (fun sequence -> sequence := (abs_id0, abs_id1, naid) :: !sequence)
        sequence;
      explore_merge ctx
  in
  explore_merge ctx

let convert_fresh_dummy_values_to_abstractions (span : Meta.span)
    (fresh_abs_kind : abs_kind) (fixed_dids : DummyVarId.Set.t)
    (ctx0 : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx0
    ^ "\n\n- fixed_dids: "
    ^ DummyVarId.Set.to_string None fixed_dids];

  let can_end = true in
  let is_fresh_did (id : DummyVarId.id) : bool =
    not (DummyVarId.Set.mem id fixed_dids)
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
                   convert_value_to_abstractions span fresh_abs_kind ~can_end
                     ctx v
                 in
                 Invariants.opt_type_check_absl span ctx absl;
                 List.map (fun abs -> EAbs abs) absl)
               else [ ee ])
         ctx.env)
  in
  let ctx = { ctx with env } in
  [%ltrace
    "after converting values to abstractions:" ^ "\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  ctx

(** Reduce an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point (this is our equivalent of Abstract Interpretation's
    **widening** operation).

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not) and convert them into abstractions. TODO: we
      don't do this anymore
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
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    ~(with_abs_conts : bool) (span : Meta.span) (fresh_abs_kind : abs_kind)
    (fixed_abs_ids : AbsId.Set.t) ?(fixed_dids : DummyVarId.Set.t option = None)
    (ctx0 : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace "- ctx0:\n" ^ eval_ctx_to_string ~span:(Some span) ctx0];

  let with_markers = merge_funs <> None in
  let can_end = true in

  let ctx = ctx0 in
  (* Convert the fresh dummy values to abstractions, if the caller requests so
     (note that when we convert values to abstractions, the resulting abstraction
     should be destructured) *)
  let ctx =
    match fixed_dids with
    | None -> ctx
    | Some fixed_dids ->
        convert_fresh_dummy_values_to_abstractions span fresh_abs_kind
          fixed_dids ctx
  in

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
        val get_borrow_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
        val get_to_loans : abs_borrows_loans_maps -> Set.t AbsId.Map.t
      end) =
  struct
    (* We iterate over the *new* abstractions, then over the **loans**
       (concrete or symbolic) in the abstractions.

       We do this because we want to control the order in which abstractions
       are merged (the ids are iterated in increasing order). Otherwise, we
       could simply iterate over all the borrows in [loan_to_abs] for instance... *)
    let iterate_loans (ctx : ctx_with_info) (merge : abs_id * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Iterate over the loans *)
          let lids = AbsId.Map.find abs_id0 (Marked.get_to_loans ctx.info) in
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
            match AbsId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                [%ltrace
                  "merging abstraction " ^ AbsId.to_string abs_id1 ^ " into "
                  ^ AbsId.to_string abs_id0 ^ ":" ^ "\n- abs "
                  ^ AbsId.to_string abs_id1 ^ ":\n"
                  ^ abs_to_string span ctx.ctx (ctx_lookup_abs ctx.ctx abs_id1)
                  ^ "\n\n- abs " ^ AbsId.to_string abs_id0 ^ ":\n"
                  ^ abs_to_string span ctx.ctx (ctx_lookup_abs ctx.ctx abs_id0)
                  ^ "\n\n"
                  ^ eval_ctx_to_string ~span:(Some span) ctx.ctx];
                Some (abs_id0, abs_id1))

    (* Iterate over the loans and merge the abstractions *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge span fixed_abs_ids fresh_abs_kind ~can_end
        ~with_abs_conts sequence merge_funs iterate_loans merge_policy ctx
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
    "- after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers at this point. *)
  let ctx = reorder_fresh_abs span true fixed_abs_ids ctx in

  [%ltrace
    "- after reduce and reorder borrows/loans and abstractions:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Return the new context *)
  ctx

(** reduce_ctx can only be called in a context with no markers *)
let reduce_ctx config (span : Meta.span)
    ?(sequence : (abs_id * abs_id * abs_id) list ref option = None)
    ~(with_abs_conts : bool) (fresh_abs_kind : abs_kind)
    (fixed_abs_ids : AbsId.Set.t) (fixed_dids : DummyVarId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  (* Simplify the context *)
  let ctx, _ =
    InterpBorrows.simplify_dummy_values_useless_abs config span ctx
  in
  (* Reduce *)
  let ctx =
    reduce_ctx_with_markers None sequence span ~with_abs_conts fresh_abs_kind
      fixed_abs_ids ~fixed_dids:(Some fixed_dids) ctx
  in
  eliminate_shared_loans span ctx

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
let collapse_ctx_collapse (span : Meta.span)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "\n- initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  let can_end = true in
  let ctx0 = ctx in

  let invert_proj_marker = function
    | PNone -> [%craise] span "Unreachable"
    | PLeft -> PRight
    | PRight -> PLeft
  in

  let fixed_aids = ctx_get_frozen_abs_set ctx in

  (* Merge all the mergeable abs where the same element is present in both abs,
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
        val get_to_borrows : abs_borrows_loans_maps -> Set.t AbsId.Map.t
        val get_to_loans : abs_borrows_loans_maps -> Set.t AbsId.Map.t
        val get_borrow_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
        val get_loan_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
      end) =
  struct
    (* The iter function: iterate over the abstractions, and inside an abstraction
       over the borrows (projectors) then the loan (projectors) *)
    let iter (ctx : ctx_with_info) (f : AbsId.id * bool * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Small helper *)
          let iterate is_borrow =
            let m =
              if is_borrow then Marked.get_to_borrows ctx.info
              else Marked.get_to_loans ctx.info
            in
            let ids = AbsId.Map.find abs_id0 m in
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
    let swap_abs (info : abs_borrows_loans_maps) (abs_id0 : abs_id)
        (abs_id1 : abs_id) =
      let abs0_borrows =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements
                (AbsId.Map.find abs_id0 (Marked.get_to_borrows info))))
      in
      let abs1_loans =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements (AbsId.Map.find abs_id1 (Marked.get_to_loans info))))
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
            match AbsId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                (* Check if we need to swap *)
                Some
                  (if swap_abs ctx.info abs_id0 abs_id1 then (abs_id1, abs_id0)
                   else (abs_id0, abs_id1)))

    (* Iterate and merge *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge span fixed_aids fresh_abs_kind ~can_end
        ~with_abs_conts sequence (Some merge_funs) iter merge_policy ctx
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
    "- after collapse:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers yet *)
  let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
  let ctx = reorder_fresh_abs span true fixed_aids ctx in

  [%ltrace
    "- after collapse and reorder borrows/loans:\n"
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
let collapse_ctx_aux config (span : Meta.span)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_id * ty) list ref option)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs) (ctx0 : eval_ctx) : eval_ctx =
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx0];
  let fixed_aids =
    (* We forbid modifying the abs which are frozen or which don't have any markers *)
    let frozen = ctx_get_frozen_abs_set ctx0 in
    let abs = AbsId.Map.values (ctx_get_abs ctx0) in
    let no_markers =
      List.filter_map
        (fun (abs : abs) ->
          if abs_has_markers abs then None else Some abs.abs_id)
        abs
    in
    AbsId.Set.add_list no_markers frozen
  in

  [%ldebug "fixed_aids: " ^ AbsId.Set.to_string None fixed_aids];

  let ctx =
    reduce_ctx_with_markers (Some merge_funs) sequence span ~with_abs_conts
      fresh_abs_kind fixed_aids ctx0
  in
  [%ldebug "ctx after reduce:\n" ^ eval_ctx_to_string ctx];
  let ctx =
    collapse_ctx_collapse span ~with_abs_conts sequence fresh_abs_kind
      merge_funs ctx
  in
  [%ldebug "ctx after reduce and collapse:\n" ^ eval_ctx_to_string ctx];

  let ctx = eliminate_shared_borrow_markers span shared_borrows_seq ctx in
  [%ldebug
    "ctx after reduce, collapse and eliminate_shared_borrow_markers:\n"
    ^ eval_ctx_to_string ctx];

  let ctx = eliminate_shared_loans span ctx in
  [%ldebug
    "ctx after reduce, collapse and eliminate_shared_loans:\n"
    ^ eval_ctx_to_string ctx];

  (* Sanity check: there are no markers remaining *)
  [%sanity_check] span (not (eval_ctx_has_markers ctx));

  (* One last cleanup *)
  let ctx, _ =
    InterpBorrows.simplify_dummy_values_useless_abs config span ctx
  in
  ctx

let mk_collapse_ctx_merge_duplicate_funs (span : Meta.span)
    (fresh_abs_kind : abs_kind) (with_abs_conts : bool) (ctx : eval_ctx) :
    merge_duplicates_funcs =
  (* Rem.: the merge functions raise exceptions (that we catch). *)
  let module S : MatchJoinState = struct
    let span = span
    let fresh_abs_kind = fresh_abs_kind
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
      ABorrow (ASharedBorrow (PNone, id, ctx.fresh_shared_borrow_id ()))
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

let merge_into_first_abstraction (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(with_abs_conts : bool) (ctx : eval_ctx)
    (aid0 : AbsId.id) (aid1 : AbsId.id) : eval_ctx * AbsId.id =
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span abs_kind with_abs_conts ctx
  in
  InterpAbs.merge_into_first_abstraction span abs_kind ~can_end ~with_abs_conts
    (Some merge_funs) ctx aid0 aid1

let collapse_ctx config (span : Meta.span)
    ?(sequence : (abs_id * abs_id * abs_id) list ref option = None)
    ?(shared_borrows_seq :
        (abs_id * int * proj_marker * borrow_id * ty) list ref option =
      None) (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool)
    (ctx : eval_ctx) : eval_ctx =
  [%ldebug "Initial ctx:\n" ^ eval_ctx_to_string ctx];
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span fresh_abs_kind with_abs_conts ctx
  in
  try
    collapse_ctx_aux config span ~with_abs_conts sequence shared_borrows_seq
      fresh_abs_kind merge_funs ctx
  with ValueMatchFailure _ -> [%internal_error] span

let add_shared_borrows (span : Meta.span)
    (shared_borrows_seq : (abs_id * int * proj_marker * borrow_id * ty) list)
    (ctx : eval_ctx) : eval_ctx =
  let loans = get_non_marked_shared_loans ctx in

  let ctx = ref ctx in
  let update
      ((abs_id, i, pm, bid, ty) : abs_id * int * proj_marker * borrow_id * ty) :
      unit =
    [%sanity_check] span (BorrowId.Set.mem bid loans);
    let abs = ctx_lookup_abs !ctx abs_id in
    let rid = RegionId.Set.choose abs.regions.owned in
    let r : region = RVar (Free rid) in
    let rec update_avalues (i : int) (avl : tavalue list) : tavalue list =
      if i = 0 then (
        (* TODO: really annoying to have to insert a type here *)
        [%sanity_check] span (ty_no_regions ty);
        let nv : tavalue =
          {
            value =
              ABorrow (ASharedBorrow (pm, bid, !ctx.fresh_shared_borrow_id ()));
            ty = mk_ref_ty r ty RShared;
          }
        in
        nv :: avl)
      else
        match avl with
        | [] -> [%internal_error] span
        | av :: avl' -> av :: update_avalues (i - 1) avl'
    in
    let abs = { abs with avalues = update_avalues i abs.avalues } in
    let ctx', _ = ctx_subst_abs span !ctx abs.abs_id abs in
    ctx := ctx'
  in
  List.iter update shared_borrows_seq;

  !ctx

(** Collapse a context following a sequence *)
let collapse_ctx_following_sequence (span : Meta.span)
    (sequence : (abs_id * abs_id * abs_id) list)
    (shared_borrows_seq : (abs_id * int * proj_marker * borrow_id * ty) list)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool) (ctx0 : eval_ctx) :
    eval_ctx =
  [%ltrace
    "- ctx0:\n" ^ eval_ctx_to_string ctx0 ^ "\n- sequence:\n"
    ^ String.concat "\n"
        (List.map
           (fun (a0, a1, a2) ->
             "(" ^ AbsId.to_string a0 ^ "," ^ AbsId.to_string a1 ^ ") -> "
             ^ AbsId.to_string a2)
           sequence)];
  let ctx = ref ctx0 in
  let nabs_map = ref AbsId.Map.empty in
  let get_id (aid : abs_id) : abs_id =
    match AbsId.Map.find_opt aid !nabs_map with
    | None -> aid
    | Some aid -> aid
  in

  (* Apply the sequence of merges *)
  List.iter
    (fun (abs0, abs1, nabs) ->
      (* Substitute - the ids may have changed *)
      let abs0 = get_id abs0 in
      let abs1 = get_id abs1 in
      (* Attempt to merge - note that some region might be missing, because
         it appears only in one environment and not the other *)
      match (ctx_lookup_abs_opt !ctx abs0, ctx_lookup_abs_opt !ctx abs1) with
      | Some _, Some _ ->
          (* Merge and register the new id *)
          [%ldebug
            "Merging: " ^ AbsId.to_string abs0 ^ " <- " ^ AbsId.to_string abs1];
          let nctx, nabs' =
            InterpAbs.merge_into_first_abstraction span fresh_abs_kind
              ~can_end:true ~with_abs_conts None !ctx abs0 abs1
          in
          ctx := nctx;
          [%ldebug
            "Context after merging " ^ AbsId.to_string nabs' ^ " := ("
            ^ AbsId.to_string abs0 ^ " <- " ^ AbsId.to_string abs1 ^ "):\n"
            ^ eval_ctx_to_string !ctx];
          nabs_map := AbsId.Map.add nabs nabs' !nabs_map
      | None, Some abs | Some abs, None ->
          (* We don't have to merge anything, meaning the abstraction resulting
           from the merge is exactly the abstraction we found (what happened is
           that we're in the situation where we had to merge an abstraction
           from one side with another abstracction from the other side). *)
          [%ldebug
            "Registering: " ^ AbsId.to_string nabs ^ " --> "
            ^ AbsId.to_string abs.abs_id];
          nabs_map := AbsId.Map.add nabs abs.abs_id !nabs_map
      | None, None ->
          (* The abs, after substitution of its id, should be in one of the two environments *)
          [%internal_error] span)
    sequence;
  let ctx = !ctx in
  [%ldebug "ctx after applying the merge sequence:\n" ^ eval_ctx_to_string ctx];

  let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
  let ctx = reorder_fresh_abs span true fixed_aids ctx in
  [%ldebug "ctx after reordering the fresh abs:\n" ^ eval_ctx_to_string ctx];

  (* Update the ids used in the sequence of shared borrows *)
  let shared_borrows_seq =
    List.map
      (fun (abs_id, i, pm, bid, ty) ->
        (AbsId.Map.find abs_id !nabs_map, i, pm, bid, ty))
      shared_borrows_seq
  in
  let ctx = add_shared_borrows span shared_borrows_seq ctx in
  [%ldebug "ctx after adding the shared borrows:\n" ^ eval_ctx_to_string ctx];

  let ctx = eliminate_shared_loans span ctx in
  [%ldebug "ctx after eliminating the shared loans:\n" ^ eval_ctx_to_string ctx];

  ctx

let collapse_ctx_no_markers_following_sequence (span : Meta.span)
    (sequence : (abs_id * abs_id * abs_id) list)
    (shared_borrows_seq : (abs_id * int * proj_marker * borrow_id * ty) list)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool) (ctx : eval_ctx) :
    eval_ctx =
  try
    collapse_ctx_following_sequence span ~with_abs_conts sequence
      shared_borrows_seq fresh_abs_kind ctx
  with ValueMatchFailure _ -> [%internal_error] span
