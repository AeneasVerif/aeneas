(** This module implements support for loops.

    Throughout the module, we will use the following code as example to
    illustrate what the functions do (this function simply returns a mutable
    borrow to the nth element of a list):
    {[
      pub fn list_nth_mut<'a, T>(mut ls: &'a mut List<T>, mut i: u32) -> &'a mut T {
          loop {
              match ls {
                  List::Nil => {
                      panic!()
                  }
                  List::Cons(x, tl) => {
                      if i == 0 {
                          return x;
                      } else {
                          ls = tl;
                          i -= 1;
                      }
                  }
              }
          }
      }
    ]}

    Upon reaching the loop entry, the environment is as follows (ignoring the
    dummy variables):
    {[
      abs@0 { ML l0 }
      ls -> MB l0 (s2 : loops::List<T>)
      i -> s1 : u32
    ]}

    Upon reaching the [continue] at the end of the first iteration, the environment
    is as follows:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
      _@2 -> MB l2 (@Box (ML l4))                      // tail
      _@3 -> MB l1 (s@3 : T)                           // hd
    ]}

    The fixed point we compute is:
    {[
      abs@0 { ML l0 }
      ls -> MB l1 (s@3 : loops::List<T>)
      i -> s@4 : u32
      abs@fp { // fp: fixed-point
        MB l0
        ML l1
      }
    ]}

    From here, we deduce that [abs@fp { MB l0, ML l1}] is the loop abstraction.
  *)

module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
module S = SynthesizeSymbolic
module UF = UnionFind
open Cps
open InterpreterUtils
open InterpreterBorrows
open InterpreterExpressions

(** The local logger *)
let log = L.loops_log

type updt_env_kind =
  | AbsInLeft of V.AbstractionId.id
  | LoanInLeft of V.BorrowId.id
  | LoansInLeft of V.BorrowId.Set.t
  | AbsInRight of V.AbstractionId.id
  | LoanInRight of V.BorrowId.id
  | LoansInRight of V.BorrowId.Set.t

(** Utility exception *)
exception ValueMatchFailure of updt_env_kind

(** Utility exception *)
exception Distinct of string

type ctx_or_update = (C.eval_ctx, updt_env_kind) result

(** Union Find *)
module UnionFind = UF.Make (UF.StoreMap)

(** A small utility -

    Rem.: some environments may be ill-formed (they may contain several times
    the same loan or borrow - this happens for instance when merging
    environments). This is the reason why we use sets in some places (for
    instance, [borrow_to_abs] maps to a *set* of ids).
*)
type abs_borrows_loans_maps = {
  abs_ids : V.AbstractionId.id list;
  abs_to_borrows : V.BorrowId.Set.t V.AbstractionId.Map.t;
  abs_to_loans : V.BorrowId.Set.t V.AbstractionId.Map.t;
  abs_to_borrows_loans : V.BorrowId.Set.t V.AbstractionId.Map.t;
  borrow_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
  loan_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
  borrow_loan_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
}

(** Compute various maps linking the abstractions and the borrows/loans they contain.

    The [explore] function is used to filter abstractions.

    [no_duplicates] checks that borrows/loans are not referenced more than once
    (see the documentation for {!abs_borrows_loans_maps}).
 *)
let compute_abs_borrows_loans_maps (no_duplicates : bool)
    (explore : V.abs -> bool) (env : C.env) : abs_borrows_loans_maps =
  let abs_ids = ref [] in
  let abs_to_borrows = ref V.AbstractionId.Map.empty in
  let abs_to_loans = ref V.AbstractionId.Map.empty in
  let abs_to_borrows_loans = ref V.AbstractionId.Map.empty in
  let borrow_to_abs = ref V.BorrowId.Map.empty in
  let loan_to_abs = ref V.BorrowId.Map.empty in
  let borrow_loan_to_abs = ref V.BorrowId.Map.empty in

  let module R (Id0 : Identifiers.Id) (Id1 : Identifiers.Id) = struct
    (*
       [check_singleton_sets]: check that the mapping maps to a singletong.
       [check_not_already_registered]: check if the mapping was not already registered.
    *)
    let register_mapping (check_singleton_sets : bool)
        (check_not_already_registered : bool) (map : Id1.Set.t Id0.Map.t ref)
        (id0 : Id0.id) (id1 : Id1.id) : unit =
      (* Sanity check *)
      (if check_singleton_sets || check_not_already_registered then
       match Id0.Map.find_opt id0 !map with
       | None -> ()
       | Some set ->
           assert (
             (not check_not_already_registered) || not (Id1.Set.mem id1 set)));
      (* Update the mapping *)
      map :=
        Id0.Map.update id0
          (fun ids ->
            match ids with
            | None -> Some (Id1.Set.singleton id1)
            | Some ids ->
                (* Sanity check *)
                assert (not check_singleton_sets);
                assert (
                  (not check_not_already_registered)
                  || not (Id1.Set.mem id1 ids));
                (* Update *)
                Some (Id1.Set.add id1 ids))
          !map
  end in
  let module RAbsBorrow = R (V.AbstractionId) (V.BorrowId) in
  let module RBorrowAbs = R (V.BorrowId) (V.AbstractionId) in
  let register_borrow_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_borrows abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates borrow_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
  in

  let register_loan_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_loans abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates loan_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
  in

  let explore_abs =
    object (self : 'self)
      inherit [_] V.iter_typed_avalue as super

      (** Make sure we don't register the ignored ids *)
      method! visit_aloan_content abs_id lc =
        match lc with
        | AMutLoan _ | ASharedLoan _ ->
            (* Process those normally *)
            super#visit_aloan_content abs_id lc
        | AIgnoredMutLoan (_, child)
        | AEndedIgnoredMutLoan { child; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child ->
            (* Ignore the id of the loan, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutLoan _ | AEndedSharedLoan _ -> raise (Failure "Unreachable")

      (** Make sure we don't register the ignored ids *)
      method! visit_aborrow_content abs_id bc =
        match bc with
        | AMutBorrow _ | ASharedBorrow _ | AProjSharedBorrow _ ->
            (* Process those normally *)
            super#visit_aborrow_content abs_id bc
        | AIgnoredMutBorrow (_, child)
        | AEndedIgnoredMutBorrow { child; given_back = _; given_back_meta = _ }
          ->
            (* Ignore the id of the borrow, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            raise (Failure "Unreachable")

      method! visit_borrow_id abs_id bid = register_borrow_id abs_id bid
      method! visit_loan_id abs_id lid = register_loan_id abs_id lid
    end
  in

  C.env_iter_abs
    (fun abs ->
      let abs_id = abs.abs_id in
      if explore abs then (
        abs_to_borrows :=
          V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty !abs_to_borrows;
        abs_to_loans :=
          V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty !abs_to_loans;
        abs_ids := abs.abs_id :: !abs_ids;
        List.iter (explore_abs#visit_typed_avalue abs.abs_id) abs.avalues)
      else ())
    env;

  (* Rem.: there is no need to reverse the abs ids, because we explored the environment
     starting with the freshest values and abstractions *)
  {
    abs_ids = !abs_ids;
    abs_to_borrows = !abs_to_borrows;
    abs_to_loans = !abs_to_loans;
    abs_to_borrows_loans = !abs_to_borrows_loans;
    borrow_to_abs = !borrow_to_abs;
    loan_to_abs = !loan_to_abs;
    borrow_loan_to_abs = !borrow_loan_to_abs;
  }

(** Refresh the ids of the fresh abstractions.

    We do this because {!prepare_ashared_loans} introduces some non-fixed
    abstractions in contexts which are later joined: we have to make sure two
    contexts we join don't have non-fixed abstractions with the same ids.
  *)
let refresh_abs (old_abs : V.AbstractionId.Set.t) (ctx : C.eval_ctx) :
    C.eval_ctx =
  let ids, _ = compute_context_ids ctx in
  let abs_to_refresh = V.AbstractionId.Set.diff ids.aids old_abs in
  let aids_subst =
    List.map
      (fun id -> (id, C.fresh_abstraction_id ()))
      (V.AbstractionId.Set.elements abs_to_refresh)
  in
  let aids_subst = V.AbstractionId.Map.of_list aids_subst in
  let subst id =
    match V.AbstractionId.Map.find_opt id aids_subst with
    | None -> id
    | Some id -> id
  in
  let env =
    Subst.env_subst_ids
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      subst ctx.env
  in
  { ctx with C.env }

(** Reorder the loans and borrows in the fresh abstractions.

    We do this in order to enforce some structure in the environments: this
    allows us to find fixed-points. Note that this function needs to be
    called typically after we merge abstractions together (see {!collapse_ctx}
    for instance).
 *)
let reorder_loans_borrows_in_fresh_abs (old_abs_ids : V.AbstractionId.Set.t)
    (ctx : C.eval_ctx) : C.eval_ctx =
  let reorder_in_fresh_abs (abs : V.abs) : V.abs =
    (* Split between the loans and borrows *)
    let is_borrow (av : V.typed_avalue) : bool =
      match av.V.value with
      | ABorrow _ -> true
      | ALoan _ -> false
      | _ -> raise (Failure "Unexpected")
    in
    let aborrows, aloans = List.partition is_borrow abs.V.avalues in

    (* Reoder the borrows, and the loans.

       After experimenting, it seems that a good way of reordering the loans
       and the borrows to find fixed points is simply to sort them by increasing
       order of id (taking the smallest id of a set of ids, in case of sets).
    *)
    let get_borrow_id (av : V.typed_avalue) : V.BorrowId.id =
      match av.V.value with
      | V.ABorrow (V.AMutBorrow (bid, _) | V.ASharedBorrow bid) -> bid
      | _ -> raise (Failure "Unexpected")
    in
    let get_loan_id (av : V.typed_avalue) : V.BorrowId.id =
      match av.V.value with
      | V.ALoan (V.AMutLoan (lid, _)) -> lid
      | V.ALoan (V.ASharedLoan (lids, _, _)) -> V.BorrowId.Set.min_elt lids
      | _ -> raise (Failure "Unexpected")
    in
    (* We use ordered maps to reorder the borrows and loans *)
    let reorder (get_bid : V.typed_avalue -> V.BorrowId.id)
        (values : V.typed_avalue list) : V.typed_avalue list =
      List.map snd
        (V.BorrowId.Map.bindings
           (V.BorrowId.Map.of_list (List.map (fun v -> (get_bid v, v)) values)))
    in
    let aborrows = reorder get_borrow_id aborrows in
    let aloans = reorder get_loan_id aloans in
    let avalues = List.append aborrows aloans in
    { abs with V.avalues }
  in

  let reorder_in_abs (abs : V.abs) =
    if V.AbstractionId.Set.mem abs.abs_id old_abs_ids then abs
    else reorder_in_fresh_abs abs
  in

  let env = C.env_map_abs reorder_in_abs ctx.env in

  { ctx with C.env }

(** Destructure all the new abstractions *)
let destructure_new_abs (loop_id : V.LoopId.id)
    (old_abs_ids : V.AbstractionId.Set.t) (ctx : C.eval_ctx) : C.eval_ctx =
  let abs_kind = V.Loop (loop_id, None, V.LoopSynthInput) in
  let can_end = true in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_abs_ids)
  in
  let env =
    C.env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs abs_kind can_end destructure_shared_values ctx abs
          in
          abs
        else abs)
      ctx.env
  in
  { ctx with env }

(** Decompose the shared avalues, so as not to have nested shared loans
    inside of abstractions.

    For instance:
    {[
      abs'0 { shared_aloan ls0 (true, shared_loan ls1 s0) _ }

        ~~>

      abs'0 {
        shared_aloan ls0 (true, s0) _
        shared_aloan ls1 s1 _
      }
    ]}

    Note that we decompose only in the "fresh" abstractions (this is controled
    by the [old_aids] parameter).

    TODO: how to factorize with {!InterpreterBorrows.destructure_abs}?
 *)
let decompose_shared_avalues (loop_id : V.LoopId.id)
    (old_aids : V.AbstractionId.Set.t) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Decompose the shared avalues in a fresh abstraction. We only decompose
     in fresh (i.e., non-fixed) abstractions: {!decompose_in_abs} below
     ignores the fixed abstractions and delegates to this function *)
  let decompose_in_fresh_abs (abs : V.abs) : V.abs =
    let new_loans = ref [] in
    (* When decomposing, we need to duplicate the symbolic values (we
       simply introduce fresh ids) *)
    let mk_value_with_fresh_sids (v : V.typed_value) : V.typed_value =
      let visitor =
        object
          inherit [_] V.map_typed_avalue
          method! visit_symbolic_value_id _ _ = C.fresh_symbolic_value_id ()
        end
      in
      visitor#visit_typed_value () v
    in
    (* Visit the values: whenever we enter a shared loan (which is necessarily
       a strict subvalue of a shared aloan, because we only explore abstractions)
       we move it outside (we remove the shared loan, register a shared value
       to insert in the abstraction, and use fresh symbolic values in this new
       shared value).
    *)
    let loan_visitor =
      object (self : 'self)
        inherit [_] V.map_typed_avalue as super

        method! visit_typed_value env v =
          match v.V.value with
          | V.Loan (V.SharedLoan (lids, sv)) ->
              let sv = self#visit_typed_value env sv in

              (* Introduce fresh symbolic values for the new loan *)
              let nsv = mk_value_with_fresh_sids sv in
              new_loans := List.append !new_loans [ (lids, nsv) ];

              (* Return *)
              sv
          | _ -> super#visit_typed_value env v
      end
    in
    let rid = T.RegionId.Set.min_elt abs.regions in

    (* We registered new loans to add in the abstraction: actually create those
       loans, and insert them in the abstraction *)
    let mk_ashared_loan (lids : V.BorrowId.Set.t) (sv : V.typed_value) :
        V.typed_avalue =
      (* There shouldn't be nested borrows *)
      let sv_ty = ety_no_regions_to_rty sv.V.ty in
      let ty = T.Ref (T.Var rid, sv_ty, T.Shared) in
      let child_av = mk_aignored sv_ty in
      let value = V.ALoan (V.ASharedLoan (lids, sv, child_av)) in
      { V.value; ty }
    in
    let avalues =
      List.map
        (fun av ->
          new_loans := [];
          let av = loan_visitor#visit_typed_avalue () av in
          let new_loans =
            List.map (fun (lids, sv) -> mk_ashared_loan lids sv) !new_loans
          in
          av :: List.rev new_loans)
        abs.V.avalues
    in
    let avalues = List.concat avalues in
    let abs_id = C.fresh_abstraction_id () in
    let kind = V.Loop (loop_id, None, V.LoopSynthInput) in
    let can_end = true in
    let abs = { abs with V.abs_id; kind; can_end; avalues } in
    abs
  in

  (* Decompose only in the fresh abstractions *)
  let decompose_in_abs abs =
    if V.AbstractionId.Set.mem abs.V.abs_id old_aids then abs
    else decompose_in_fresh_abs abs
  in

  (* Apply in the environment *)
  let env = C.env_map_abs decompose_in_abs ctx.env in
  { ctx with C.env }

(** Collapse an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point.

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not) and convert them into abstractions
    - whenever there is a new abstraction in the context, and some of its
      its borrows are associated to loans in another new abstraction, we
      merge them.
    In effect, this allows us to merge newly introduced abstractions/borrows
    with their parent abstractions.
    
    For instance, when evaluating the first loop iteration, we start in the
    following environment:
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

    We finally merge the new abstractions together. It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@4 { MB l0, ML l4 }
    ]}

    [merge_funs]: those are used to merge loans or borrows which appear in both
    abstractions (rem.: here we mean that, for instance, both abstractions
    contain a shared loan with id l0).
    This can happen when merging environments (note that such environments are not well-formed -
    they become well formed again after collapsing).
 *)
let collapse_ctx (loop_id : V.LoopId.id)
    (merge_funs : merge_duplicates_funcs option) (old_ids : ids_sets)
    (ctx0 : C.eval_ctx) : C.eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      ("collapse_ctx:\n\n- fixed_ids:\n" ^ show_ids_sets old_ids
     ^ "\n\n- ctx0:\n" ^ eval_ctx_to_string ctx0 ^ "\n\n"));

  let abs_kind = V.Loop (loop_id, None, LoopSynthInput) in
  let can_end = true in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_ids.aids)
  in
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    not (C.DummyVarId.Set.mem id old_ids.dids)
  in
  (* Convert the dummy values to abstractions (note that when we convert
     values to abstractions, the resulting abstraction should be destructured) *)
  (* Note that we preserve the order of the dummy values: we replace them with
     abstractions in place - this makes matching easier *)
  let env =
    List.concat
      (List.map
         (fun ee ->
           match ee with
           | C.Abs _ | C.Frame | C.Var (VarBinder _, _) -> [ ee ]
           | C.Var (DummyBinder id, v) ->
               if is_fresh_did id then
                 let absl =
                   convert_value_to_abstractions abs_kind can_end
                     destructure_shared_values ctx0 v
                 in
                 List.map (fun abs -> C.Abs abs) absl
               else [ ee ])
         ctx0.env)
  in
  let ctx = { ctx0 with C.env } in
  log#ldebug
    (lazy
      ("collapse_ctx: after converting values to abstractions:\n"
     ^ show_ids_sets old_ids ^ "\n\n- ctx:\n" ^ eval_ctx_to_string ctx ^ "\n\n"
      ));

  log#ldebug
    (lazy
      ("collapse_ctx: after decomposing the shared values in the abstractions:\n"
     ^ show_ids_sets old_ids ^ "\n\n- ctx:\n" ^ eval_ctx_to_string ctx ^ "\n\n"
      ));

  (* Explore all the *new* abstractions, and compute various maps *)
  let explore (abs : V.abs) = is_fresh_abs_id abs.abs_id in
  let ids_maps =
    compute_abs_borrows_loans_maps (merge_funs = None) explore env
  in
  let {
    abs_ids;
    abs_to_borrows;
    abs_to_loans = _;
    abs_to_borrows_loans;
    borrow_to_abs = _;
    loan_to_abs;
    borrow_loan_to_abs;
  } =
    ids_maps
  in

  (* Change the merging behaviour depending on the input parameters *)
  let abs_to_borrows, loan_to_abs =
    if merge_funs <> None then (abs_to_borrows_loans, borrow_loan_to_abs)
    else (abs_to_borrows, loan_to_abs)
  in

  (* Merge the abstractions together *)
  let merged_abs : V.AbstractionId.id UF.elem V.AbstractionId.Map.t =
    V.AbstractionId.Map.of_list (List.map (fun id -> (id, UF.make id)) abs_ids)
  in

  let ctx = ref ctx in

  (* Merge all the mergeable abs.

     We iterate over the abstractions, then over the borrows in the abstractions.
     We do this because we want to control the order in which abstractions
     are merged (the ids are iterated in increasing order). Otherwise, we
     could simply iterate over all the borrows in [borrow_to_abs]...
  *)
  List.iter
    (fun abs_id0 ->
      let bids = V.AbstractionId.Map.find abs_id0 abs_to_borrows in
      let bids = V.BorrowId.Set.elements bids in
      List.iter
        (fun bid ->
          match V.BorrowId.Map.find_opt bid loan_to_abs with
          | None -> (* Nothing to do *) ()
          | Some abs_ids1 ->
              V.AbstractionId.Set.iter
                (fun abs_id1 ->
                  (* We need to merge - unless we have already merged *)
                  (* First, find the representatives for the two abstractions (the
                     representative is the abstraction into which we merged) *)
                  let abs_ref0 =
                    UF.find (V.AbstractionId.Map.find abs_id0 merged_abs)
                  in
                  let abs_id0 = UF.get abs_ref0 in
                  let abs_ref1 =
                    UF.find (V.AbstractionId.Map.find abs_id1 merged_abs)
                  in
                  let abs_id1 = UF.get abs_ref1 in
                  (* If the two ids are the same, it means the abstractions were already merged *)
                  if abs_id0 = abs_id1 then ()
                  else (
                    (* We actually need to merge the abstractions *)

                    (* Debug *)
                    log#ldebug
                      (lazy
                        ("collapse_ctx: merging abstraction "
                        ^ V.AbstractionId.to_string abs_id1
                        ^ " into "
                        ^ V.AbstractionId.to_string abs_id0
                        ^ ":\n\n" ^ eval_ctx_to_string !ctx));

                    (* Update the environment - pay attention to the order: we
                       we merge [abs_id1] *into* [abs_id0] *)
                    let nctx, abs_id =
                      merge_into_abstraction abs_kind can_end merge_funs !ctx
                        abs_id1 abs_id0
                    in
                    ctx := nctx;

                    (* Update the union find *)
                    let abs_ref_merged = UF.union abs_ref0 abs_ref1 in
                    UF.set abs_ref_merged abs_id))
                abs_ids1)
        bids)
    abs_ids;

  log#ldebug
    (lazy
      ("collapse_ctx:\n\n- fixed_ids:\n" ^ show_ids_sets old_ids
     ^ "\n\n- after collapse:\n" ^ eval_ctx_to_string !ctx ^ "\n\n"));

  (* Reorder the loans and borrows in the fresh abstractions *)
  let ctx = reorder_loans_borrows_in_fresh_abs old_ids.aids !ctx in

  log#ldebug
    (lazy
      ("collapse_ctx:\n\n- fixed_ids:\n" ^ show_ids_sets old_ids
     ^ "\n\n- after collapse and reorder borrows/loans:\n"
     ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Return the new context *)
  ctx

(** Match two types during a join. *)
let rec match_types (match_distinct_types : 'r T.ty -> 'r T.ty -> 'r T.ty)
    (match_regions : 'r -> 'r -> 'r) (ty0 : 'r T.ty) (ty1 : 'r T.ty) : 'r T.ty =
  let match_rec = match_types match_distinct_types match_regions in
  match (ty0, ty1) with
  | Adt (id0, regions0, tys0), Adt (id1, regions1, tys1) ->
      assert (id0 = id1);
      let id = id0 in
      let regions =
        List.map
          (fun (id0, id1) -> match_regions id0 id1)
          (List.combine regions0 regions1)
      in
      let tys =
        List.map (fun (ty0, ty1) -> match_rec ty0 ty1) (List.combine tys0 tys1)
      in
      Adt (id, regions, tys)
  | TypeVar vid0, TypeVar vid1 ->
      assert (vid0 = vid1);
      let vid = vid0 in
      TypeVar vid
  | Bool, Bool | Char, Char | Never, Never | Str, Str -> ty0
  | Integer int_ty0, Integer int_ty1 ->
      assert (int_ty0 = int_ty1);
      ty0
  | Array ty0, Array ty1 | Slice ty0, Slice ty1 -> match_rec ty0 ty1
  | Ref (r0, ty0, k0), Ref (r1, ty1, k1) ->
      let r = match_regions r0 r1 in
      let ty = match_rec ty0 ty1 in
      assert (k0 = k1);
      let k = k0 in
      Ref (r, ty, k)
  | _ -> match_distinct_types ty0 ty1

(** See {!Match}.

    This module contains specialized match functions to instantiate the generic
    {!Match} functor.
  *)
module type Matcher = sig
  val match_etys : T.ety -> T.ety -> T.ety
  val match_rtys : T.rty -> T.rty -> T.rty

  (** The input primitive values are not equal *)
  val match_distinct_primitive_values :
    T.ety -> V.primitive_value -> V.primitive_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts : T.ety -> V.adt_value -> V.adt_value -> V.typed_value

  (** The meta-value is the result of a match.

      We take an additional function as input, which acts as a matcher over
      typed values, to be able to lookup the shared values and match them.
      We do this for shared borrows (and not, e.g., mutable borrows) because
      shared borrows introduce indirections, while mutable borrows carry the
      borrowed values with them: we might want to explore and match those
      borrowed values, in which case we have to manually look them up before
      calling the match function.
   *)
  val match_shared_borrows :
    (V.typed_value -> V.typed_value -> V.typed_value) ->
    T.ety ->
    V.borrow_id ->
    V.borrow_id ->
    V.borrow_id

  (** The input parameters are:
      - [ty]
      - [bid0]: first borrow id
      - [bv0]: first borrowed value
      - [bid1]
      - [bv1]
      - [bv]: the result of matching [bv0] with [bv1]
  *)
  val match_mut_borrows :
    T.ety ->
    V.borrow_id ->
    V.typed_value ->
    V.borrow_id ->
    V.typed_value ->
    V.typed_value ->
    V.borrow_id * V.typed_value

  (** Parameters:
      [ty]
      [ids0]
      [ids1]
      [v]: the result of matching the shared values coming from the two loans
   *)
  val match_shared_loans :
    T.ety ->
    V.loan_id_set ->
    V.loan_id_set ->
    V.typed_value ->
    V.loan_id_set * V.typed_value

  val match_mut_loans : T.ety -> V.loan_id -> V.loan_id -> V.loan_id

  (** There are no constraints on the input symbolic values *)
  val match_symbolic_values :
    V.symbolic_value -> V.symbolic_value -> V.symbolic_value

  (** Match a symbolic value with a value which is not symbolic.

      If the boolean is [true], it means the symbolic value comes from the
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_symbolic_with_other :
    bool -> V.symbolic_value -> V.typed_value -> V.typed_value

  (** Match a bottom value with a value which is not bottom.

      If the boolean is [true], it means the bottom value comes from the
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_bottom_with_other : bool -> V.typed_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_aadts :
    T.rty -> V.adt_avalue -> T.rty -> V.adt_avalue -> T.rty -> V.typed_avalue

  (** Parameters:
      [ty0]
      [bid0]
      [ty1]
      [bid1]
      [ty]: result of matching ty0 and ty1
   *)
  val match_ashared_borrows :
    T.rty -> V.borrow_id -> T.rty -> V.borrow_id -> T.rty -> V.typed_avalue

  (** Parameters:
      [ty0]
      [bid0]
      [av0]
      [ty1]
      [bid1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_borrows :
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.typed_avalue ->
    V.typed_avalue

  (** Parameters:
      [ty0]
      [ids0]
      [v0]
      [av0]
      [ty1]
      [ids1]
      [v1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [v]:  result of matching v0 and v1
      [av]: result of matching av0 and av1
   *)
  val match_ashared_loans :
    T.rty ->
    V.loan_id_set ->
    V.typed_value ->
    V.typed_avalue ->
    T.rty ->
    V.loan_id_set ->
    V.typed_value ->
    V.typed_avalue ->
    T.rty ->
    V.typed_value ->
    V.typed_avalue ->
    V.typed_avalue

  (** Parameters:
      [ty0]
      [id0]
      [av0]
      [ty1]
      [id1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_loans :
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.typed_avalue ->
    V.typed_avalue

  (** Match two arbitrary avalues whose constructors don't match (this function
      is typically used to raise the proper exception).
   *)
  val match_avalues : V.typed_avalue -> V.typed_avalue -> V.typed_avalue
end

(** Generic functor to implement matching functions between values, environments,
    etc.

    We use it for joins, to check if two environments are convertible, etc.
    See for instance {!MakeJoinMatcher} and {!MakeCheckEquivMatcher}.

    The functor is parameterized by a {!Matcher}, which implements the
    non-generic part of the match. More precisely, the role of {!Match} is two
    provide generic functions which recursively match two values (by recursively
    matching the fields of ADT values for instance). When it does need to match
    values in a non-trivial manner (if two ADT values don't have the same
    variant for instance) it calls the corresponding specialized function from
    {!Matcher}.
 *)
module Match (M : Matcher) = struct
  (** Match two values.

      Rem.: this function raises exceptions of type {!ValueMatchFailure}.
   *)
  let rec match_typed_values (ctx : C.eval_ctx) (v0 : V.typed_value)
      (v1 : V.typed_value) : V.typed_value =
    let match_rec = match_typed_values ctx in
    let ty = M.match_etys v0.V.ty v1.V.ty in
    match (v0.V.value, v1.V.value) with
    | V.Primitive pv0, V.Primitive pv1 ->
        if pv0 = pv1 then v1 else M.match_distinct_primitive_values ty pv0 pv1
    | V.Adt av0, V.Adt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_rec f0 f1) fields
          in
          let value : V.value =
            V.Adt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty = v1.V.ty }
        else (
          (* For now, we don't merge ADTs which contain borrows *)
          assert (not (value_has_borrows ctx v0.V.value));
          assert (not (value_has_borrows ctx v1.V.value));
          (* Merge *)
          M.match_distinct_adts ty av0 av1)
    | Bottom, Bottom -> v0
    | Borrow bc0, Borrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | SharedBorrow bid0, SharedBorrow bid1 ->
              let bid = M.match_shared_borrows match_rec ty bid0 bid1 in
              V.SharedBorrow bid
          | MutBorrow (bid0, bv0), MutBorrow (bid1, bv1) ->
              let bv = match_rec bv0 bv1 in
              assert (not (value_has_borrows ctx bv.V.value));
              let bid, bv = M.match_mut_borrows ty bid0 bv0 bid1 bv1 bv in
              V.MutBorrow (bid, bv)
          | ReservedMutBorrow _, _
          | _, ReservedMutBorrow _
          | SharedBorrow _, MutBorrow _
          | MutBorrow _, SharedBorrow _ ->
              (* If we get here, either there is a typing inconsistency, or we are
                 trying to match a reserved borrow, which shouldn't happen because
                 reserved borrow should be eliminated very quickly - they are introduced
                 just before function calls which activate them *)
              raise (Failure "Unexpected")
        in
        { V.value = V.Borrow bc; ty }
    | Loan lc0, Loan lc1 ->
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        let lc =
          match (lc0, lc1) with
          | SharedLoan (ids0, sv0), SharedLoan (ids1, sv1) ->
              let sv = match_rec sv0 sv1 in
              assert (not (value_has_borrows ctx sv.V.value));
              let ids, sv = M.match_shared_loans ty ids0 ids1 sv in
              V.SharedLoan (ids, sv)
          | MutLoan id0, MutLoan id1 ->
              let id = M.match_mut_loans ty id0 id1 in
              V.MutLoan id
          | SharedLoan _, MutLoan _ | MutLoan _, SharedLoan _ ->
              raise (Failure "Unreachable")
        in
        { V.value = Loan lc; ty = v1.V.ty }
    | Symbolic sv0, Symbolic sv1 ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        assert (not (value_has_borrows ctx v0.V.value));
        assert (not (value_has_borrows ctx v1.V.value));
        (* Match *)
        let sv = M.match_symbolic_values sv0 sv1 in
        { v1 with V.value = V.Symbolic sv }
    | Loan lc, _ -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInLeft ids))
        | MutLoan id -> raise (ValueMatchFailure (LoanInLeft id)))
    | _, Loan lc -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInRight ids))
        | MutLoan id -> raise (ValueMatchFailure (LoanInRight id)))
    | Symbolic sv, _ -> M.match_symbolic_with_other true sv v1
    | _, Symbolic sv -> M.match_symbolic_with_other false sv v0
    | Bottom, _ -> M.match_bottom_with_other true v1
    | _, Bottom -> M.match_bottom_with_other false v0
    | _ ->
        log#ldebug
          (lazy
            ("Unexpected match case:\n- value0: "
            ^ typed_value_to_string ctx v0
            ^ "\n- value1: "
            ^ typed_value_to_string ctx v1));
        raise (Failure "Unexpected match case")

  (** Match two avalues.

      Rem.: this function raises exceptions of type {!ValueMatchFailure}.
   *)
  and match_typed_avalues (ctx : C.eval_ctx) (v0 : V.typed_avalue)
      (v1 : V.typed_avalue) : V.typed_avalue =
    log#ldebug
      (lazy
        ("match_typed_avalues:\n- value0: "
        ^ typed_avalue_to_string ctx v0
        ^ "\n- value1: "
        ^ typed_avalue_to_string ctx v1));

    let match_rec = match_typed_values ctx in
    let match_arec = match_typed_avalues ctx in
    let ty = M.match_rtys v0.V.ty v1.V.ty in
    match (v0.V.value, v1.V.value) with
    | V.AAdt av0, V.AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_arec f0 f1) fields
          in
          let value : V.avalue =
            V.AAdt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty }
        else (* Merge *)
          M.match_distinct_aadts v0.V.ty av0 v1.V.ty av1 ty
    | ABottom, ABottom -> mk_abottom ty
    | AIgnored, AIgnored -> mk_aignored ty
    | ABorrow bc0, ABorrow bc1 -> (
        log#ldebug (lazy "match_typed_avalues: borrows");
        match (bc0, bc1) with
        | ASharedBorrow bid0, ASharedBorrow bid1 ->
            log#ldebug (lazy "match_typed_avalues: shared borrows");
            M.match_ashared_borrows v0.V.ty bid0 v1.V.ty bid1 ty
        | AMutBorrow (bid0, av0), AMutBorrow (bid1, av1) ->
            log#ldebug (lazy "match_typed_avalues: mut borrows");
            log#ldebug
              (lazy
                "match_typed_avalues: mut borrows: matching children values");
            let av = match_arec av0 av1 in
            log#ldebug
              (lazy "match_typed_avalues: mut borrows: matched children values");
            M.match_amut_borrows v0.V.ty bid0 av0 v1.V.ty bid1 av1 ty av
        | AIgnoredMutBorrow _, AIgnoredMutBorrow _ ->
            (* The abstractions are destructured: we shouldn't get there *)
            raise (Failure "Unexpected")
        | AProjSharedBorrow asb0, AProjSharedBorrow asb1 -> (
            match (asb0, asb1) with
            | [], [] ->
                (* This case actually stands for ignored shared borrows, when
                   there are no nested borrows *)
                v0
            | _ ->
                (* We should get there only if there are nested borrows *)
                raise (Failure "Unexpected"))
        | _ ->
            (* TODO: getting there is not necessarily inconsistent (it may
               just be because the environments don't match) so we may want
               to call a specific function (which could raise the proper
               exception).
               Rem.: we shouldn't get to the ended borrow cases, because
               an abstraction should never contain ended borrows unless
               we are *currently* ending it, in which case we need
               to completely end it before continuing.
            *)
            raise (Failure "Unexpected"))
    | ALoan lc0, ALoan lc1 -> (
        log#ldebug (lazy "match_typed_avalues: loans");
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        match (lc0, lc1) with
        | ASharedLoan (ids0, sv0, av0), ASharedLoan (ids1, sv1, av1) ->
            log#ldebug (lazy "match_typed_avalues: shared loans");
            let sv = match_rec sv0 sv1 in
            let av = match_arec av0 av1 in
            assert (not (value_has_borrows ctx sv.V.value));
            M.match_ashared_loans v0.V.ty ids0 sv0 av0 v1.V.ty ids1 sv1 av1 ty
              sv av
        | AMutLoan (id0, av0), AMutLoan (id1, av1) ->
            log#ldebug (lazy "match_typed_avalues: mut loans");
            log#ldebug
              (lazy "match_typed_avalues: mut loans: matching children values");
            let av = match_arec av0 av1 in
            log#ldebug
              (lazy "match_typed_avalues: mut loans: matched children values");
            M.match_amut_loans v0.V.ty id0 av0 v1.V.ty id1 av1 ty av
        | AIgnoredMutLoan _, AIgnoredMutLoan _
        | AIgnoredSharedLoan _, AIgnoredSharedLoan _ ->
            (* Those should have been filtered when destructuring the abstractions -
               they are necessary only when there are nested borrows *)
            raise (Failure "Unreachable")
        | _ -> raise (Failure "Unreachable"))
    | ASymbolic _, ASymbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        raise (Failure "Unreachable")
    | _ -> M.match_avalues v0 v1
end

(* Very annoying: functors only take modules as inputs... *)
module type MatchJoinState = sig
  (** The current context *)
  val ctx : C.eval_ctx

  (** The current loop *)
  val loop_id : V.LoopId.id

  (** The abstractions introduced when performing the matches *)
  val nabs : V.abs list ref
end

(** A matcher for joins (we use joins to compute loop fixed points).

    See the explanations for {!Match}.

    In case of loop joins:
    - we match *concrete* values
    - we check that the "fixed" abstractions (the abstractions to be framed
      - i.e., the abstractions which are the same in the two environments to
      join) are equal
    - we keep the abstractions which are not in the frame, then merge those
      together (if they have borrows/loans in common) later
    The join matcher is used to match the *concrete* values only. For this
    reason, we fail on the functions which match avalues.
 *)
module MakeJoinMatcher (S : MatchJoinState) : Matcher = struct
  (** Small utility *)
  let push_abs (abs : V.abs) : unit = S.nabs := abs :: !S.nabs

  let push_absl (absl : V.abs list) : unit = List.iter push_abs absl

  let match_etys ty0 ty1 =
    assert (ty0 = ty1);
    ty0

  let match_rtys ty0 ty1 =
    (* The types must be equal - in effect, this forbids to match symbolic
       values containing borrows *)
    assert (ty0 = ty1);
    ty0

  let match_distinct_primitive_values (ty : T.ety) (_ : V.primitive_value)
      (_ : V.primitive_value) : V.typed_value =
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_distinct_adts (ty : T.ety) (adt0 : V.adt_value) (adt1 : V.adt_value)
      : V.typed_value =
    (* Check that the ADTs don't contain borrows - this is redundant with checks
       performed by the caller, but we prefer to be safe with regards to future
       updates
    *)
    let check_no_borrows (v : V.typed_value) =
      assert (not (value_has_borrows S.ctx v.V.value))
    in
    List.iter check_no_borrows adt0.field_values;
    List.iter check_no_borrows adt1.field_values;

    (* Check if there are loans: we request to end them *)
    let check_loans (left : bool) (fields : V.typed_value list) : unit =
      match InterpreterBorrowsCore.get_first_loan_in_values fields with
      | Some (V.SharedLoan (ids, _)) ->
          if left then raise (ValueMatchFailure (LoansInLeft ids))
          else raise (ValueMatchFailure (LoansInRight ids))
      | Some (V.MutLoan id) ->
          if left then raise (ValueMatchFailure (LoanInLeft id))
          else raise (ValueMatchFailure (LoanInRight id))
      | None -> ()
    in
    check_loans true adt0.field_values;
    check_loans false adt1.field_values;

    (* No borrows, no loans: we can introduce a symbolic value *)
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_shared_borrows _ (ty : T.ety) (bid0 : V.borrow_id)
      (bid1 : V.borrow_id) : V.borrow_id =
    if bid0 = bid1 then bid0
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { SB bid0, SB bid1, SL {bid2} }
         ]}
      *)
      let rid = C.fresh_region_id () in
      let bid2 = C.fresh_borrow_id () in

      (* Generate a fresh symbolic value for the shared value *)
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin bv_ty in

      let borrow_ty =
        mk_ref_ty (T.Var rid) (ety_no_regions_to_rty bv_ty) kind
      in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : V.borrow_id) : V.typed_avalue =
        let value = V.ABorrow (V.ASharedBorrow bid) in
        { V.value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0; mk_aborrow bid1 ] in

      let loan =
        V.ASharedLoan
          ( V.BorrowId.Set.singleton bid2,
            sv,
            mk_aignored (ety_no_regions_to_rty bv_ty) )
      in
      (* Note that an aloan has a borrow type *)
      let loan = { V.value = V.ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          V.abs_id = C.fresh_abstraction_id ();
          kind = V.Loop (S.loop_id, None, LoopSynthInput);
          can_end = true;
          parents = V.AbstractionId.Set.empty;
          original_parents = [];
          regions = T.RegionId.Set.singleton rid;
          ancestors_regions = T.RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      bid2

  let match_mut_borrows (ty : T.ety) (bid0 : V.borrow_id) (bv0 : V.typed_value)
      (bid1 : V.borrow_id) (bv1 : V.typed_value) (bv : V.typed_value) :
      V.borrow_id * V.typed_value =
    if bid0 = bid1 then (
      (* If the merged value is not the same as the original value, we introduce
         an abstraction:

         {[
           { MB bid0, ML nbid }  // where nbid fresh
         ]}

         and we use bid' for the borrow id that we return.

         We do this because we want to make sure that, whenever a mutably
         borrowed value is modified in a loop iteration, then there is
         a fresh abstraction between this borrowed value and the fixed
         abstractions.
      *)
      assert (not (value_has_borrows S.ctx bv.V.value));

      if bv0 = bv1 then (
        assert (bv0 = bv);
        (bid0, bv))
      else
        let rid = C.fresh_region_id () in
        let nbid = C.fresh_borrow_id () in

        let kind = T.Mut in
        let bv_ty = ety_no_regions_to_rty bv.V.ty in
        let borrow_ty = mk_ref_ty (T.Var rid) bv_ty kind in

        let borrow_av =
          let ty = borrow_ty in
          let value = V.ABorrow (V.AMutBorrow (bid0, mk_aignored bv_ty)) in
          mk_typed_avalue ty value
        in

        let loan_av =
          let ty = borrow_ty in
          let value = V.ALoan (V.AMutLoan (nbid, mk_aignored bv_ty)) in
          mk_typed_avalue ty value
        in

        let avalues = [ borrow_av; loan_av ] in

        (* Generate the abstraction *)
        let abs =
          {
            V.abs_id = C.fresh_abstraction_id ();
            kind = V.Loop (S.loop_id, None, LoopSynthInput);
            can_end = true;
            parents = V.AbstractionId.Set.empty;
            original_parents = [];
            regions = T.RegionId.Set.singleton rid;
            ancestors_regions = T.RegionId.Set.empty;
            avalues;
          }
        in
        push_abs abs;

        (* Return the new borrow *)
        (nbid, bv))
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { MB bid0, MB bid1, ML bid2 }
         ]}
      *)
      let rid = C.fresh_region_id () in
      let bid2 = C.fresh_borrow_id () in

      (* Generate a fresh symbolic value for the borrowed value *)
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin bv_ty in

      let borrow_ty =
        mk_ref_ty (T.Var rid) (ety_no_regions_to_rty bv_ty) kind
      in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : V.borrow_id) (bv : V.typed_value) : V.typed_avalue =
        let bv_ty = ety_no_regions_to_rty bv.V.ty in
        let value = V.ABorrow (V.AMutBorrow (bid, mk_aignored bv_ty)) in
        { V.value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0 bv0; mk_aborrow bid1 bv1 ] in

      let loan = V.AMutLoan (bid2, mk_aignored (ety_no_regions_to_rty bv_ty)) in
      (* Note that an aloan has a borrow type *)
      let loan = { V.value = V.ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          V.abs_id = C.fresh_abstraction_id ();
          kind = V.Loop (S.loop_id, None, LoopSynthInput);
          can_end = true;
          parents = V.AbstractionId.Set.empty;
          original_parents = [];
          regions = T.RegionId.Set.singleton rid;
          ancestors_regions = T.RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (bid2, sv)

  let match_shared_loans (_ : T.ety) (ids0 : V.loan_id_set)
      (ids1 : V.loan_id_set) (sv : V.typed_value) :
      V.loan_id_set * V.typed_value =
    (* Check if the ids are the same - Rem.: we forbid the sets of loans
       to be different. However, if we dive inside data-structures (by
       using a shared borrow) the shared values might themselves contain
       shared loans, which need to be matched. For this reason, we destructure
       the shared values (see {!destructure_abs}).
    *)
    let extra_ids_left = V.BorrowId.Set.diff ids0 ids1 in
    let extra_ids_right = V.BorrowId.Set.diff ids1 ids0 in
    if not (V.BorrowId.Set.is_empty extra_ids_left) then
      raise (ValueMatchFailure (LoansInLeft extra_ids_left));
    if not (V.BorrowId.Set.is_empty extra_ids_right) then
      raise (ValueMatchFailure (LoansInRight extra_ids_right));

    (* This should always be true if we get here *)
    assert (ids0 = ids1);
    let ids = ids0 in

    (* Return *)
    (ids, sv)

  let match_mut_loans (_ : T.ety) (id0 : V.loan_id) (id1 : V.loan_id) :
      V.loan_id =
    if id0 = id1 then id0
    else
      (* We forbid this case for now: if we get there, we force to end
         both borrows *)
      raise (ValueMatchFailure (LoanInLeft id0))

  let match_symbolic_values (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) :
      V.symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in
    if id0 = id1 then (
      (* Sanity check *)
      assert (sv0 = sv1);
      (* Return *)
      sv0)
    else (
      (* The caller should have checked that the symbolic values don't contain
         borrows *)
      assert (not (ty_has_borrows S.ctx.type_context.type_infos sv0.sv_ty));
      (* We simply introduce a fresh symbolic value *)
      mk_fresh_symbolic_value V.LoopJoin sv0.sv_ty)

  let match_symbolic_with_other (left : bool) (sv : V.symbolic_value)
      (v : V.typed_value) : V.typed_value =
    (* Check that:
       - there are no borrows in the symbolic value
       - there are no borrows in the "regular" value
       If there are loans in the regular value, raise an exception.
    *)
    assert (not (ty_has_borrows S.ctx.type_context.type_infos sv.sv_ty));
    assert (not (value_has_borrows S.ctx v.V.value));
    let value_is_left = not left in
    (match InterpreterBorrowsCore.get_first_loan_in_value v with
    | None -> ()
    | Some (SharedLoan (ids, _)) ->
        if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
        else raise (ValueMatchFailure (LoansInRight ids))
    | Some (MutLoan id) ->
        if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
        else raise (ValueMatchFailure (LoanInRight id)));
    (* Return a fresh symbolic value *)
    mk_fresh_symbolic_typed_value V.LoopJoin sv.sv_ty

  let match_bottom_with_other (left : bool) (v : V.typed_value) : V.typed_value
      =
    (* If there are outer loans in the non-bottom value, raise an exception.
       Otherwise, convert it to an abstraction and return [Bottom].
    *)
    let with_borrows = false in
    let value_is_left = not left in
    match
      InterpreterBorrowsCore.get_first_outer_loan_or_borrow_in_value
        with_borrows v
    with
    | Some (BorrowContent _) -> raise (Failure "Unreachable")
    | Some (LoanContent lc) -> (
        match lc with
        | V.SharedLoan (ids, _) ->
            if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
            else raise (ValueMatchFailure (LoansInRight ids))
        | V.MutLoan id ->
            if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
            else raise (ValueMatchFailure (LoanInRight id)))
    | None ->
        (* Convert the value to an abstraction *)
        let abs_kind = V.Loop (S.loop_id, None, LoopSynthInput) in
        let can_end = true in
        let destructure_shared_values = true in
        let absl =
          convert_value_to_abstractions abs_kind can_end
            destructure_shared_values S.ctx v
        in
        push_absl absl;
        (* Return [Bottom] *)
        mk_bottom v.V.ty

  (* As explained in comments: we don't use the join matcher to join avalues,
     only concrete values *)

  let match_distinct_aadts _ _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_borrows _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_borrows _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_loans _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_avalues _ _ = raise (Failure "Unreachable")
end

let mk_collapse_ctx_merge_duplicate_funs (loop_id : V.LoopId.id)
    (ctx : C.eval_ctx) : merge_duplicates_funcs =
  (* Rem.: the merge functions raise exceptions (that we catch). *)
  let module S : MatchJoinState = struct
    let ctx = ctx
    let loop_id = loop_id
    let nabs = ref []
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = Match (JM) in
  (* Functions to match avalues (see {!merge_duplicates_funcs}).

     Those functions are used to merge borrows/loans with the *same ids*.

     They will always be called on destructured avalues (whose children are
     [AIgnored] - we enforce that through sanity checks). We rely on the join
     matcher [JM] to match the concrete values (for shared loans for instance).
     Note that the join matcher doesn't implement match functions for avalues
     (see the comments in {!MakeJoinMatcher}.
  *)
  let merge_amut_borrows id ty0 child0 _ty1 child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);

    (* We need to pick a type for the avalue. The types on the left and on the
       right may use different regions: it doesn't really matter (here, we pick
       the one from the left), because we will merge those regions together
       anyway (see the comments for {!merge_into_abstraction}).
    *)
    let ty = ty0 in
    let child = child0 in
    let value = V.ABorrow (V.AMutBorrow (id, child)) in
    { V.value; ty }
  in

  let merge_ashared_borrows id ty0 ty1 =
    (* Sanity checks *)
    let _ =
      let _, ty0, _ = ty_as_ref ty0 in
      let _, ty1, _ = ty_as_ref ty1 in
      assert (not (ty_has_borrows ctx.type_context.type_infos ty0));
      assert (not (ty_has_borrows ctx.type_context.type_infos ty1))
    in

    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let value = V.ABorrow (V.ASharedBorrow id) in
    { V.value; ty }
  in

  let merge_amut_loans id ty0 child0 _ty1 child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);
    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let child = child0 in
    let value = V.ALoan (V.AMutLoan (id, child)) in
    { V.value; ty }
  in
  let merge_ashared_loans ids ty0 (sv0 : V.typed_value) child0 _ty1
      (sv1 : V.typed_value) child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);
    (* Same remarks as for [merge_amut_borrows].

       This time we need to also merge the shared values. We rely on the
       join matcher [JM] to do so.
    *)
    assert (not (value_has_loans_or_borrows ctx sv0.V.value));
    assert (not (value_has_loans_or_borrows ctx sv1.V.value));
    let ty = ty0 in
    let child = child0 in
    let sv = M.match_typed_values ctx sv0 sv1 in
    let value = V.ALoan (V.ASharedLoan (ids, sv, child)) in
    { V.value; ty }
  in
  {
    merge_amut_borrows;
    merge_ashared_borrows;
    merge_amut_loans;
    merge_ashared_loans;
  }

let merge_into_abstraction (loop_id : V.LoopId.id) (abs_kind : V.abs_kind)
    (can_end : bool) (ctx : C.eval_ctx) (aid0 : V.AbstractionId.id)
    (aid1 : V.AbstractionId.id) : C.eval_ctx * V.AbstractionId.id =
  let merge_funs = mk_collapse_ctx_merge_duplicate_funs loop_id ctx in
  merge_into_abstraction abs_kind can_end (Some merge_funs) ctx aid0 aid1

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging functions.

    We do this because when we join environments, we may introduce duplicated
    loans and borrows. See the explanations for {!join_ctxs}.
 *)
let collapse_ctx_with_merge (loop_id : V.LoopId.id) (old_ids : ids_sets)
    (ctx : C.eval_ctx) : C.eval_ctx =
  let merge_funs = mk_collapse_ctx_merge_duplicate_funs loop_id ctx in
  try collapse_ctx loop_id (Some merge_funs) old_ids ctx
  with ValueMatchFailure _ -> raise (Failure "Unexpected")

(** Join two contexts.

    We use this to join the environments at loop (re-)entry to progressively
    compute a fixed point.

    We make the hypothesis (and check it) that the environments have the same
    prefixes (same variable ids, same abstractions, etc.). The prefix of
    variable and abstraction ids is given by the [fixed_ids] identifier sets. We
    check that those prefixes are the same (the dummy variables are the same,
    the abstractions are the same), match the values mapped to by the variables
    which are not dummy, then group the additional dummy variables/abstractions
    together. In a sense, the [fixed_ids] define a frame (in a separation logic
    sense).

    Note that when joining the values mapped to by the non-dummy variables, we
    may introduce duplicated borrows. Also, we don't match the abstractions
    which are not in the prefix, and this can also lead to borrow
    duplications. For this reason, the environment needs to be collapsed
    afterwards to get rid of those duplicated loans/borrows.

    For instance, if we have:
    {[
      fixed = { abs0 }

      env0 = {
        abs0 { ML l0 }
        l -> MB l0 s0
      }

      env1 = {
        abs0 { ML l0 }
        l -> MB l1 s1
        abs1 { MB l0, ML l1 }
      }
    ]}

    We get:
    {[
      join env0 env1 = {
        abs0 { ML l0 } (* abs0 is fixed: we simply check it is equal in env0 and env1 *)
        l -> MB l2 s2
        abs1 { MB l0, ML l1 } (* abs1 is new: we keep it unchanged *)
        abs2 { MB l0, MB l1, ML l2 } (* Introduced when joining on the "l" variable *)
      }
    ]}

    Rem.: in practice, this join works because we take care of pushing new values
    and abstractions *at the end* of the environments, meaning the environment
    prefixes keep the same structure.

    Rem.: assuming that the environment has some structure poses *no soundness
    issue*. It can only make the join fail if the environments actually don't have
    this structure: this is a *completeness issue*.
  *)
let join_ctxs (loop_id : V.LoopId.id) (fixed_ids : ids_sets) (ctx0 : C.eval_ctx)
    (ctx1 : C.eval_ctx) : ctx_or_update =
  (* Debug *)
  log#ldebug
    (lazy
      ("join_ctxs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx1
      ^ "\n\n"));

  let env0 = List.rev ctx0.env in
  let env1 = List.rev ctx1.env in

  (* We need to pick a context for some functions like [match_typed_values]:
     the context is only used to lookup module data, so we can pick whichever
     we want.
     TODO: this is not very clean. Maybe we should just carry this data around.
  *)
  let ctx = ctx0 in

  let nabs = ref [] in

  (* Explore the environments. *)
  let join_suffixes (env0 : C.env) (env1 : C.env) : C.env =
    (* Debug *)
    log#ldebug
      (lazy
        ("join_suffixes:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
       ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string_no_filter { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string_no_filter { ctx1 with env = List.rev env1 }
        ^ "\n\n"));

    (* Sanity check: there are no values/abstractions which should be in the prefix *)
    let check_valid (ee : C.env_elem) : unit =
      match ee with
      | C.Var (C.VarBinder _, _) ->
          (* Variables are necessarily in the prefix *)
          raise (Failure "Unreachable")
      | Var (C.DummyBinder did, _) ->
          assert (not (C.DummyVarId.Set.mem did fixed_ids.dids))
      | Abs abs ->
          assert (not (V.AbstractionId.Set.mem abs.abs_id fixed_ids.aids))
      | Frame ->
          (* This should have been eliminated *)
          raise (Failure "Unreachable")
    in
    List.iter check_valid env0;
    List.iter check_valid env1;
    (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
    let absl = List.map (fun abs -> C.Abs abs) (List.rev !nabs) in
    List.concat [ env0; env1; absl ]
  in

  let module S : MatchJoinState = struct
    (* The context is only used to lookup module data: we can pick whichever we want *)
    let ctx = ctx
    let loop_id = loop_id
    let nabs = nabs
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = Match (JM) in
  (* Rem.: this function raises exceptions *)
  let rec join_prefixes (env0 : C.env) (env1 : C.env) : C.env =
    match (env0, env1) with
    | ( (C.Var (C.DummyBinder b0, v0) as var0) :: env0',
        (C.Var (C.DummyBinder b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: DummyBinders:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
            ^ env_elem_to_string ctx var0
            ^ "\n\n- value1:\n"
            ^ env_elem_to_string ctx var1
            ^ "\n\n"));

        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and we must join their values. Otherwise, it means we
           are not in the prefix anymore *)
        if C.DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Still in the prefix: match the values *)
          assert (b0 = b1);
          let b = b0 in
          let v = M.match_typed_values ctx v0 v1 in
          let var = C.Var (C.DummyBinder b, v) in
          (* Continue *)
          var :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | ( (C.Var (C.VarBinder b0, v0) as var0) :: env0',
        (C.Var (C.VarBinder b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: VarBinders:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
            ^ env_elem_to_string ctx var0
            ^ "\n\n- value1:\n"
            ^ env_elem_to_string ctx var1
            ^ "\n\n"));

        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        assert (b0 = b1);
        (* Match the values *)
        let b = b0 in
        let v = M.match_typed_values ctx v0 v1 in
        let var = C.Var (C.VarBinder b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (C.Abs abs0 as abs) :: env0', C.Abs abs1 :: env1' ->
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: Abs:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- abs0:\n" ^ abs_to_string ctx abs0
           ^ "\n\n- abs1:\n" ^ abs_to_string ctx abs1 ^ "\n\n"));

        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
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
      | C.Frame :: env0, C.Frame :: env1 -> (env0, env1)
      | _ -> raise (Failure "Unreachable")
    in

    log#ldebug
      (lazy
        ("- env0:\n" ^ C.show_env env0 ^ "\n\n- env1:\n" ^ C.show_env env1
       ^ "\n\n"));

    let env = List.rev (C.Frame :: join_prefixes env0 env1) in

    (* Construct the joined context - of course, the type, fun, etc. contexts
     * should be the same in the two contexts *)
    let {
      C.type_context;
      fun_context;
      global_context;
      region_groups;
      type_vars;
      env = _;
      ended_regions = ended_regions0;
    } =
      ctx0
    in
    let {
      C.type_context = _;
      fun_context = _;
      global_context = _;
      region_groups = _;
      type_vars = _;
      env = _;
      ended_regions = ended_regions1;
    } =
      ctx1
    in
    let ended_regions = T.RegionId.Set.union ended_regions0 ended_regions1 in
    Ok
      {
        C.type_context;
        fun_context;
        global_context;
        region_groups;
        type_vars;
        env;
        ended_regions;
      }
  with ValueMatchFailure e -> Error e

(** See {!MakeCheckEquivMatcher}.

    Very annoying: functors only take modules as inputs...
 *)
module type MatchCheckEquivState = sig
  (** [true] if we check equivalence between contexts, [false] if we match
      a source context with a target context. *)
  val check_equiv : bool

  val ctx : C.eval_ctx
  val rid_map : T.RegionId.InjSubst.t ref

  (** Substitution for the loan and borrow ids - used only if [check_equiv] is true *)
  val blid_map : V.BorrowId.InjSubst.t ref

  (** Substitution for the borrow ids - used only if [check_equiv] is false *)
  val borrow_id_map : V.BorrowId.InjSubst.t ref

  (** Substitution for the loans ids - used only if [check_equiv] is false *)
  val loan_id_map : V.BorrowId.InjSubst.t ref

  val sid_map : V.SymbolicValueId.InjSubst.t ref
  val sid_to_value_map : V.typed_value V.SymbolicValueId.Map.t ref
  val aid_map : V.AbstractionId.InjSubst.t ref
  val lookup_shared_value_in_ctx0 : V.BorrowId.id -> V.typed_value
  val lookup_shared_value_in_ctx1 : V.BorrowId.id -> V.typed_value
end

(** An auxiliary matcher that we use for two purposes:
    - to check if two contexts are equivalent modulo id substitution (i.e.,
      alpha equivalent) (see {!ctxs_are_equivalent}).
    - to compute a mapping between the borrows and the symbolic values in a
      target context to the values and borrows in a source context (see
      {!match_ctx_with_target}).

    TODO: rename
 *)
module MakeCheckEquivMatcher (S : MatchCheckEquivState) = struct
  module MkGetSetM (Id : Identifiers.Id) = struct
    module Inj = Id.InjSubst

    let add (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) =
      (* Check if k0 is already registered as a key *)
      match Inj.find_opt k0 !m with
      | None ->
          (* Not registered: check if k1 is in the set of values,
             otherwise add the binding *)
          if Inj.Set.mem k1 (Inj.elements !m) then
            raise
              (Distinct
                 (msg ^ "adding [k0=" ^ Id.to_string k0 ^ " -> k1="
                ^ Id.to_string k1 ^ " ]: k1 already in the set of elements"))
          else (
            m := Inj.add k0 k1 !m;
            k1)
      | Some k1' ->
          (* It is: check that the bindings are consistent *)
          if k1 <> k1' then raise (Distinct (msg ^ "already a binding for k0"))
          else k1

    let match_e (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) : Id.id
        =
      (* TODO: merge the add and merge functions *)
      add msg m k0 k1

    let match_el (msg : string) (m : Inj.t ref) (kl0 : Id.id list)
        (kl1 : Id.id list) : Id.id list =
      List.map (fun (k0, k1) -> match_e msg m k0 k1) (List.combine kl0 kl1)

    (** Figuring out mappings between sets of ids is hard in all generality...
        We use the fact that the fresh ids should have been generated
        the same way (i.e., in the same order) and match the ids two by
        two in increasing order.
     *)
    let match_es (msg : string) (m : Inj.t ref) (ks0 : Id.Set.t)
        (ks1 : Id.Set.t) : Id.Set.t =
      Id.Set.of_list
        (match_el msg m (Id.Set.elements ks0) (Id.Set.elements ks1))
  end

  module GetSetRid = MkGetSetM (T.RegionId)

  let match_rid = GetSetRid.match_e "match_rid: " S.rid_map

  (*  let match_ridl = GetSetRid.match_el S.rid_map *)
  let match_rids = GetSetRid.match_es "match_rids: " S.rid_map

  module GetSetBid = MkGetSetM (V.BorrowId)

  let match_blid msg = GetSetBid.match_e msg S.blid_map
  let match_blidl msg = GetSetBid.match_el msg S.blid_map
  let match_blids msg = GetSetBid.match_es msg S.blid_map

  let match_borrow_id =
    if S.check_equiv then match_blid "match_borrow_id: "
    else GetSetBid.match_e "match_borrow_id: " S.borrow_id_map

  let match_borrow_idl =
    if S.check_equiv then match_blidl "match_borrow_idl: "
    else GetSetBid.match_el "match_borrow_idl: " S.borrow_id_map

  let match_borrow_ids =
    if S.check_equiv then match_blids "match_borrow_ids: "
    else GetSetBid.match_es "match_borrow_ids: " S.borrow_id_map

  let match_loan_id =
    if S.check_equiv then match_blid "match_loan_id: "
    else GetSetBid.match_e "match_loan_id: " S.loan_id_map

  let match_loan_idl =
    if S.check_equiv then match_blidl "match_loan_idl: "
    else GetSetBid.match_el "match_loan_idl: " S.loan_id_map

  let match_loan_ids =
    if S.check_equiv then match_blids "match_loan_ids: "
    else GetSetBid.match_es "match_loan_ids: " S.loan_id_map

  module GetSetSid = MkGetSetM (V.SymbolicValueId)
  module GetSetAid = MkGetSetM (V.AbstractionId)

  let match_aid = GetSetAid.match_e "match_aid: " S.aid_map
  let match_aidl = GetSetAid.match_el "match_aidl: " S.aid_map
  let match_aids = GetSetAid.match_es "match_aids: " S.aid_map

  (** *)
  let match_etys ty0 ty1 =
    if ty0 <> ty1 then raise (Distinct "match_etys") else ty0

  let match_rtys ty0 ty1 =
    let match_distinct_types _ _ = raise (Distinct "match_rtys") in
    let match_regions r0 r1 =
      match (r0, r1) with
      | T.Static, T.Static -> r1
      | Var rid0, Var rid1 ->
          let rid = match_rid rid0 rid1 in
          Var rid
      | _ -> raise (Distinct "match_rtys")
    in
    match_types match_distinct_types match_regions ty0 ty1

  let match_distinct_primitive_values (ty : T.ety) (_ : V.primitive_value)
      (_ : V.primitive_value) : V.typed_value =
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_distinct_adts (_ty : T.ety) (_adt0 : V.adt_value)
      (_adt1 : V.adt_value) : V.typed_value =
    raise (Distinct "match_distinct_adts")

  let match_shared_borrows
      (match_typed_values : V.typed_value -> V.typed_value -> V.typed_value)
      (_ty : T.ety) (bid0 : V.borrow_id) (bid1 : V.borrow_id) : V.borrow_id =
    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher: match_shared_borrows: " ^ "bid0: "
       ^ V.BorrowId.to_string bid0 ^ ", bid1: " ^ V.BorrowId.to_string bid1));

    let bid = match_borrow_id bid0 bid1 in
    (* If we don't check for equivalence (i.e., we apply a fixed-point),
       we lookup the shared values and match them.
    *)
    let _ =
      if S.check_equiv then ()
      else
        let v0 = S.lookup_shared_value_in_ctx0 bid0 in
        let v1 = S.lookup_shared_value_in_ctx1 bid1 in
        log#ldebug
          (lazy
            ("MakeCheckEquivMatcher: match_shared_borrows: looked up values:"
           ^ "sv0: "
            ^ typed_value_to_string S.ctx v0
            ^ ", sv1: "
            ^ typed_value_to_string S.ctx v1));

        let _ = match_typed_values v0 v1 in
        ()
    in
    bid

  let match_mut_borrows (_ty : T.ety) (bid0 : V.borrow_id)
      (_bv0 : V.typed_value) (bid1 : V.borrow_id) (_bv1 : V.typed_value)
      (bv : V.typed_value) : V.borrow_id * V.typed_value =
    let bid = match_borrow_id bid0 bid1 in
    (bid, bv)

  let match_shared_loans (_ : T.ety) (ids0 : V.loan_id_set)
      (ids1 : V.loan_id_set) (sv : V.typed_value) :
      V.loan_id_set * V.typed_value =
    let ids = match_loan_ids ids0 ids1 in
    (ids, sv)

  let match_mut_loans (_ : T.ety) (bid0 : V.loan_id) (bid1 : V.loan_id) :
      V.loan_id =
    match_loan_id bid0 bid1

  let match_symbolic_values (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) :
      V.symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in

    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher: match_symbolic_values: " ^ "sv0: "
        ^ V.SymbolicValueId.to_string id0
        ^ ", sv1: "
        ^ V.SymbolicValueId.to_string id1));

    (* If we don't check for equivalence, we also update the map from sids
       to values *)
    if S.check_equiv then
      (* Create the joined symbolic value *)
      let sv_id =
        GetSetSid.match_e "match_symbolic_values: ids: " S.sid_map id0 id1
      in
      let sv_ty = match_rtys sv0.V.sv_ty sv1.V.sv_ty in
      let sv_kind =
        if sv0.V.sv_kind = sv1.V.sv_kind then sv0.V.sv_kind
        else raise (Distinct "match_symbolic_values: sv_kind")
      in
      let sv = { V.sv_id; sv_ty; sv_kind } in
      sv
    else (
      (* Check: fixed values are fixed *)
      assert (id0 = id1 || not (V.SymbolicValueId.InjSubst.mem id0 !S.sid_map));

      (* Update the symbolic value mapping *)
      let sv1 = mk_typed_value_from_symbolic_value sv1 in

      (* Update the symbolic value mapping *)
      S.sid_to_value_map :=
        V.SymbolicValueId.Map.add_strict id0 sv1 !S.sid_to_value_map;

      (* Return - the returned value is not used: we can return  whatever
         we want *)
      sv0)

  let match_symbolic_with_other (left : bool) (sv : V.symbolic_value)
      (v : V.typed_value) : V.typed_value =
    if S.check_equiv then raise (Distinct "match_symbolic_with_other")
    else (
      assert left;
      let id = sv.sv_id in
      (* Check: fixed values are fixed *)
      assert (not (V.SymbolicValueId.InjSubst.mem id !S.sid_map));
      (* Update the binding for the target symbolic value *)
      S.sid_to_value_map :=
        V.SymbolicValueId.Map.add_strict id v !S.sid_to_value_map;
      (* Return - the returned value is not used, so we can return whatever we want *)
      v)

  let match_bottom_with_other (left : bool) (v : V.typed_value) : V.typed_value
      =
    (* It can happen that some variables get initialized in some branches
       and not in some others, which causes problems when matching. *)
    (* TODO: the returned value is not used, while it should: in generality it
       should be ok to match a fixed-point with the environment we get at
       a continue, where the fixed point contains some bottom values. *)
    if left && not (value_has_loans_or_borrows S.ctx v.V.value) then
      mk_bottom v.V.ty
    else raise (Distinct "match_bottom_with_other")

  let match_distinct_aadts _ _ _ _ _ = raise (Distinct "match_distinct_adts")

  let match_ashared_borrows _ty0 bid0 _ty1 bid1 ty =
    let bid = match_borrow_id bid0 bid1 in
    let value = V.ABorrow (V.ASharedBorrow bid) in
    { V.value; ty }

  let match_amut_borrows _ty0 bid0 _av0 _ty1 bid1 _av1 ty av =
    let bid = match_borrow_id bid0 bid1 in
    let value = V.ABorrow (V.AMutBorrow (bid, av)) in
    { V.value; ty }

  let match_ashared_loans _ty0 ids0 _v0 _av0 _ty1 ids1 _v1 _av1 ty v av =
    let bids = match_loan_ids ids0 ids1 in
    let value = V.ALoan (V.ASharedLoan (bids, v, av)) in
    { V.value; ty }

  let match_amut_loans _ty0 id0 _av0 _ty1 id1 _av1 ty av =
    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher:match_amut_loans:" ^ "\n- id0: "
       ^ V.BorrowId.to_string id0 ^ "\n- id1: " ^ V.BorrowId.to_string id1
       ^ "\n- ty: " ^ rty_to_string S.ctx ty ^ "\n- av: "
        ^ typed_avalue_to_string S.ctx av));

    let id = match_loan_id id0 id1 in
    let value = V.ALoan (V.AMutLoan (id, av)) in
    { V.value; ty }

  let match_avalues v0 v1 =
    log#ldebug
      (lazy
        ("avalues don't match:\n- v0: "
        ^ typed_avalue_to_string S.ctx v0
        ^ "\n- v1: "
        ^ typed_avalue_to_string S.ctx v1));
    raise (Distinct "match_avalues")
end

(** See {!match_ctxs} *)
type ids_maps = {
  aid_map : V.AbstractionId.InjSubst.t;
  blid_map : V.BorrowId.InjSubst.t;
      (** Substitution for the loan and borrow ids *)
  borrow_id_map : V.BorrowId.InjSubst.t;  (** Substitution for the borrow ids *)
  loan_id_map : V.BorrowId.InjSubst.t;  (** Substitution for the loan ids *)
  rid_map : T.RegionId.InjSubst.t;
  sid_map : V.SymbolicValueId.InjSubst.t;
  sid_to_value_map : V.typed_value V.SymbolicValueId.Map.t;
}
[@@deriving show]

(** Compute whether two contexts are equivalent modulo an identifier substitution.

    [fixed_ids]: ids for which we force the mapping to be the identity.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for {!join_ctxs}.

    TODO: explanations.

    [check_equiv]: if [true], check if the two contexts are equivalent.
    If [false], compute a mapping from the first context to the second context,
    in the sense of [match_ctx_with_target].

    The lookup functions are used to match the shared values when [check_equiv]
    is [false] (we sometimes use [match_ctxs] on partial environments, meaning
    we have to lookup the shared values in the complete environment, otherwise
    we miss some mappings).

    We return an optional ids map: [Some] if the match succeeded, [None] otherwise.
 *)
let match_ctxs (check_equiv : bool) (fixed_ids : ids_sets)
    (lookup_shared_value_in_ctx0 : V.BorrowId.id -> V.typed_value)
    (lookup_shared_value_in_ctx1 : V.BorrowId.id -> V.typed_value)
    (ctx0 : C.eval_ctx) (ctx1 : C.eval_ctx) : ids_maps option =
  log#ldebug
    (lazy
      ("match_ctxs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx1
      ^ "\n\n"));

  (* Initialize the maps and instantiate the matcher *)
  let module IdMap (Id : Identifiers.Id) = struct
    let mk_map_ref (ids : Id.Set.t) : Id.InjSubst.t ref =
      ref
        (Id.InjSubst.of_list (List.map (fun x -> (x, x)) (Id.Set.elements ids)))
  end in
  let rid_map =
    let module IdMap = IdMap (T.RegionId) in
    IdMap.mk_map_ref fixed_ids.rids
  in
  let blid_map =
    let module IdMap = IdMap (V.BorrowId) in
    IdMap.mk_map_ref fixed_ids.blids
  in
  let borrow_id_map =
    let module IdMap = IdMap (V.BorrowId) in
    IdMap.mk_map_ref fixed_ids.borrow_ids
  in
  let loan_id_map =
    let module IdMap = IdMap (V.BorrowId) in
    IdMap.mk_map_ref fixed_ids.loan_ids
  in
  let aid_map =
    let module IdMap = IdMap (V.AbstractionId) in
    IdMap.mk_map_ref fixed_ids.aids
  in
  let sid_map =
    let module IdMap = IdMap (V.SymbolicValueId) in
    IdMap.mk_map_ref fixed_ids.sids
  in
  (* In case we don't try to check equivalence but want to compute a mapping
     from a source context to a target context, we use a map from symbolic
     value ids to values (rather than to ids).
  *)
  let sid_to_value_map : V.typed_value V.SymbolicValueId.Map.t ref =
    ref V.SymbolicValueId.Map.empty
  in

  let module S : MatchCheckEquivState = struct
    let check_equiv = check_equiv
    let ctx = ctx0
    let rid_map = rid_map
    let blid_map = blid_map
    let borrow_id_map = borrow_id_map
    let loan_id_map = loan_id_map
    let sid_map = sid_map
    let sid_to_value_map = sid_to_value_map
    let aid_map = aid_map
    let lookup_shared_value_in_ctx0 = lookup_shared_value_in_ctx0
    let lookup_shared_value_in_ctx1 = lookup_shared_value_in_ctx1
  end in
  let module CEM = MakeCheckEquivMatcher (S) in
  let module M = Match (CEM) in
  (* Match the environments - we assume that they have the same structure
     (and fail if they don't) *)

  (* Small utility: check that ids are fixed/mapped to themselves *)
  let ids_are_fixed (ids : ids_sets) : bool =
    let { aids; blids = _; borrow_ids; loan_ids; dids; rids; sids } = ids in
    V.AbstractionId.Set.subset aids fixed_ids.aids
    && V.BorrowId.Set.subset borrow_ids fixed_ids.borrow_ids
    && V.BorrowId.Set.subset loan_ids fixed_ids.loan_ids
    && C.DummyVarId.Set.subset dids fixed_ids.dids
    && T.RegionId.Set.subset rids fixed_ids.rids
    && V.SymbolicValueId.Set.subset sids fixed_ids.sids
  in

  (* We need to pick a context for some functions like [match_typed_values]:
     the context is only used to lookup module data, so we can pick whichever
     we want.
     TODO: this is not very clean. Maybe we should just carry the relevant data
     (i.e.e, not the whole context) around.
  *)
  let ctx = ctx0 in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let match_abstractions (abs0 : V.abs) (abs1 : V.abs) : unit =
    let {
      V.abs_id = abs_id0;
      kind = kind0;
      can_end = can_end0;
      parents = parents0;
      original_parents = original_parents0;
      regions = regions0;
      ancestors_regions = ancestors_regions0;
      avalues = avalues0;
    } =
      abs0
    in

    let {
      V.abs_id = abs_id1;
      kind = kind1;
      can_end = can_end1;
      parents = parents1;
      original_parents = original_parents1;
      regions = regions1;
      ancestors_regions = ancestors_regions1;
      avalues = avalues1;
    } =
      abs1
    in

    let _ = CEM.match_aid abs_id0 abs_id1 in
    if kind0 <> kind1 || can_end0 <> can_end1 then
      raise (Distinct "match_abstractions: kind or can_end");
    let _ = CEM.match_aids parents0 parents1 in
    let _ = CEM.match_aidl original_parents0 original_parents1 in
    let _ = CEM.match_rids regions0 regions1 in
    let _ = CEM.match_rids ancestors_regions0 ancestors_regions1 in

    log#ldebug (lazy "match_abstractions: matching values");
    let _ =
      List.map
        (fun (v0, v1) -> M.match_typed_avalues ctx v0 v1)
        (List.combine avalues0 avalues1)
    in
    log#ldebug (lazy "match_abstractions: values matched OK");
    ()
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let rec match_envs (env0 : C.env) (env1 : C.env) : unit =
    log#ldebug
      (lazy
        ("match_ctxs: match_envs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
       ^ "\n\n- rid_map: "
        ^ T.RegionId.InjSubst.show_t !rid_map
        ^ "\n- blid_map: "
        ^ V.BorrowId.InjSubst.show_t !blid_map
        ^ "\n- sid_map: "
        ^ V.SymbolicValueId.InjSubst.show_t !sid_map
        ^ "\n- aid_map: "
        ^ V.AbstractionId.InjSubst.show_t !aid_map
        ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string_no_filter { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string_no_filter { ctx1 with env = List.rev env1 }
        ^ "\n\n"));

    match (env0, env1) with
    | ( C.Var (C.DummyBinder b0, v0) :: env0',
        C.Var (C.DummyBinder b1, v1) :: env1' ) ->
        (* Sanity check: if the dummy value is an old value, the bindings must
           be the same and their values equal (and the borrows/loans/symbolic *)
        if C.DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Fixed values: the values must be equal *)
          assert (b0 = b1);
          assert (v0 = v1);
          (* The ids present in the left value must be fixed *)
          let ids, _ = compute_typed_value_ids v0 in
          assert ((not S.check_equiv) || ids_are_fixed ids));
        (* We still match the values - allows to compute mappings (which
           are the identity actually) *)
        let _ = M.match_typed_values ctx v0 v1 in
        match_envs env0' env1'
    | C.Var (C.VarBinder b0, v0) :: env0', C.Var (C.VarBinder b1, v1) :: env1'
      ->
        assert (b0 = b1);
        (* Match the values *)
        let _ = M.match_typed_values ctx v0 v1 in
        (* Continue *)
        match_envs env0' env1'
    | C.Abs abs0 :: env0', C.Abs abs1 :: env1' ->
        log#ldebug (lazy "match_ctxs: match_envs: matching abs");
        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          log#ldebug (lazy "match_ctxs: match_envs: matching abs: fixed abs");
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
          (* Their ids must be fixed *)
          let ids, _ = compute_abs_ids abs0 in
          assert ((not S.check_equiv) || ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else (
          log#ldebug
            (lazy "match_ctxs: match_envs: matching abs: not fixed abs");
          (* Match the values *)
          match_abstractions abs0 abs1;
          (* Continue *)
          match_envs env0' env1')
    | [], [] ->
        (* Done *)
        ()
    | _ ->
        (* The elements don't match *)
        raise (Distinct "match_ctxs: match_envs: env elements don't match")
  in

  (* Match the environments.

     Rem.: we don't match the ended regions (would it make any sense actually?) *)
  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0 = List.rev ctx0.env in
    let env1 = List.rev ctx1.env in
    let env0, env1 =
      match (env0, env1) with
      | C.Frame :: env0, C.Frame :: env1 -> (env0, env1)
      | _ -> raise (Failure "Unreachable")
    in

    match_envs env0 env1;
    let maps =
      {
        aid_map = !aid_map;
        blid_map = !blid_map;
        borrow_id_map = !borrow_id_map;
        loan_id_map = !loan_id_map;
        rid_map = !rid_map;
        sid_map = !sid_map;
        sid_to_value_map = !sid_to_value_map;
      }
    in
    Some maps
  with Distinct msg ->
    log#ldebug (lazy ("match_ctxs: distinct: " ^ msg));
    None

(** Compute whether two contexts are equivalent modulo an identifier substitution.

    [fixed_ids]: ids for which we force the mapping to be the identity.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for {!join_ctxs}.

    For instance, the following environments are equivalent:
    {[
      env0 = {
        abs@0 { ML l0 }
        ls -> MB l1 (s2 : loops::List<T>)
        i -> s1 : u32
        abs@1 { MB l0, ML l1 }
      }

      env1 = {
        abs@0 { ML l0 }
        ls -> MB l2 (s4 : loops::List<T>)
        i -> s3 : u32
        abs@2 { MB l0, ML l2 }
      }
    ]}
    
    We can go from [env0] to [env1] with the substitution:
    {[
      abs_id_subst: { abs@1 -> abs@2 }
      borrow_id_subst: { l1 -> l2 }
      symbolic_id_subst: { s1 -> s3, s2 -> s4 }
    ]}
 *)
let ctxs_are_equivalent (fixed_ids : ids_sets) (ctx0 : C.eval_ctx)
    (ctx1 : C.eval_ctx) : bool =
  let check_equivalent = true in
  let lookup_shared_value _ = raise (Failure "Unreachable") in
  Option.is_some
    (match_ctxs check_equivalent fixed_ids lookup_shared_value
       lookup_shared_value ctx0 ctx1)

(** Join the context at the entry of the loop with the contexts upon reentry
    (upon reaching the [Continue] statement - the goal is to compute a fixed
    point for the loop entry).

    As we may have to end loans in the environments before doing the join,
    we return those updated environments, and the joined environment.
 *)
let loop_join_origin_with_continue_ctxs (config : C.config)
    (loop_id : V.LoopId.id) (fixed_ids : ids_sets) (old_ctx : C.eval_ctx)
    (ctxl : C.eval_ctx list) : (C.eval_ctx * C.eval_ctx list) * C.eval_ctx =
  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
     Rem.: we should never have to end loans in the aggregated context, only
     in the one we are trying to add to the join.
  *)
  let joined_ctx = ref old_ctx in
  let rec join_one_aux (ctx : C.eval_ctx) : C.eval_ctx =
    match join_ctxs loop_id fixed_ids !joined_ctx ctx with
    | Ok nctx ->
        joined_ctx := nctx;
        ctx
    | Error err ->
        let ctx =
          match err with
          | LoanInRight bid ->
              InterpreterBorrows.end_borrow_no_synth config bid ctx
          | LoansInRight bids ->
              InterpreterBorrows.end_borrows_no_synth config bids ctx
          | AbsInRight _ | AbsInLeft _ | LoanInLeft _ | LoansInLeft _ ->
              raise (Failure "Unexpected")
        in
        join_one_aux ctx
  in
  let join_one (ctx : C.eval_ctx) : C.eval_ctx =
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: initial ctx:\n"
       ^ eval_ctx_to_string ctx));

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs loop_id fixed_ids.aids ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after destructure:\n"
       ^ eval_ctx_to_string ctx));

    (* Collapse the context we want to add to the join *)
    let ctx = collapse_ctx loop_id None fixed_ids ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after collapse:\n"
       ^ eval_ctx_to_string ctx));

    (* Refresh the fresh abstractions *)
    let ctx = refresh_abs fixed_ids.aids ctx in

    (* Join the two contexts  *)
    let ctx1 = join_one_aux ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after join:\n"
       ^ eval_ctx_to_string ctx1));

    (* Collapse again - the join might have introduce abstractions we want
       to merge with the others (note that those abstractions may actually
       lead to borrows/loans duplications) *)
    joined_ctx := collapse_ctx_with_merge loop_id fixed_ids !joined_ctx;
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after join-collapse:\n"
        ^ eval_ctx_to_string !joined_ctx));

    (* Sanity check *)
    if !Config.check_invariants then Invariants.check_invariants !joined_ctx;
    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  ((old_ctx, ctxl), !joined_ctx)

(** Prepare the shared loans in the abstractions by moving them to fresh
    abstractions.

    We use this to prepare an evaluation context before computing a fixed point.

    Because a loop iteration might lead to symbolic value expansions and create
    shared loans in shared values inside the *fixed* abstractions, which we want
    to leave unchanged, we introduce some reborrows in the following way:

    {[
      abs'0 { SL {l0, l1} s0 }
      l0 -> SB l0
      l1 -> SB l1

        ~~>

      abs'0 { SL {l0, l1} s0 }
      l0 -> SB l2
      l1 -> SB l3
      abs'2 { SB l0, SL {l2} s2 }
      abs'3 { SB l1, SL {l3} s3 }
    ]}

    This is sound but leads to information loss. This way, the fixed abstraction
    [abs'0] is never modified because [s0] is never accessed (and thus never
    expanded).

    We do this because it makes it easier to compute joins and fixed points.

    **REMARK**:
    As a side note, we only reborrow the loan ids whose corresponding borrows
    appear in values (i.e., not in abstractions).

    For instance, if we have:
    {[
      abs'0 {
        SL {l0} s0
        SL {l1} s1
      }
      abs'1 { SB l0 }
      x -> SB l1
    ]}

    we only introduce a fresh abstraction for [l1].
  *)
let prepare_ashared_loans (loop_id : V.LoopId.id option) : cm_fun =
 fun cf ctx0 ->
  let ctx = ctx0 in
  (* Compute the set of borrows which appear in the abstractions, so that
     we can filter the borrows that we reborrow.
  *)
  let absl =
    List.filter_map
      (function C.Var _ | C.Frame -> None | C.Abs abs -> Some abs)
      ctx.env
  in
  let absl_ids, absl_id_maps = compute_absl_ids absl in
  let abs_borrow_ids = absl_ids.borrow_ids in

  (* Map from the fresh sids to the original symbolic values *)
  let sid_subst = ref [] in

  (* Return the same value but where:
     - the shared loans have been removed
     - the symbolic values have been replaced with fresh symbolic values
     - the region ids found in the value and belonging to the set [rids] have
       been substituted with [nrid]
  *)
  let mk_value_with_fresh_sids_no_shared_loans (rids : T.RegionId.Set.t)
      (nrid : T.RegionId.id) (v : V.typed_value) : V.typed_value =
    (* Remove the shared loans *)
    let v = value_remove_shared_loans v in
    (* Substitute the symbolic values and the region *)
    Subst.typed_value_subst_ids
      (fun r -> if T.RegionId.Set.mem r rids then nrid else r)
      (fun x -> x)
      (fun x -> x)
      (fun id ->
        let nid = C.fresh_symbolic_value_id () in
        let sv = V.SymbolicValueId.Map.find id absl_id_maps.sids_to_values in
        sid_subst := (nid, sv) :: !sid_subst;
        nid)
      (fun x -> x)
      v
  in

  let borrow_substs = ref [] in
  let fresh_absl = ref [] in

  (* Auxiliary function to create a new abstraction for a shared value found in
     an abstraction.

     Example:
     ========
     When exploring:
     {[
       abs'0 { SL {l0, l1} s0 }
     ]}

     we find the shared value:

     {[
       SL {l0, l1} s0
     ]}

     and introduce the corresponding abstraction:
     {[
       abs'2 { SB l0, SL {l2} s2 }
     ]}
  *)
  let push_abs_for_shared_value (abs : V.abs) (sv : V.typed_value)
      (lid : V.BorrowId.id) : unit =
    (* Create a fresh borrow (for the reborrow) *)
    let nlid = C.fresh_borrow_id () in

    (* We need a fresh region for the new abstraction *)
    let nrid = C.fresh_region_id () in

    (* Prepare the shared value *)
    let nsv = mk_value_with_fresh_sids_no_shared_loans abs.regions nrid sv in

    (* Save the borrow substitution, to apply it to the context later *)
    borrow_substs := (lid, nlid) :: !borrow_substs;

    (* Rem.: the below sanity checks are not really necessary *)
    assert (V.AbstractionId.Set.is_empty abs.parents);
    assert (abs.original_parents = []);
    assert (T.RegionId.Set.is_empty abs.ancestors_regions);

    (* Introduce the new abstraction for the shared values *)
    let rty = ety_no_regions_to_rty sv.V.ty in

    (* Create the shared loan child *)
    let child_rty = rty in
    let child_av = mk_aignored child_rty in

    (* Create the shared loan *)
    let loan_rty = T.Ref (T.Var nrid, rty, T.Shared) in
    let loan_value =
      V.ALoan (V.ASharedLoan (V.BorrowId.Set.singleton nlid, nsv, child_av))
    in
    let loan_value = mk_typed_avalue loan_rty loan_value in

    (* Create the shared borrow *)
    let borrow_rty = loan_rty in
    let borrow_value = V.ABorrow (V.ASharedBorrow lid) in
    let borrow_value = mk_typed_avalue borrow_rty borrow_value in

    (* Create the abstraction *)
    let avalues = [ borrow_value; loan_value ] in
    let kind =
      match loop_id with
      | Some loop_id -> V.Loop (loop_id, None, V.LoopSynthInput)
      | None -> V.Identity
    in
    let can_end = true in
    let fresh_abs =
      {
        V.abs_id = C.fresh_abstraction_id ();
        kind;
        can_end;
        parents = V.AbstractionId.Set.empty;
        original_parents = [];
        regions = T.RegionId.Set.singleton nrid;
        ancestors_regions = T.RegionId.Set.empty;
        avalues;
      }
    in
    fresh_absl := fresh_abs :: !fresh_absl
  in

  (* Explore the shared values in the context abstractions, and introduce
     fresh abstractions with reborrows for those shared values.

     We simply explore the context and call {!push_abs_for_shared_value}
     when necessary.
  *)
  let collect_shared_values_in_abs (abs : V.abs) : unit =
    let collect_shared_value lids (sv : V.typed_value) =
      (* Sanity check: we don't support nested borrows for now *)
      assert (not (value_has_borrows ctx sv.V.value));

      (* Filter the loan ids whose corresponding borrows appear in abstractions
         (see the documentation of the function) *)
      let lids = V.BorrowId.Set.diff lids abs_borrow_ids in

      (* Generate fresh borrows and values *)
      V.BorrowId.Set.iter (push_abs_for_shared_value abs sv) lids
    in

    let visit_avalue =
      object
        inherit [_] V.iter_typed_avalue as super

        method! visit_SharedLoan env lids sv =
          collect_shared_value lids sv;

          (* Continue the exploration *)
          super#visit_SharedLoan env lids sv

        method! visit_ASharedLoan env lids sv _ =
          collect_shared_value lids sv;

          (* Continue the exploration *)
          super#visit_SharedLoan env lids sv

        (** Check that there are no symbolic values with *borrows* inside the
            abstraction - shouldn't happen if the symbolic values are greedily
            expanded.
            We do this because those values could contain shared borrows:
            if it is the case, we need to duplicate them too.
            TODO: implement this more general behavior.
         *)
        method! visit_symbolic_value env sv =
          assert (not (symbolic_value_has_borrows ctx sv));
          super#visit_symbolic_value env sv
      end
    in
    List.iter (visit_avalue#visit_typed_avalue None) abs.avalues
  in
  C.env_iter_abs collect_shared_values_in_abs ctx.env;

  (* Update the borrow ids in the environment.

     Example:
     ========
     If we start with environment:
     {[
       abs'0 { SL {l0, l1} s0 }
       l0 -> SB l0
       l1 -> SB l1
     ]}

     We introduce the following abstractions:
     {[
       abs'2 { SB l0, SL {l2} s2 }
       abs'3 { SB l1, SL {l3} s3 }
     ]}

     While doing so, we registered the fact that we introduced [l2] for [l0]
     and [l3] for [l1]: we now need to perform the proper substitutions in
     the values [l0] and [l1]. This gives:

     {[
       l0 -> SB l0
       l1 -> SB l1

         ~~>

       l0 -> SB l2
       l1 -> SB l3
     ]}
  *)
  let env =
    let bmap = V.BorrowId.Map.of_list !borrow_substs in
    let bsusbt bid =
      match V.BorrowId.Map.find_opt bid bmap with
      | None -> bid
      | Some bid -> bid
    in

    let visitor =
      object
        inherit [_] C.map_env
        method! visit_borrow_id _ bid = bsusbt bid
      end
    in
    visitor#visit_env () ctx.env
  in

  (* Add the abstractions *)
  let fresh_absl = List.map (fun abs -> C.Abs abs) !fresh_absl in
  let env = List.append fresh_absl env in
  let ctx = { ctx with env } in

  let _, new_ctx_ids_map = compute_context_ids ctx in

  (* Synthesize *)
  match cf ctx with
  | None -> None
  | Some e ->
      (* Add the let-bindings which introduce the fresh symbolic values *)
      Some
        (List.fold_left
           (fun e (sid, v) ->
             let v = mk_typed_value_from_symbolic_value v in
             let sv =
               V.SymbolicValueId.Map.find sid new_ctx_ids_map.sids_to_values
             in
             SymbolicAst.IntroSymbolic (ctx, None, sv, v, e))
           e !sid_subst)

let prepare_ashared_loans_no_synth (loop_id : V.LoopId.id) (ctx : C.eval_ctx) :
    C.eval_ctx =
  get_cf_ctx_no_synth (prepare_ashared_loans (Some loop_id)) ctx

(** Compute a fixed-point for the context at the entry of the loop.
    We also return:
    - the sets of fixed ids
    - the map from region group id to the corresponding abstraction appearing
      in the fixed point (this is useful to compute the return type of the loop
      backward functions for instance).

    Rem.: the list of symbolic values should be computable by simply exploring
    the fixed point environment and listing all the symbolic values we find.
    In the future, we might want to do something more precise, by listing only
    the values which are read or modified (some symbolic values may be ignored).
 *)
let compute_loop_entry_fixed_point (config : C.config) (loop_id : V.LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) :
    C.eval_ctx * ids_sets * V.abs T.RegionGroupId.Map.t =
  (* The continuation for when we exit the loop - we register the
     environments upon loop *reentry*, and synthesize nothing by
     returning [None]
  *)
  let ctxs = ref [] in
  let register_ctx ctx = ctxs := ctx :: !ctxs in

  (* Introduce "reborrows" for the shared values in the abstractions, so that
     the shared values in the fixed abstractions never get modified (technically,
     they are immutable, but in practice we can introduce more shared loans, or
     expand symbolic values).

     For more details, see the comments for {!prepare_ashared_loans}
  *)
  let ctx = prepare_ashared_loans_no_synth loop_id ctx0 in

  (* Debug *)
  log#ldebug
    (lazy
      ("compute_loop_entry_fixed_point: after prepare_ashared_loans:"
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n\n"));

  let cf_exit_loop_body (res : statement_eval_res) : m_fun =
   fun ctx ->
    match res with
    | Return | Panic | Break _ -> None
    | Unit ->
        (* See the comment in {!eval_loop} *)
        raise (Failure "Unreachable")
    | Continue i ->
        (* For now we don't support continues to outer loops *)
        assert (i = 0);
        register_ctx ctx;
        None
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We don't support nested loops for now *)
        raise (Failure "Nested loops are not supported for now")
  in

  (* The fixed ids. They are the ids of the original ctx, after we ended
     the borrows/loans which end during the first loop iteration (we do
     one loop iteration, then set it to [Some].
  *)
  let fixed_ids : ids_sets option ref = ref None in

  (* Join the contexts at the loop entry - ctx1 is the current joined
     context (the context at the loop entry, after we called
     {!prepare_ashared_loans}, if this is the first iteration) *)
  let join_ctxs (ctx1 : C.eval_ctx) : C.eval_ctx =
    (* If this is the first iteration, end the borrows/loans/abs which
       appear in ctx1 and not in the other contexts, then compute the
       set of fixed ids. This means those borrows/loans have to end
       in the loop, and we rather end them *before* the loop. *)
    let ctx1 =
      match !fixed_ids with
      | Some _ -> ctx1
      | None ->
          let old_ids, _ = compute_context_ids ctx1 in
          let new_ids, _ = compute_contexts_ids !ctxs in
          let blids = V.BorrowId.Set.diff old_ids.blids new_ids.blids in
          let aids = V.AbstractionId.Set.diff old_ids.aids new_ids.aids in
          (* End those borrows and abstractions *)
          let end_borrows_abs blids aids ctx =
            let ctx =
              InterpreterBorrows.end_borrows_no_synth config blids ctx
            in
            let ctx =
              InterpreterBorrows.end_abstractions_no_synth config aids ctx
            in
            ctx
          in
          (* End the borrows/abs in [ctx1] *)
          let ctx1 = end_borrows_abs blids aids ctx1 in
          (* We can also do the same in the contexts [ctxs]: if there are
             several contexts, maybe one of them ended some borrows and some
             others didn't. As we need to end those borrows anyway (the join
             will detect them and ask to end them) we do it preemptively.
          *)
          ctxs := List.map (end_borrows_abs blids aids) !ctxs;
          (* Note that the fixed ids are given by the original context, from *before*
             we introduce fresh abstractions/reborrows for the shared values *)
          fixed_ids := Some (fst (compute_context_ids ctx0));
          ctx1
    in

    let fixed_ids = Option.get !fixed_ids in
    let (_, _), ctx2 =
      loop_join_origin_with_continue_ctxs config loop_id fixed_ids ctx1 !ctxs
    in
    ctxs := [];
    ctx2
  in
  (* Compute the set of fixed ids - for the symbolic ids, we compute the
     intersection of ids between the original environment and the list
     of new environments *)
  let compute_fixed_ids (ctxl : C.eval_ctx list) : ids_sets =
    let fixed_ids, _ = compute_context_ids ctx0 in
    let { aids; blids; borrow_ids; loan_ids; dids; rids; sids } = fixed_ids in
    let sids = ref sids in
    List.iter
      (fun ctx ->
        let fixed_ids, _ = compute_context_ids ctx in
        sids := V.SymbolicValueId.Set.inter !sids fixed_ids.sids)
      ctxl;
    let sids = !sids in
    let fixed_ids = { aids; blids; borrow_ids; loan_ids; dids; rids; sids } in
    fixed_ids
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values.
  *)
  let equiv_ctxs (ctx1 : C.eval_ctx) (ctx2 : C.eval_ctx) : bool =
    let fixed_ids = compute_fixed_ids [ ctx1; ctx2 ] in
    let check_equivalent = true in
    let lookup_shared_value _ = raise (Failure "Unreachable") in
    Option.is_some
      (match_ctxs check_equivalent fixed_ids lookup_shared_value
         lookup_shared_value ctx1 ctx2)
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  let rec compute_fixed_point (ctx : C.eval_ctx) (i0 : int) (i : int) :
      C.eval_ctx =
    if i = 0 then
      raise
        (Failure
           ("Could not compute a loop fixed point in " ^ string_of_int i0
          ^ " iterations"))
    else
      (* Evaluate the loop body to register the different contexts upon reentry *)
      let _ = eval_loop_body cf_exit_loop_body ctx in
      (* Compute the join between the original contexts and the contexts computed
         upon reentry *)
      let ctx1 = join_ctxs ctx in

      (* Debug *)
      log#ldebug
        (lazy
          ("compute_fixed_point:" ^ "\n\n- ctx0:\n"
          ^ eval_ctx_to_string_no_filter ctx
          ^ "\n\n- ctx1:\n"
          ^ eval_ctx_to_string_no_filter ctx1
          ^ "\n\n"));

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 i0 (i - 1)
  in
  let fp = compute_fixed_point ctx max_num_iter max_num_iter in

  (* Debug *)
  log#ldebug
    (lazy
      ("compute_fixed_point: fixed point computed before matching with input \
        region groups:" ^ "\n\n- fp:\n"
      ^ eval_ctx_to_string_no_filter fp
      ^ "\n\n"));

  (* Make sure we have exactly one loop abstraction per function region (merge
     abstractions accordingly).

     Rem.: this shouldn't impact the set of symbolic value ids (because we
     already merged abstractions "vertically" and are now merging them
     "horizontally": the symbolic values contained in the abstractions (typically
     the shared values) will be preserved.
  *)
  let fp, rg_to_abs =
    (* List the loop abstractions in the fixed-point *)
    let fp_aids, add_aid, _mem_aid = V.AbstractionId.Set.mk_stateful_set () in

    let list_loop_abstractions =
      object
        inherit [_] C.map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              (* The abstractions introduced so far should be endable *)
              assert (abs.can_end = true);
              add_aid abs.abs_id;
              abs
          | _ -> abs
      end
    in
    let fp = list_loop_abstractions#visit_eval_ctx () fp in

    (* For every input region group:
     * - evaluate until we get to a [return]
     * - end the input abstraction corresponding to the input region group
     * - find which loop abstractions end at that moment
     *
     * [fp_ended_aids] links region groups to sets of ended abstractions.
     *)
    let fp_ended_aids = ref T.RegionGroupId.Map.empty in
    let add_ended_aids (rg_id : T.RegionGroupId.id)
        (aids : V.AbstractionId.Set.t) : unit =
      match T.RegionGroupId.Map.find_opt rg_id !fp_ended_aids with
      | None ->
          fp_ended_aids := T.RegionGroupId.Map.add rg_id aids !fp_ended_aids
      | Some aids' ->
          let aids = V.AbstractionId.Set.union aids aids' in
          fp_ended_aids := T.RegionGroupId.Map.add rg_id aids !fp_ended_aids
    in
    let cf_loop : st_m_fun =
     fun res ctx ->
      match res with
      | Continue _ | Panic ->
          (* We don't want to generate anything *)
          None
      | Break _ ->
          (* We enforce that we can't get there: see {!PrePasses.remove_loop_breaks} *)
          raise (Failure "Unreachable")
      | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
          (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
             For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
          *)
          raise (Failure "Unreachable")
      | Return ->
          (* Should we consume the return value and pop the frame?
           * If we check in [Interpreter] that the loop abstraction we end is
           * indeed the correct one, I think it is sound to under-approximate here
           * (and it shouldn't make any difference).
           *)
          let _ =
            List.iter
              (fun rg_id ->
                (* Lookup the input abstraction - we use the fact that the
                   abstractions should have been introduced in a specific
                   order (and we check that it is indeed the case) *)
                let abs_id =
                  V.AbstractionId.of_int (T.RegionGroupId.to_int rg_id)
                in
                (* By default, the [SynthInput] abs can't end *)
                let ctx = C.ctx_set_abs_can_end ctx abs_id true in
                assert (
                  let abs = C.ctx_lookup_abs ctx abs_id in
                  abs.kind = V.SynthInput rg_id);
                (* End this abstraction *)
                let ctx =
                  InterpreterBorrows.end_abstraction_no_synth config abs_id ctx
                in
                (* Explore the context, and check which abstractions are not there anymore *)
                let ids, _ = compute_context_ids ctx in
                let ended_ids = V.AbstractionId.Set.diff !fp_aids ids.aids in
                add_ended_aids rg_id ended_ids)
              ctx.region_groups
          in
          (* We don't want to generate anything *)
          None
    in
    let _ = eval_loop_body cf_loop fp in

    (* Check that the sets of abstractions we need to end per region group are pairwise
     * disjoint *)
    let aids_union = ref V.AbstractionId.Set.empty in
    let _ =
      T.RegionGroupId.Map.iter
        (fun _ ids ->
          assert (V.AbstractionId.Set.disjoint !aids_union ids);
          aids_union := V.AbstractionId.Set.union ids !aids_union)
        !fp_ended_aids
    in

    (* We also check that all the regions need to end - this is not necessary per
       se, but if it doesn't happen it is bizarre and worth investigating... *)
    assert (V.AbstractionId.Set.equal !aids_union !fp_aids);

    (* Merge the abstractions which need to be merged, and compute the map from
       region id to abstraction id *)
    let fp = ref fp in
    let rg_to_abs = ref T.RegionGroupId.Map.empty in
    let _ =
      T.RegionGroupId.Map.iter
        (fun rg_id ids ->
          let ids = V.AbstractionId.Set.elements ids in
          (* Retrieve the first id of the group *)
          match ids with
          | [] ->
              (* We shouldn't get there: we actually introduce reborrows with
                 {!prepare_ashared_loans} and in the [match_mut_borrows] function
                 of {!MakeJoinMatcher} to introduce some fresh abstractions for
                 this purpose.
              *)
              raise (Failure "Unexpected")
          | id0 :: ids ->
              let id0 = ref id0 in
              (* Add the proper region group into the abstraction *)
              let abs_kind = V.Loop (loop_id, Some rg_id, V.LoopSynthInput) in
              let abs = C.ctx_lookup_abs !fp !id0 in
              let abs = { abs with V.kind = abs_kind } in
              let fp', _ = C.ctx_subst_abs !fp !id0 abs in
              fp := fp';
              (* Merge all the abstractions into this one *)
              List.iter
                (fun id ->
                  try
                    log#ldebug
                      (lazy
                        ("compute_loop_entry_fixed_point: merge FP \
                          abstraction: "
                        ^ V.AbstractionId.to_string id
                        ^ " into "
                        ^ V.AbstractionId.to_string !id0));
                    (* Note that we merge *into* [id0] *)
                    let fp', id0' =
                      merge_into_abstraction loop_id abs_kind false !fp id !id0
                    in
                    fp := fp';
                    id0 := id0';
                    ()
                  with ValueMatchFailure _ -> raise (Failure "Unexpected"))
                ids;
              (* Register the mapping *)
              let abs = C.ctx_lookup_abs !fp !id0 in
              rg_to_abs := T.RegionGroupId.Map.add_strict rg_id abs !rg_to_abs)
        !fp_ended_aids
    in
    let rg_to_abs = !rg_to_abs in

    (* Reorder the loans and borrows in the fresh abstractions in the fixed-point *)
    let fp =
      reorder_loans_borrows_in_fresh_abs (Option.get !fixed_ids).aids !fp
    in

    (* Update the abstraction's [can_end] field and their kinds.

       Note that if [remove_rg_id] is [true], we set the region id to [None]
       and set the abstractions as endable: this is so that we can check that
       we have a fixed point (so far in the fixed point the loop abstractions had
       no region group, and we set them as endable just above).

       If [remove_rg_id] is [false], we simply set the abstractions as non-endable
       to freeze them (we will use the fixed point as starting point for the
       symbolic execution of the loop body, and we have to make sure the input
       abstractions are frozen).
    *)
    let update_loop_abstractions (remove_rg_id : bool) =
      object
        inherit [_] C.map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              let kind =
                if remove_rg_id then V.Loop (loop_id, None, V.LoopSynthInput)
                else abs.kind
              in
              { abs with can_end = remove_rg_id; kind }
          | _ -> abs
      end
    in
    let update_kinds_can_end (remove_rg_id : bool) ctx =
      (update_loop_abstractions remove_rg_id)#visit_eval_ctx () ctx
    in
    let fp = update_kinds_can_end false fp in

    (* Sanity check: we still have a fixed point - we simply call [compute_fixed_point]
       while allowing exactly one iteration to see if it fails *)
    let _ =
      let fp_test = update_kinds_can_end true fp in
      log#ldebug
        (lazy
          ("compute_fixed_point: fixed point after matching with the function \
            region groups:\n"
          ^ eval_ctx_to_string_no_filter fp_test));
      compute_fixed_point fp_test 1 1
    in

    (* Return *)
    (fp, rg_to_abs)
  in
  let fixed_ids = compute_fixed_ids [ fp ] in

  (* Return *)
  (fp, fixed_ids, rg_to_abs)

(** Split an environment between the fixed abstractions, values, etc. and
    the new abstractions, values, etc.

    Returns: (fixed, new abs, new dummies)
 *)
let ctx_split_fixed_new (fixed_ids : ids_sets) (ctx : C.eval_ctx) :
    C.env * V.abs list * V.typed_value list =
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    not (C.DummyVarId.Set.mem id fixed_ids.dids)
  in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id fixed_ids.aids)
  in
  (* Filter the new abstractions and dummy variables (there shouldn't be any new dummy variable
     though) in the target context *)
  let is_fresh (ee : C.env_elem) : bool =
    match ee with
    | C.Var (VarBinder _, _) | C.Frame -> false
    | C.Var (DummyBinder bv, _) -> is_fresh_did bv
    | C.Abs abs -> is_fresh_abs_id abs.abs_id
  in
  let new_eel, filt_env = List.partition is_fresh ctx.env in
  let is_abs ee = match ee with C.Abs _ -> true | _ -> false in
  let new_absl, new_dummyl = List.partition is_abs new_eel in
  let new_absl =
    List.map
      (fun ee ->
        match ee with C.Abs abs -> abs | _ -> raise (Failure "Unreachable"))
      new_absl
  in
  let new_dummyl =
    List.map
      (fun ee ->
        match ee with
        | C.Var (DummyBinder _, v) -> v
        | _ -> raise (Failure "Unreachable"))
      new_dummyl
  in
  (filt_env, new_absl, new_dummyl)

type borrow_loan_corresp = {
  borrow_to_loan_id_map : V.BorrowId.InjSubst.t;
  loan_to_borrow_id_map : V.BorrowId.InjSubst.t;
}
[@@deriving show]

let ids_sets_empty_borrows_loans (ids : ids_sets) : ids_sets =
  let { aids; blids = _; borrow_ids = _; loan_ids = _; dids; rids; sids } =
    ids
  in
  let empty = V.BorrowId.Set.empty in
  let ids =
    {
      aids;
      blids = empty;
      borrow_ids = empty;
      loan_ids = empty;
      dids;
      rids;
      sids;
    }
  in
  ids

(** Utility *)
type loans_borrows_pair = {
  loans : V.BorrowId.Set.t;
  borrows : V.BorrowId.Set.t;
}
[@@deriving show, ord]

(** For the abstractions in the fixed point, compute the correspondance between
    the borrows ids and the loans ids, if we want to introduce equivalent
    identity abstractions (i.e., abstractions which do nothing - the input
    borrows are exactly the output loans).

    **Context:**
    ============
    When we (re-enter) the loop, we want to introduce identity abstractions
    (i.e., abstractions which actually only introduce fresh identifiers for
    some borrows, to abstract away a bit the borrow graph) which have the same
    shape as the abstractions introduced for the fixed point (see the explanations
    for [match_ctx_with_target]). This allows us to transform the environment
    into a fixed point (again, see the explanations for [match_ctx_with_target]).

    In order to introduce those identity abstractions, we need to figure out,
    for those abstractions, which loans should be linked to which borrows.
    We do this in the following way.

    We match the fixed point environment with the environment upon first entry
    in the loop, and exploit the fact that the fixed point was derived by also
    joining this first entry environment: because of that, the borrows in the
    abstractions introduced for the fixed-point actually exist in this first
    environment (they are not fresh). For [list_nth_mut] (see the explanations
    at the top of the file) we have the following:

    {[
      // Environment upon first entry in the loop
      env0 = {
        abs@0 { ML l0 }
        ls -> MB l0 (s2 : loops::List<T>)
        i -> s1 : u32
      }

      // Fixed-point environment
      env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s3 : loops::List<T>)
        i -> s4 : u32
        abs@fp {
          MB l0 // this borrow appears in [env0]
          ML l1
        }
      }
    ]}

    We filter those environments to remove the non-fixed dummy variables,
    abstractions, etc. in a manner similar to [match_ctx_with_target]. We
    get:

    {[
      filtered_env0 = {
        abs@0 { ML l0 }
        ls -> MB l0 (s2 : loops::List<T>)
        i -> s1 : u32
      }

      filtered_env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s3 : loops::List<T>)
        i -> s@ : u32
        // removed abs@fp
      }
    ]}

    We then match [filtered_env_fp] with [filtered_env0], taking care to not
    consider loans and borrows in a disjoint manner, and ignoring the fixed
    values, abstractions, loans, etc. We get:
    {[
      borrows_map: { l1 -> l0 } // because we matched [MB l1 ...] with [MB l0 ...] in [ls]
      loans_map: {} // we ignore abs@0, which is "fixed"
    ]}

    From there we deduce that, if we want to introduce an identity abstraction with the
    shape of [abs@fp], we should link [l1] to [l0]. In other words, the value retrieved
    through the loan [l1] is actually the value which has to be given back to [l0].
 *)
let compute_fixed_point_id_correspondance (fixed_ids : ids_sets)
    (src_ctx : C.eval_ctx) (tgt_ctx : C.eval_ctx) : borrow_loan_corresp =
  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- fixed_ids:\n"
     ^ show_ids_sets fixed_ids ^ "\n\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
     ^ "\n\n- tgt_ctx:\n" ^ eval_ctx_to_string tgt_ctx ^ "\n\n"));

  let filt_src_env, _, _ = ctx_split_fixed_new fixed_ids src_ctx in
  let filt_src_ctx = { src_ctx with env = filt_src_env } in
  let filt_tgt_env, new_absl, _ = ctx_split_fixed_new fixed_ids tgt_ctx in
  let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in

  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- fixed_ids:\n"
     ^ show_ids_sets fixed_ids ^ "\n\n- filt_src_ctx:\n"
      ^ eval_ctx_to_string filt_src_ctx
      ^ "\n\n- filt_tgt_ctx:\n"
      ^ eval_ctx_to_string filt_tgt_ctx
      ^ "\n\n"));

  (* Match the source context and the filtered target context *)
  let maps =
    let check_equiv = false in
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : V.typed_value =
      match snd (lookup_loan ek_all lid ctx) with
      | Concrete (V.SharedLoan (_, v)) -> v
      | Abstract (V.ASharedLoan (_, v, _)) -> v
      | _ -> raise (Failure "Unreachable")
    in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    Option.get
      (match_ctxs check_equiv fixed_ids lookup_in_tgt lookup_in_src filt_tgt_ctx
         filt_src_ctx)
  in

  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- tgt_to_src_maps:\n"
     ^ show_ids_maps maps ^ "\n\n"));

  let src_to_tgt_borrow_map =
    V.BorrowId.Map.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (V.BorrowId.InjSubst.bindings maps.borrow_id_map))
  in

  (* Sanity check: for every abstraction, the target loans and borrows are mapped
     to the same set of source loans and borrows.

     For instance, if we map the [env_fp] to [env0] (only looking at the bindings,
     ignoring the abstractions) below:
     {[
       env0 = {
         abs@0 { ML l0 }
         ls -> MB l0 (s2 : loops::List<T>)
         i -> s1 : u32
       }

       env_fp = {
         abs@0 { ML l0 }
         ls -> MB l1 (s3 : loops::List<T>)
         i -> s4 : u32
         abs@fp {
           MB l0
           ML l1
         }
       }
     ]}

     We get that l1 is mapped to l0. From there, we see that abs@fp consumes
     the same borrows that it gives: it is indeed an identity function.

     TODO: we should also check the mappings for the shared values (to
     make sure the abstractions are indeed the identity)...
  *)
  List.iter
    (fun abs ->
      let ids, _ = compute_abs_ids abs in
      (* Map the *loan* ids (we just match the corresponding *loans* ) *)
      let loan_ids =
        V.BorrowId.Set.map
          (fun x -> V.BorrowId.InjSubst.find x maps.borrow_id_map)
          ids.loan_ids
      in
      (* Check that the loan and borrows are related *)
      assert (V.BorrowId.Set.equal ids.borrow_ids loan_ids))
    new_absl;

  (* For every target abstraction (going back to the [list_nth_mut] example,
     we have to visit [abs@fp { ML l0, MB l1 }]):
     - go through the tgt borrows ([l1])
     - for every tgt borrow, find the corresponding src borrow ([l0], because
       we have: [borrows_map: { l1 -> l0 }])
     - from there, find the corresponding tgt loan ([l0])

     Note that this borrow does not necessarily appear in the src_to_tgt_borrow_map,
     if it actually corresponds to a borrows introduced when decomposing the
     abstractions to move the shared values out of the source context abstractions.
  *)
  let tgt_borrow_to_loan = ref V.BorrowId.InjSubst.empty in
  let visit_tgt =
    object
      inherit [_] V.iter_abs

      method! visit_borrow_id _ id =
        (* Find the target borrow *)
        let tgt_borrow_id = V.BorrowId.Map.find id src_to_tgt_borrow_map in
        (* Update the map *)
        tgt_borrow_to_loan :=
          V.BorrowId.InjSubst.add id tgt_borrow_id !tgt_borrow_to_loan
    end
  in
  List.iter (visit_tgt#visit_abs ()) new_absl;

  (* Compute the map from loan to borrows *)
  let tgt_loan_to_borrow =
    V.BorrowId.InjSubst.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (V.BorrowId.InjSubst.bindings !tgt_borrow_to_loan))
  in

  (* Return *)
  {
    borrow_to_loan_id_map = !tgt_borrow_to_loan;
    loan_to_borrow_id_map = tgt_loan_to_borrow;
  }

(** Match a context with a target context.

    This is used to compute application of loop translations: we use this
    to introduce "identity" abstractions upon (re-)entering the loop.

    For instance, the fixed point for [list_nth_mut] (see the top of the file)
    is:
    {[
      env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s@3 : loops::List<T>)
        i -> s@4 : u32
        abs@fp {
          MB l0
          ML l1
        }
      }
    ]}

    Upon re-entering the loop, starting from the fixed point, we get the
    following environment:
    {[
      env = {
        abs@0 { ML l0 }
        ls -> MB l5 (s@6 : loops::List<T>)
        i -> s@7 : u32
        abs@1 { MB l0, ML l1 }
        _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
        _@2 -> MB l3 (@Box (ML l5))                      // tail
        _@3 -> MB l2 (s@3 : T)                           // hd
     }
   ]}

   We want to introduce an abstraction [abs@2], which has the same shape as [abs@fp]
   above (the fixed-point abstraction), and which is actually the identity. If we do so,
   we get an environment which is actually also a fixed point (we can collapse
   the dummy variables and [abs@1] to actually retrieve the fixed point we
   computed, and we use the fact that those values and abstractions can't be
   *directly* manipulated unless we end this newly introduced [abs@2], which we
   forbid).

   We match the *fixed point context* with the context upon entering the loop
   by doing the following.

   1. We filter [env_fp] and [env] to remove the newly introduced dummy variables
   and abstractions. We get:

   {[
     filtered_env_fp = {
       abs@0 { ML l0 }
       ls -> MB l1 (s@3 : loops::List<T>)
       i -> s@4 : u32
       // removed abs@fp
     }

     filtered_env = {
       abs@0 { ML l0 }
       ls -> MB l5 (s@6 : loops::List<T>)
       i -> s@7 : u32
       // removed abs@1, _@1, etc.
     }
   ]}

   2. We match [filtered_env_fp] with [filtered_env] to compute a map from
   the FP borrows/loans to the current borrows/loans (and also from symbolic values to
   values). Note that we take care to *consider loans and borrows separately*,
   and we ignore the "fixed" abstractions (which are unchanged - we checked that
   when computing the fixed point).
   We get:
   {[
     borrows_map: { l1 -> l5 } // because we matched [MB l1 ...] with [MB l5 ...]
     loans_map: {} // we ignore abs@0, which is "fixed"
   ]}

   3. We want to introduce an instance of [abs@fp] which is actually the
   identity. From [compute_fixed_point_id_correspondance] and looking at
   [abs@fp], we know we should link the instantiation of loan [l1] with the
   instantiation of loan [l0]. We substitute [l0] with [l5] (following step 2.)
   and introduce a fresh borrow [l6] for [l5] that we use to instantiate [l1].
   We get the following environment:

   {[
     env = {
       abs@0 { ML l0 }
       ls -> MB l6 (s@6 : loops::List<T>)
       i -> s@7 : u32
       abs@1 { MB l0, ML l1 }
       _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
       _@2 -> MB l3 (@Box (ML l5))                      // tail
       _@3 -> MB l2 (s@3 : T)                           // hd
       abs@2 { MB l5, ML l6 } // this is actually the identity: l6 = l5
     }
   ]}

   4. As we now have a fixed point (see above comments), we can consider than
   [abs@2] links the current iteration to the last one before we exit. What we
   are interested in is that:
   - upon inserting [abs@2] we re-entered the loop, meaning in the translation
     we need to insert a recursive call to the loop forward function
   - upon ending [abs@2] we need to insert a call to the loop backward function

   Because we want to ignore them, we end the loans in the newly introduced
   [abs@2] abstraction (i.e., [l6]). We get:
   {[
     env = {
       abs@0 { ML l0 }
       ls -> ⊥
       i -> s@7 : u32
       abs@1 { MB l0, ML l1 }
       _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
       _@2 -> MB l3 (@Box (ML l5))                      // tail
       _@3 -> MB l2 (s@3 : T)                           // hd
       abs@2 { MB l5 }
     }
   ]}

   TODO: we shouldn't need to end the loans, we should actually remove them
   before inserting the new abstractions (we may have issues with the symbolic
   values, if they contain borrows - above i points to [s@7], but it should
   be a different symbolic value...).

   Finally, we use the map from symbolic values to values to compute the list of
   input values of the loop: we simply list the values, by order of increasing
   symbolic value id. We *do* use the fixed values (though they are in the frame)
   because they may be *read* inside the loop.

   We can then proceed to finishing the symbolic execution and doing the
   synthesis.

   Rem.: we might reorganize the [tgt_ctx] by ending loans for instance.

   **Parameters**:
   [is_loop_entry]: [true] if first entry into the loop, [false] if re-entry
   (i.e., continue).
   [fp_input_svalues]: the list of symbolic values appearing in the fixed
   point and which must be instantiated during the match (this is the list
   of input parameters of the loop).
 *)
let match_ctx_with_target (config : C.config) (loop_id : V.LoopId.id)
    (is_loop_entry : bool) (fp_bl_maps : borrow_loan_corresp)
    (fp_input_svalues : V.SymbolicValueId.id list) (fixed_ids : ids_sets)
    (src_ctx : C.eval_ctx) : st_cm_fun =
 fun cf tgt_ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("match_ctx_with_target:\n" ^ "\n- fixed_ids: " ^ show_ids_sets fixed_ids
     ^ "\n" ^ "\n- src_ctx: " ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: "
     ^ eval_ctx_to_string tgt_ctx));

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations)
  *)
  (* End the loans which lead to mismatches when joining *)
  let rec cf_reorganize_join_tgt : cm_fun =
   fun cf tgt_ctx ->
    (* Collect fixed values in the source and target contexts: end the loans in the
       source context which don't appear in the target context *)
    let filt_src_env, _, _ = ctx_split_fixed_new fixed_ids src_ctx in
    let filt_tgt_env, _, _ = ctx_split_fixed_new fixed_ids tgt_ctx in

    log#ldebug
      (lazy
        ("match_ctx_with_target:\n" ^ "\n- fixed_ids: "
       ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- filt_src_ctx: "
        ^ env_to_string src_ctx filt_src_env
        ^ "\n- filt_tgt_ctx: "
        ^ env_to_string tgt_ctx filt_tgt_env));

    (* Remove the abstractions *)
    let filter (ee : C.env_elem) : bool =
      match ee with Var _ -> true | Abs _ | Frame -> false
    in
    let filt_src_env = List.filter filter filt_src_env in
    let filt_tgt_env = List.filter filter filt_tgt_env in

    (* Match the values to check if there are loans to eliminate *)

    (* We need to pick a context for some functions like [match_typed_values]:
       the context is only used to lookup module data, so we can pick whichever
       we want.
       TODO: this is not very clean. Maybe we should just carry this data around.
    *)
    let ctx = tgt_ctx in

    let nabs = ref [] in

    let module S : MatchJoinState = struct
      (* The context is only used to lookup module data: we can pick whichever we want *)
      let ctx = ctx
      let loop_id = loop_id
      let nabs = nabs
    end in
    let module JM = MakeJoinMatcher (S) in
    let module M = Match (JM) in
    try
      let _ =
        List.iter
          (fun (var0, var1) ->
            match (var0, var1) with
            | C.Var (C.DummyBinder b0, v0), C.Var (C.DummyBinder b1, v1) ->
                assert (b0 = b1);
                let _ = M.match_typed_values ctx v0 v1 in
                ()
            | C.Var (C.VarBinder b0, v0), C.Var (C.VarBinder b1, v1) ->
                assert (b0 = b1);
                let _ = M.match_typed_values ctx v0 v1 in
                ()
            | _ -> raise (Failure "Unexpected"))
          (List.combine filt_src_env filt_tgt_env)
      in
      (* No exception was thrown: continue *)
      cf tgt_ctx
    with ValueMatchFailure e ->
      (* Exception: end the corresponding borrows, and continue *)
      let cc =
        match e with
        | LoanInRight bid -> InterpreterBorrows.end_borrow config bid
        | LoansInRight bids -> InterpreterBorrows.end_borrows config bids
        | AbsInRight _ | AbsInLeft _ | LoanInLeft _ | LoansInLeft _ ->
            raise (Failure "Unexpected")
      in
      comp cc cf_reorganize_join_tgt cf tgt_ctx
  in

  (* Introduce the "identity" abstractions for the loop reentry.

     Match the target context with the source context so as to compute how to
     map the borrows from the target context (i.e., the fixed point context)
     to the borrows in the source context.

     Substitute the *loans* in the abstractions introduced by the target context
     (the abstractions of the fixed point) to properly link those abstraction:
     we introduce *identity* abstractions (the loans are equal to the borrows):
     we substitute the loans and introduce fresh ids for the borrows, symbolic
     values, etc. About the *identity abstractions*, see the comments for
     [compute_fixed_point_id_correspondance].

     TODO: this whole thing is very technical and error-prone.
     We should rely on a more primitive and safer function
     [add_identity_abs] to add the identity abstractions one by one.
  *)
  let cf_introduce_loop_fp_abs : m_fun =
   fun tgt_ctx ->
    (* Match the source and target contexts *)
    let filt_tgt_env, _, _ = ctx_split_fixed_new fixed_ids tgt_ctx in
    let filt_src_env, new_absl, new_dummyl =
      ctx_split_fixed_new fixed_ids src_ctx
    in
    assert (new_dummyl = []);
    let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in
    let filt_src_ctx = { src_ctx with env = filt_src_env } in

    let src_to_tgt_maps =
      let check_equiv = false in
      let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
      let open InterpreterBorrowsCore in
      let lookup_shared_loan lid ctx : V.typed_value =
        match snd (lookup_loan ek_all lid ctx) with
        | Concrete (V.SharedLoan (_, v)) -> v
        | Abstract (V.ASharedLoan (_, v, _)) -> v
        | _ -> raise (Failure "Unreachable")
      in
      let lookup_in_src id = lookup_shared_loan id src_ctx in
      let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
      (* Match *)
      Option.get
        (match_ctxs check_equiv fixed_ids lookup_in_src lookup_in_tgt
           filt_src_ctx filt_tgt_ctx)
    in
    let tgt_to_src_borrow_map =
      V.BorrowId.Map.of_list
        (List.map
           (fun (x, y) -> (y, x))
           (V.BorrowId.InjSubst.bindings src_to_tgt_maps.borrow_id_map))
    in

    (* Debug *)
    log#ldebug
      (lazy
        ("match_ctx_with_target: cf_introduce_loop_fp_abs:" ^ "\n\n- tgt_ctx: "
       ^ eval_ctx_to_string tgt_ctx ^ "\n\n- src_ctx: "
       ^ eval_ctx_to_string src_ctx ^ "\n\n- filt_tgt_ctx: "
        ^ eval_ctx_to_string_no_filter filt_tgt_ctx
        ^ "\n\n- filt_src_ctx: "
        ^ eval_ctx_to_string_no_filter filt_src_ctx
        ^ "\n\n- new_absl:\n"
        ^ eval_ctx_to_string
            { src_ctx with C.env = List.map (fun abs -> C.Abs abs) new_absl }
        ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- fp_bl_maps:\n"
        ^ show_borrow_loan_corresp fp_bl_maps
        ^ "\n\n- src_to_tgt_maps: "
        ^ show_ids_maps src_to_tgt_maps));

    (* Update the borrows and symbolic ids in the source context.

       Going back to the [list_nth_mut_example], the original environment upon
       re-entering the loop is:

       {[
         abs@0 { ML l0 }
         ls -> MB l5 (s@6 : loops::List<T>)
         i -> s@7 : u32
         _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
         _@2 -> MB l2 (@Box (ML l4))                      // tail
         _@3 -> MB l1 (s@3 : T)                           // hd
         abs@1 { MB l4, ML l5 }
       ]}

       The fixed-point environment is:
       {[
         env_fp = {
           abs@0 { ML l0 }
           ls -> MB l1 (s3 : loops::List<T>)
           i -> s4 : u32
           abs@fp {
             MB l0 // this borrow appears in [env0]
             ML l1
           }
         }
       ]}

       Through matching, we detect that in [env_fp], [l1] is matched
       to [l5]. We introduce a fresh borrow [l6] for [l1], and remember
       in the map [src_fresh_borrows_map] that: [{ l1 -> l6}].

       We get:
       {[
         abs@0 { ML l0 }
         ls -> MB l6 (s@6 : loops::List<T>) // l6 is fresh and doesn't have a corresponding loan
         i -> s@7 : u32
         _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
         _@2 -> MB l2 (@Box (ML l4))                      // tail
         _@3 -> MB l1 (s@3 : T)                           // hd
         abs@1 { MB l4, ML l5 }
       ]}

       Later, we will introduce the identity abstraction:
       {[
         abs@2 { MB l5, ML l6 }
       ]}
    *)
    (* First, compute the set of borrows which appear in the fresh abstractions
       of the fixed-point: we want to introduce fresh ids only for those. *)
    let new_absl_ids, _ = compute_absl_ids new_absl in
    let src_fresh_borrows_map = ref V.BorrowId.Map.empty in
    let visit_tgt =
      object
        inherit [_] C.map_eval_ctx

        method! visit_borrow_id _ id =
          (* Map the borrow, if it needs to be mapped *)
          if
            (* We map the borrows for which we computed a mapping *)
            V.BorrowId.InjSubst.Set.mem id
              (V.BorrowId.InjSubst.elements src_to_tgt_maps.borrow_id_map)
            (* And which have corresponding loans in the fresh fixed-point abstractions *)
            && V.BorrowId.Set.mem
                 (V.BorrowId.Map.find id tgt_to_src_borrow_map)
                 new_absl_ids.loan_ids
          then (
            let src_id = V.BorrowId.Map.find id tgt_to_src_borrow_map in
            let nid = C.fresh_borrow_id () in
            src_fresh_borrows_map :=
              V.BorrowId.Map.add src_id nid !src_fresh_borrows_map;
            nid)
          else id
      end
    in
    let tgt_ctx = visit_tgt#visit_eval_ctx () tgt_ctx in

    log#ldebug
      (lazy
        ("match_ctx_with_target: cf_introduce_loop_fp_abs: \
          src_fresh_borrows_map:\n"
        ^ V.BorrowId.Map.show V.BorrowId.to_string !src_fresh_borrows_map
        ^ "\n"));

    (* Rem.: we don't update the symbolic values. It is not necessary
       because there shouldn't be any symbolic value containing borrows.

       Rem.: we will need to do something about the symbolic values in the
       abstractions and in the *variable bindings* once we allow symbolic
       values containing borrows to not be eagerly expanded.
    *)
    assert Config.greedy_expand_symbolics_with_borrows;

    (* Update the borrows and loans in the abstractions of the target context.

       Going back to the [list_nth_mut] example and by using [src_fresh_borrows_map],
       we instantiate the fixed-point abstractions that we will insert into the
       context.
       The abstraction is [abs { MB l0, ML l1 }].
       Because of [src_fresh_borrows_map], we substitute [l1] with [l6].
       Because of the match between the contexts, we substitute [l0] with [l5].
       We get:
       {[
         abs@2 { MB l5, ML l6 }
       ]}
    *)
    let region_id_map = ref T.RegionId.Map.empty in
    let get_rid rid =
      match T.RegionId.Map.find_opt rid !region_id_map with
      | Some rid -> rid
      | None ->
          let nid = C.fresh_region_id () in
          region_id_map := T.RegionId.Map.add rid nid !region_id_map;
          nid
    in
    let visit_src =
      object
        inherit [_] C.map_eval_ctx as super

        method! visit_borrow_id _ bid =
          log#ldebug
            (lazy
              ("match_ctx_with_target: cf_introduce_loop_fp_abs: \
                visit_borrow_id: " ^ V.BorrowId.to_string bid ^ "\n"));

          (* Lookup the id of the loan corresponding to this borrow *)
          let src_lid =
            V.BorrowId.InjSubst.find bid fp_bl_maps.borrow_to_loan_id_map
          in

          log#ldebug
            (lazy
              ("match_ctx_with_target: cf_introduce_loop_fp_abs: looked up \
                src_lid: "
              ^ V.BorrowId.to_string src_lid
              ^ "\n"));

          (* Lookup the tgt borrow id to which this borrow was mapped *)
          let tgt_bid =
            V.BorrowId.InjSubst.find src_lid src_to_tgt_maps.borrow_id_map
          in

          log#ldebug
            (lazy
              ("match_ctx_with_target: cf_introduce_loop_fp_abs: looked up \
                tgt_bid: "
              ^ V.BorrowId.to_string tgt_bid
              ^ "\n"));

          tgt_bid

        method! visit_loan_id _ id =
          log#ldebug
            (lazy
              ("match_ctx_with_target: cf_introduce_loop_fp_abs: \
                visit_loan_id: " ^ V.BorrowId.to_string id ^ "\n"));
          (* Map the borrow - rem.: we mapped the borrows *in the values*,
             meaning we know how to map the *corresponding loans in the
             abstractions* *)
          match V.BorrowId.Map.find_opt id !src_fresh_borrows_map with
          | None ->
              (* No mapping: this means that the borrow was mapped when
                 we matched values (it doesn't come from a fresh abstraction)
                 and because of this, it should actually be mapped to itself *)
              assert (
                V.BorrowId.InjSubst.find id src_to_tgt_maps.borrow_id_map = id);
              id
          | Some id -> id

        method! visit_symbolic_value_id _ _ = C.fresh_symbolic_value_id ()
        method! visit_abstraction_id _ _ = C.fresh_abstraction_id ()
        method! visit_region_id _ id = get_rid id

        (** We also need to change the abstraction kind *)
        method! visit_abs env abs =
          match abs.kind with
          | V.Loop (loop_id', rg_id, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              let can_end = false in
              let kind = V.Loop (loop_id, rg_id, V.LoopCall) in
              let abs = { abs with kind; can_end } in
              super#visit_abs env abs
          | _ -> super#visit_abs env abs
      end
    in
    let new_absl = List.map (visit_src#visit_abs ()) new_absl in
    let new_absl = List.map (fun abs -> C.Abs abs) new_absl in

    (* Add the abstractions from the target context to the source context *)
    let nenv = List.append new_absl tgt_ctx.env in
    let tgt_ctx = { tgt_ctx with env = nenv } in

    log#ldebug
      (lazy
        ("match_ctx_with_target:cf_introduce_loop_fp_abs:\n- result ctx:\n"
       ^ eval_ctx_to_string tgt_ctx));

    (* Sanity check *)
    if !Config.check_invariants then
      Invariants.check_borrowed_values_invariant tgt_ctx;

    (* End all the borrows which appear in the *new* abstractions *)
    let new_borrows =
      V.BorrowId.Set.of_list
        (List.map snd (V.BorrowId.Map.bindings !src_fresh_borrows_map))
    in
    let cc = InterpreterBorrows.end_borrows config new_borrows in

    (* Compute the loop input values *)
    let input_values =
      V.SymbolicValueId.Map.of_list
        (List.map
           (fun sid ->
             ( sid,
               V.SymbolicValueId.Map.find sid src_to_tgt_maps.sid_to_value_map
             ))
           fp_input_svalues)
    in

    (* Continue *)
    cc
      (cf
         (if is_loop_entry then EndEnterLoop (loop_id, input_values)
         else EndContinue (loop_id, input_values)))
      tgt_ctx
  in

  (* Compose and continue *)
  cf_reorganize_join_tgt cf_introduce_loop_fp_abs tgt_ctx

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  (* We need a loop id for the [LoopReturn]. In practice it won't be used
     (it is useful only for the symbolic execution *)
  let loop_id = C.fresh_loop_id () in
  (* Continuation for after we evaluate the loop body: depending the result
     of doing one loop iteration:
     - redoes a loop iteration
     - exits the loop
     - other...

     We need a specific function because of the {!Continue} case: in case we
     continue, we might have to reevaluate the current loop body with the
     new context (and repeat this an indefinite number of times).
  *)
  let rec reeval_loop_body (res : statement_eval_res) : m_fun =
    match res with
    | Return -> cf (LoopReturn loop_id)
    | Panic -> cf Panic
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res
    | Continue 0 ->
        (* Re-evaluate the loop body *)
        eval_loop_body reeval_loop_body
    | Continue i ->
        (* Continue to an outer loop *)
        cf (Continue (i - 1))
    | Unit ->
        (* We can't get there.
         * Note that if we decide not to fail here but rather do
         * the same thing as for [Continue 0], we could make the
         * code slightly simpler: calling {!reeval_loop_body} with
         * {!Unit} would account for the first iteration of the loop.
         * We prefer to write it this way for consistency and sanity,
         * though. *)
        raise (Failure "Unreachable")
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We can't get there: this is only used in symbolic mode *)
        raise (Failure "Unreachable")
  in

  (* Apply *)
  eval_loop_body reeval_loop_body ctx

(** Compute the set of "quantified" symbolic value ids in a fixed-point context.

    We compute:
    - the set of symbolic value ids that are freshly introduced
    - the list of input symbolic values
 *)
let compute_fp_ctx_symbolic_values (ctx : C.eval_ctx) (fp_ctx : C.eval_ctx) :
    V.SymbolicValueId.Set.t * V.symbolic_value list =
  let old_ids, _ = compute_context_ids ctx in
  let fp_ids, fp_ids_maps = compute_context_ids fp_ctx in
  let fresh_sids = V.SymbolicValueId.Set.diff fp_ids.sids old_ids.sids in

  (* Compute the set of symbolic values which appear in shared values inside
     *fixed* abstractions: because we introduce fresh abstractions and reborrows
     with {!prepare_ashared_loans}, those values are never accessed directly
     inside the loop iterations: we can ignore them (and should, because
     otherwise it leads to a very ugly translation with duplicated, unused
     values) *)
  let shared_sids_in_fixed_abs =
    let fixed_absl =
      List.filter
        (fun (ee : C.env_elem) ->
          match ee with
          | C.Var _ | C.Frame -> false
          | Abs abs -> V.AbstractionId.Set.mem abs.abs_id old_ids.aids)
        ctx.env
    in

    (* Rem.: as we greedily expand the symbolic values containing borrows, and
       in particular the (mutable/shared) borrows, we could simply list the
       symbolic values appearing in the abstractions: those are necessarily
       shared values. We prefer to be more general, in prevision of later
       changes.
    *)
    let sids = ref V.SymbolicValueId.Set.empty in
    let visitor =
      object (self)
        inherit [_] C.iter_env

        method! visit_ASharedLoan inside_shared _ sv child_av =
          self#visit_typed_value true sv;
          self#visit_typed_avalue inside_shared child_av

        method! visit_symbolic_value_id inside_shared sid =
          if inside_shared then sids := V.SymbolicValueId.Set.add sid !sids
      end
    in
    visitor#visit_env false fixed_absl;
    !sids
  in

  (* Remove the shared symbolic values present in the fixed abstractions -
     see comments for [shared_sids_in_fixed_abs]. *)
  let sids_to_values = fp_ids_maps.sids_to_values in

  log#ldebug
    (lazy
      ("compute_fp_ctx_symbolic_values:" ^ "\n- shared_sids_in_fixed_abs:"
      ^ V.SymbolicValueId.Set.show shared_sids_in_fixed_abs
      ^ "\n- all_sids_to_values: "
      ^ V.SymbolicValueId.Map.show (symbolic_value_to_string ctx) sids_to_values
      ^ "\n"));

  let sids_to_values =
    V.SymbolicValueId.Map.filter
      (fun sid _ ->
        not (V.SymbolicValueId.Set.mem sid shared_sids_in_fixed_abs))
      sids_to_values
  in

  (* List the input symbolic values in proper order.

     We explore the environment, and order the symbolic values in the order
     in which they are found - this way, the symbolic values found in a
     variable [x] which appears before [y] are listed first, for instance.
  *)
  let input_svalues =
    let found_sids = ref V.SymbolicValueId.Set.empty in
    let ordered_sids = ref [] in

    let visitor =
      object (self)
        inherit [_] C.iter_env

        (** We lookup the shared values *)
        method! visit_SharedBorrow env bid =
          let open InterpreterBorrowsCore in
          let v =
            match snd (lookup_loan ek_all bid fp_ctx) with
            | Concrete (V.SharedLoan (_, v)) -> v
            | Abstract (V.ASharedLoan (_, v, _)) -> v
            | _ -> raise (Failure "Unreachable")
          in
          self#visit_typed_value env v

        method! visit_symbolic_value_id _ id =
          if not (V.SymbolicValueId.Set.mem id !found_sids) then (
            found_sids := V.SymbolicValueId.Set.add id !found_sids;
            ordered_sids := id :: !ordered_sids)
      end
    in

    List.iter (visitor#visit_env_elem ()) (List.rev fp_ctx.env);

    List.filter_map
      (fun id -> V.SymbolicValueId.Map.find_opt id sids_to_values)
      (List.rev !ordered_sids)
  in

  log#ldebug
    (lazy
      ("compute_fp_ctx_symbolic_values:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string_no_filter fp_ctx
      ^ "\n- fresh_sids: "
      ^ V.SymbolicValueId.Set.show fresh_sids
      ^ "\n- input_svalues: "
      ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
      ^ "\n\n"));

  (fresh_sids, input_svalues)

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : C.config) (eval_loop_body : st_cm_fun) :
    st_cm_fun =
 fun cf ctx ->
  (* Debug *)
  log#ldebug
    (lazy ("eval_loop_symbolic:\nContext:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Generate a fresh loop id *)
  let loop_id = C.fresh_loop_id () in

  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids, rg_to_abs =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nInitial context:\n" ^ eval_ctx_to_string ctx
     ^ "\n\nFixed point:\n" ^ eval_ctx_to_string fp_ctx));

  (* Compute the loop input parameters *)
  let fresh_sids, input_svalues = compute_fp_ctx_symbolic_values ctx fp_ctx in
  let fp_input_svalues = List.map (fun sv -> sv.V.sv_id) input_svalues in

  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation
  *)
  let fp_bl_corresp =
    compute_fixed_point_id_correspondance fixed_ids ctx fp_ctx
  in
  let end_expr =
    match_ctx_with_target config loop_id true fp_bl_corresp fp_input_svalues
      fixed_ids fp_ctx cf ctx
  in

  (* Synthesize the loop body by evaluating it, with the continuation for
     after the loop starting at the *fixed point*, but with a special
     treatment for the [Break] and [Continue] cases *)
  let cf_loop : st_m_fun =
   fun res ctx ->
    match res with
    | Return ->
        (* We replace the [Return] with a [LoopReturn] *)
        cf (LoopReturn loop_id) ctx
    | Panic -> cf res ctx
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res ctx
    | Continue i ->
        (* We don't support nested loops for now *)
        assert (i = 0);
        let cc =
          match_ctx_with_target config loop_id false fp_bl_corresp
            fp_input_svalues fixed_ids fp_ctx
        in
        cc cf ctx
    | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        raise (Failure "Unreachable")
  in
  let loop_expr = eval_loop_body cf_loop fp_ctx in

  log#ldebug
    (lazy
      ("eval_loop_symbolic: result:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string_no_filter fp_ctx
      ^ "\n- fixed_sids: "
      ^ V.SymbolicValueId.Set.show fixed_ids.sids
      ^ "\n- fresh_sids: "
      ^ V.SymbolicValueId.Set.show fresh_sids
      ^ "\n- input_svalues: "
      ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
      ^ "\n\n"));

  (* For every abstraction introduced by the fixed-point, compute the
     types of the given back values.

     We need to explore the abstractions, looking for the mutable borrows.
     Moreover, we list the borrows in the same order as the loans (this
     is important in {!SymbolicToPure}, where we expect the given back
     values to have a specific order.
  *)
  let compute_abs_given_back_tys (abs : V.abs) : T.RegionId.Set.t * T.rty list =
    let is_borrow (av : V.typed_avalue) : bool =
      match av.V.value with
      | ABorrow _ -> true
      | ALoan _ -> false
      | _ -> raise (Failure "Unreachable")
    in
    let borrows, loans = List.partition is_borrow abs.avalues in

    let borrows =
      List.filter_map
        (fun av ->
          match av.V.value with
          | V.ABorrow (V.AMutBorrow (bid, child_av)) ->
              assert (is_aignored child_av.V.value);
              Some (bid, child_av.V.ty)
          | V.ABorrow (V.ASharedBorrow _) -> None
          | _ -> raise (Failure "Unreachable"))
        borrows
    in
    let borrows = ref (V.BorrowId.Map.of_list borrows) in

    let loan_ids =
      List.filter_map
        (fun av ->
          match av.V.value with
          | V.ALoan (V.AMutLoan (bid, child_av)) ->
              assert (is_aignored child_av.V.value);
              Some bid
          | V.ALoan (V.ASharedLoan _) -> None
          | _ -> raise (Failure "Unreachable"))
        loans
    in

    (* List the given back types, in the order given by the loans *)
    let given_back_tys =
      List.map
        (fun lid ->
          let bid =
            V.BorrowId.InjSubst.find lid fp_bl_corresp.loan_to_borrow_id_map
          in
          let ty = V.BorrowId.Map.find bid !borrows in
          borrows := V.BorrowId.Map.remove bid !borrows;
          ty)
        loan_ids
    in
    assert (V.BorrowId.Map.is_empty !borrows);

    (abs.regions, given_back_tys)
  in
  let rg_to_given_back =
    T.RegionGroupId.Map.map compute_abs_given_back_tys rg_to_abs
  in

  (* Put together *)
  S.synthesize_loop loop_id input_svalues fresh_sids rg_to_given_back end_expr
    loop_expr

(** Evaluate a loop *)
let eval_loop (config : C.config) (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.C.mode with
  | ConcreteMode -> eval_loop_concrete eval_loop_body cf ctx
  | SymbolicMode ->
      (* We want to make sure the loop will *not* manipulate shared avalues
         containing themselves shared loans (i.e., nested shared loans in
         the abstractions), because it complexifies the matches between values
         (when joining environments, or checking that two environments are
         equivalent).

         We thus call {!prepare_ashared_loans} once *before* diving into
         the loop, to make sure the shared values are deconstructed.

         Note that we will call this function again inside {!eval_loop_symbolic},
         to introduce fresh, non-fixed abstractions containing the shared values
         which can be manipulated (and thus borrowed, expanded, etc.) so
         that the fixed abstractions are never modified.

         This is important to understand: we call this function once here to
         introduce *fixed* abstractions, and again later to introduce
         *non-fixed* abstractions.
      *)
      let cc = prepare_ashared_loans None in
      comp cc (eval_loop_symbolic config eval_loop_body) cf ctx
