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
exception Distinct

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

  List.iter
    (fun (ee : C.env_elem) ->
      match ee with
      | Var _ | Frame -> ()
      | Abs abs ->
          let abs_id = abs.abs_id in
          if explore abs then (
            abs_to_borrows :=
              V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty
                !abs_to_borrows;
            abs_to_loans :=
              V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty !abs_to_loans;
            abs_ids := abs.abs_id :: !abs_ids;
            List.iter (explore_abs#visit_typed_avalue abs.abs_id) abs.avalues)
          else ())
    env;

  {
    abs_ids = List.rev !abs_ids;
    abs_to_borrows = !abs_to_borrows;
    abs_to_loans = !abs_to_loans;
    abs_to_borrows_loans = !abs_to_borrows_loans;
    borrow_to_abs = !borrow_to_abs;
    loan_to_abs = !loan_to_abs;
    borrow_loan_to_abs = !borrow_loan_to_abs;
  }

(** Destructure all the new abstractions *)
let destructure_new_abs (loop_id : V.LoopId.id)
    (old_abs_ids : V.AbstractionId.Set.t) (ctx : C.eval_ctx) : C.eval_ctx =
  let abs_kind = V.Loop (loop_id, None, V.LoopSynthInput) in
  let can_end = false in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_abs_ids)
  in
  let env =
    List.map
      (fun ee ->
        match ee with
        | C.Var _ | C.Frame -> ee
        | C.Abs abs ->
            if is_fresh_abs_id abs.abs_id then
              let abs =
                destructure_abs abs_kind can_end destructure_shared_values ctx
                  abs
              in
              C.Abs abs
            else ee)
      ctx.env
  in
  { ctx with env }

(** Collapse an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point.

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not)
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
    considered as new. We collapse them.
    
    We first convert the dummy values to abstractions. It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@1 { MB l0, ML l1, ML l2 }
      abs@2 { MB l2, ML l4 }
      abs@3 { MB l1 }
    ]}

    We then merge those abstractions together. It gives:
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
  let can_end = false in
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
  log#ldebug
    (lazy
      ("collapse_ctx: after converting values to abstractions:\n"
     ^ show_ids_sets old_ids ^ "\n\n- ctx:\n"
      ^ eval_ctx_to_string { ctx0 with env }
      ^ "\n\n"));

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

  let ctx = ref { ctx0 with C.env } in

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
                  else
                    (* We actually need to merge the abstractions *)

                    (* Update the environment *)
                    let nctx, abs_id =
                      merge_abstractions abs_kind can_end merge_funs !ctx
                        abs_id0 abs_id1
                    in
                    ctx := nctx;

                    (* Update the union find *)
                    let abs_ref_merged = UF.union abs_ref0 abs_ref1 in
                    UF.set abs_ref_merged abs_id)
                abs_ids1)
        bids)
    abs_ids;

  (* Return the new context *)
  !ctx

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

  (** The meta-value is the result of a match *)
  val match_shared_borrows : T.ety -> V.borrow_id -> V.borrow_id -> V.borrow_id

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
              let bid = M.match_shared_borrows ty bid0 bid1 in
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
        match (bc0, bc1) with
        | ASharedBorrow bid0, ASharedBorrow bid1 ->
            M.match_ashared_borrows v0.V.ty bid0 v1.V.ty bid1 ty
        | AMutBorrow (bid0, av0), AMutBorrow (bid1, av1) ->
            let av = match_arec av0 av1 in
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
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        match (lc0, lc1) with
        | ASharedLoan (ids0, sv0, av0), ASharedLoan (ids1, sv1, av1) ->
            let sv = match_rec sv0 sv1 in
            let av = match_arec av0 av1 in
            assert (not (value_has_borrows ctx sv.V.value));
            M.match_ashared_loans v0.V.ty ids0 sv0 av0 v1.V.ty ids1 sv1 av1 ty
              sv av
        | AMutLoan (id0, av0), AMutLoan (id1, av1) ->
            let av = match_arec av0 av1 in
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

  let match_shared_borrows (ty : T.ety) (bid0 : V.borrow_id)
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
          can_end = false;
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
    if bid0 = bid1 then (bid0, bv)
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
          can_end = false;
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
        let can_end = false in
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
       anyway (see the comments for {!merge_abstractions}).
    *)
    let ty = ty0 in
    let child = child0 in
    let value = V.ABorrow (V.AMutBorrow (id, child)) in
    { V.value; ty }
  in

  let merge_ashared_borrows id ty0 ty1 =
    (* Sanity checks *)
    assert (not (ty_has_borrows ctx.type_context.type_infos ty0));
    assert (not (ty_has_borrows ctx.type_context.type_infos ty1));

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

let merge_abstractions (loop_id : V.LoopId.id) (abs_kind : V.abs_kind)
    (can_end : bool) (ctx : C.eval_ctx) (aid0 : V.AbstractionId.id)
    (aid1 : V.AbstractionId.id) : C.eval_ctx * V.AbstractionId.id =
  let merge_funs = mk_collapse_ctx_merge_duplicate_funs loop_id ctx in
  merge_abstractions abs_kind can_end (Some merge_funs) ctx aid0 aid1

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
    which are not in the prefix, which can also lead to borrow duplications. For
    this reason, the environment needs to be collapsed afterwards to get rid of
    those duplicated loans/borrows.

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
end

(** An auxiliary matcher that we use for two purposes:
    - to check if two contexts are equivalent modulo id substitution (i.e.,
      alpha equivalent) (see {!ctxs_are_equivalent}).
    - to compute a mapping between the borrows and the symbolic values in a
      target context to the values and borrows in a source context (see
      {!match_ctx_with_target}).
 *)
module MakeCheckEquivMatcher (S : MatchCheckEquivState) = struct
  module MkGetSetM (Id : Identifiers.Id) = struct
    module Inj = Id.InjSubst

    let get (m : Inj.t ref) (k : Id.id) : Id.id =
      match Inj.find_opt k !m with None -> k | Some k -> k

    let add (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) =
      if Inj.mem k0 !m then raise Distinct
      else if Inj.Set.mem k1 (Inj.elements !m) then raise Distinct
      else (
        m := Inj.add k0 k1 !m;
        k1)

    let match_e (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) : Id.id =
      let k0 = get m k0 in
      if k0 = k1 then k1 else add m k0 k1

    let match_el (m : Inj.t ref) (kl0 : Id.id list) (kl1 : Id.id list) :
        Id.id list =
      List.map (fun (k0, k1) -> match_e m k0 k1) (List.combine kl0 kl1)

    (** Figuring out mappings between sets of ids is hard in all generality...
        We use the fact that the fresh ids should have been generated
        the same way (i.e., in the same order) and match the ids two by
        two in increasing order.
     *)
    let match_es (m : Inj.t ref) (ks0 : Id.Set.t) (ks1 : Id.Set.t) : Id.Set.t =
      Id.Set.of_list (match_el m (Id.Set.elements ks0) (Id.Set.elements ks1))
  end

  module GetSetRid = MkGetSetM (T.RegionId)

  let match_rid = GetSetRid.match_e S.rid_map

  (*  let match_ridl = GetSetRid.match_el S.rid_map *)
  let match_rids = GetSetRid.match_es S.rid_map

  module GetSetBid = MkGetSetM (V.BorrowId)

  let get_blid = GetSetBid.get S.blid_map
  let match_blid = GetSetBid.match_e S.blid_map
  let match_blidl = GetSetBid.match_el S.blid_map
  let match_blids = GetSetBid.match_es S.blid_map

  let get_borrow_id =
    if S.check_equiv then get_blid else GetSetBid.get S.borrow_id_map

  let match_borrow_id =
    if S.check_equiv then match_blid else GetSetBid.match_e S.borrow_id_map

  let match_borrow_idl =
    if S.check_equiv then match_blidl else GetSetBid.match_el S.borrow_id_map

  let match_borrow_ids =
    if S.check_equiv then match_blids else GetSetBid.match_es S.borrow_id_map

  let get_loan_id =
    if S.check_equiv then get_blid else GetSetBid.get S.loan_id_map

  let match_loan_id =
    if S.check_equiv then match_blid else GetSetBid.match_e S.loan_id_map

  let match_loan_idl =
    if S.check_equiv then match_blidl else GetSetBid.match_el S.loan_id_map

  let match_loan_ids =
    if S.check_equiv then match_blids else GetSetBid.match_es S.loan_id_map

  module GetSetSid = MkGetSetM (V.SymbolicValueId)

  (* If we check for equivalence, we map sids to sids, otherwise we map sids
     to values. *)
  let match_sid =
    if S.check_equiv then GetSetSid.match_e S.sid_map
    else fun _ -> raise (Failure "Unexpected")

  let match_value_with_sid (v : V.typed_value) (id : V.SymbolicValueId.id) :
      unit =
    (* Even when we don't use it, the sids map contains the fixed ids: check
       that we are not trying to map a fixed id. *)
    assert (not (V.SymbolicValueId.InjSubst.mem id !S.sid_map));

    (* Check that we are not overriding a binding *)
    assert (not (V.SymbolicValueId.Map.mem id !S.sid_to_value_map));

    (* Add the mapping *)
    S.sid_to_value_map := V.SymbolicValueId.Map.add id v !S.sid_to_value_map

  (*  let match_sidl = GetSetSid.match_el S.sid_map *)
  (*  let match_sids = GetSetSid.match_es S.sid_map *)

  module GetSetAid = MkGetSetM (V.AbstractionId)

  let match_aid = GetSetAid.match_e S.aid_map
  let match_aidl = GetSetAid.match_el S.aid_map
  let match_aids = GetSetAid.match_es S.aid_map

  (** *)
  let match_etys ty0 ty1 = if ty0 <> ty1 then raise Distinct else ty0

  let match_rtys ty0 ty1 =
    let match_distinct_types _ _ = raise Distinct in
    let match_regions r0 r1 =
      match (r0, r1) with
      | T.Static, T.Static -> r1
      | Var rid0, Var rid1 ->
          let rid = match_rid rid0 rid1 in
          Var rid
      | _ -> raise Distinct
    in
    match_types match_distinct_types match_regions ty0 ty1

  let match_distinct_primitive_values (ty : T.ety) (_ : V.primitive_value)
      (_ : V.primitive_value) : V.typed_value =
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_distinct_adts (_ty : T.ety) (_adt0 : V.adt_value)
      (_adt1 : V.adt_value) : V.typed_value =
    raise Distinct

  let match_shared_borrows (_ty : T.ety) (bid0 : V.borrow_id)
      (bid1 : V.borrow_id) : V.borrow_id =
    let bid = match_borrow_id bid0 bid1 in
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
    let id1 = sv1.sv_id in
    if S.check_equiv then
      let id0 = sv0.sv_id in
      let sv_id = match_sid id0 id1 in
      let sv_ty = match_rtys sv0.V.sv_ty sv1.V.sv_ty in
      let sv_kind =
        if sv0.V.sv_kind = sv1.V.sv_kind then sv0.V.sv_kind else raise Distinct
      in
      { V.sv_id; sv_ty; sv_kind }
    else (
      (* Update the binding for the target symbolic value *)
      match_value_with_sid (mk_typed_value_from_symbolic_value sv0) id1;
      (* Return - the returned value is not used, so we can return whatever *)
      sv1)

  let match_symbolic_with_other (left : bool) (sv : V.symbolic_value)
      (v : V.typed_value) : V.typed_value =
    if S.check_equiv then raise Distinct
    else (
      assert (not left);
      (* Update the binding for the target symbolic value *)
      match_value_with_sid v sv.sv_id;
      (* Return - the returned value is not used, so we can return whatever *)
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
    else raise Distinct

  let match_distinct_aadts _ _ _ _ _ = raise Distinct

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
    raise Distinct
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

    We return an optional ids map: [Some] if the match succeeded, [None] otherwise.
 *)
let match_ctxs (check_equiv : bool) (fixed_ids : ids_sets) (ctx0 : C.eval_ctx)
    (ctx1 : C.eval_ctx) : ids_maps option =
  log#ldebug
    (lazy
      ("ctxs_are_equivalent:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
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
    log#ldebug
      (lazy
        ("match_ctxs: match_abstractions: " ^ "\n\n- abs0: " ^ V.show_abs abs0
       ^ "\n\n- abs0: " ^ V.show_abs abs1));
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
    if kind0 <> kind1 || can_end0 <> can_end1 then raise Distinct;
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
    ()
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let rec match_envs (env0 : C.env) (env1 : C.env) : unit =
    log#ldebug
      (lazy
        ("ctxs_are_equivalent: match_envs:\n\n- fixed_ids:\n"
       ^ show_ids_sets fixed_ids ^ "\n\n- rid_map: "
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
        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and their values equal (and the borrows/loans/symbolic
           values they reference must be fixed) *)
        if C.DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Fixed values: the values must be equal *)
          assert (b0 = b1);
          assert (v0 = v1);
          (* The ids present in the left value must be fixed *)
          let ids = compute_typed_value_ids v0 in
          assert ((not S.check_equiv) || ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else
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
        log#ldebug (lazy "ctxs_are_equivalent: match_envs: matching abs");
        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          log#ldebug
            (lazy "ctxs_are_equivalent: match_envs: matching abs: fixed abs");
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
          (* Their ids must be fixed *)
          let ids = compute_abs_ids abs0 in
          assert ((not S.check_equiv) || ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else (
          log#ldebug
            (lazy
              "ctxs_are_equivalent: match_envs: matching abs: not fixed abs");
          (* Match the values *)
          match_abstractions abs0 abs1;
          (* Continue *)
          match_envs env0' env1')
    | [], [] ->
        (* Done *)
        ()
    | _ ->
        (* The elements don't match *)
        raise Distinct
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
  with Distinct -> None

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
  Option.is_some (match_ctxs check_equivalent fixed_ids ctx0 ctx1)

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

(** Compute a fixed-point for the context at the entry of the loop.
    We also return the sets of fixed ids.
 *)
let compute_loop_entry_fixed_point (config : C.config) (loop_id : V.LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) : C.eval_ctx * ids_sets =
  (* The continuation for when we exit the loop - we register the
     environments upon loop *reentry*, and synthesize nothing by
     returning [None]
  *)
  let ctx_upon_entry = ref None in
  let ctxs = ref [] in
  let register_ctx ctx = ctxs := ctx :: !ctxs in
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
    | LoopReturn | EndEnterLoop _ | EndContinue _ ->
        (* We don't support nested loops for now *)
        raise (Failure "Nested loops are not supported for now")
  in

  (* The fixed ids. They are the ids of the original ctx, after we ended
     the borrows/loans which end during the first loop iteration (we do
     one loop iteration, then set it to [Some].
  *)
  let fixed_ids = ref None in

  (* Join the contexts at the loop entry *)
  let join_ctxs (ctx0 : C.eval_ctx) : C.eval_ctx =
    (* If this is the first iteration, end the borrows/loans/abs which
       appear in ctx0 and not in the other contexts, then compute the
       set of fixed ids. This means those borrows/loans have to end
       in the loop, and we rather end them *before* the loop. *)
    let ctx0 =
      match !fixed_ids with
      | Some _ -> ctx0
      | None ->
          let old_ids = compute_context_ids ctx0 in
          let new_ids = compute_contexts_ids !ctxs in
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
          (* End the borrows/abs in [ctx0] *)
          let ctx0 = end_borrows_abs blids aids ctx0 in
          (* We can also do the same in the contexts [ctxs]: if there are
             several contexts, maybe one of them ended some borrows and some
             others didn't. As we need to end those borrows anyway (the join
             will detect them and ask to end them) we do it preemptively.
          *)
          ctxs := List.map (end_borrows_abs blids aids) !ctxs;
          fixed_ids := Some (compute_context_ids ctx0);
          ctx0
    in

    let fixed_ids = Option.get !fixed_ids in
    let (ctx0', _), ctx1 =
      loop_join_origin_with_continue_ctxs config loop_id fixed_ids ctx0 !ctxs
    in
    ctxs := [];
    if !ctx_upon_entry = None then ctx_upon_entry := Some ctx0';
    ctx1
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values.
  *)
  let compute_fixed_ids (ctx1 : C.eval_ctx) (ctx2 : C.eval_ctx) : ids_sets =
    (* Compute the set of fixed ids - for the symbolic ids, we compute the
       intersection of ids between the original environment and [ctx1]
       and [ctx2] *)
    let fixed_ids = compute_context_ids (Option.get !ctx_upon_entry) in
    let { aids; blids; borrow_ids; loan_ids; dids; rids; sids } = fixed_ids in
    let fixed_ids1 = compute_context_ids ctx1 in
    let fixed_ids2 = compute_context_ids ctx2 in
    let sids =
      V.SymbolicValueId.Set.inter sids
        (V.SymbolicValueId.Set.inter fixed_ids1.sids fixed_ids2.sids)
    in
    let fixed_ids = { aids; blids; borrow_ids; loan_ids; dids; rids; sids } in
    fixed_ids
  in
  let equiv_ctxs (ctx1 : C.eval_ctx) (ctx2 : C.eval_ctx) : bool =
    let fixed_ids = compute_fixed_ids ctx1 ctx2 in
    ctxs_are_equivalent fixed_ids ctx1 ctx2
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
  let fp = compute_fixed_point ctx0 max_num_iter max_num_iter in

  (* Make sure we have exactly one loop abstraction per function region (merge
     abstractions accordingly) *)
  let fp =
    (* List the loop abstractions in the fixed-point, and set all the abstractions
       as endable *)
    let fp_aids, add_aid, _mem_aid = V.AbstractionId.Set.mk_stateful_set () in

    let list_loop_abstractions =
      object
        inherit [_] C.map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              add_aid abs.abs_id;
              { abs with can_end = true }
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
      | Unit | LoopReturn | EndEnterLoop _ | EndContinue _ ->
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
                let abs = C.ctx_lookup_abs ctx abs_id in
                assert (abs.kind = V.SynthInput rg_id);
                (* End this abstraction *)
                let ctx =
                  InterpreterBorrows.end_abstraction_no_synth config abs_id ctx
                in
                (* Explore the context, and check which abstractions are not there anymore *)
                let ids = compute_context_ids ctx in
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
    assert (!aids_union = !fp_aids);

    (* Merge the abstractions which need to be merged *)
    let fp = ref fp in
    let _ =
      T.RegionGroupId.Map.iter
        (fun rg_id ids ->
          let ids = V.AbstractionId.Set.elements ids in
          (* Retrieve the first id of the group *)
          match ids with
          | [] ->
              (* This would be rather unexpected... let's fail for now to see
                 in which situations this happens *)
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
                    let fp', id0' =
                      merge_abstractions loop_id abs_kind false !fp !id0 id
                    in
                    fp := fp';
                    id0 := id0';
                    ()
                  with ValueMatchFailure _ -> raise (Failure "Unexpected"))
                ids)
        !fp_ended_aids
    in

    (* Reset the loop abstracions as not endable *)
    let list_loop_abstractions (remove_rg_id : bool) =
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
              { abs with can_end = false; kind }
          | _ -> abs
      end
    in
    let update_kinds_can_end (remove_rg_id : bool) ctx =
      (list_loop_abstractions remove_rg_id)#visit_eval_ctx () ctx
    in
    let fp = update_kinds_can_end false !fp in

    (* Check that we still have a fixed point - we simply call [compute_fixed_point]
       while allowing exactly one iteration to see if it fails *)
    let _ = compute_fixed_point (update_kinds_can_end true fp) 1 1 in

    (* Return *)
    fp
  in
  let fixed_ids = compute_fixed_ids (Option.get !ctx_upon_entry) fp in

  (* Return *)
  (fp, fixed_ids)

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
  let check_equiv = false in
  let maps =
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    Option.get (match_ctxs check_equiv fixed_ids filt_tgt_ctx filt_src_ctx)
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
     to the same set of source loans and borrows *)
  List.iter
    (fun abs ->
      let ids = compute_abs_ids abs in
      (* Map the *loan* ids (we just match the corresponding *loans* ) *)
      let loan_ids =
        V.BorrowId.Set.map
          (fun x -> V.BorrowId.InjSubst.find x maps.borrow_id_map)
          ids.loan_ids
      in
      (* Check that the loan and borrows are related *)
      assert (ids.borrow_ids = loan_ids))
    new_absl;

  (* For every target abstraction (going back to the [list_nth_mut] example,
     we have to visit [abs@fp { ML l0, MB l1 }]):
     - go through the tgt borrows ([l1])
     - for every tgt borrow, find the corresponding src borrow ([l0], because
       we have: [borrows_map: { l1 -> l0 }])
     - from there, find the corresponding tgt loan ([l0])
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

   We do the following.

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

   **Parameters**:
   [is_loop_entry]: [true] if first entry into the loop, [false] if re-entry
   (i.e., continue).
 *)
let match_ctx_with_target (config : C.config) (loop_id : V.LoopId.id)
    (is_loop_entry : bool) (fp_bl_maps : borrow_loan_corresp)
    (fixed_ids : ids_sets) (tgt_ctx : C.eval_ctx) : st_cm_fun =
 fun cf src_ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("match_ctx_with_target:\n" ^ "\n- fixed_ids: " ^ show_ids_sets fixed_ids
     ^ "\n\n- src_ctx: " ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: "
     ^ eval_ctx_to_string tgt_ctx));

  (* We first reorganize [src_ctx] so that we can match it with [tgt_ctx] *)
  let rec cf_reorganize_src : cm_fun =
   fun cf src_ctx ->
    (* Collect fixed values in the source and target contexts: end the loans in the
       source context which don't appear in the target context *)
    let filt_src_env, _, _ = ctx_split_fixed_new fixed_ids src_ctx in
    let filt_tgt_env, _, _ = ctx_split_fixed_new fixed_ids tgt_ctx in

    log#ldebug
      (lazy
        ("match_ctx_with_target:\n" ^ "\n- fixed_ids: "
       ^ show_ids_sets fixed_ids ^ "\n\n- filt_src_ctx: "
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
    let ctx = src_ctx in

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
      cf src_ctx
    with ValueMatchFailure e ->
      (* Exception: end the corresponding borrows, and continue *)
      let cc =
        match e with
        | LoanInLeft bid -> InterpreterBorrows.end_borrow config bid
        | LoansInLeft bids -> InterpreterBorrows.end_borrows config bids
        | AbsInLeft _ | AbsInRight _ | LoanInRight _ | LoansInRight _ ->
            raise (Failure "Unexpected")
      in
      comp cc cf_reorganize_src cf src_ctx
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
  *)
  let cf_introduce_loop_fp_abs : m_fun =
   fun src_ctx ->
    (* Match the src and target contexts *)
    let filt_src_env, _, _ = ctx_split_fixed_new fixed_ids src_ctx in
    let filt_tgt_env, new_absl, new_dummyl =
      ctx_split_fixed_new fixed_ids tgt_ctx
    in
    assert (new_dummyl = []);
    let filt_src_ctx = { src_ctx with env = filt_src_env } in
    let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in

    let check_equiv = false in
    let tgt_to_src_maps =
      let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
      Option.get (match_ctxs check_equiv fixed_ids filt_tgt_ctx filt_src_ctx)
    in
    let src_to_tgt_borrow_map =
      V.BorrowId.Map.of_list
        (List.map
           (fun (x, y) -> (y, x))
           (V.BorrowId.InjSubst.bindings tgt_to_src_maps.borrow_id_map))
    in

    (* Debug *)
    log#ldebug
      (lazy
        ("match_ctx_with_target:cf_introduce_loop_fp_abs:"
       ^ "\n\n- filt_src_ctx: "
        ^ eval_ctx_to_string filt_src_ctx
        ^ "\n\n- filt_tgt_ctx: "
        ^ eval_ctx_to_string filt_tgt_ctx
        ^ "\n\n- tgt_to_src_maps: "
        ^ show_ids_maps tgt_to_src_maps));

    (* Update the borrows and symbolic ids in the source context.

       Going back to the [list_nth_mut_example], the source environment upon
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

       Through matching, we detected that in [env_fp], [l1] will be matched
       to [l5]. We introduced a fresh borrow [l6] for [l1], and remember
       in the map [tgt_fresh_borrows_map] that: [{ l1 -> l6}].

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
    *)
    let tgt_fresh_borrows_map = ref V.BorrowId.Map.empty in
    let visit_src =
      object
        inherit [_] C.map_eval_ctx

        method! visit_borrow_id _ id =
          (* Map the borrow, if it needs to be mapped *)
          if
            V.BorrowId.InjSubst.Set.mem id
              (V.BorrowId.InjSubst.elements tgt_to_src_maps.borrow_id_map)
          then (
            let tgt_id = V.BorrowId.Map.find id src_to_tgt_borrow_map in
            let nid = C.fresh_borrow_id () in
            tgt_fresh_borrows_map :=
              V.BorrowId.Map.add tgt_id nid !tgt_fresh_borrows_map;
            nid)
          else id
      end
    in
    let src_ctx = visit_src#visit_eval_ctx () src_ctx in

    (* Rem.: we don't update the symbolic values. It is not necessary
       because there shouldn't be any symbolic value containing borrows.

       Rem.: we will need to do something about the symbolic values in the
       abstractions and in the *variable bindings* once we allow symbolic
       values containing borrows to not be eagerly expanded.
    *)
    assert Config.greedy_expand_symbolics_with_borrows;

    (* Update the borrows and loans in the abstractions of the target context.

       Going back to the [list_nth_mut] example and by using [tgt_fresh_borrows_map],
       we instantiate the fixed-point abstractions that we will insert into the
       context.
       The abstraction is [abs { MB l0, ML l1 }].
       Because of [tgt_fresh_borrows_map], we substitute [l1] with [l6].
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
    let visit_tgt =
      object
        inherit [_] C.map_eval_ctx as super

        method! visit_borrow_id _ bid =
          (* Lookup the id of the loan corresponding to this borrow *)
          let tgt_lid =
            V.BorrowId.InjSubst.find bid fp_bl_maps.borrow_to_loan_id_map
          in
          (* Lookup the src borrow id to which this borrow was mapped *)
          let src_bid =
            V.BorrowId.InjSubst.find tgt_lid tgt_to_src_maps.borrow_id_map
          in
          src_bid

        method! visit_loan_id _ id =
          (* Map the borrow - rem.: we mapped the borrows *in the values*,
             meaning we know how to map the *corresponding loans in the
             abstractions* *)
          V.BorrowId.Map.find id !tgt_fresh_borrows_map

        method! visit_symbolic_value_id _ _ = C.fresh_symbolic_value_id ()
        method! visit_abstraction_id _ _ = C.fresh_abstraction_id ()
        method! visit_region_id _ id = get_rid id

        (** We also need to change the abstraction kind *)
        method! visit_abs env abs =
          match abs.kind with
          | V.Loop (loop_id', rg_id, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              let kind = V.Loop (loop_id, rg_id, V.LoopSynthRet) in
              let abs = { abs with kind } in
              super#visit_abs env abs
          | _ -> super#visit_abs env abs
      end
    in
    let new_absl = List.map (visit_tgt#visit_abs ()) new_absl in

    (* Add the abstractions from the target context to the source context *)
    let nenv =
      List.append (List.map (fun abs -> C.Abs abs) new_absl) src_ctx.env
    in
    let src_ctx = { src_ctx with env = nenv } in

    log#ldebug
      (lazy
        ("match_ctx_with_target:cf_introduce_loop_fp_abs:\n- result ctx:"
       ^ eval_ctx_to_string src_ctx));

    (* Sanity check *)
    if !Config.check_invariants then
      Invariants.check_borrowed_values_invariant src_ctx;

    (* End all the borrows which appear in the *new* abstractions *)
    let new_borrows =
      V.BorrowId.Set.of_list
        (List.map snd (V.BorrowId.Map.bindings !tgt_fresh_borrows_map))
    in
    let cc = InterpreterBorrows.end_borrows config new_borrows in

    (* List the loop input values - when iterating over a map, we iterate
       over the keys, in increasing order *)
    let input_values =
      List.map snd
        (V.SymbolicValueId.Map.bindings tgt_to_src_maps.sid_to_value_map)
    in

    (* Continue *)
    cc
      (cf
         (if is_loop_entry then EndEnterLoop input_values
         else EndContinue input_values))
      src_ctx
  in

  (* Compose and continue *)
  cf_reorganize_src cf_introduce_loop_fp_abs src_ctx

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
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
    | Return -> cf LoopReturn
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
    | LoopReturn | EndEnterLoop _ | EndContinue _ ->
        (* We can't get there: this is only used in symbolic mode *)
        raise (Failure "Unreachable")
  in

  (* Apply *)
  eval_loop_body reeval_loop_body ctx

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : C.config) (eval_loop_body : st_cm_fun) :
    st_cm_fun =
 fun cf ctx ->
  (* Debug *)
  log#ldebug
    (lazy ("eval_loop_symbolic:\nContext:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Compute a fresh loop id *)
  let loop_id = C.fresh_loop_id () in
  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nInitial context:\n" ^ eval_ctx_to_string ctx
     ^ "\n\nFixed point:\n" ^ eval_ctx_to_string fp_ctx));

  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation
  *)
  let fp_bl_corresp =
    compute_fixed_point_id_correspondance fixed_ids ctx fp_ctx
  in
  let end_expr =
    match_ctx_with_target config loop_id true fp_bl_corresp fixed_ids fp_ctx cf
      ctx
  in

  (* Synthesize the loop body by evaluating it, with the continuation for
     after the loop starting at the *fixed point*, but with a special
     treatment for the [Break] and [Continue] cases *)
  let cf_loop : st_m_fun =
   fun res ctx ->
    match res with
    | Return | Panic -> cf res ctx
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res ctx
    | Continue i ->
        (* We don't support nested loops for now *)
        assert (i = 0);
        let cc =
          match_ctx_with_target config loop_id false fp_bl_corresp fixed_ids
            fp_ctx
        in
        cc cf ctx
    | Unit | LoopReturn | EndEnterLoop _ | EndContinue _ ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        raise (Failure "Unreachable")
  in
  let loop_expr = eval_loop_body cf_loop fp_ctx in

  (* Put together *)
  S.synthesize_loop loop_id end_expr loop_expr

(** Evaluate a loop *)
let eval_loop (config : C.config) (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.C.mode with
  | ConcreteMode -> eval_loop_concrete eval_loop_body cf ctx
  | SymbolicMode -> eval_loop_symbolic config eval_loop_body cf ctx
