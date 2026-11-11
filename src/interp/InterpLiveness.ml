open Types
open Values
open Expressions
open LlbcAst
open Contexts
open Cps
open InterpUtils
open InterpBorrowsCore

(** {1 Backward Liveness Analysis on LLBC} *)

type loop_targets = {
  break_live : LocalId.Set.t;
  continue_live : LocalId.Set.t;
}

let rec add_operand_reads (op : operand) (acc : LocalId.Set.t) : LocalId.Set.t =
  match op with
  | Copy p | Move p -> add_place_reads p acc
  | Constant _ -> acc

and add_proj_elem_reads (pe : projection_elem) (acc : LocalId.Set.t) :
    LocalId.Set.t =
  match pe with
  | Deref | Field _ | PtrMetadata -> acc
  | ProjIndex (op, _) | Offset (op, _, _, _) -> add_operand_reads op acc
  | Subslice (op1, op2, _) -> add_operand_reads op1 (add_operand_reads op2 acc)

and add_place_reads (p : place) (acc : LocalId.Set.t) : LocalId.Set.t =
  match p.kind with
  | PlaceLocal x -> LocalId.Set.add x acc
  | PlaceGlobal _ -> acc
  | PlaceProjection (sub_p, pe) ->
      add_proj_elem_reads pe (add_place_reads sub_p acc)

(** When writing to a projected place (e.g. [*r = ...] or [x.f = ...]):
    - index/offset operands along the projection path are always read;
    - if the projection path contains a [Deref], everything beneath that [Deref]
      is read to compute the target address;
    - if there is no [Deref] (e.g. [x.0 = ...]), the root local [x] is neither
      killed (sibling fields stay intact) nor read. *)
let rec add_subplace_write_reads (p : place) (acc : LocalId.Set.t) :
    LocalId.Set.t =
  match p.kind with
  | PlaceLocal _ | PlaceGlobal _ -> acc
  | PlaceProjection (sub_p, Deref) -> add_place_reads sub_p acc
  | PlaceProjection (sub_p, pe) ->
      add_subplace_write_reads sub_p (add_proj_elem_reads pe acc)

let apply_place_write (p : place) (live_after : LocalId.Set.t) : LocalId.Set.t =
  match p.kind with
  | PlaceLocal x -> LocalId.Set.remove x live_after
  | PlaceGlobal _ -> live_after
  | PlaceProjection _ -> add_subplace_write_reads p live_after

let add_rvalue_reads (rv : rvalue) (acc : LocalId.Set.t) : LocalId.Set.t =
  match rv with
  | Use (op, _) | UnaryOp (_, op) | Repeat (op, _, _, _) ->
      add_operand_reads op acc
  | RvRef (p, _, op) | RawPtr (p, _, op) ->
      add_operand_reads op (add_place_reads p acc)
  | BinaryOp (_, op1, op2) -> add_operand_reads op1 (add_operand_reads op2 acc)
  | NullaryOp _ -> acc
  | Discriminant p -> add_place_reads p acc
  | Aggregate (_, ops) ->
      List.fold_left (fun a op -> add_operand_reads op a) acc ops

let add_fn_operand_reads (fn_op : fn_operand) (acc : LocalId.Set.t) :
    LocalId.Set.t =
  match fn_op with
  | FnOpRegular _ -> acc
  | FnOpDynamic (op, _) -> add_operand_reads op acc

let add_scrutinee_reads (scrut : switch_scrutinee) (acc : LocalId.Set.t) :
    LocalId.Set.t =
  match scrut with
  | SwitchValue op -> add_operand_reads op acc
  | SwitchDiscriminant p -> add_place_reads p acc

let add_asm_operands_liveness (ops : asm_operand list)
    (live_after : LocalId.Set.t) : LocalId.Set.t =
  let after_writes =
    List.fold_left
      (fun acc op ->
        match op with
        | Out (_, _, Some p) | InOut (_, _, _, Some p) ->
            apply_place_write p acc
        | In _
        | Out (_, _, None)
        | InOut (_, _, _, None)
        | Const _ | SymFn _ | SymStatic _ | Label _ -> acc)
      live_after ops
  in
  List.fold_left
    (fun acc op ->
      match op with
      | In (_, in_op) | InOut (_, _, in_op, _) -> add_operand_reads in_op acc
      | Out _ | Const _ | SymFn _ | SymStatic _ | Label _ -> acc)
    after_writes ops

let compute_liveness (root_block : block) : liveness_info =
  let stmt_map = ref StatementId.Map.empty in
  let block_map = ref BlockId.Map.empty in

  let rec eval_block ~(record : bool) (loop_stack : loop_targets list)
      (b : block) (live_after : LocalId.Set.t) : LocalId.Set.t =
    if record then block_map := BlockId.Map.add b.block_id live_after !block_map;
    List.fold_right
      (fun st live_out -> eval_stmt ~record loop_stack st live_out)
      b.statements live_after
  and eval_stmt ~(record : bool) (loop_stack : loop_targets list)
      (st : statement) (live_after : LocalId.Set.t) : LocalId.Set.t =
    let live_before =
      match st.kind with
      | Assign (p, rv) ->
          let live = apply_place_write p live_after in
          add_rvalue_reads rv live
      | SetDiscriminant (p, _) -> add_subplace_write_reads p live_after
      | StorageLive x | StorageDead x -> LocalId.Set.remove x live_after
      | PlaceMention p -> add_place_reads p live_after
      | Borrowck bck -> (
          match bck with
          | FakeRead p -> add_place_reads p live_after
          | SetType _ | SetOutlives _ | PredicateHolds _ -> live_after)
      | Drop (p, _, _, _) ->
          if !Config.drop_as_no_op then live_after
          else apply_place_write p live_after
      | Assert (assertion, _, _) -> add_operand_reads assertion.cond live_after
      | Call (call, dest, _) ->
          let live = apply_place_write dest live_after in
          let live =
            List.fold_left
              (fun acc op -> add_operand_reads op acc)
              live call.args
          in
          add_fn_operand_reads call.func live
      | InlineAsm (asm, fallthrough, labels, _) ->
          let post =
            match fallthrough with
            | None -> LocalId.Set.empty
            | Some fb -> eval_block ~record loop_stack fb live_after
          in
          let post =
            List.fold_left
              (fun acc lb ->
                LocalId.Set.union acc
                  (eval_block ~record loop_stack lb live_after))
              post labels
          in
          add_asm_operands_liveness asm.operands post
      | Switch (data, branches) ->
          let branches_live =
            List.fold_left
              (fun acc br ->
                LocalId.Set.union acc
                  (eval_block ~record loop_stack br live_after))
              LocalId.Set.empty branches
          in
          add_scrutinee_reads data.scrutinee branches_live
      | Loop body ->
          let rec fixpoint (entry : LocalId.Set.t) : LocalId.Set.t =
            let targets = { break_live = live_after; continue_live = entry } in
            let next =
              eval_block ~record:false (targets :: loop_stack) body entry
            in
            if LocalId.Set.equal next entry then entry else fixpoint next
          in
          let converged = fixpoint LocalId.Set.empty in
          (if record then
             let targets =
               { break_live = live_after; continue_live = converged }
             in
             let _ =
               eval_block ~record:true (targets :: loop_stack) body converged
             in
             ());
          converged
      | Break i -> (
          match List.nth_opt loop_stack i with
          | Some t -> t.break_live
          | None -> live_after)
      | Continue i -> (
          match List.nth_opt loop_stack i with
          | Some t -> t.continue_live
          | None -> live_after)
      | Return -> LocalId.Set.singleton LocalId.zero
      | Panic _ | UnwindTerminate | UnwindResume | UndefinedBehavior ->
          LocalId.Set.empty
      | Nop -> live_after
    in
    if record then
      stmt_map := StatementId.Map.add st.statement_id live_before !stmt_map;
    live_before
  in
  let _ = eval_block ~record:true [] root_block LocalId.Set.empty in
  { live_before_stmt = !stmt_map; live_after_block = !block_map }

(** {1 Soundness Check & Early Ending for [alive_hint = Some Short]} *)

exception Blocked

let value_has_ended_regions (ended_regions : RegionId.Set.t) (v : tvalue) : bool
    =
  if RegionId.Set.is_empty ended_regions then false
  else
    let visitor =
      object
        inherit [_] iter_tvalue

        method! visit_symbolic_value _ sv =
          if symbolic_value_has_ended_regions ended_regions sv then
            raise Utils.Found
      end
    in
    try
      visitor#visit_tvalue () v;
      false
    with Utils.Found -> true

let collect_loans_in_value (v : tvalue) : BorrowId.id list =
  let loans = ref [] in
  let visitor =
    object
      inherit [_] iter_tvalue as super

      method! visit_loan_content env lc =
        (match lc with
        | VMutLoan bid | VSharedLoan (bid, _) -> loans := bid :: !loans);
        super#visit_loan_content env lc
    end
  in
  visitor#visit_tvalue () v;
  !loans

(** Check whether ending [abs] would directly give back a mutable borrow or
    symbolic borrow projector into a frozen abstraction ([frozen_abs]). *)
let abs_borrows_loans_in_frozen (span : Meta.span) (ctx : eval_ctx)
    (frozen_abs : AbsId.Set.t) (abs : abs) : bool =
  if AbsId.Set.is_empty frozen_abs then false
  else
    let check_loan_in_frozen (bid : BorrowId.id) : unit =
      match fst (ctx_lookup_loan span ek_all bid ctx) with
      | AbsId aid when AbsId.Set.mem aid frozen_abs -> raise Utils.Found
      | _ -> ()
    in
    let check_proj_in_frozen (proj : symbolic_proj) : unit =
      let visitor =
        object
          inherit [_] iter_abs as super

          method! visit_AProjLoans loan_abs proj' =
            if
              proj.sv_id = proj'.proj.sv_id
              && projections_intersect span ctx abs.regions.owned proj.proj_ty
                   loan_abs.regions.owned proj'.proj.proj_ty
            then raise Utils.Found
            else super#visit_AProjLoans loan_abs proj'
        end
      in
      List.iter
        (function
          | EAbs loan_abs when AbsId.Set.mem loan_abs.abs_id frozen_abs ->
              visitor#visit_abs loan_abs loan_abs
          | EAbs _ | EBinding _ | EFrame -> ())
        ctx.env
    in
    let visitor =
      object
        inherit [_] iter_abs as super

        method! visit_borrow_content env bc =
          super#visit_borrow_content env bc;
          match bc with
          | VMutBorrow (bid, _) -> check_loan_in_frozen bid
          | VSharedBorrow _ | VReservedMutBorrow _ -> ()

        method! visit_aborrow_content env bc =
          super#visit_aborrow_content env bc;
          match bc with
          | AMutBorrow (_, bid, _) -> check_loan_in_frozen bid
          | ASharedBorrow _
          | AIgnoredMutBorrow _
          | AEndedMutBorrow _
          | AEndedSharedBorrow
          | AEndedIgnoredMutBorrow _
          | AProjSharedBorrow _ -> ()

        method! visit_aproj env sproj =
          super#visit_aproj env sproj;
          match sproj with
          | AProjBorrows aproj -> check_proj_in_frozen aproj.proj
          | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
              ()
      end
    in
    try
      visitor#visit_abs () abs;
      false
    with Utils.Found -> true

(** Return [true] iff calling [end_abs] on [target_abs_id] right now: 1. only
    ends endable abstractions (and does not prematurely end any active [Long] or
    [Regular] abstraction or mutate any frozen abstraction), and 2. does not
    invalidate any borrow or region inside any live local variable
    ([live_locals]). *)
let can_end_abs_for_short (span : Meta.span) (live_locals : LocalId.Set.t)
    (frozen_abs : AbsId.Set.t) (ctx : eval_ctx) (target_abs_id : AbsId.id) :
    bool =
  let is_live_binder (binder : var_binder) : bool =
    match binder with
    | BVar var -> LocalId.Set.mem var.index live_locals
    | BDummy _ -> false
  in
  let visited_abs = ref AbsId.Set.empty in
  let visited_loans = ref BorrowId.Set.empty in

  let update_outer (outer : BorrowId.id option) (bid : BorrowId.id) :
      BorrowId.id option =
    match outer with
    | Some _ -> outer
    | None -> Some bid
  in

  let rec require_end_abs (aid : AbsId.id) : unit =
    if AbsId.Set.mem aid !visited_abs then ()
    else
      match ctx_lookup_abs_opt ctx aid with
      | None -> ()
      | Some abs ->
          if not (abs_is_endable ctx abs) then raise Blocked;
          (if aid <> target_abs_id then
             match abs.alive_hint with
             | Some (Long | Regular) when abs_has_borrows_or_loans ctx abs ->
                 raise Blocked
             | Some (Long | Regular | Short) | None -> ());
          if abs_borrows_loans_in_frozen span ctx frozen_abs abs then
            raise Blocked;
          visited_abs := AbsId.Set.add aid !visited_abs;

          (* Check that no live local holds a symbolic value mentioning a region
             owned by [abs]. *)
          let owned_rids =
            TypesUtils.region_set_get_region_ids abs.regions.owned
          in
          if not (RegionId.Set.is_empty owned_rids) then
            List.iter
              (function
                | EBinding (binder, v)
                  when is_live_binder binder
                       && value_has_ended_regions owned_rids v -> raise Blocked
                | EBinding _ | EAbs _ | EFrame -> ())
              ctx.env;

          (* Parent abstractions must end first. *)
          AbsId.Set.iter require_end_abs abs.parents;

          (* Active loans and loan projectors inside [abs] must end. *)
          let loans = ref [] in
          let proj_loans = ref [] in
          let visitor =
            object
              inherit [_] iter_abs as super

              method! visit_aloan_content env lc =
                (match lc with
                | AMutLoan (_, bid, _) | ASharedLoan (_, bid, _, _) ->
                    loans := bid :: !loans
                | AEndedMutLoan _
                | AEndedSharedLoan _
                | AIgnoredMutLoan _
                | AEndedIgnoredMutLoan _
                | AIgnoredSharedLoan _ -> ());
                super#visit_aloan_content env lc

              method! visit_aproj env sproj =
                (match sproj with
                | AProjLoans aproj -> proj_loans := aproj.proj :: !proj_loans
                | AProjBorrows _
                | AEndedProjLoans _
                | AEndedProjBorrows _
                | AEmpty -> ());
                super#visit_aproj env sproj
            end
          in
          visitor#visit_abs () abs;
          List.iter require_end_loan !loans;
          List.iter (require_end_proj_loans abs.regions.owned) !proj_loans
  and require_end_loan (lid : BorrowId.id) : unit =
    if BorrowId.Set.mem lid !visited_loans then ()
    else
      match ctx_lookup_loan_opt span ek_all lid ctx with
      | None -> ()
      | Some (loan_owner, _) ->
          (match loan_owner with
          | AbsId aid when AbsId.Set.mem aid frozen_abs -> raise Blocked
          | AbsId _ | LocalId _ | DummyVarId _ -> ());
          visited_loans := BorrowId.Set.add lid !visited_loans;

          let rec check_concrete_value ~(in_live_bvar : bool)
              (outer : BorrowId.id option) (v : tvalue) : unit =
            match v.value with
            | VLiteral _ | VBottom | VSymbolic _ -> ()
            | VAdt adt ->
                List.iter (check_concrete_value ~in_live_bvar outer) adt.fields
            | VLoan (VMutLoan _) -> ()
            | VLoan (VSharedLoan (bid', sv)) ->
                check_concrete_value ~in_live_bvar (update_outer outer bid') sv
            | VBorrow (VSharedBorrow (bid', _) | VReservedMutBorrow (bid', _))
              ->
                if bid' = lid then
                  if in_live_bvar then raise Blocked
                  else Option.iter require_end_loan outer
            | VBorrow (VMutBorrow (bid', bv)) ->
                if bid' = lid then (
                  if in_live_bvar then raise Blocked;
                  Option.iter require_end_loan outer;
                  List.iter require_end_loan (collect_loans_in_value bv))
                else
                  check_concrete_value ~in_live_bvar (update_outer outer bid')
                    bv
          in

          let check_abs (abs : abs) : unit =
            let visitor =
              object (self)
                inherit [_] iter_abs as super

                method! visit_aloan_content in_abs lc =
                  match lc with
                  | ASharedLoan (_, sl_bid, sv, child) ->
                      check_concrete_value ~in_live_bvar:false (Some sl_bid) sv;
                      self#visit_tavalue in_abs child
                  | AEndedSharedLoan (sv, child) ->
                      check_concrete_value ~in_live_bvar:false None sv;
                      self#visit_tavalue in_abs child
                  | AMutLoan _
                  | AEndedMutLoan _
                  | AIgnoredMutLoan _
                  | AEndedIgnoredMutLoan _
                  | AIgnoredSharedLoan _ -> super#visit_aloan_content in_abs lc

                method! visit_aborrow_content in_abs bc =
                  (match bc with
                  | AMutBorrow (_, bid', _) | ASharedBorrow (_, bid', _) ->
                      if bid' = lid then require_end_abs abs.abs_id
                  | AProjSharedBorrow asb ->
                      if
                        List.exists
                          (function
                            | AsbBorrow (bid', _) -> bid' = lid
                            | AsbProjReborrows _ -> false)
                          asb
                      then require_end_abs abs.abs_id
                  | AIgnoredMutBorrow _
                  | AEndedMutBorrow _
                  | AEndedSharedBorrow
                  | AEndedIgnoredMutBorrow _ -> ());
                  super#visit_aborrow_content in_abs bc

                method! visit_borrow_content in_abs bc =
                  (match bc with
                  | VMutBorrow (bid', _)
                  | VSharedBorrow (bid', _)
                  | VReservedMutBorrow (bid', _) ->
                      if bid' = lid then require_end_abs abs.abs_id);
                  super#visit_borrow_content in_abs bc
              end
            in
            visitor#visit_abs () abs
          in

          List.iter
            (function
              | EBinding (binder, v) ->
                  check_concrete_value ~in_live_bvar:(is_live_binder binder)
                    None v
              | EAbs abs -> check_abs abs
              | EFrame -> ())
            ctx.env
  and require_end_proj_loans (regions : RegionSet.t) (proj : symbolic_proj) :
      unit =
    let rec check_concrete_sv ~(in_live_bvar : bool)
        (outer : BorrowId.id option) (v : tvalue) : unit =
      match v.value with
      | VLiteral _ | VBottom -> ()
      | VSymbolic sv ->
          if sv.sv_id = proj.sv_id then
            if in_live_bvar then raise Blocked
            else Option.iter require_end_loan outer
      | VAdt adt -> List.iter (check_concrete_sv ~in_live_bvar outer) adt.fields
      | VLoan (VMutLoan _) -> ()
      | VLoan (VSharedLoan (bid', sv)) ->
          check_concrete_sv ~in_live_bvar (update_outer outer bid') sv
      | VBorrow (VSharedBorrow _ | VReservedMutBorrow _) -> ()
      | VBorrow (VMutBorrow (bid', bv)) ->
          check_concrete_sv ~in_live_bvar (update_outer outer bid') bv
    in
    let check_abs_shared_sv (abs : abs) : unit =
      let visitor =
        object (self)
          inherit [_] iter_abs as super

          method! visit_aloan_content env lc =
            match lc with
            | ASharedLoan (_, sl_bid, sv, child) ->
                check_concrete_sv ~in_live_bvar:false (Some sl_bid) sv;
                self#visit_tavalue env child
            | AEndedSharedLoan (sv, child) ->
                check_concrete_sv ~in_live_bvar:false None sv;
                self#visit_tavalue env child
            | AMutLoan _
            | AEndedMutLoan _
            | AIgnoredMutLoan _
            | AEndedIgnoredMutLoan _
            | AIgnoredSharedLoan _ -> super#visit_aloan_content env lc
        end
      in
      visitor#visit_abs () abs
    in
    List.iter
      (function
        | EBinding (binder, v) ->
            check_concrete_sv ~in_live_bvar:(is_live_binder binder) None v
        | EAbs abs -> check_abs_shared_sv abs
        | EFrame -> ())
      ctx.env;
    match lookup_intersecting_aproj_borrows_opt span true regions proj ctx with
    | None -> ()
    | Some projs ->
        List.iter
          (fun (aid, _, _) -> require_end_abs aid)
          (projs.shared_projs @ projs.non_shared_projs)
  in

  try
    require_end_abs target_abs_id;
    true
  with Blocked -> false

let env_has_short_abs (env : env) : bool =
  List.exists
    (function
      | EAbs { alive_hint = Some Short; _ } -> true
      | EAbs { alive_hint = Some (Long | Regular) | None; _ }
      | EBinding _ | EFrame -> false)
    env

let end_short_abstractions (config : config) (span : Meta.span)
    (live_locals : LocalId.Set.t) : cm_fun =
 fun ctx ->
  if not (env_has_short_abs ctx.env) then (ctx, fun e -> e)
  else
    let rec loop (ctx : eval_ctx) :
        eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
      let frozen_abs =
        AbsId.Set.of_list
          (List.filter_map
             (function
               | EAbs abs when not abs.can_end -> Some abs.abs_id
               | EAbs _ | EBinding _ | EFrame -> None)
             ctx.env)
      in
      let next_short =
        List.find_map
          (function
            | EAbs ({ alive_hint = Some Short; _ } as abs)
              when can_end_abs_for_short span live_locals frozen_abs ctx
                     abs.abs_id -> Some abs.abs_id
            | EAbs _ | EBinding _ | EFrame -> None)
          ctx.env
      in
      match next_short with
      | None -> (ctx, fun e -> e)
      | Some aid ->
          let ctx, cc = InterpBorrows.end_abs config span aid 0 ctx in
          Invariants.check_invariants span ctx;
          comp cc (loop ctx)
    in
    loop ctx

let end_short_abstractions_before_stmt (config : config) (st : statement) :
    cm_fun =
 fun ctx ->
  match config.liveness with
  | None -> (ctx, fun e -> e)
  | Some liveness -> (
      match
        StatementId.Map.find_opt st.statement_id liveness.live_before_stmt
      with
      | None -> (ctx, fun e -> e)
      | Some live_locals ->
          end_short_abstractions config st.span live_locals ctx)

let end_short_abstractions_after_block (config : config) (b : block) : cm_fun =
 fun ctx ->
  match config.liveness with
  | None -> (ctx, fun e -> e)
  | Some liveness -> (
      match BlockId.Map.find_opt b.block_id liveness.live_after_block with
      | None -> (ctx, fun e -> e)
      | Some live_locals -> end_short_abstractions config b.span live_locals ctx
      )
