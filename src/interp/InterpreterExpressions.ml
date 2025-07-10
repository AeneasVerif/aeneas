open Types
open Values
open Scalars
open Expressions
open Utils
open Contexts
open TypesUtils
open ValuesUtils
open SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterExpansion
open InterpreterPaths
open Errors

(** The local logger *)
let log = Logging.expressions_log

(** As long as there are symbolic values at a given place (potentially in
    subvalues) which contain borrows and are expandable, expand them.

    We use this function before copying values.

    Note that the place should have been prepared so that there are no remaining
    loans. *)
let expand_if_borrows_at_place (config : config) (span : Meta.span)
    (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  (* Small helper *)
  let rec expand : cm_fun =
   fun ctx ->
    let v = read_place span access p ctx in
    match
      find_first_expandable_sv_with_borrows (Some span) ctx.type_ctx.type_decls
        ctx.type_ctx.type_infos v
    with
    | None -> (ctx, fun e -> e)
    | Some sv ->
        let ctx, cc =
          expand_symbolic_value_no_branching config span sv
            (Some (mk_mplace span p ctx))
            ctx
        in
        comp cc (expand ctx)
  in
  (* Apply *)
  expand ctx

(** Read a place.

    We check that the value *doesn't contain bottoms or reserved borrows*. *)
let read_place_check (span : Meta.span) (access : access_kind) (p : place)
    (ctx : eval_ctx) : typed_value =
  let v = read_place span access p ctx in
  (* Check that there are no bottoms in the value *)
  cassert __FILE__ __LINE__
    (not (bottom_in_value ctx.ended_regions v))
    span "There should be no bottoms in the value";
  (* Check that there are no reserved borrows in the value *)
  cassert __FILE__ __LINE__
    (not (reserved_in_value v))
    span "There should be no reserved borrows in the value";
  (* Return *)
  v

let access_rplace_reorganize_and_read (config : config) (span : Meta.span)
    (greedy_expand : bool) (access : access_kind) (p : place) (ctx : eval_ctx) :
    typed_value * eval_ctx * (SymbolicAst.expression -> SymbolicAst.expression)
    =
  (* Make sure we can evaluate the path *)
  let ctx, cc = update_ctx_along_read_place config span access p ctx in
  (* End the proper loans at the place itself *)
  let ctx, cc = comp cc (end_loans_at_place config span access p ctx) in
  (* Expand the copyable values which contain borrows (which are necessarily shared
   * borrows) *)
  let ctx, cc =
    comp cc
      (if greedy_expand then expand_if_borrows_at_place config span access p ctx
       else (ctx, fun e -> e))
  in
  (* Read the place - note that this checks that the value doesn't contain bottoms *)
  let ty_value = read_place_check span access p ctx in
  (* Compose *)
  (ty_value, ctx, cc)

let access_rplace_reorganize (config : config) (span : Meta.span)
    (greedy_expand : bool) (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  let _, ctx, f =
    access_rplace_reorganize_and_read config span greedy_expand access p ctx
  in
  (ctx, f)

(** Convert an operand constant operand value to a typed value *)
let literal_to_typed_value (span : Meta.span) (ty : literal_type) (cv : literal)
    : typed_value =
  (* Check the type while converting - we actually need some information
   * contained in the type *)
  log#ltrace
    (lazy
      ("literal_to_typed_value:" ^ "\n- cv: "
      ^ Print.Values.literal_to_string cv));
  match (ty, cv) with
  (* Scalar, boolean... *)
  | TBool, VBool v -> { value = VLiteral (VBool v); ty = TLiteral ty }
  | TChar, VChar v -> { value = VLiteral (VChar v); ty = TLiteral ty }
  | TInteger int_ty, VScalar v ->
      (* Check the type and the ranges *)
      sanity_check __FILE__ __LINE__ (int_ty = v.int_ty) span;
      sanity_check __FILE__ __LINE__ (check_scalar_value_in_range v) span;
      { value = VLiteral (VScalar v); ty = TLiteral ty }
  (* Remaining cases (invalid) *)
  | _, _ -> craise __FILE__ __LINE__ span "Improperly typed constant value"

(** Copy a value, and return the: the original value (we may have need to update
    it - see the remark about the symbolic values with borrows) and the
    resulting value.

    Note that copying values might update the context. For instance, when
    copying shared borrows, we need to insert new shared borrows in the context.

    Also, this function is actually more general than it should be: it can be
    used to copy concrete ADT values, while ADT copy should be done through the
    Copy trait (i.e., by calling a dedicated function). This is why we added a
    parameter to control this copy ([allow_adt_copy]). Note that here by ADT we
    mean the user-defined ADTs (not tuples or builtin types).

    **Symbolic values with borrows**: Side note about copying symbolic values
    with borrows: in order to make the joins easier to compute, especially for
    the loops, whenever we copy a symbolic value containing borrows we introduce
    an auxiliary abstraction and freshen the copied value. This enforces the
    invariant that there can't be several occurrences of the same borrow
    projector over the same symbolic value. More precisely, we do something like
    this:
    {[
      // x -> s0
      y = copy x
      // x -> s1
      // y -> s2
      // abs { proj_borrows s0, proj_loans s1, proj_loans s2 }
    ]} *)
let rec copy_value (span : Meta.span) (allow_adt_copy : bool) (config : config)
    (ctx : eval_ctx) (v : typed_value) :
    typed_value
    * typed_value
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  log#ltrace
    (lazy
      ("copy_value: "
      ^ typed_value_to_string ~span:(Some span) ctx v
      ^ "\n- context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));
  (* Remark: at some point we rewrote this function to use iterators, but then
   * we reverted the changes: the result was less clear actually. In particular,
   * the fact that we have exhaustive matches below makes very obvious the cases
   * in which we need to fail *)
  match v.value with
  | VLiteral _ -> (v, v, ctx, fun e -> e)
  | VAdt av ->
      (* Sanity check *)
      (match v.ty with
      | TAdt { id = TBuiltin TBox; _ } ->
          exec_raise __FILE__ __LINE__ span
            "Can't copy an builtin value other than Option"
      | TAdt { id = TAdtId _; _ } as ty ->
          sanity_check __FILE__ __LINE__
            (allow_adt_copy || ty_is_copyable ty)
            span
      | TAdt { id = TTuple; _ } -> () (* Ok *)
      | TAdt
          {
            id = TBuiltin (TSlice | TArray);
            generics =
              {
                regions = [];
                types = [ ty ];
                const_generics = [];
                trait_refs = [];
              };
          } ->
          exec_assert __FILE__ __LINE__ (ty_is_copyable ty) span
            "The type is not primitively copyable"
      | _ -> exec_raise __FILE__ __LINE__ span "Unreachable");
      let (ctx, cc), fields =
        List.fold_left_map
          (fun (ctx, cc) v ->
            let v, copied, ctx, cc1 =
              copy_value span allow_adt_copy config ctx v
            in
            ((ctx, cc_comp cc cc1), (v, copied)))
          (ctx, fun e -> e)
          av.field_values
      in
      let fields, copied_fields = List.split fields in
      let copied =
        { v with value = VAdt { av with field_values = copied_fields } }
      in
      let v = { v with value = VAdt { av with field_values = fields } } in
      (v, copied, ctx, cc)
  | VBottom -> exec_raise __FILE__ __LINE__ span "Can't copy ⊥"
  | VBorrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | VSharedBorrow bid ->
          (* We need to create a new borrow id for the copied borrow, and
           * update the context accordingly *)
          let bid' = fresh_borrow_id () in
          let ctx = InterpreterBorrows.reborrow_shared span bid bid' ctx in
          (v, { v with value = VBorrow (VSharedBorrow bid') }, ctx, fun e -> e)
      | VMutBorrow (_, _) ->
          exec_raise __FILE__ __LINE__ span "Can't copy a mutable borrow"
      | VReservedMutBorrow _ ->
          exec_raise __FILE__ __LINE__ span "Can't copy a reserved mut borrow")
  | VLoan lc -> (
      (* We can only copy shared loans *)
      match lc with
      | VMutLoan _ ->
          exec_raise __FILE__ __LINE__ span "Can't copy a mutable loan"
      | VSharedLoan (sids, sv) ->
          (* We don't copy the shared loan: only the shared value inside *)
          let updt_value, copied_value, ctx, cf =
            copy_value span allow_adt_copy config ctx sv
          in
          ( { v with value = VLoan (VSharedLoan (sids, updt_value)) },
            copied_value,
            ctx,
            cf ))
  | VSymbolic sp ->
      (* We can copy only if the type is "primitively" copyable.
         Note that in the general case, copy is a trait: copying values
         thus requires calling the proper function. Here, we copy values
         for very simple types such as integers, shared borrows, etc. *)
      cassert __FILE__ __LINE__
        (ty_is_copyable (Substitute.erase_regions sp.sv_ty))
        span "Not primitively copyable";
      (* Check if the symbolic value contains borrows: if it does, we need to
         introduce au auxiliary region abstraction (see document of the function) *)
      if not (ty_has_borrows (Some span) ctx.type_ctx.type_infos v.ty) then
        (* No borrows: do nothing *)
        (v, v, ctx, fun e -> e)
      else
        let ctx0 = ctx in
        (* There are borrows: we need to introduce one region abstraction per live
           region present in the type *)
        let regions, ty =
          InterpreterBorrowsCore.refresh_live_regions_in_ty span ctx sp.sv_ty
        in
        let updated_sv = mk_fresh_symbolic_value span ty in
        let copied_sv = mk_fresh_symbolic_value span ty in
        let mk_abs (r_id : RegionId.id) (avalues : typed_avalue list) : abs =
          let abs =
            {
              abs_id = fresh_abstraction_id ();
              kind = CopySymbolicValue;
              can_end = true;
              parents = AbstractionId.Set.empty;
              original_parents = [];
              regions =
                {
                  owned = RegionId.Set.singleton r_id;
                  ancestors = RegionId.Set.empty;
                };
              avalues;
            }
          in
          Invariants.opt_type_check_abs span ctx abs;
          (* *)
          abs
        in

        let abs =
          List.map
            (fun rid ->
              let mk_proj (is_borrows : bool) sv_id : typed_avalue =
                let proj =
                  if is_borrows then AProjBorrows (sv_id, ty, [])
                  else AProjLoans (sv_id, ty, [])
                in
                let value = ASymbolic (PNone, proj) in
                { value; ty }
              in
              let sv = mk_proj true sp.sv_id in
              let updated_sv = mk_proj false updated_sv.sv_id in
              let copied_sv = mk_proj false copied_sv.sv_id in
              mk_abs rid [ sv; updated_sv; copied_sv ])
            (RegionId.Map.values regions)
        in
        let abs = List.map (fun a -> EAbs a) (List.rev abs) in
        let ctx = { ctx with env = abs @ ctx.env } in
        (* Create the continuation: we need to introduce intermediate let-bindings *)
        let cf e =
          let mk sv e =
            SymbolicAst.IntroSymbolic
              (ctx0, None, sv, SymbolicAst.VaSingleValue v, e)
          in
          mk updated_sv (mk copied_sv e)
        in
        ( mk_typed_value_from_symbolic_value updated_sv,
          mk_typed_value_from_symbolic_value copied_sv,
          ctx,
          cf )

(** Reorganize the environment in preparation for the evaluation of an operand.

    Evaluating an operand requires reorganizing the environment to get access to
    a given place (by ending borrows, expanding symbolic values...) then
    applying the operand operation (move, copy, etc.).

    Sometimes, we want to decouple the two operations. Consider the following
    example:
    {[
      context = {
        x -> shared_borrow l0
        y -> shared_loan {l0} v
      }

      dest <- f(move x, move y);
      ...
    ]}

    Because of the way {!end_borrow} is implemented, when giving back the borrow
    [l0] upon evaluating [move y], if we have already moved the value of x, we
    won't notice that [shared_borrow l0] has disappeared from the environment
    (it has been moved and not assigned yet, and so is hanging in "thin air").

    By first "preparing" the operands evaluation, we make sure no such thing
    happens. To be more precise, we make sure all the updates to borrows
    triggered by access *and* move operations have already been applied.

    Rem.: in the formalization, we always have an explicit "reorganization" step
    in the rule premises, before the actual operand evaluation, that allows to
    reorganize the environment so that it satisfies the proper conditions. This
    function's role is to do the reorganization.

    Rem.: doing this is actually not completely necessary because when
    generating MIR, rustc introduces intermediate assignments for all the
    function parameters. Still, it is better for soundness purposes, and
    corresponds to what we do in the formalization (because we don't enforce the
    same constraints as MIR in the formalization). *)
let prepare_eval_operand_reorganize (config : config) (span : Meta.span)
    (op : operand) : cm_fun =
 fun ctx ->
  match op with
  | Constant _ ->
      (* No need to reorganize the context *)
      (ctx, fun e -> e)
  | Copy p ->
      (* Access the value *)
      let access = Read in
      (* Expand the symbolic values, if necessary *)
      let greedy_expand = true in
      access_rplace_reorganize config span greedy_expand access p ctx
  | Move p ->
      (* Access the value *)
      let access = Move in
      let greedy_expand = false in
      access_rplace_reorganize config span greedy_expand access p ctx

(** Evaluate an operand, without reorganizing the context before *)
let eval_operand_no_reorganize (config : config) (span : Meta.span)
    (op : operand) (ctx : eval_ctx) :
    typed_value * eval_ctx * (SymbolicAst.expression -> SymbolicAst.expression)
    =
  (* Debug *)
  log#ltrace
    (lazy
      ("eval_operand_no_reorganize: op: " ^ operand_to_string ctx op
     ^ "\n- ctx:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n"));
  (* Evaluate *)
  match op with
  | Constant cv -> begin
      match cv.value with
      | CLiteral lit -> (
          (* FIXME: the str type is not in [literal_type] *)
          match cv.ty with
          | TAdt { id = TBuiltin TStr; _ } ->
              let v : typed_value = { value = VLiteral lit; ty = cv.ty } in
              (v, ctx, fun e -> e)
          | TLiteral lit_ty ->
              (literal_to_typed_value span lit_ty lit, ctx, fun e -> e)
          | _ ->
              craise __FILE__ __LINE__ span
                ("Encountered an incorrectly typed constant: "
                ^ constant_expr_to_string ctx cv
                ^ " : " ^ ty_to_string ctx cv.ty))
      | CTraitConst (trait_ref, const_name) ->
          let ctx0 = ctx in
          (* Simply introduce a fresh symbolic value *)
          let ty = cv.ty in
          let v = mk_fresh_symbolic_typed_value span ty in
          (* Wrap the generated expression *)
          let cf e =
            SymbolicAst.IntroSymbolic
              ( ctx0,
                None,
                value_as_symbolic span v.value,
                SymbolicAst.VaTraitConstValue (trait_ref, const_name),
                e )
          in
          (v, ctx, cf)
      | CVar var ->
          let vid = expect_free_var (Some span) var in
          let ctx0 = ctx in
          (* In concrete mode: lookup the const generic value.
             In symbolic mode: introduce a fresh symbolic value.

             We have nothing to do: the value is copyable, so we can freely
             duplicate it.
          *)
          let ctx, cv, cc =
            let cv = ctx_lookup_const_generic_value ctx vid in
            match config.mode with
            | ConcreteMode ->
                (* Copy the value *)
                let allow_adt_copy = false in
                let updated_value, copied_value, ctx, cc =
                  copy_value span allow_adt_copy config ctx cv
                in
                (* As we are copying a const generic, we shouldn't have updated
                   the original value *)
                sanity_check __FILE__ __LINE__ (cv = updated_value) span;
                (* *)
                (ctx, copied_value, cc)
            | SymbolicMode ->
                (* We use the looked up value only for its type *)
                let v = mk_fresh_symbolic_typed_value span cv.ty in
                (ctx, v, fun e -> e)
          in
          (* We have to wrap the generated expression *)
          let cf e =
            (* If we are synthesizing a symbolic AST, it means that we are in symbolic
               mode: the value of the const generic is necessarily symbolic. *)
            sanity_check __FILE__ __LINE__ (is_symbolic cv.value) span;
            (* *)
            SymbolicAst.IntroSymbolic
              ( ctx0,
                None,
                value_as_symbolic span cv.value,
                SymbolicAst.VaCgValue vid,
                e )
          in
          (cv, ctx, cc_comp cc cf)
      | CFnPtr _ ->
          craise __FILE__ __LINE__ span
            "Function pointers are not supported yet"
      | CRawMemory _ ->
          craise __FILE__ __LINE__ span
            "Raw memory cannot be interpreted by the interpreter"
      | COpaque reason ->
          craise __FILE__ __LINE__ span
            ("Charon failed to compile constant: " ^ reason)
    end
  | Copy p ->
      (* Access the value *)
      let access = Read in
      let v = read_place_check span access p ctx in
      (* Sanity checks *)
      exec_assert __FILE__ __LINE__
        (not (bottom_in_value ctx.ended_regions v))
        span "Can not copy a value containing bottom";
      sanity_check __FILE__ __LINE__
        (Option.is_none
           (find_first_expandable_sv_with_borrows (Some span)
              ctx.type_ctx.type_decls ctx.type_ctx.type_infos v))
        span;
      (* Copy the value *)
      let allow_adt_copy = false in
      let updated_value, copied_value, ctx, cc =
        copy_value span allow_adt_copy config ctx v
      in
      (* Update the original value *)
      let ctx = write_place span access p updated_value ctx in
      (* *)
      (copied_value, ctx, cc)
  | Move p ->
      (* Access the value *)
      let access = Move in
      let v = read_place_check span access p ctx in
      (* Check that there are no bottoms in the value we are about to move *)
      exec_assert __FILE__ __LINE__
        (not (bottom_in_value ctx.ended_regions v))
        span "There should be no bottoms in the value we are about to move";
      (* Move the value *)
      let bottom : typed_value = { value = VBottom; ty = v.ty } in
      let ctx = write_place span access p bottom ctx in
      (v, ctx, fun e -> e)

let eval_operand (config : config) (span : Meta.span) (op : operand)
    (ctx : eval_ctx) :
    typed_value * eval_ctx * (SymbolicAst.expression -> SymbolicAst.expression)
    =
  (* Debug *)
  log#ltrace
    (lazy
      ("eval_operand: op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n"));
  (* We reorganize the context, then evaluate the operand *)
  let ctx, cc = prepare_eval_operand_reorganize config span op ctx in
  comp2 cc (eval_operand_no_reorganize config span op ctx)

(** Small utility.

    See [prepare_eval_operand_reorganize]. *)
let prepare_eval_operands_reorganize (config : config) (span : Meta.span)
    (ops : operand list) : cm_fun =
  fold_left_apply_continuation (prepare_eval_operand_reorganize config span) ops

(** Evaluate several operands. *)
let eval_operands (config : config) (span : Meta.span) (ops : operand list)
    (ctx : eval_ctx) :
    typed_value list
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Prepare the operands *)
  let ctx, cc = prepare_eval_operands_reorganize config span ops ctx in
  (* Evaluate the operands *)
  comp2 cc
    (map_apply_continuation (eval_operand_no_reorganize config span) ops ctx)

let eval_two_operands (config : config) (span : Meta.span) (op1 : operand)
    (op2 : operand) (ctx : eval_ctx) :
    (typed_value * typed_value)
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  let res, ctx, cc = eval_operands config span [ op1; op2 ] ctx in
  let res =
    match res with
    | [ v1; v2 ] -> (v1, v2)
    | _ -> craise __FILE__ __LINE__ span "Unreachable"
  in
  (res, ctx, cc)

let eval_unary_op_concrete (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Evaluate the operand *)
  let v, ctx, cc = eval_operand config span op ctx in
  (* Apply the unop *)
  let r =
    match (unop, v.value) with
    | Not, VLiteral (VBool b) -> Ok { v with value = VLiteral (VBool (not b)) }
    | Not, VLiteral (VScalar i) ->
        (* The ! operator flips the bits.
           In effect, this does the operation we implement below.
        *)
        let int_ty = i.int_ty in
        let x =
          if integer_type_is_signed int_ty then Z.of_int (-1)
          else scalar_max int_ty
        in
        let value = Z.sub x i.value in
        Ok { v with value = VLiteral (VScalar { value; int_ty }) }
    | Neg OPanic, VLiteral (VScalar sv) -> (
        let i = Z.neg sv.value in
        match mk_scalar sv.int_ty i with
        | Error _ -> Error EPanic
        | Ok sv -> Ok { v with value = VLiteral (VScalar sv) })
    | ( Cast (CastScalar (TInteger src_ty, TInteger tgt_ty)),
        VLiteral (VScalar sv) ) -> (
        (* Cast between integers *)
        sanity_check __FILE__ __LINE__ (src_ty = sv.int_ty) span;
        let i = sv.value in
        match mk_scalar tgt_ty i with
        | Error _ -> Error EPanic
        | Ok sv ->
            let ty = TLiteral (TInteger tgt_ty) in
            let value = VLiteral (VScalar sv) in
            Ok { ty; value })
    | Cast (CastScalar (TBool, TInteger tgt_ty)), VLiteral (VBool sv) -> (
        (* Cast bool -> int *)
        let i = Z.of_int (if sv then 1 else 0) in
        match mk_scalar tgt_ty i with
        | Error _ -> Error EPanic
        | Ok sv ->
            let ty = TLiteral (TInteger tgt_ty) in
            let value = VLiteral (VScalar sv) in
            Ok { ty; value })
    | Cast (CastScalar (TInteger _, TBool)), VLiteral (VScalar sv) ->
        (* Cast int -> bool *)
        let b =
          if Z.of_int 0 = sv.value then false
          else if Z.of_int 1 = sv.value then true
          else
            exec_raise __FILE__ __LINE__ span
              "Conversion from int to bool: out of range"
        in
        let value = VLiteral (VBool b) in
        let ty = TLiteral TBool in
        Ok { ty; value }
    | _ ->
        exec_raise __FILE__ __LINE__ span
          ("Invalid input for unop: " ^ unop_to_string ctx unop)
  in
  (r, ctx, cc)

let cast_unsize_to_modified_fields (span : Meta.span) (ctx : eval_ctx)
    (ty0 : ty) (ty1 : ty) :
    (type_decl_id * generic_args * FieldId.id * ty * ty) option =
  let mk_msg () =
    "Invalid inputs for unsized cast:\n- input ty: " ^ ty_to_string ctx ty0
    ^ "\n- output ty: " ^ ty_to_string ctx ty1
  in
  if (not (ty_is_box ty0)) || not (ty_is_box ty1) then
    exec_raise __FILE__ __LINE__ span (mk_msg ())
  else
    let ty0 = ty_as_box ty0 in
    let ty1 = ty_as_box ty1 in
    let compatible_array_slice (ty0, ty1) =
      if ty_is_array ty0 && ty_is_slice ty1 then
        let ty0, _ = ty_as_array ty0 in
        let ty1 = ty_as_slice ty1 in
        ty0 = ty1
      else false
    in
    (* Case 1: array to slice *)
    if compatible_array_slice (ty0, ty1) then None
    else if
      (* Case 2: ADT to ADT *)
      ty_is_custom_adt ty0 && ty_is_custom_adt ty1
    then (
      let id0, generics0 = ty_as_custom_adt ty0 in
      let id1, generics1 = ty_as_custom_adt ty1 in
      cassert __FILE__ __LINE__ (id0 = id1) span (mk_msg ());
      (* Retrieve the instantiated fields and make sure they are all the same
         but the last *)
      let fields_tys0 =
        AssociatedTypes.ctx_type_get_inst_norm_variants_fields_etypes span ctx
          id0 generics0
      in
      let fields_tys1 =
        AssociatedTypes.ctx_type_get_inst_norm_variants_fields_etypes span ctx
          id1 generics1
      in
      (* The ADTs should be structures *)
      let fields_tys0, fields_tys1 =
        match (fields_tys0, fields_tys1) with
        | [ (None, tys0) ], [ (None, tys1) ] -> (tys0, tys1)
        | _ -> exec_raise __FILE__ __LINE__ span (mk_msg ())
      in
      cassert __FILE__ __LINE__
        (List.length fields_tys0 = List.length fields_tys1
        && List.length fields_tys0 > 0)
        span (mk_msg ());
      let fields_tys = List.combine fields_tys0 fields_tys1 in
      let fields_beg, last_field = Collections.List.pop_last fields_tys in
      cassert __FILE__ __LINE__
        (List.for_all (fun (ty0, ty1) -> ty0 = ty1) fields_beg)
        span (mk_msg ());
      log#ldebug
        (lazy
          (__FUNCTION__ ^ ": structure cast unsized:\n- input field type: "
          ^ ty_to_string ctx (fst last_field)
          ^ "\n- output field type: "
          ^ ty_to_string ctx (snd last_field)));
      cassert __FILE__ __LINE__
        (compatible_array_slice last_field)
        span (mk_msg ());
      Some
        ( id0,
          generics0,
          FieldId.of_int (List.length fields_beg),
          fst last_field,
          snd last_field ))
    else exec_raise __FILE__ __LINE__ span (mk_msg ())

let eval_unary_op_symbolic (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Evaluate the operand *)
  let v, ctx, cc = eval_operand config span op ctx in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = fresh_symbolic_value_id () in
  let res_sv_ty =
    match (unop, v.ty) with
    | Not, (TLiteral TBool as lty) -> lty
    | Not, (TLiteral (TInteger _) as lty) -> lty
    | Neg OPanic, (TLiteral (TInteger _) as lty) -> lty
    | Cast (CastScalar (_, tgt_ty)), _ -> TLiteral tgt_ty
    | Cast (CastUnsize (ty0, ty1, _)), _ ->
        (* If the following function succeeds, then it means the cast is well-formed
           (otherwise it throws an exception) *)
        let _ = cast_unsize_to_modified_fields span ctx ty0 ty1 in
        ty1
    | _ ->
        exec_raise __FILE__ __LINE__ span
          ("Invalid input for unop: " ^ unop_to_string ctx unop)
  in
  let res_sv = { sv_id = res_sv_id; sv_ty = res_sv_ty } in
  (* Compute the result *)
  let res = Ok (mk_typed_value_from_symbolic_value res_sv) in
  (* Synthesize the symbolic AST *)
  let cc =
    cc_comp cc
      (synthesize_unary_op ctx unop v
         (mk_opt_place_from_op span op ctx)
         res_sv None)
  in
  (res, ctx, cc)

let eval_unary_op (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  match config.mode with
  | ConcreteMode -> eval_unary_op_concrete config span unop op ctx
  | SymbolicMode -> eval_unary_op_symbolic config span unop op ctx

(** Small helper for [eval_binary_op_concrete]: computes the result of applying
    the binop *after* the operands have been successfully evaluated *)
let eval_binary_op_concrete_compute (span : Meta.span) (binop : binop)
    (v1 : typed_value) (v2 : typed_value) : (typed_value, eval_error) result =
  (* Equality check binops (Eq, Ne) accept values from a wide variety of types.
   * The remaining binops only operate on scalars. *)
  if binop = Eq || binop = Ne then (
    (* Equality operations *)
    exec_assert __FILE__ __LINE__ (v1.ty = v2.ty) span
      "The arguments given to the binop don't have the same type";
    (* Equality/inequality check is primitive only for a subset of types *)
    exec_assert __FILE__ __LINE__ (ty_is_copyable v1.ty) span
      "Type is not primitively copyable";
    let b = v1 = v2 in
    Ok { value = VLiteral (VBool b); ty = TLiteral TBool })
  else
    (* For the non-equality operations, the input values are necessarily scalars *)
    match (v1.value, v2.value) with
    | VLiteral (VScalar sv1), VLiteral (VScalar sv2) -> begin
        (* There are binops which require the two operands to have the same
           type, and binops for which it is not the case.
           There are also binops which return booleans, and binops which
           return integers.
        *)
        match binop with
        | Lt | Le | Ge | Gt ->
            (* The two operands must have the same type and the result is a boolean *)
            sanity_check __FILE__ __LINE__ (sv1.int_ty = sv2.int_ty) span;
            let b =
              match binop with
              | Lt -> Z.lt sv1.value sv2.value
              | Le -> Z.leq sv1.value sv2.value
              | Ge -> Z.geq sv1.value sv2.value
              | Gt -> Z.gt sv1.value sv2.value
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
            in
            Ok
              ({ value = VLiteral (VBool b); ty = TLiteral TBool }
                : typed_value)
        | Div OPanic
        | Rem OPanic
        | Add OPanic
        | Sub OPanic
        | Mul OPanic
        | BitXor | BitAnd | BitOr -> (
            (* The two operands must have the same type and the result is an integer *)
            sanity_check __FILE__ __LINE__ (sv1.int_ty = sv2.int_ty) span;
            let res : _ result =
              match binop with
              | Div OPanic ->
                  if sv2.value = Z.zero then Error ()
                  else mk_scalar sv1.int_ty (Z.div sv1.value sv2.value)
              | Rem OPanic ->
                  (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                  if sv2.value = Z.zero then Error ()
                  else mk_scalar sv1.int_ty (Z.rem sv1.value sv2.value)
              | Add OPanic -> mk_scalar sv1.int_ty (Z.add sv1.value sv2.value)
              | Sub OPanic -> mk_scalar sv1.int_ty (Z.sub sv1.value sv2.value)
              | Mul OPanic -> mk_scalar sv1.int_ty (Z.mul sv1.value sv2.value)
              | BitXor -> raise Unimplemented
              | BitAnd -> raise Unimplemented
              | BitOr -> raise Unimplemented
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
            in
            match res with
            | Error _ -> Error EPanic
            | Ok sv ->
                Ok
                  {
                    value = VLiteral (VScalar sv);
                    ty = TLiteral (TInteger sv1.int_ty);
                  })
        | Ne | Eq -> craise __FILE__ __LINE__ span "Unreachable"
        | _ ->
            craise __FILE__ __LINE__ span
              ("Unimplemented binary operation: " ^ binop_to_string binop)
      end
    | _ ->
        craise __FILE__ __LINE__ span
          ("Invalid inputs for binop: " ^ binop_to_string binop)

let eval_binary_op_concrete (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Evaluate the operands *)
  let (v1, v2), ctx, cc = eval_two_operands config span op1 op2 ctx in
  (* Compute the result of the binop *)
  let r = eval_binary_op_concrete_compute span binop v1 v2 in
  (* Return *)
  (r, ctx, cc)

let eval_binary_op_symbolic (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Evaluate the operands *)
  let (v1, v2), ctx, cc = eval_two_operands config span op1 op2 ctx in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = fresh_symbolic_value_id () in
  let res_sv_ty =
    if binop = Eq || binop = Ne then (
      (* Equality operations *)
      sanity_check __FILE__ __LINE__ (v1.ty = v2.ty) span;
      (* Equality/inequality check is primitive only for a subset of types *)
      exec_assert __FILE__ __LINE__ (ty_is_copyable v1.ty) span
        "The type is not primitively copyable";
      TLiteral TBool)
    else
      (* Other operations: input types are integers *)
      match (v1.ty, v2.ty) with
      | TLiteral (TInteger int_ty1), TLiteral (TInteger int_ty2) -> (
          match binop with
          | Lt | Le | Ge | Gt ->
              sanity_check __FILE__ __LINE__ (int_ty1 = int_ty2) span;
              TLiteral TBool
          | Div _ | Rem _ | Add _ | Sub _ | Mul _ | BitXor | BitAnd | BitOr ->
              sanity_check __FILE__ __LINE__ (int_ty1 = int_ty2) span;
              TLiteral (TInteger int_ty1)
          | Cmp ->
              sanity_check __FILE__ __LINE__ (int_ty1 = int_ty2) span;
              TLiteral (TInteger I8)
          (* These return `(int, bool)` / a pointer which isn't a literal type *)
          | AddChecked | SubChecked | MulChecked | Offset ->
              craise __FILE__ __LINE__ span "Unimplemented binary operation"
          | Shl _ | Shr _ ->
              (* The number of bits can be of a different integer type
                 than the operand *)
              TLiteral (TInteger int_ty1)
          | Ne | Eq -> craise __FILE__ __LINE__ span "Unreachable")
      | _ -> craise __FILE__ __LINE__ span "Invalid inputs for binop"
  in
  let res_sv = { sv_id = res_sv_id; sv_ty = res_sv_ty } in
  let v = mk_typed_value_from_symbolic_value res_sv in
  (* Synthesize the symbolic AST *)
  let p1 = mk_opt_place_from_op span op1 ctx in
  let p2 = mk_opt_place_from_op span op2 ctx in
  let cc =
    cc_comp cc (synthesize_binary_op ctx binop v1 p1 v2 p2 res_sv None)
  in
  (* Compose and apply *)
  (Ok v, ctx, cc)

let eval_binary_op (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  match config.mode with
  | ConcreteMode -> eval_binary_op_concrete config span binop op1 op2 ctx
  | SymbolicMode -> eval_binary_op_symbolic config span binop op1 op2 ctx

(** Evaluate an rvalue which creates a reference (i.e., an rvalue which is `&p`
    or `&mut p` or `&two-phase p`) *)
let eval_rvalue_ref (config : config) (span : Meta.span) (p : place)
    (bkind : borrow_kind) (ctx : eval_ctx) :
    typed_value * eval_ctx * (SymbolicAst.expression -> SymbolicAst.expression)
    =
  match bkind with
  | BUniqueImmutable ->
      craise __FILE__ __LINE__ span
        "Unique immutable closure captures are not supported"
  | BShared | BTwoPhaseMut | BShallow ->
      (* **REMARK**: we initially treated shallow borrows like shared borrows.
         In practice this restricted the behaviour too much, so for now we
         forbid them and remove them in the prepasses (see the comments there
         as to why this is sound).
      *)
      sanity_check __FILE__ __LINE__ (bkind <> BShallow) span;

      (* Access the value *)
      let access =
        match bkind with
        | BShared | BShallow -> Read
        | BTwoPhaseMut -> Write
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in

      let greedy_expand = false in
      let v, ctx, cc =
        access_rplace_reorganize_and_read config span greedy_expand access p ctx
      in
      (* Generate the fresh borrow id *)
      let bid = fresh_borrow_id () in
      (* Compute the loan value, with which to replace the value at place p *)
      let nv =
        match v.value with
        | VLoan (VSharedLoan (bids, sv)) ->
            (* Shared loan: insert the new borrow id *)
            let bids1 = BorrowId.Set.add bid bids in
            { v with value = VLoan (VSharedLoan (bids1, sv)) }
        | _ ->
            (* Not a shared loan: add a wrapper *)
            let v' = VLoan (VSharedLoan (BorrowId.Set.singleton bid, v)) in
            { v with value = v' }
      in
      (* Update the value in the context to replace it with the loan *)
      let ctx = write_place span access p nv ctx in
      (* Compute the rvalue - simply a shared borrow with the fresh id.
       * Note that the reference is *mutable* if we do a two-phase borrow *)
      let ref_kind =
        match bkind with
        | BShared | BShallow -> RShared
        | BTwoPhaseMut -> RMut
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      let rv_ty = TRef (RErased, v.ty, ref_kind) in
      let bc =
        match bkind with
        | BShared | BShallow ->
            (* See the remark at the beginning of the match branch: we
               handle shallow borrows like shared borrows *)
            VSharedBorrow bid
        | BTwoPhaseMut -> VReservedMutBorrow bid
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      let rv : typed_value = { value = VBorrow bc; ty = rv_ty } in
      (* Return *)
      (rv, ctx, cc)
  | BMut ->
      (* Access the value *)
      let access = Write in
      let greedy_expand = false in
      let v, ctx, cc =
        access_rplace_reorganize_and_read config span greedy_expand access p ctx
      in
      (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
      let bid = fresh_borrow_id () in
      let rv_ty = TRef (RErased, v.ty, RMut) in
      let rv : typed_value =
        { value = VBorrow (VMutBorrow (bid, v)); ty = rv_ty }
      in
      (* Compute the loan value with which to replace the value at place p *)
      let nv = { v with value = VLoan (VMutLoan bid) } in
      (* Update the value in the context to replace it with the loan *)
      let ctx = write_place span access p nv ctx in
      (* Return *)
      (rv, ctx, cc)

let eval_rvalue_aggregate (config : config) (span : Meta.span)
    (aggregate_kind : aggregate_kind) (ops : operand list) (ctx : eval_ctx) :
    typed_value * eval_ctx * (SymbolicAst.expression -> SymbolicAst.expression)
    =
  (* Evaluate the operands *)
  let values, ctx, cc = eval_operands config span ops ctx in
  (* Compute the value *)
  let v, cf_compute =
    (* Match on the aggregate kind *)
    match aggregate_kind with
    | AggregatedAdt ({ id = type_id; generics }, opt_variant_id, opt_field_id)
      -> (
        (* The opt_field_id is Some only for unions, that we don't support *)
        sanity_check __FILE__ __LINE__ (opt_field_id = None) span;
        match type_id with
        | TTuple ->
            let tys = List.map (fun (v : typed_value) -> v.ty) values in
            let v = VAdt { variant_id = None; field_values = values } in
            let generics = mk_generic_args [] tys [] [] in
            let ty = TAdt { id = TTuple; generics } in
            let aggregated : typed_value = { value = v; ty } in
            (aggregated, fun e -> e)
        | TAdtId def_id ->
            (* Sanity checks *)
            let type_decl = ctx_lookup_type_decl span ctx def_id in
            sanity_check __FILE__ __LINE__
              (List.length type_decl.generics.regions
              = List.length generics.regions)
              span;
            let expected_field_types =
              AssociatedTypes.ctx_type_get_inst_norm_field_etypes span ctx
                def_id opt_variant_id generics
            in
            sanity_check __FILE__ __LINE__
              (expected_field_types
              = List.map (fun (v : typed_value) -> v.ty) values)
              span;
            (* Construct the value *)
            let av : adt_value =
              { variant_id = opt_variant_id; field_values = values }
            in
            let aty = TAdt { id = TAdtId def_id; generics } in
            let aggregated : typed_value = { value = VAdt av; ty = aty } in
            (* Call the continuation *)
            (aggregated, fun e -> e)
        | TBuiltin _ -> craise __FILE__ __LINE__ span "Unreachable")
    | AggregatedArray (ety, cg) ->
        (* Sanity check: all the values have the proper type *)
        classert __FILE__ __LINE__
          (List.for_all (fun (v : typed_value) -> v.ty = ety) values)
          span
          (lazy
            ("Aggregated array: some values don't have the proper type:"
           ^ "\n- expected type: " ^ ty_to_string ctx ety ^ "\n- values: ["
            ^ String.concat ", "
                (List.map
                   (fun (v : typed_value) ->
                     typed_value_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
                   values)
            ^ "]"));
        (* Sanity check: the number of values is consistent with the length *)
        let len = (literal_as_scalar (const_generic_as_literal cg)).value in
        sanity_check __FILE__ __LINE__
          (len = Z.of_int (List.length values))
          span;
        let generics = TypesUtils.mk_generic_args [] [ ety ] [ cg ] [] in
        let ty = TAdt { id = TBuiltin TArray; generics } in
        (* In order to generate a better AST, we introduce a symbolic
           value equal to the array. The reason is that otherwise, the
           array we introduce here might be duplicated in the generated
           code: by introducing a symbolic value we introduce a let-binding
           in the generated code.

           TODO: generalize to the case where we have an array of borrows.
           For now, we introduce a symbolic value only in the case the
           array doesn't contain borrows.
        *)
        if ty_has_borrows (Some span) ctx.type_ctx.type_infos ty then
          let value = VAdt { variant_id = None; field_values = values } in
          let value : typed_value = { value; ty } in
          (value, fun e -> e)
        else
          let saggregated = mk_fresh_symbolic_typed_value span ty in
          (* Update the symbolic ast *)
          let cf e =
            (* Introduce the symbolic value in the AST *)
            let sv = ValuesUtils.value_as_symbolic span saggregated.value in
            SymbolicAst.IntroSymbolic (ctx, None, sv, VaArray values, e)
          in
          (saggregated, cf)
    | AggregatedRawPtr _ ->
        craise __FILE__ __LINE__ span
          "Aggregated raw pointers are not supported yet"
  in
  (v, ctx, cc_comp cc cf_compute)

let eval_rvalue_not_global (config : config) (span : Meta.span)
    (rvalue : rvalue) (ctx : eval_ctx) :
    (typed_value, eval_error) result
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  log#ltrace (lazy "eval_rvalue");
  (* Small helper *)
  let wrap_in_result (v, ctx, cc) = (Ok v, ctx, cc) in
  (* Delegate to the proper auxiliary function *)
  match rvalue with
  | Use op -> wrap_in_result (eval_operand config span op ctx)
  | RvRef (p, bkind) -> wrap_in_result (eval_rvalue_ref config span p bkind ctx)
  | UnaryOp (unop, op) -> eval_unary_op config span unop op ctx
  | BinaryOp (binop, op1, op2) -> eval_binary_op config span binop op1 op2 ctx
  | Aggregate (aggregate_kind, ops) ->
      wrap_in_result (eval_rvalue_aggregate config span aggregate_kind ops ctx)
  | Discriminant _ ->
      craise __FILE__ __LINE__ span
        "Unreachable: discriminant reads should have been eliminated from the \
         AST"
  | Global _ -> craise __FILE__ __LINE__ span "Unreachable"
  | Len _ -> craise __FILE__ __LINE__ span "Unhandled Len"
  | _ ->
      craise __FILE__ __LINE__ span
        ("Unsupported operation: " ^ Print.EvalCtx.rvalue_to_string ctx rvalue)

let eval_fake_read (config : config) (span : Meta.span) (p : place) : cm_fun =
 fun ctx ->
  let greedy_expand = false in
  let v, ctx, cc =
    access_rplace_reorganize_and_read config span greedy_expand Read p ctx
  in
  cassert __FILE__ __LINE__
    (not (bottom_in_value ctx.ended_regions v))
    span "Fake read: the value contains bottom";
  (ctx, cc)
