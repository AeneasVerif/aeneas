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
open InterpUtils
open InterpExpansion
open InterpPaths

(** The local logger *)
let log = Logging.expressions_log

(** As long as there are symbolic values at a given place (potentially in
    subvalues) which contain borrows and are expandable, expand them.

    We use this function before copying values.

    Note that the place should have been prepared so that there are no remaining
    loans. *)
let expand_if_borrows_at_place (span : Meta.span) (access : access_kind)
    (p : place) : cm_fun =
 fun ctx ->
  (* Small helper *)
  let rec expand : cm_fun =
   fun ctx ->
    let _, v = read_place span access p ctx in
    match
      find_first_expandable_sv_with_borrows (Some span) ctx.type_ctx.type_decls
        ctx.type_ctx.type_infos v
    with
    | None -> (ctx, fun e -> e)
    | Some sv ->
        let ctx, cc =
          expand_symbolic_value_no_branching span sv
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
    (ctx : eval_ctx) : loan_id option * tvalue =
  let lid, v = read_place span access p ctx in
  (* Check that there are no bottoms in the value *)
  [%cassert] span
    (not (bottom_in_value ctx.ended_regions v))
    "There should be no bottoms in the value";
  (* Check that there are no reserved borrows in the value *)
  [%cassert] span
    (not (reserved_in_value v))
    "There should be no reserved borrows in the value";
  (* Return *)
  (lid, v)

let access_rplace_reorganize_and_read (config : config) (span : Meta.span)
    (greedy_expand : bool) (access : access_kind) (p : place) (ctx : eval_ctx) :
    loan_id option * tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)
    =
  (* Make sure we can evaluate the path *)
  let ctx, cc = update_ctx_along_read_place config span access p ctx in
  (* End the proper loans at the place itself *)
  let ctx, cc = comp cc (end_loans_at_place config span access p ctx) in
  (* Expand the copyable values which contain borrows (which are necessarily shared
   * borrows) *)
  let ctx, cc =
    comp cc
      (if greedy_expand then expand_if_borrows_at_place span access p ctx
       else (ctx, fun e -> e))
  in
  (* Read the place - note that this checks that the value doesn't contain bottoms *)
  let lid, value = read_place_check span access p ctx in
  (* Compose *)
  (lid, value, ctx, cc)

let access_rplace_reorganize (config : config) (span : Meta.span)
    (greedy_expand : bool) (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  if ExpressionsUtils.place_accesses_global p then (ctx, fun x -> x)
  else
    let _, _, ctx, f =
      access_rplace_reorganize_and_read config span greedy_expand access p ctx
    in
    (ctx, f)

(** Convert an operand constant operand value to a typed value *)
let literal_to_tvalue (span : Meta.span) (ty : literal_type) (cv : literal)
    (ctx : eval_ctx) : tvalue =
  (* Check the type while converting - we actually need some information
   * contained in the type *)
  [%ltrace "- cv: " ^ Print.Values.literal_to_string cv];
  let ptr_size = ctx.crate.target_information.target_pointer_size in
  match (ty, cv) with
  (* Scalar, boolean... *)
  | TBool, VBool v -> { value = VLiteral (VBool v); ty = TLiteral ty }
  | TChar, VChar v -> { value = VLiteral (VChar v); ty = TLiteral ty }
  | TInt int_ty, VScalar (SignedScalar (sv_ty, _) as sv) ->
      (* Check the type and the ranges *)
      [%sanity_check] span (int_ty = sv_ty);
      [%sanity_check] span (check_scalar_value_in_range ptr_size sv);
      { value = VLiteral (VScalar sv); ty = TLiteral ty }
  | TUInt int_ty, VScalar (UnsignedScalar (sv_ty, _) as sv) ->
      (* Check the type and the ranges *)
      [%sanity_check] span (int_ty = sv_ty);
      [%sanity_check] span (check_scalar_value_in_range ptr_size sv);
      { value = VLiteral (VScalar sv); ty = TLiteral ty }
  (* Remaining cases (invalid) *)
  | _, _ -> [%craise] span "Improperly typed constant value"

(** Copy a value, and return the: the original value (we may have need to update
    it - see the remark about the symbolic values with borrows) and the
    resulting value.

    This function essentially duplicates the value while refreshing the shared
    borrow identifiers (which uniquely identify shared borrows).

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
    (ctx : eval_ctx) (v : tvalue) :
    tvalue * tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  [%ltrace
    tvalue_to_string ~span:(Some span) ctx v
    ^ "\n- context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
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
          [%craise] span "Can't copy an builtin value other than Option"
      | TAdt { id = TAdtId _; _ } as ty ->
          [%sanity_check] span (allow_adt_copy || ty_is_copyable ty)
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
          [%cassert] span (ty_is_copyable ty)
            "The type is not primitively copyable"
      | _ -> [%craise] span "Unreachable");
      let (ctx, cc), fields =
        List.fold_left_map
          (fun (ctx, cc) v ->
            let v, copied, ctx, cc1 =
              copy_value span allow_adt_copy config ctx v
            in
            ((ctx, cc_comp cc cc1), (v, copied)))
          (ctx, fun e -> e)
          av.fields
      in
      let fields, copied_fields = List.split fields in
      let copied = { v with value = VAdt { av with fields = copied_fields } } in
      let v = { v with value = VAdt { av with fields } } in
      (v, copied, ctx, cc)
  | VBottom -> [%craise] span "Can't copy ⊥"
  | VBorrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | VSharedBorrow (bid, _) ->
          (* We need to create a new borrow id for the copied borrow, and
           * update the context accordingly *)
          let sid' = ctx.fresh_shared_borrow_id () in
          ( v,
            { v with value = VBorrow (VSharedBorrow (bid, sid')) },
            ctx,
            fun e -> e )
      | VMutBorrow (_, _) -> [%craise] span "Can't copy a mutable borrow"
      | VReservedMutBorrow _ ->
          [%craise] span "Can't copy a reserved mut borrow")
  | VLoan lc -> (
      (* We can only copy shared loans *)
      match lc with
      | VMutLoan _ -> [%craise] span "Can't copy a mutable loan"
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
      [%cassert] span
        (ty_is_copyable (Substitute.erase_regions sp.sv_ty))
        "Not primitively copyable";
      (* Check if the symbolic value contains borrows: if it does, we need to
         introduce au auxiliary region abstraction (see document of the function) *)
      if not (ty_has_borrows (Some span) ctx.type_ctx.type_infos v.ty) then
        (* No borrows: do nothing *)
        (v, v, ctx, fun e -> e)
      else begin
        (* There are borrows: check that they are all live (i.e., the symbolic
           value doesn't contain bottom) *)
        [%cassert] span
          (not (symbolic_value_has_ended_regions ctx.ended_regions sp))
          "Attempted to copy a symbolic value containing ended borrows";
        let ctx0 = ctx in
        (* There are borrows: we need to introduce one region abstraction per live
           region present in the type *)
        let regions, ty =
          InterpBorrowsCore.refresh_live_regions_in_ty span ctx sp.sv_ty
        in
        let updated_sv = mk_fresh_symbolic_value span ctx ty in
        let copied_sv = mk_fresh_symbolic_value span ctx ty in

        let abs =
          List.map
            (fun rid ->
              let owned = RegionId.Set.singleton rid in

              (* Create the continuation, for the translation *)
              let abs_cont : abs_cont =
                (* Note that the values don't give back anything (we will
                   simplify the given back value to unit when translating
                   to pure) so we can simply ignore them. *)
                {
                  input = Some (mk_eignored mk_unit_ty);
                  output = Some { value = EIgnored; ty };
                }
              in

              (* Create the abstraction values *)
              let mk_proj (is_borrows : bool) sv_id : tavalue =
                let proj : symbolic_proj = { sv_id; proj_ty = ty } in
                let proj =
                  if is_borrows then AProjBorrows { proj; loans = [] }
                  else AProjLoans { proj; consumed = []; borrows = [] }
                in
                let value = ASymbolic (PNone, proj) in
                { value; ty }
              in
              let sv = mk_proj true sp.sv_id in
              let updated_sv = mk_proj false updated_sv.sv_id in
              let copied_sv = mk_proj false copied_sv.sv_id in

              let abs =
                {
                  abs_id = ctx.fresh_abs_id ();
                  kind = CopySymbolicValue;
                  can_end = true;
                  parents = AbsId.Set.empty;
                  original_parents = [];
                  regions = { owned };
                  avalues = [ sv; updated_sv; copied_sv ];
                  cont = Some abs_cont;
                }
              in
              Invariants.opt_type_check_abs span ctx abs;
              (* *)
              abs
              (*mk_abs rid [ sv; updated_sv; copied_sv ]*))
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
        ( mk_tvalue_from_symbolic_value updated_sv,
          mk_tvalue_from_symbolic_value copied_sv,
          ctx,
          cf )
      end

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
    tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Evaluate *)
  match op with
  | Constant cv -> begin
      match cv.kind with
      | CLiteral lit -> (
          (* FIXME: the str type is not in [literal_type] *)
          match cv.ty with
          | TAdt { id = TBuiltin TStr; _ } ->
              let v : tvalue = { value = VLiteral lit; ty = cv.ty } in
              (v, ctx, fun e -> e)
          | TLiteral lit_ty ->
              (literal_to_tvalue span lit_ty lit ctx, ctx, fun e -> e)
          | _ ->
              [%craise] span
                ("Encountered an incorrectly typed constant: "
                ^ constant_expr_to_string ctx cv
                ^ " : " ^ ty_to_string ctx cv.ty))
      | CTraitConst (trait_ref, const_name) ->
          let ctx0 = ctx in
          (* Simply introduce a fresh symbolic value *)
          let ty = cv.ty in
          let v = mk_fresh_symbolic_tvalue span ctx ty in
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
                [%sanity_check] span (cv = updated_value);
                (* *)
                (ctx, copied_value, cc)
            | SymbolicMode ->
                (* We use the looked up value only for its type *)
                let v = mk_fresh_symbolic_tvalue span ctx cv.ty in
                (ctx, v, fun e -> e)
          in
          (* We have to wrap the generated expression *)
          let cf e =
            (* If we are synthesizing a symbolic AST, it means that we are in symbolic
               mode: the value of the const generic is necessarily symbolic. *)
            [%sanity_check] span (is_symbolic cv.value);
            (* *)
            SymbolicAst.IntroSymbolic
              ( ctx0,
                None,
                value_as_symbolic span cv.value,
                SymbolicAst.VaCgValue vid,
                e )
          in
          (cv, ctx, cc_comp cc cf)
      | CFnDef _ -> [%craise] span "Function definitions are not supported yet"
      | CRawMemory _ ->
          [%craise] span "Raw memory cannot be interpreted by the interpreter"
      | COpaque reason ->
          [%craise] span ("Charon failed to compile constant: " ^ reason)
    end
  | Copy p ->
      (* Access the value *)
      let access = Read in
      let _, v = read_place_check span access p ctx in
      (* Sanity checks *)
      [%cassert] span
        (not (bottom_in_value ctx.ended_regions v))
        "Can not copy a value containing bottom";
      [%sanity_check] span
        (Option.is_none
           (find_first_expandable_sv_with_borrows (Some span)
              ctx.type_ctx.type_decls ctx.type_ctx.type_infos v));
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
      let _, v = read_place_check span access p ctx in
      (* Check that there are no bottoms in the value we are about to move *)
      [%cassert] span
        (not (bottom_in_value ctx.ended_regions v))
        "There should be no bottoms in the value we are about to move";
      (* Move the value *)
      let bottom : tvalue = { value = VBottom; ty = v.ty } in
      let ctx = write_place span access p bottom ctx in
      (v, ctx, fun e -> e)

let eval_operand (config : config) (span : Meta.span) (op : operand)
    (ctx : eval_ctx) :
    tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
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
    tvalue list * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Prepare the operands *)
  let ctx, cc = prepare_eval_operands_reorganize config span ops ctx in
  (* Evaluate the operands *)
  comp2 cc
    (map_apply_continuation (eval_operand_no_reorganize config span) ops ctx)

let eval_two_operands (config : config) (span : Meta.span) (op1 : operand)
    (op2 : operand) (ctx : eval_ctx) :
    (tvalue * tvalue) * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  let res, ctx, cc = eval_operands config span [ op1; op2 ] ctx in
  let res =
    match res with
    | [ v1; v2 ] -> (v1, v2)
    | _ -> [%craise] span "Unreachable"
  in
  (res, ctx, cc)

let eval_unary_op_concrete (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Evaluate the operand *)
  let v, ctx, cc = eval_operand config span op ctx in
  let ptr_size = ctx.crate.target_information.target_pointer_size in
  (* Apply the unop *)
  let r =
    match (unop, v.value) with
    | Not, VLiteral (VBool b) -> Ok { v with value = VLiteral (VBool (not b)) }
    | Not, VLiteral (VScalar i) ->
        (* The ! operator flips the bits.
           In effect, this does the operation we implement below.
        *)
        let int_ty = get_ty i in
        let x =
          if integer_type_is_signed int_ty then Z.of_int (-1)
          else scalar_max ptr_size int_ty
        in
        let value = Z.sub x (get_val i) in
        Ok
          {
            v with
            value =
              VLiteral
                (VScalar (Result.get_ok (mk_scalar ptr_size int_ty value)));
          }
    | Neg OPanic, VLiteral (VScalar sv) -> (
        let i = Z.neg (get_val sv) in
        match mk_scalar ptr_size (get_ty sv) i with
        | Error _ -> Error EPanic
        | Ok sv -> Ok { v with value = VLiteral (VScalar sv) })
    | Cast (CastScalar (src, tgt)), VLiteral (VScalar sv)
      when literal_type_is_integer src && literal_type_is_integer tgt -> (
        (* Cast between integers *)
        let src_ty, tgt_ty = (literal_as_integer src, literal_as_integer tgt) in
        [%sanity_check] span (src_ty = get_ty sv);
        let i = get_val sv in
        match mk_scalar ptr_size tgt_ty i with
        | Error _ -> Error EPanic
        | Ok sv ->
            let ty = TLiteral tgt in
            let value = VLiteral (VScalar sv) in
            Ok { ty; value })
    | Cast (CastScalar (TBool, tgt)), VLiteral (VBool sv)
      when literal_type_is_integer tgt -> (
        (* Cast bool -> int *)
        let tgt_ty = literal_as_integer tgt in
        let i = Z.of_int (if sv then 1 else 0) in
        match mk_scalar ptr_size tgt_ty i with
        | Error _ -> Error EPanic
        | Ok sv ->
            let ty = TLiteral tgt in
            let value = VLiteral (VScalar sv) in
            Ok { ty; value })
    | Cast (CastScalar (src, TBool)), VLiteral (VScalar sv)
      when literal_type_is_integer src ->
        (* Cast int -> bool *)
        let b =
          if Z.of_int 0 = get_val sv then false
          else if Z.of_int 1 = get_val sv then true
          else [%craise] span "Conversion from int to bool: out of range"
        in
        let value = VLiteral (VBool b) in
        let ty = TLiteral TBool in
        Ok { ty; value }
    | _ -> [%craise] span ("Invalid input for unop: " ^ unop_to_string ctx unop)
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
    [%craise] span (mk_msg ())
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
      [%cassert] span (id0 = id1) (mk_msg ());
      (* Retrieve the instantiated fields and make sure they are all the same
         but the last *)
      let fields_tys0 =
        Contexts.ctx_type_get_instantiated_variants_fields_etypes span ctx id0
          generics0
      in
      let fields_tys1 =
        Contexts.ctx_type_get_instantiated_variants_fields_etypes span ctx id1
          generics1
      in
      (* The ADTs should be structures *)
      let fields_tys0, fields_tys1 =
        match (fields_tys0, fields_tys1) with
        | [ (None, tys0) ], [ (None, tys1) ] -> (tys0, tys1)
        | _ -> [%craise] span (mk_msg ())
      in
      [%cassert] span
        (List.length fields_tys0 = List.length fields_tys1
        && List.length fields_tys0 > 0)
        (mk_msg ());
      let fields_tys = List.combine fields_tys0 fields_tys1 in
      let fields_beg, last_field = Collections.List.pop_last fields_tys in
      [%cassert] span
        (List.for_all (fun (ty0, ty1) -> ty0 = ty1) fields_beg)
        (mk_msg ());
      [%ldebug
        "structure cast unsized:\n- input field type: "
        ^ ty_to_string ctx (fst last_field)
        ^ "\n- output field type: "
        ^ ty_to_string ctx (snd last_field)];
      [%cassert] span (compatible_array_slice last_field) (mk_msg ());
      Some
        ( id0,
          generics0,
          FieldId.of_int (List.length fields_beg),
          fst last_field,
          snd last_field ))
    else [%craise] span (mk_msg ())

let eval_unary_op_symbolic (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Evaluate the operand *)
  let v, ctx, cc = eval_operand config span op ctx in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = ctx.fresh_symbolic_value_id () in
  let res_sv_ty =
    match (unop, v.ty) with
    | Not, (TLiteral TBool as lty) -> lty
    | Not, (TLiteral (TInt _) as lty) -> lty
    | Not, (TLiteral (TUInt _) as lty) -> lty
    | Neg OPanic, (TLiteral (TInt _) as lty) -> lty
    | Neg OPanic, (TLiteral (TUInt _) as lty) -> lty
    | Cast (CastScalar (_, tgt_ty)), _ -> TLiteral tgt_ty
    | Cast (CastUnsize (ty0, ty1, _)), _ ->
        (* If the following function succeeds, then it means the cast is well-formed
           (otherwise it throws an exception) *)
        let _ = cast_unsize_to_modified_fields span ctx ty0 ty1 in
        ty1
    | _ ->
        [%craise] span
          ("Invalid input for unop: " ^ unop_to_string ctx unop ^ " on "
         ^ ty_to_string ctx v.ty)
  in
  let res_sv = { sv_id = res_sv_id; sv_ty = res_sv_ty } in
  (* Compute the result *)
  let res = Ok (mk_tvalue_from_symbolic_value res_sv) in
  (* Synthesize the symbolic AST *)
  let cc =
    cc_comp cc
      (synthesize_unary_op span ctx unop v
         (mk_opt_place_from_op span op ctx)
         res_sv None)
  in
  (res, ctx, cc)

let eval_unary_op (config : config) (span : Meta.span) (unop : unop)
    (op : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  match config.mode with
  | ConcreteMode -> eval_unary_op_concrete config span unop op ctx
  | SymbolicMode -> eval_unary_op_symbolic config span unop op ctx

(** Small helper for [eval_binary_op_concrete]: computes the result of applying
    the binop *after* the operands have been successfully evaluated *)
let eval_binary_op_concrete_compute (span : Meta.span) (binop : binop)
    (v1 : tvalue) (v2 : tvalue) (ctx : eval_ctx) : (tvalue, eval_error) result =
  (* Equality check binops (Eq, Ne) accept values from a wide variety of types.
   * The remaining binops only operate on scalars. *)
  if binop = Eq || binop = Ne then (
    (* Equality operations *)
    [%cassert] span (v1.ty = v2.ty)
      "The arguments given to the binop don't have the same type";
    (* Equality/inequality check is primitive only for a subset of types *)
    [%cassert] span (ty_is_copyable v1.ty) "Type is not primitively copyable";
    let b = v1 = v2 in
    Ok { value = VLiteral (VBool b); ty = TLiteral TBool })
  else
    (* For the non-equality operations, the input values are necessarily scalars *)
    match (v1.value, v2.value) with
    | VLiteral (VScalar sv1), VLiteral (VScalar sv2) -> begin
        let ptr_size = ctx.crate.target_information.target_pointer_size in
        let sv1_value, sv2_value = (get_val sv1, get_val sv2) in
        let sv1_int_ty, sv2_int_ty = (get_ty sv1, get_ty sv2) in
        (* There are binops which require the two operands to have the same
           type, and binops for which it is not the case.
           There are also binops which return booleans, and binops which
           return integers.
        *)
        match binop with
        | Lt | Le | Ge | Gt ->
            (* The two operands must have the same type and the result is a boolean *)
            [%sanity_check] span (sv1_int_ty = sv2_int_ty);
            let b =
              match binop with
              | Lt -> Z.lt sv1_value sv2_value
              | Le -> Z.leq sv1_value sv2_value
              | Ge -> Z.geq sv1_value sv2_value
              | Gt -> Z.gt sv1_value sv2_value
              | _ -> [%craise] span "Unreachable"
            in
            Ok ({ value = VLiteral (VBool b); ty = TLiteral TBool } : tvalue)
        | Div OPanic
        | Rem OPanic
        | Add OPanic
        | Sub OPanic
        | Mul OPanic
        | BitXor | BitAnd | BitOr -> (
            (* The two operands must have the same type and the result is an integer *)
            [%sanity_check] span (sv1_int_ty = sv2_int_ty);
            let res : _ result =
              match binop with
              | Div OPanic ->
                  if sv2_value = Z.zero then Error ()
                  else mk_scalar ptr_size sv1_int_ty (Z.div sv1_value sv2_value)
              | Rem OPanic ->
                  (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                  if sv2_value = Z.zero then Error ()
                  else mk_scalar ptr_size sv1_int_ty (Z.rem sv1_value sv2_value)
              | Add OPanic ->
                  mk_scalar ptr_size sv1_int_ty (Z.add sv1_value sv2_value)
              | Sub OPanic ->
                  mk_scalar ptr_size sv1_int_ty (Z.sub sv1_value sv2_value)
              | Mul OPanic ->
                  mk_scalar ptr_size sv1_int_ty (Z.mul sv1_value sv2_value)
              | BitXor -> raise Unimplemented
              | BitAnd -> raise Unimplemented
              | BitOr -> raise Unimplemented
              | _ -> [%craise] span "Unreachable"
            in
            match res with
            | Error _ -> Error EPanic
            | Ok sv ->
                Ok
                  {
                    value = VLiteral (VScalar sv);
                    ty = TLiteral (integer_as_literal sv1_int_ty);
                  })
        | Ne | Eq -> [%craise] span "Unreachable"
        | _ ->
            [%craise] span
              ("Unimplemented binary operation: " ^ binop_to_string binop)
      end
    | _ -> [%craise] span ("Invalid inputs for binop: " ^ binop_to_string binop)

let eval_binary_op_concrete (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Evaluate the operands *)
  let (v1, v2), ctx, cc = eval_two_operands config span op1 op2 ctx in
  (* Compute the result of the binop *)
  let r = eval_binary_op_concrete_compute span binop v1 v2 ctx in
  (* Return *)
  (r, ctx, cc)

let eval_binary_op_symbolic (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Evaluate the operands *)
  let (v1, v2), ctx, cc = eval_two_operands config span op1 op2 ctx in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = ctx.fresh_symbolic_value_id () in
  let res_sv_ty =
    if binop = Eq || binop = Ne then (
      (* Equality operations *)
      [%sanity_check] span (v1.ty = v2.ty);
      (* Equality/inequality check is primitive only for a subset of types *)
      [%cassert] span (ty_is_copyable v1.ty)
        "The type is not primitively copyable";
      TLiteral TBool)
    else
      (* Other operations: input types are integers *)
      match (v1.ty, v2.ty) with
      | TLiteral lty1, TLiteral lty2
        when literal_type_is_integer lty1 && literal_type_is_integer lty2 -> (
          let int_ty1, int_ty2 = (ty_as_integer v1.ty, ty_as_integer v2.ty) in
          match binop with
          | Lt | Le | Ge | Gt ->
              [%sanity_check] span (int_ty1 = int_ty2);
              TLiteral TBool
          | Div _ | Rem _ | Add _ | Sub _ | Mul _ | BitXor | BitAnd | BitOr ->
              [%sanity_check] span (int_ty1 = int_ty2);
              TLiteral (integer_as_literal int_ty1)
          | Cmp ->
              [%sanity_check] span (int_ty1 = int_ty2);
              TLiteral (TInt I8)
          (* These return `(int, bool)` / a pointer which isn't a literal type *)
          | AddChecked | SubChecked | MulChecked | Offset ->
              [%craise] span "Unimplemented binary operation"
          | Shl _ | Shr _ ->
              (* The number of bits can be of a different integer type
                 than the operand *)
              TLiteral (integer_as_literal int_ty1)
          | Ne | Eq -> [%craise] span "Unreachable")
      | _ -> [%craise] span "Invalid inputs for binop"
  in
  let res_sv = { sv_id = res_sv_id; sv_ty = res_sv_ty } in
  let v = mk_tvalue_from_symbolic_value res_sv in
  (* Synthesize the symbolic AST *)
  let p1 = mk_opt_place_from_op span op1 ctx in
  let p2 = mk_opt_place_from_op span op2 ctx in
  let cc =
    cc_comp cc (synthesize_binary_op span ctx binop v1 p1 v2 p2 res_sv None)
  in
  (* Compose and apply *)
  (Ok v, ctx, cc)

let eval_binary_op (config : config) (span : Meta.span) (binop : binop)
    (op1 : operand) (op2 : operand) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  match config.mode with
  | ConcreteMode -> eval_binary_op_concrete config span binop op1 op2 ctx
  | SymbolicMode -> eval_binary_op_symbolic config span binop op1 op2 ctx

(** Evaluate an rvalue which creates a reference (i.e., an rvalue which is `&p`
    or `&mut p` or `&two-phase p`) *)
let eval_rvalue_ref (config : config) (span : Meta.span) (p : place)
    (bkind : borrow_kind) (ctx : eval_ctx) :
    tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  match bkind with
  | BUniqueImmutable ->
      [%craise] span "Unique immutable closure captures are not supported"
  | BShared | BTwoPhaseMut | BShallow ->
      (* **REMARK**: we initially treated shallow borrows like shared borrows.
         In practice this restricted the behaviour too much, so for now we
         forbid them and remove them in the prepasses (see the comments there
         as to why this is sound).
      *)
      [%sanity_check] span (bkind <> BShallow);

      (* Access the value *)
      let access =
        match bkind with
        | BShared | BShallow -> Read
        | BTwoPhaseMut -> Write
        | _ -> [%craise] span "Unreachable"
      in

      let greedy_expand = false in
      let lid, v, ctx, cc =
        access_rplace_reorganize_and_read config span greedy_expand access p ctx
      in
      (* Generate the fresh shared borrow id *)
      let sid = ctx.fresh_shared_borrow_id () in
      (* Compute the loan value, with which to replace the value at place p *)
      let bid, nv =
        match (lid, v.value) with
        | Some lid, _ | None, VLoan (VSharedLoan (lid, _)) ->
            (* The value is (directly inside) a shared loan: we do not need to do anything *)
            (lid, v)
        | _ ->
            (* Not a shared loan: add a wrapper *)
            let bid = ctx.fresh_borrow_id () in
            let v' = VLoan (VSharedLoan (bid, v)) in
            (bid, { v with value = v' })
      in
      (* Update the value in the context to replace it with the loan *)
      let ctx = write_place span access p nv ctx in
      (* Compute the rvalue - simply a shared borrow with the fresh id.
       * Note that the reference is *mutable* if we do a two-phase borrow *)
      let ref_kind =
        match bkind with
        | BShared | BShallow -> RShared
        | BTwoPhaseMut -> RMut
        | _ -> [%craise] span "Unreachable"
      in
      let rv_ty = TRef (RErased, v.ty, ref_kind) in
      let bc =
        match bkind with
        | BShared | BShallow ->
            (* See the remark at the beginning of the match branch: we
               handle shallow borrows like shared borrows *)
            VSharedBorrow (bid, sid)
        | BTwoPhaseMut -> VReservedMutBorrow (bid, sid)
        | _ -> [%craise] span "Unreachable"
      in
      let rv : tvalue = { value = VBorrow bc; ty = rv_ty } in
      (* Return *)
      (rv, ctx, cc)
  | BMut ->
      (* Access the value *)
      let access = Write in
      let greedy_expand = false in
      let _, v, ctx, cc =
        access_rplace_reorganize_and_read config span greedy_expand access p ctx
      in
      (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
      let bid = ctx.fresh_borrow_id () in
      let rv_ty = TRef (RErased, v.ty, RMut) in
      let rv : tvalue = { value = VBorrow (VMutBorrow (bid, v)); ty = rv_ty } in
      (* Compute the loan value with which to replace the value at place p *)
      let nv = { v with value = VLoan (VMutLoan bid) } in
      (* Update the value in the context to replace it with the loan *)
      let ctx = write_place span access p nv ctx in
      (* Return *)
      (rv, ctx, cc)

let eval_rvalue_aggregate (config : config) (span : Meta.span)
    (aggregate_kind : aggregate_kind) (ops : operand list) (ctx : eval_ctx) :
    tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Evaluate the operands *)
  let values, ctx, cc = eval_operands config span ops ctx in
  (* Compute the value *)
  let v, cf_compute =
    (* Match on the aggregate kind *)
    match aggregate_kind with
    | AggregatedAdt ({ id = type_id; generics }, opt_variant_id, opt_field_id)
      -> (
        (* The opt_field_id is Some only for unions, that we don't support *)
        [%sanity_check] span (opt_field_id = None);
        match type_id with
        | TTuple ->
            let tys = List.map (fun (v : tvalue) -> v.ty) values in
            let v = VAdt { variant_id = None; fields = values } in
            let generics = mk_generic_args [] tys [] [] in
            let ty = TAdt { id = TTuple; generics } in
            let aggregated : tvalue = { value = v; ty } in
            (aggregated, fun e -> e)
        | TAdtId def_id ->
            (* Sanity checks *)
            let type_decl = ctx_lookup_type_decl span ctx def_id in
            [%sanity_check] span
              (List.length type_decl.generics.regions
              = List.length generics.regions);
            let expected_field_types =
              ctx_type_get_instantiated_field_etypes span ctx def_id
                opt_variant_id generics
            in
            [%sanity_check] span
              (expected_field_types = List.map (fun (v : tvalue) -> v.ty) values);
            (* Construct the value *)
            let av : adt_value =
              { variant_id = opt_variant_id; fields = values }
            in
            let aty = TAdt { id = TAdtId def_id; generics } in
            let aggregated : tvalue = { value = VAdt av; ty = aty } in
            (* Call the continuation *)
            (aggregated, fun e -> e)
        | TBuiltin _ -> [%craise] span "Unreachable")
    | AggregatedArray (ety, cg) ->
        (* Sanity check: all the values have the proper type *)
        [%classert] span
          (List.for_all (fun (v : tvalue) -> v.ty = ety) values)
          (lazy
            ("Aggregated array: some values don't have the proper type:"
           ^ "\n- expected type: " ^ ty_to_string ctx ety ^ "\n- values: ["
            ^ String.concat ", "
                (List.map
                   (fun (v : tvalue) ->
                     tvalue_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
                   values)
            ^ "]"));
        (* Sanity check: the number of values is consistent with the length *)
        let len = get_val (literal_as_scalar (const_generic_as_literal cg)) in
        [%sanity_check] span (len = Z.of_int (List.length values));
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
          let value = VAdt { variant_id = None; fields = values } in
          let value : tvalue = { value; ty } in
          (value, fun e -> e)
        else
          let saggregated = mk_fresh_symbolic_tvalue span ctx ty in
          (* Update the symbolic ast *)
          let cf e =
            (* Introduce the symbolic value in the AST *)
            let sv = ValuesUtils.value_as_symbolic span saggregated.value in
            SymbolicAst.IntroSymbolic (ctx, None, sv, VaArray values, e)
          in
          (saggregated, cf)
    | AggregatedRawPtr _ ->
        [%craise] span "Aggregated raw pointers are not supported yet"
  in
  (v, ctx, cc_comp cc cf_compute)

let eval_rvalue_not_global (config : config) (span : Meta.span)
    (rvalue : rvalue) (ctx : eval_ctx) :
    (tvalue, eval_error) result
    * eval_ctx
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  [%ltrace ""];
  (* Small helper *)
  let wrap_in_result (v, ctx, cc) = (Ok v, ctx, cc) in
  (* Delegate to the proper auxiliary function *)
  match rvalue with
  | Use op -> wrap_in_result (eval_operand config span op ctx)
  | RvRef (p, bkind, _) ->
      wrap_in_result (eval_rvalue_ref config span p bkind ctx)
  | UnaryOp (unop, op) -> eval_unary_op config span unop op ctx
  | BinaryOp (binop, op1, op2) -> eval_binary_op config span binop op1 op2 ctx
  | Aggregate (aggregate_kind, ops) ->
      wrap_in_result (eval_rvalue_aggregate config span aggregate_kind ops ctx)
  | Discriminant _ ->
      [%craise] span
        "Unreachable: discriminant reads should have been eliminated from the \
         AST"
  | Len _ -> [%craise] span "Unhandled Len"
  | _ ->
      [%craise] span
        ("Unsupported operation: " ^ Print.EvalCtx.rvalue_to_string ctx rvalue)

let eval_fake_read (config : config) (span : Meta.span) (p : place) : cm_fun =
 fun ctx ->
  let greedy_expand = false in
  let _, v, ctx, cc =
    access_rplace_reorganize_and_read config span greedy_expand Read p ctx
  in
  [%cassert] span
    (not (bottom_in_value ctx.ended_regions v))
    "Fake read: the value contains bottom";
  (ctx, cc)
