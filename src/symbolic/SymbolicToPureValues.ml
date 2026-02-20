open Pure
open PureUtils
open SymbolicToPureCore
open SymbolicToPureTypes

(** The local logger *)
let log = Logging.symbolic_to_pure_values_log

(** WARNING: do not call this function directly when translating symbolic values
    from LLBC. Call [fresh_named_var_for_symbolic_value] instead: it will
    register the mapping from the LLBC symbolic value to the (fresh) pure
    symbolic value. *)
let fresh_var_llbc_ty (basename : string option) (ty : T.ty) (ctx : bs_ctx) :
    bs_ctx * fvar =
  let ty = ctx_translate_fwd_ty ctx ty in
  fresh_var basename ty ctx

let fresh_named_var_for_symbolic_value (basename : string option)
    (sv : V.symbolic_value) (ctx : bs_ctx) : bs_ctx * fvar =
  (* Generate the fresh variable *)
  let ctx, var = fresh_var_llbc_ty basename sv.sv_ty ctx in
  (* Insert in the map from symbolic value to variable *)
  let sv_to_var = V.SymbolicValueId.Map.add sv.sv_id var ctx.sv_to_var in
  (* Update the context *)
  let ctx = { ctx with sv_to_var } in
  (* Return *)
  (ctx, var)

let fresh_var_for_symbolic_value (sv : V.symbolic_value) (ctx : bs_ctx) :
    bs_ctx * fvar =
  fresh_named_var_for_symbolic_value None sv ctx

let fresh_vars_for_symbolic_values (svl : V.symbolic_value list) (ctx : bs_ctx)
    : bs_ctx * fvar list =
  List.fold_left_map (fun ctx sv -> fresh_var_for_symbolic_value sv ctx) ctx svl

let fresh_named_vars_for_symbolic_values
    (svl : (string option * V.symbolic_value) list) (ctx : bs_ctx) :
    bs_ctx * fvar list =
  List.fold_left_map
    (fun ctx (name, sv) -> fresh_named_var_for_symbolic_value name sv ctx)
    ctx svl

(** Translate a symbolic value.

    Because we do not necessarily introduce variables for the symbolic values of
    (translated) type unit, it is important that we do not lookup variables in
    case the symbolic value has type unit. *)
let symbolic_value_to_texpr (ctx : bs_ctx) (sv : V.symbolic_value) : texpr =
  (* Translate the type *)
  let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
  (* If the type is unit, directly return unit *)
  if ty_is_unit ty then mk_unit_texpr
  else
    (* Otherwise lookup the variable *)
    match lookup_var_for_symbolic_value sv.sv_id ctx with
    | Some var -> mk_texpr_from_fvar var
    | None ->
        {
          e =
            EError
              ( None,
                "Could not find var for symbolic value: "
                ^ V.SymbolicValueId.to_string sv.sv_id );
          ty;
        }

(** Translate a typed value.

    It is used, for instance, on values used as inputs for function calls.

    **IMPORTANT**: this function makes the assumption that the typed value
    doesn't contain ⊥. This means in particular that symbolic values don't
    contain ended regions.

    TODO: we might want to remember in the symbolic AST the set of ended
    regions, at the points where we need it, for sanity checks (though the
    sanity checks in the symbolic interpreter should be enough). The points
    where we need this set so far:
    - function call
    - end abstraction
    - return *)
let rec tvalue_to_texpr (ctx : bs_ctx) (ectx : C.eval_ctx) (v : V.tvalue) :
    texpr =
  (* We need to ignore boxes *)
  let v = ValuesUtils.unbox_tvalue ctx.span v in
  let translate = tvalue_to_texpr ctx ectx in
  (* Translate the type *)
  let ty = ctx_translate_fwd_ty ctx v.ty in
  (* Translate the value *)
  let value =
    match v.value with
    | VLiteral cv ->
        let cv = translate_literal cv in
        { e = Const cv; ty }
    | VAdt av -> (
        let variant_id = av.variant_id in
        let fields = List.map translate av.fields in
        (* Eliminate the tuple wrapper if it is a tuple with exactly one field *)
        match v.ty with
        | TAdt { id = TTuple; _ } ->
            [%sanity_check] ctx.span (variant_id = None);
            mk_simpl_tuple_texpr ctx.span fields
        | _ ->
            (* Retrieve the type and the translated generics from the translated
               type (simpler this way) *)
            let adt_id, generics = ty_as_adt ctx.span ty in
            (* Create the constructor *)
            let qualif_id = AdtCons { adt_id; variant_id = av.variant_id } in
            let qualif = { id = qualif_id; generics } in
            let cons_e = Qualif qualif in
            let field_tys = List.map (fun (v : texpr) -> v.ty) fields in
            let cons_ty = mk_arrows field_tys ty in
            let cons = { e = cons_e; ty = cons_ty } in
            (* Apply the constructor *)
            [%add_loc] mk_apps ctx.span cons fields)
    | VBottom -> [%craise] ctx.span "Unexpected bottom value"
    | VLoan lc -> (
        match lc with
        | VSharedLoan (_, v) -> translate v
        | VMutLoan _ -> [%craise] ctx.span "Unreachable")
    | VBorrow bc -> (
        match bc with
        | VSharedBorrow (bid, _) ->
            (* Lookup the shared value in the context, and continue *)
            let sv =
              InterpBorrowsCore.ctx_lookup_shared_value ctx.span ectx bid
            in
            translate sv
        | VReservedMutBorrow (bid, _) ->
            (* Same as for shared borrows. However, note that we use reserved borrows
             * only in *meta-data*: a value *actually used* in the translation can't come
             * from an unpromoted reserved borrow *)
            let sv =
              InterpBorrowsCore.ctx_lookup_shared_value ctx.span ectx bid
            in
            translate sv
        | VMutBorrow (_, v) ->
            (* Borrows are the identity in the extraction *)
            translate v)
    | VSymbolic sv -> symbolic_value_to_texpr ctx sv
  in
  (* Debugging *)
  [%ltrace
    "result:" ^ "\n- input value:\n" ^ tvalue_to_string ctx v
    ^ "\n- translated expression:\n" ^ texpr_to_string ctx value];
  (* Sanity check *)
  type_check_texpr ctx value;
  (* Return *)
  value

type borrow_kind = BMut | BShared [@@deriving show]

(** An avalue/evalue is either produced from a borrow projector (if it is an
    input to a function) or from a loan projector (if it is an ouptput). This
    means that an avalue has either:
    - only borrows and borrow projections over symbolic values
    - only loans and loan projections over symbolic values
    - none of those

    **REMARK:** this will not be valid anymore once we have nested borrows, as
    an ended proj loan can contain borrows in one of its children. In this
    situation, we will need to first project the avalues at the proper level,
    before translating them. *)
type proj_kind =
  | BorrowProj of borrow_kind
      (** The value was produced by a borrow projector (it contains borrows or
          borrow projections).

          The kind is [BMut] if we found at least one (non-ignored) mutable
          borrow, [BShared] otherwise. *)
  | LoanProj of borrow_kind
      (** The value was produced by a loan projector (it contains loans or loan
          projections).

          The kind is [BMut] if we found at least one (non-ignored) mutable
          loan, [BShared] otherwise. *)
  | UnknownProj
      (** No borrows, loans or projections inside the value so we can't know for
          sure *)
[@@deriving show]

let compute_tavalue_proj_kind span type_infos (abs_regions : T.RegionId.Set.t)
    (abs_level : abs_level) (current_level : abs_level) (av : V.tavalue) :
    proj_kind =
  let has_borrows = ref false in
  let has_mut_borrows = ref false in
  let has_loans = ref false in
  let has_mut_loans = ref false in

  let set_has_loans level = if level = abs_level then has_loans := true in
  let set_has_borrows level = if level = abs_level then has_borrows := true in
  let set_has_mut_loans level =
    if level = abs_level then (
      has_loans := true;
      has_mut_loans := true)
  in
  let set_has_mut_borrows level =
    if level = abs_level then (
      has_borrows := true;
      has_mut_borrows := true)
  in

  let keep_region (r : T.region) =
    match r with
    | T.RVar (Free rid) -> T.RegionId.Set.mem rid abs_regions
    | _ -> false
  in
  let ty_has_mut_region =
    TypesUtils.ty_has_mut_borrow_for_region_in_pred type_infos keep_region
  in
  let visitor =
    object
      inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
      method incr_level (level, ty) = (level + 1, ty)

      method! visit_tavalue (level, _) av =
        (* Remember the type of the current value *)
        super#visit_tavalue (level, av.ty) av

      method! visit_adt_avalue (level, ty) av =
        if ty_has_mut_region ty then
          if
            (* TODO: problem with nested borrows *)
            av.borrow_proj
          then set_has_mut_borrows level
          else set_has_mut_loans level;
        super#visit_adt_avalue (level, ty) av

      method! visit_ALoan (level, ty) lc =
        set_has_loans level;
        begin
          match lc with
          | ASharedLoan _
          | AEndedSharedLoan _
          | AIgnoredMutLoan _
          | AEndedIgnoredMutLoan _
          | AIgnoredSharedLoan _ -> ()
          | AMutLoan _ | AEndedMutLoan _ -> set_has_mut_loans level
        end;
        (* Continue exploring as a sanity check: we want to make sure we don't find borrows *)
        super#visit_ALoan (level, ty) lc

      method! visit_ABorrow (level, ty) bc =
        set_has_borrows level;
        begin
          match bc with
          | ASharedBorrow _
          | AEndedSharedBorrow
          | AIgnoredMutBorrow _
          | AEndedIgnoredMutBorrow _
          | AProjSharedBorrow _ -> ()
          | AMutBorrow _ | AEndedMutBorrow _ -> set_has_mut_borrows level
        end;
        (* Continue exploring as a sanity check: we want to make sure we don't find loans *)
        super#visit_ABorrow (level, ty) bc

      method! visit_ASymbolic (level, ty) pm aproj =
        [%sanity_check] span (pm = PNone);
        (* TODO: levels may be wrong here *)
        (* We forbid nested mutable borrows for now *)
        let info = TypesAnalysis.analyze_ty (Some span) type_infos ty in
        [%cassert] span (not info.contains_nested_mut) "Unimplemented";
        match aproj with
        | V.AEndedProjLoans _ ->
            set_has_loans level;
            (* We need to check wether the projected loans are mutable or not *)
            if ty_has_mut_region ty then set_has_mut_loans level;
            (* Continue exploring (same reasons as above) *)
            super#visit_ASymbolic (level, ty) pm aproj
        | AProjLoans _ ->
            set_has_loans level;
            (* We need to check wether the projected loans are mutable or not *)
            if ty_has_mut_region ty then set_has_mut_loans level;
            (* Continue exploring (same reasons as above) *)
            super#visit_ASymbolic (level, ty) pm aproj
        | AEndedProjBorrows _ ->
            set_has_borrows level;
            (* We need to check wether the projected borrows are mutable or not *)
            if ty_has_mut_region ty then set_has_mut_borrows level;
            (* Continue exploring (same reasons as above) *)
            super#visit_ASymbolic (level, ty) pm aproj
        | AProjBorrows _ ->
            set_has_borrows level;
            (* We need to check wether the projected borrows are mutable or not *)
            if ty_has_mut_region ty then set_has_mut_borrows level;
            (* Continue exploring (same reasons as above) *)
            super#visit_ASymbolic (level, ty) pm aproj
        | AEmpty ->
            (* Continue exploring (same reasons as above) *)
            super#visit_ASymbolic (level, ty) pm aproj
    end
  in
  visitor#visit_tavalue (current_level, av.ty) av;
  [%cassert] span ((not !has_borrows) || not !has_loans) "Unreachable";
  let to_borrow_kind b = if b then BMut else BShared in
  if !has_borrows then BorrowProj (to_borrow_kind !has_mut_borrows)
  else if !has_loans then LoanProj (to_borrow_kind !has_mut_loans)
  else UnknownProj

(** A smaller helper which allows us to isolate the logic by which we handle
    ADTs. *)
let gtranslate_adt_fields ~(project_borrows : bool)
    (input_to_string : 'v -> string) (output_to_string : 'o -> string)
    (translate : filter:bool -> bs_ctx -> 'v -> bs_ctx * ('info * 'o) option)
    (compute_proj_kind : 'v -> proj_kind) (mk_adt : 'o list -> 'o)
    (mk_tuple : 'o list -> 'o) ~(filter : bool) (ctx : bs_ctx) (av : 'v)
    (av_ty : T.ty) (fields : 'v list) : bs_ctx * ('info list * 'o) option =
  let span = ctx.span in
  (* We do not do the same thing depending on whether we visit a tuple
     or a "regular" ADT *)
  let adt_id, _ = TypesUtils.ty_as_adt av_ty in
  (* Check if the ADT contains borrows *)
  let proj_kind = compute_proj_kind av in
  [%ldebug
    "- filter: " ^ string_of_bool filter ^ "\n- av: " ^ input_to_string av
    ^ "\n- av_ty: " ^ ty_to_string ctx av_ty ^ "\n- proj_kind: "
    ^ show_proj_kind proj_kind];
  match proj_kind with
  | UnknownProj when filter ->
      [%ldebug "UnknownProj && filter"];
      (* If we filter: ignore the value.
         Otherwise, translate everything (case below). *)
      (ctx, None)
  | UnknownProj | BorrowProj _ | LoanProj _ -> begin
      [%ldebug "not (UnknownProj && filter)"];
      begin
        match proj_kind with
        | BorrowProj _ -> [%sanity_check] span project_borrows
        | LoanProj _ -> [%sanity_check] span (not project_borrows)
        | UnknownProj -> ()
      end;

      (* Translate the field values *)
      let filter_fields =
        filter
        &&
        match adt_id with
        | TTuple | TBuiltin TBox -> true
        | TBuiltin _ | TAdtId _ -> (
            match proj_kind with
            | UnknownProj | BorrowProj BShared | LoanProj BShared -> true
            | _ -> false)
      in
      let ctx, info_fields =
        List.fold_left_map (translate ~filter:filter_fields) ctx fields
      in
      [%ldebug
        "- input fields (length: "
        ^ string_of_int (List.length fields)
        ^ "):\n"
        ^ String.concat "\n" (List.map input_to_string fields)
        ^ "\n- output fields:\n"
        ^ String.concat "\n"
            (List.map
               (Print.option_to_string (fun (_, x) -> output_to_string x))
               info_fields)];
      match adt_id with
      | TAdtId _ ->
          if filter_fields then (
            [%sanity_check] span (List.for_all Option.is_none info_fields);
            (ctx, None))
          else
            (* We should preserve all the fields *)
            let infos, fields =
              List.split (List.map ([%try_unwrap] span) info_fields)
            in
            let pat = mk_adt fields in
            (ctx, Some (infos, pat))
      | TBuiltin TBox -> begin
          (* The box type becomes the identity in the translation *)
          match info_fields with
          | [ None ] -> (ctx, None)
          | [ Some (info, v) ] -> (ctx, Some ([ info ], v))
          | _ -> [%craise] span "Unreachable"
        end
      | TBuiltin TStr ->
          (* This case is unreachable:
             - for strings: the [str] is not polymorphic.
          *)
          [%craise] span "Unreachable"
      | TTuple ->
          (* If the filtering is activated, we ignore the fields which do not
             consume values (i.e., which do not contain ended mutable borrows). *)
          if filter then
            let info_fields = List.filter_map (fun x -> x) info_fields in
            if info_fields = [] then (ctx, None)
            else
              (* Note that if there is exactly one field value,
               * [mk_simpl_tuple_rvalue] is the identity *)
              let info, fields = List.split info_fields in
              (ctx, Some (info, mk_tuple fields))
          else
            (* If we do not filter the fields, all the values should be [Some ...] *)
            let infos, fields =
              List.split (List.map ([%option_get] span) info_fields)
            in
            (ctx, Some (infos, mk_tuple fields))
    end

(** Explore an abstraction value and convert it to a consumed value by
    collecting all the meta-values from the ended *loans*. We assume the avalue
    was generated by a loan projector.

    Consumed values are rvalues because when an abstraction ends we introduce a
    call to a backward function in the synthesized program, which takes as
    inputs those consumed values:
    {[
      // Rust:
      fn choose<'a>(b: bool, x : &'a mut u32, y : &'a mut u32) -> &'a mut u32;

      // Synthesis:
      let ... = choose_back b x y nz in
                                  ^^
    ]} *)
let rec tavalue_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (av : V.tavalue) : texpr option =
  let value =
    match av.value with
    | AAdt adt_v ->
        adt_avalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          current_level av adt_v
    | ALoan lc ->
        aloan_content_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          current_level lc
    | ABorrow bc ->
        aborrow_content_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          current_level bc
    | ASymbolic (pm, aproj) ->
        [%sanity_check] ctx.span (pm = PNone);
        aproj_to_consumed_aux ctx abs_regions abs_level current_level aproj
          av.ty
    | AIgnored mv -> (
        if filter then None
        else
          (* If we do not filter it means we are inside an ADT: in this case,
             the meta-value was produced by a projector (and not introduced
             because of a join, because when doing joins we destructure the
             values): there **must** be a meta-value. The consumed value
             is the meta-value. *)
          match mv with
          | None -> [%craise] ctx.span "Unreachable"
          | Some mv -> Some (tvalue_to_texpr ctx ectx mv))
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_texpr ctx value);
  (* Return *)
  value

and adt_avalue_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (av : V.tavalue) (adt_v : V.adt_avalue) :
    texpr option =
  let _, out =
    gtranslate_adt_fields ~project_borrows:false (tavalue_to_string ctx)
      (texpr_to_string ctx)
      (fun ~filter ctx v ->
        ( ctx,
          match
            tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
              current_level v
          with
          | None -> None
          | Some x -> Some ((), x) ))
      (compute_tavalue_proj_kind ctx.span ctx.type_ctx.type_infos abs_regions
         abs_level current_level)
      (fun fields ->
        let ty = translate_fwd_ty (Some ctx.span) ctx.decls_ctx av.ty in
        mk_adt_texpr ctx.span ty adt_v.variant_id fields)
      (mk_simpl_tuple_texpr ctx.span)
      ~filter ctx av av.ty adt_v.fields
  in
  Option.map snd out

and aloan_content_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (lc : V.aloan_content) : texpr option =
  match lc with
  | AMutLoan (_, _, _) | ASharedLoan (_, _, _, _) ->
      [%craise] ctx.span "Unreachable"
  | AEndedMutLoan { child; given_back; given_back_meta } ->
      if abs_level = current_level then (
        [%cassert] ctx.span (ValuesUtils.is_aignored child.value) "Unreachable";
        [%cassert] ctx.span
          (ValuesUtils.is_aignored given_back.value)
          "Unreachable";
        (* Return the meta-value *)
        Some (tvalue_to_texpr ctx ectx given_back_meta))
      else
        let child =
          tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
            current_level child
        in
        let given_back =
          tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
            (current_level + 1) given_back
        in
        [%cassert] ctx.span (child = None) "Unimplemented";
        [%cassert] ctx.span (given_back = None) "Unimplemented";
        None
  | AEndedSharedLoan (sv, child) ->
      [%cassert] ctx.span (ValuesUtils.is_aignored child.value) "Unreachable";
      (* We don't dive into shared loans: there is nothing to give back
         inside (note that there could be a mutable borrow in the shared
         value, pointing to a mutable loan in the child avalue, but this
         borrow is in practice immutable) *)
      if filter then None else Some (tvalue_to_texpr ctx ectx sv)
  | AIgnoredMutLoan (_, _) ->
      (* There can be *inner* non ended mutable loans, but not outer ones *)
      [%craise] ctx.span "Unreachable"
  | AEndedIgnoredMutLoan { child; given_back; given_back_meta = _ } -> (
      (* This happens with nested borrows: we need to dive in *)
      let child =
        tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          current_level child
      in
      let given_back =
        tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          (current_level + 1) given_back
      in
      match (child, given_back) with
      | Some v, None | None, Some v -> Some v
      | None, None -> None
      | _ ->
          (* Is this unreachable? *)
          [%craise] ctx.span "Unimplemented")
  | AIgnoredSharedLoan _ ->
      (* This case happens with nested borrows *)
      [%craise] ctx.span "Unimplemented"

and aborrow_content_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (bc : V.aborrow_content) : texpr option =
  match bc with
  | V.AMutBorrow (_, _, child) | V.AIgnoredMutBorrow (_, child) ->
      (* Can happen with nested borrows, when ending sub-abstractions *)
      tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
        current_level child
  | V.ASharedBorrow _ -> None
  | V.AEndedMutBorrow (_, _) ->
      (* TODO? *)
      None
  | V.AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } -> (
      let child =
        tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          current_level child
      in
      let given_back =
        tavalue_to_consumed_aux ~filter ctx ectx abs_regions abs_level
          (current_level + 1) given_back
      in
      match (child, given_back) with
      | Some v, None | None, Some v -> Some v
      | None, None -> None
      | _ ->
          (* TODO: unreachable? *)
          [%craise] ctx.span "Unimplemented")
  | V.AEndedSharedBorrow | V.AProjSharedBorrow _ ->
      [%craise] ctx.span "Unimplemented"

and aproj_to_consumed_aux (ctx : bs_ctx) (_abs_regions : T.RegionId.Set.t)
    (abs_level : abs_level) (current_level : abs_level) (aproj : V.aproj)
    (ty : T.ty) : texpr option =
  match aproj with
  | V.AEndedProjLoans { proj = msv; consumed = []; borrows = [] } ->
      if abs_level = current_level then
        (* The symbolic value was left unchanged.

           We're using the projection type as the type of the symbolic value -
           it doesn't really matter. *)
        let msv : V.symbolic_value = { sv_id = msv; sv_ty = ty } in
        Some (symbolic_value_to_texpr ctx msv)
      else None
  | V.AEndedProjLoans
      { proj = _; consumed = [ (mnv, child_aproj) ]; borrows = [] } ->
      if abs_level = current_level then (
        [%sanity_check] ctx.span (child_aproj = AEmpty);
        (* TODO: check that the updated symbolic values covers all the cases
           (part of the symbolic value might have been updated, and the rest
           left unchanged) - it might happen with nested borrows (see the documentation
           of [AProjLoans]). For now we check that there are no nested borrows
           to make sure we have to update this part of the code once we add support
           for nested borrows.
        *)
        [%sanity_check] ctx.span
          (not
             (TypesUtils.ty_has_nested_borrows (Some ctx.span)
                ctx.type_ctx.type_infos ty));
        (* The symbolic value was updated.

         We're using the projection type as the type of the symbolic value -
         it doesn't really matter. *)
        let mnv : V.symbolic_value = { sv_id = mnv.sv_id; sv_ty = ty } in
        Some (symbolic_value_to_texpr ctx mnv))
      else [%craise] ctx.span "Unimplemented"
  | V.AEndedProjLoans _ ->
      (* The symbolic value was updated, and the given back values come from several
         abstractions *)
      [%craise] ctx.span "Unimplemented"
  | AEndedProjBorrows { mvalues = _; loans } -> (
      (* Happens in the case of nested borrows *)
      match loans with
      | [] ->
          (* No inner loans because of additional nested borrows *)
          None
      | _ -> [%craise] ctx.span "Unimplemented")
  | AEmpty | AProjLoans _ | AProjBorrows _ -> [%craise] ctx.span "Unreachable"

let tavalue_to_consumed (ctx : bs_ctx) (ectx : C.eval_ctx)
    (abs_regions : T.RegionId.Set.t) (abs_level : abs_level) (av : V.tavalue) :
    texpr option =
  (* Check if the value was generated from a loan projector: if yes, and if
     it contains mutable loans, then we generate a consumed value (because
     upon ending the borrow we consumed a value).
     Otherwise we ignore it. *)
  [%ltrace
    "Projecting abs_regions: "
    ^ T.RegionId.Set.to_string None abs_regions
    ^ ":\n"
    ^ tavalue_to_string ~with_ended:true ctx av
    ^ "\n<: " ^ ty_to_string ctx av.ty];
  match
    compute_tavalue_proj_kind ctx.span ctx.type_ctx.type_infos abs_regions
      abs_level 0 av
  with
  | LoanProj BMut ->
      [%ltrace "the value contains mutable loan projectors"];
      tavalue_to_consumed_aux ~filter:true ctx ectx abs_regions abs_level 0 av
  | LoanProj BShared | BorrowProj _ | UnknownProj ->
      (* If it is a borrow proj we ignore it. If it is an unknown projection,
         it means the value doesn't contain loans nor borrows, so nothing
         is consumed upon ending the abstraction: we can ignore it as well. *)
      [%ltrace
        "the value doesn't contains mutable loan projectors (ignoring it)"];
      None

(** Convert the abstraction values in an abstraction to consumed values.

    See [tavalue_to_consumed_aux]. *)
let abs_to_consumed (ctx : bs_ctx) (ectx : C.eval_ctx) (abs : V.abs)
    (abs_level : abs_level) : texpr list =
  [%ltrace
    "- abs:\n"
    ^ abs_to_string ~with_ended:true ctx abs
    ^ "\n- abs_level: " ^ string_of_int abs_level];
  let values =
    List.filter_map
      (tavalue_to_consumed ctx ectx abs.regions.owned abs_level)
      abs.avalues
  in
  [%ltrace
    "- abs: "
    ^ abs_to_string ~with_ended:true ctx abs
    ^ "\n- abs_level: " ^ string_of_int abs_level ^ "\n- values: "
    ^ Print.list_to_string (texpr_to_string ctx) values];
  values

let translate_mprojection_elem span (pe : E.projection_elem) :
    mprojection_elem option =
  match pe with
  | Deref -> None
  | Field (pkind, field_id) -> Some { pkind; field_id }
  | ProjIndex _ | Subslice _ -> None
  | PtrMetadata ->
      [%craise_opt_span] span "supported place projection: pointer metadata"

(** Translate a "meta"-place *)
let rec translate_mplace span type_infos (p : S.mplace) : mplace =
  match p with
  | PlaceLocal bv -> PlaceLocal (bv.index, bv.name)
  | PlaceGlobal { id; generics } ->
      let global_generics =
        translate_fwd_generic_args span type_infos generics
      in
      PlaceGlobal { global_id = id; global_generics }
  | PlaceProjection (p, pe) -> (
      let p = translate_mplace span type_infos p in
      let pe = translate_mprojection_elem span pe in
      match pe with
      | None -> p
      | Some pe -> PlaceProjection (p, pe))

let translate_opt_mplace span type_infos (p : S.mplace option) : mplace option =
  match p with
  | None -> None
  | Some p -> Some (translate_mplace span type_infos p)

type borrow_or_symbolic_id =
  | Borrow of V.BorrowId.id
  | Symbolic of V.SymbolicValueId.id
[@@deriving show, ord]

(** Explore an abstraction value which we know **was generated by a borrow
    projection** (this means we won't find loans or loan projectors inside it)
    and convert it to a given back value by collecting all the meta-values from
    the ended *borrows*.

    Note that given back values are *open* patterns. They are patterns because
    when an abstraction ends we introduce a call to a backward function in the
    synthesized program, which introduces new values:
    {[
      let (nx, ny) = f_back ... in
          ^^^^^^^^
    ]}
    The patterns are open, because functions like [mk_let] expect open patterns
    (and they close them when creating the let).

    [mp]: it is possible to provide some meta-place information, to guide the
    heuristics which later find pretty names for the variables.

    - [under_mut]: if [true] it means we are below a mutable borrow. This
      influences whether we filter values or not.

    Note that we return:
    - an updated context (because the patterns introduce fresh variables)
    - a map from variable ids (introduced in the returned pattern) to either the
      mutable borrow which gave back this value, or the projected symbolic value
      which gave it back. We need this to compute default values (see
      [bs_ctx.mut_borrow_to_consumed]).
    - the pattern *)
let rec tavalue_to_given_back_aux ~(filter : bool)
    (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (mp : mplace option) (av : V.tavalue)
    (ctx : bs_ctx) : bs_ctx * tpat option =
  [%ldebug
    "- current_level: "
    ^ string_of_int current_level
    ^ "\n- av: "
    ^ tavalue_to_string ~with_ended:true ctx av];
  let (ctx, value) : _ * tpat option =
    match av.value with
    | AAdt adt_v ->
        adt_avalue_to_given_back_aux ~filter abs_regions abs_level current_level
          av adt_v ctx
    | ALoan lc ->
        aloan_content_to_given_back_aux ~filter abs_regions abs_level
          current_level mp lc ctx
    | ABorrow bc ->
        aborrow_content_to_given_back_aux ~filter abs_regions abs_level
          current_level mp bc av.ty ctx
    | ASymbolic (pm, aproj) ->
        [%sanity_check] ctx.span (pm = PNone);
        aproj_to_given_back_aux abs_level current_level mp aproj av.ty ctx
    | AIgnored _ ->
        (* If we do not filter, we have to create an ignored pattern *)
        if filter then (ctx, None)
        else
          let ty = translate_fwd_ty (Some ctx.span) ctx.decls_ctx av.ty in
          (ctx, Some (mk_ignored_pat ty))
  in
  (* Sanity checks - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_pat ctx value);
  (* Return *)
  (ctx, value)

and adt_avalue_to_given_back_aux ~(filter : bool)
    (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (av : V.tavalue) (adt_v : V.adt_avalue)
    (ctx : bs_ctx) : bs_ctx * tpat option =
  let ctx, out =
    gtranslate_adt_fields ~project_borrows:true (tavalue_to_string ctx)
      (tpat_to_string ctx)
      (fun ~filter ctx v ->
        let ctx, v =
          tavalue_to_given_back_aux ~filter abs_regions abs_level current_level
            None v ctx
        in
        match v with
        | None -> (ctx, None)
        | Some x -> (ctx, Some ((), x)))
      (compute_tavalue_proj_kind ctx.span ctx.type_ctx.type_infos abs_regions
         abs_level current_level)
      (fun fields ->
        let ty = translate_fwd_ty (Some ctx.span) ctx.decls_ctx av.ty in
        mk_adt_pat ty adt_v.variant_id fields)
      mk_simpl_tuple_pat ~filter ctx av av.ty adt_v.fields
  in
  (ctx, Option.map snd out)

and aloan_content_to_given_back_aux ~(filter : bool)
    (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (mp : mplace option) (lc : V.aloan_content)
    (ctx : bs_ctx) : bs_ctx * tpat option =
  match lc with
  | V.AMutLoan (_, _, child) | V.AIgnoredMutLoan (_, child) ->
      (* Can happen with nested borrows *)
      tavalue_to_given_back_aux ~filter abs_regions abs_level current_level mp
        child ctx
  | V.ASharedLoan _ -> (ctx, None)
  | V.AEndedMutLoan { child; given_back; given_back_meta = _ }
  | V.AEndedIgnoredMutLoan { child; given_back; given_back_meta = _ } -> (
      let ctx, child =
        tavalue_to_given_back_aux ~filter abs_regions abs_level current_level mp
          child ctx
      in
      let ctx, given_back =
        tavalue_to_given_back_aux ~filter abs_regions abs_level
          (current_level + 1) mp given_back ctx
      in
      match (child, given_back) with
      | Some v, None | None, Some v -> (ctx, Some v)
      | None, None -> (ctx, None)
      | _ -> [%craise] ctx.span "Unimplemented")
  | V.AEndedSharedLoan _ -> (ctx, None)
  | V.AIgnoredSharedLoan _ -> (ctx, None)

and aborrow_content_to_given_back_aux ~(filter : bool)
    (abs_regions : T.RegionId.Set.t) (abs_level : abs_level)
    (current_level : abs_level) (mp : mplace option) (bc : V.aborrow_content)
    (ty : T.ty) (ctx : bs_ctx) : bs_ctx * tpat option =
  match bc with
  | V.AMutBorrow (_, _, child) | V.AIgnoredMutBorrow (_, child) ->
      tavalue_to_given_back_aux ~filter abs_regions abs_level current_level mp
        child ctx
  | ASharedBorrow _ -> (ctx, None)
  | AEndedMutBorrow (msv, child) ->
      if abs_level = current_level then
        (* Return the meta symbolic-value *)
        let ctx, var = fresh_var_for_symbolic_value msv.given_back ctx in
        let pat = mk_tpat_from_fvar mp var in
        (* Lookup the default value and update the [var_id_to_default] map.
           Note that the default value might be missing, for instance for
           abstractions which were not introduced because of function calls but
           rather because of loops.
        *)
        let ctx =
          match V.BorrowId.Map.find_opt msv.bid ctx.mut_borrow_to_consumed with
          | None -> ctx
          | Some e ->
              {
                ctx with
                var_id_to_default =
                  FVarId.Map.add var.id e ctx.var_id_to_default;
              }
        in
        (* *)
        (ctx, Some pat)
      else
        tavalue_to_given_back_aux ~filter abs_regions abs_level current_level mp
          child ctx
  | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } -> (
      let ctx, child =
        tavalue_to_given_back_aux ~filter abs_regions abs_level current_level mp
          child ctx
      in
      let ctx, given_back =
        tavalue_to_given_back_aux ~filter abs_regions abs_level
          (current_level + 1) mp given_back ctx
      in
      match (child, given_back) with
      | Some v, None | None, Some v -> (ctx, Some v)
      | None, None -> (ctx, None)
      | _ -> [%craise] ctx.span "Unimplemented")
  | AEndedSharedBorrow | AProjSharedBorrow _ ->
      if filter then (ctx, None)
      else
        let ty = translate_fwd_ty (Some ctx.span) ctx.decls_ctx ty in
        (ctx, Some (mk_ignored_pat ty))

and aproj_to_given_back_aux (_abs_level : abs_level)
    (_current_level : abs_level) (mp : mplace option) (aproj : V.aproj)
    (ty : T.ty) (ctx : bs_ctx) : bs_ctx * tpat option =
  match aproj with
  | V.AEndedProjLoans { proj = _; consumed; borrows } ->
      [%cassert] ctx.span (borrows = []) "Unimplemented";
      (match consumed with
      | [] | [ _ ] -> ()
      | _ -> [%craise] ctx.span "Unimplemented");
      (ctx, None)
  | AEndedProjBorrows { mvalues = mv; loans } ->
      [%cassert] ctx.span (loans = []) "Unreachable";
      (* Return the meta-value *)
      let ctx, var = fresh_var_for_symbolic_value mv.given_back ctx in
      let pat = mk_tpat_from_fvar mp var in
      (* Register the default value *)
      let ctx =
        (* Using the projection type as the type of the symbolic value - it
           doesn't really matter *)
        let sv : V.symbolic_value = { sv_id = mv.consumed; sv_ty = ty } in
        {
          ctx with
          var_id_to_default =
            FVarId.Map.add var.id
              (symbolic_value_to_texpr ctx sv)
              ctx.var_id_to_default;
        }
      in
      (ctx, Some pat)
  | AEmpty | AProjLoans _ | AProjBorrows _ -> [%craise] ctx.span "Unreachable"

let tavalue_to_given_back (abs_regions : T.RegionId.Set.t)
    (abs_level : abs_level) (mp : mplace option) (v : V.tavalue) (ctx : bs_ctx)
    : bs_ctx * tpat option =
  (* Check if the value was generated from a borrow projector: if yes, and if
     it contains mutable borrows we generate a given back pattern (because
     upon ending the borrow the abstraction gave back a value).
     Otherwise we ignore it. *)
  match
    compute_tavalue_proj_kind ctx.span ctx.type_ctx.type_infos abs_regions
      abs_level 0 v
  with
  | BorrowProj BMut ->
      tavalue_to_given_back_aux abs_regions abs_level 0 mp ~filter:true v ctx
  | BorrowProj BShared | LoanProj _ | UnknownProj ->
      (* If it is a loan proj we ignore it. If it is an unknown projection,
         it means the value doesn't contain loans nor borrows, so nothing
         is given back: we can ignore it as well. *)
      (ctx, None)

(** Convert the abstraction values in an abstraction to given back values.

    See [tavalue_to_given_back]. *)
let abs_to_given_back (mpl : mplace option list option) (abs : V.abs)
    (abs_level : abs_level) (ctx : bs_ctx) : bs_ctx * tpat list =
  [%ltrace
    "- abs:\n"
    ^ abs_to_string ~with_ended:true ctx abs
    ^ "\n- abs_level: " ^ string_of_int abs_level];
  let avalues =
    match mpl with
    | None -> List.map (fun av -> (None, av)) abs.avalues
    | Some mpl -> List.combine mpl abs.avalues
  in
  let ctx, values =
    List.fold_left_map
      (fun ctx (mp, av) ->
        tavalue_to_given_back abs.regions.owned abs_level mp av ctx)
      ctx avalues
  in
  let values = List.filter_map (fun x -> x) values in
  [%ltrace
    "After translation to given back patterns:\n- abs: "
    ^ abs_to_string ~with_ended:true ctx abs
    ^ "\n- patterns: "
    ^ Print.list_to_string (tpat_to_string ctx) values];
  (ctx, values)

(** Simply calls [abs_to_given_back] *)
let abs_to_given_back_no_mp (abs : V.abs) (abs_level : abs_level) (ctx : bs_ctx)
    : bs_ctx * tpat list =
  let mpl = List.map (fun _ -> None) abs.avalues in
  abs_to_given_back (Some mpl) abs abs_level ctx

(** Register the values consumed by a region abstraction through mutable
    borrows.

    We need this to compute default values for given back values - see the
    explanations about [bs_ctx.mut_borrow_to_consumed]. *)
let register_consumed_mut_borrows (ectx : C.eval_ctx) (ctx : bs_ctx)
    (v : V.tvalue) : bs_ctx =
  let ctx = ref ctx in
  let visitor =
    object
      inherit [_] V.iter_tvalue as super

      method! visit_VMutBorrow env bid v =
        let e = tvalue_to_texpr !ctx ectx v in
        ctx :=
          {
            !ctx with
            mut_borrow_to_consumed =
              V.BorrowId.Map.add bid e !ctx.mut_borrow_to_consumed;
          };
        super#visit_VMutBorrow env bid v
    end
  in
  visitor#visit_tvalue () v;
  !ctx
