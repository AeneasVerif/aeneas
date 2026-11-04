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
    match V.SymbolicValueId.Map.find_opt sv.sv_id ctx.sv_to_expr with
    | Some e -> e
    | None -> (
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
            })

(** Should we erase the boxes and borrows? See
    {!Config.erase_boxes_and_borrows}. *)
let erase_boxes_and_borrows () : bool = !Config.erase_boxes_and_borrows

(** Wrap an expression, unless we erase the boxes and the borrows *)
let wrap_texpr (span : Meta.span) (k : wrapper_kind) (e : texpr) : texpr =
  if erase_boxes_and_borrows () then e else mk_wrapper_texpr span k e

(** Wrap a pattern, unless we erase the boxes and the borrows *)
let wrap_pat (k : wrapper_kind) (p : tpat) : tpat =
  if erase_boxes_and_borrows () then p else mk_wrapper_pat k p

(** Check if the representation of the values of type [ty] is not the same in
    the forward functions and in the backward functions.

    The values consumed and given back by the backward functions are the values
    of the mutably borrowed values: whenever we see a mutable borrow [&mut T] at
    the top of a type, or below a tuple or a box, the backward function
    manipulates a value of type [T] instead of a value of type [MutBorrow T].
    Similarly, the boxes are transparent. However, the values inside ADTs (for
    instance [Option<&mut T>]) keep their forward representation, as the types
    of the fields are fixed. See {!SymbolicToPureTypes.translate_back_ty_aux}.
*)
let rec ty_has_different_back_repr (ctx : bs_ctx) (ty : T.ty) : bool =
  if erase_boxes_and_borrows () then false
  else
    match ty with
    | TRef (_, _, RMut) -> true
    | TAdt { builtin = Some TBox; generics = { types = [ ty ]; _ }; _ } ->
        (* The boxes which contain mutable borrows are transparent (see
           {!SymbolicToPureTypes.translate_back_ty_aux}). Note that the boxes
           which don't contain mutable borrows keep their forward
           representation: they are filtered by
           {!SymbolicToPureTypes.translate_back_ty_aux} if they are not below
           a mutable borrow, in which case they use the forward
           representation. *)
        TypesUtils.ty_has_mut_borrows ctx.type_ctx.type_infos ty
    | TAdt { builtin = Some TTuple; generics; _ } ->
        List.exists (ty_has_different_back_repr ctx) generics.types
    | _ -> false

(** Translate a type to the representation used by the backward functions (see
    {!ty_has_different_back_repr}). *)
let rec translate_back_repr_ty (ctx : bs_ctx) (ty : T.ty) : ty =
  if not (ty_has_different_back_repr ctx ty) then ctx_translate_fwd_ty ctx ty
  else
    match ty with
    | TRef (_, rty, RMut) -> ctx_translate_fwd_ty ctx rty
    | TAdt { builtin = Some TBox; generics = { types = [ ty ]; _ }; _ } ->
        translate_back_repr_ty ctx ty
    | TAdt { builtin = Some TTuple; generics; _ } ->
        mk_simpl_tuple_ty (List.map (translate_back_repr_ty ctx) generics.types)
    | _ -> [%internal_error] ctx.span

(** Destruct a tuple expression, if it is a tuple literal *)
let opt_destruct_tuple_literal_texpr (e : texpr) : texpr list option =
  let cons, fields = destruct_apps e in
  match cons.e with
  | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ } -> Some fields
  | _ -> None

(** Convert an expression from its forward representation to its backward
    representation (see {!ty_has_different_back_repr}). *)
let rec fwd_to_back_repr_texpr (ctx : bs_ctx) (ty : T.ty) (e : texpr) : texpr =
  if not (ty_has_different_back_repr ctx ty) then e
  else
    match ty with
    | TRef (_, _, RMut) -> mk_wrapper_proj ctx.span e
    | TAdt { builtin = Some TBox; generics = { types = [ ty ]; _ }; _ } ->
        fwd_to_back_repr_texpr ctx ty (mk_wrapper_proj ctx.span e)
    | TAdt { builtin = Some TTuple; generics = { types = [ ty ]; _ }; _ } ->
        (* Tuples with exactly one field are simplified *)
        fwd_to_back_repr_texpr ctx ty e
    | TAdt { builtin = Some TTuple; generics; _ } -> (
        match opt_destruct_tuple_literal_texpr e with
        | Some fields when List.length fields = List.length generics.types ->
            mk_simpl_tuple_texpr ctx.span
              (List.map2 (fwd_to_back_repr_texpr ctx) generics.types fields)
        | _ ->
            [%craise] ctx.span
              "Unimplemented: tuple containing mutable borrows or boxes")
    | _ -> [%internal_error] ctx.span

(** Convert an expression from its backward representation to its forward
    representation (see {!ty_has_different_back_repr}). *)
let rec back_to_fwd_repr_texpr (ctx : bs_ctx) (ty : T.ty) (e : texpr) : texpr =
  if not (ty_has_different_back_repr ctx ty) then e
  else
    match ty with
    | TRef (_, _, RMut) -> mk_wrapper_texpr ctx.span WMut e
    | TAdt { builtin = Some TBox; generics = { types = [ ty ]; _ }; _ } ->
        mk_wrapper_texpr ctx.span WBox (back_to_fwd_repr_texpr ctx ty e)
    | TAdt { builtin = Some TTuple; generics = { types = [ ty ]; _ }; _ } ->
        (* Tuples with exactly one field are simplified *)
        back_to_fwd_repr_texpr ctx ty e
    | TAdt { builtin = Some TTuple; generics; _ } -> (
        match opt_destruct_tuple_literal_texpr e with
        | Some fields when List.length fields = List.length generics.types ->
            mk_simpl_tuple_texpr ctx.span
              (List.map2 (back_to_fwd_repr_texpr ctx) generics.types fields)
        | _ ->
            [%craise] ctx.span
              "Unimplemented: tuple containing mutable borrows or boxes")
    | _ -> [%internal_error] ctx.span

(** Convert a pattern from its backward representation to its forward
    representation (see {!ty_has_different_back_repr}). *)
let rec back_to_fwd_repr_pat (ctx : bs_ctx) (ty : T.ty) (p : tpat) : tpat =
  if not (ty_has_different_back_repr ctx ty) then p
  else
    match ty with
    | TRef (_, _, RMut) -> mk_wrapper_pat WMut p
    | TAdt { builtin = Some TBox; generics = { types = [ ty ]; _ }; _ } ->
        mk_wrapper_pat WBox (back_to_fwd_repr_pat ctx ty p)
    | TAdt { builtin = Some TTuple; generics = { types = [ ty ]; _ }; _ } ->
        (* Tuples with exactly one field are simplified *)
        back_to_fwd_repr_pat ctx ty p
    | TAdt { builtin = Some TTuple; generics; _ } -> (
        match p.pat with
        | PAdt { variant_id = None; fields }
          when List.length fields = List.length generics.types ->
            mk_simpl_tuple_pat
              (List.map2 (back_to_fwd_repr_pat ctx) generics.types fields)
        | PIgnored -> mk_ignored_pat (ctx_translate_fwd_ty ctx ty)
        | _ ->
            [%craise] ctx.span
              "Unimplemented: tuple containing mutable borrows or boxes")
    | _ -> [%internal_error] ctx.span

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
  (* We need to ignore boxes, if we erase them *)
  let v =
    if erase_boxes_and_borrows () then ValuesUtils.unbox_tvalue ctx.span v
    else v
  in
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
        | TAdt { builtin = Some TTuple; _ } ->
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
            wrap_texpr ctx.span WShared (translate sv)
        | VReservedMutBorrow (bid, _) ->
            (* Same as for shared borrows. However, note that we use reserved borrows
             * only in *meta-data*: a value *actually used* in the translation can't come
             * from an unpromoted reserved borrow *)
            let sv =
              InterpBorrowsCore.ctx_lookup_shared_value ctx.span ectx bid
            in
            wrap_texpr ctx.span WShared (translate sv)
        | VMutBorrow (_, v) ->
            (* Borrows are either the identity in the extraction, or wrappers *)
            wrap_texpr ctx.span WMut (translate v))
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

let compute_tavalue_proj_kind span type_infos (abs_regions : T.region_set)
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
    | (T.RVar (Free _) | T.RStatic) as r' -> T.RegionSet.mem r' abs_regions
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
    ADTs.

    The translated values use the backward representation (see
    {!ty_has_different_back_repr}), except for the fields of the "regular" ADTs
    which use the forward representation (because the types of the fields are
    fixed): [back_to_fwd ty v] converts a value [v] of type [ty] from the
    backward representation to the forward representation.

    Remark: the avalues/evalues introduced to convert values to abstractions
    (see {!InterpAbs.convert_value_to_input_avalues}) are not well-typed: a loan
    inside an ADT has type [&mut T] while the type of the corresponding field is
    [T]. In this case, the loan stands for the borrowed value: its backward
    representation is the forward representation of the field and we don't need
    to convert it. *)
let gtranslate_adt_fields ~(project_borrows : bool)
    (input_to_string : 'v -> string) (output_to_string : 'o -> string)
    (translate : filter:bool -> bs_ctx -> 'v -> bs_ctx * ('info * 'o) option)
    (compute_proj_kind : 'v -> proj_kind) (mk_adt : 'o list -> 'o)
    (mk_tuple : 'o list -> 'o) (mk_box : 'o -> 'o) (get_ty : 'v -> T.ty)
    (back_to_fwd : T.ty -> 'o -> 'o) ~(filter : bool)
    ~(variant_id : VariantId.id option) (ctx : bs_ctx) (av : 'v) (av_ty : T.ty)
    (fields : 'v list) : bs_ctx * ('info list * 'o) option =
  let span = ctx.span in
  (* We do not do the same thing depending on whether we visit a tuple
     or a "regular" ADT *)
  let adt = TypesUtils.ty_as_adt av_ty in
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
        match adt.builtin with
        | Some (TTuple | TBox) -> true
        | Some _ | None -> (
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
      match adt.builtin with
      | None ->
          if filter_fields then (
            [%sanity_check] span (List.for_all Option.is_none info_fields);
            (ctx, None))
          else
            (* We should preserve all the fields *)
            let infos, out_fields =
              List.split (List.map ([%try_unwrap] span) info_fields)
            in
            (* Convert the fields to the forward representation *)
            let out_fields =
              if erase_boxes_and_borrows () then out_fields
              else
                let def =
                  [%silent_unwrap] span
                    (T.TypeDeclId.Map.find_opt adt.id
                       ctx.decls_ctx.type_ctx.type_decls)
                in
                let field_tys =
                  Substitute.type_decl_get_instantiated_field_types def
                    variant_id adt.generics
                in
                [%sanity_check] span (List.length field_tys = List.length fields);
                List.map2
                  (fun (field_ty, v) o ->
                    match (field_ty, get_ty v) with
                    | T.TRef _, _ -> back_to_fwd field_ty o
                    | _, T.TRef _ ->
                        (* See the remark in the documentation *)
                        o
                    | _ -> back_to_fwd field_ty o)
                  (List.combine field_tys fields)
                  out_fields
            in
            let pat = mk_adt out_fields in
            (ctx, Some (infos, pat))
      | Some TBox -> begin
          (* The box type is the identity in the backward representation,
             unless it doesn't contain mutable borrows (see
             {!ty_has_different_back_repr}) *)
          match info_fields with
          | [ None ] -> (ctx, None)
          | [ Some (info, v) ] ->
              let v =
                if
                  erase_boxes_and_borrows ()
                  || ty_has_different_back_repr ctx av_ty
                then v
                else mk_box v
              in
              (ctx, Some ([ info ], v))
          | _ -> [%craise] span "Unreachable"
        end
      | Some TStr ->
          (* This case is unreachable:
             - for strings: the [str] is not polymorphic.
          *)
          [%craise] span "Unreachable"
      | Some TTuple ->
          (* If the filtering is activated, we ignore the fields which do not
             consume values (i.e., which do not contain ended mutable borrows). *)
          if filter then
            let info_fields = List.filter_map (fun x -> x) info_fields in
            if info_fields = [] then (ctx, None)
            else
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
    (ectx : C.eval_ctx) (abs_regions : T.region_set) (abs_level : abs_level)
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
          | Some mv ->
              let e = tvalue_to_texpr ctx ectx mv in
              Some (fwd_to_back_repr_texpr ctx av.ty e))
  in
  (* Sanity check - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_texpr ctx value);
  (* Return *)
  value

and adt_avalue_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.region_set) (abs_level : abs_level)
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
      (mk_wrapper_texpr ctx.span WBox)
      (fun (v : V.tavalue) -> v.ty)
      (back_to_fwd_repr_texpr ctx)
      ~filter ~variant_id:adt_v.variant_id ctx av av.ty adt_v.fields
  in
  Option.map snd out

and aloan_content_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.region_set) (abs_level : abs_level)
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
      if filter then None
      else Some (wrap_texpr ctx.span WShared (tvalue_to_texpr ctx ectx sv))
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
      (* An ignored shared loan: this doesn't consume anything. Note that
         there might be mutable borrows inside the shared value, but those
         are frozen (immutable) under the shared context. *)
      None

and aborrow_content_to_consumed_aux ~(filter : bool) (ctx : bs_ctx)
    (ectx : C.eval_ctx) (abs_regions : T.region_set) (abs_level : abs_level)
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

and aproj_to_consumed_aux (ctx : bs_ctx) (_abs_regions : T.region_set)
    (abs_level : abs_level) (current_level : abs_level) (aproj : V.aproj)
    (ty : T.ty) : texpr option =
  match aproj with
  | V.AEndedProjLoans { proj = msv; consumed = []; borrows = [] } ->
      if abs_level = current_level then
        (* The symbolic value was left unchanged.

           We're using the projection type as the type of the symbolic value -
           it doesn't really matter. *)
        let msv : V.symbolic_value = { sv_id = msv; sv_ty = ty } in
        let e = symbolic_value_to_texpr ctx msv in
        Some (fwd_to_back_repr_texpr ctx ty e)
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
        let e = symbolic_value_to_texpr ctx mnv in
        Some (fwd_to_back_repr_texpr ctx ty e))
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
    (abs_regions : T.region_set) (abs_level : abs_level) (av : V.tavalue) :
    texpr option =
  (* Check if the value was generated from a loan projector: if yes, and if
     it contains mutable loans, then we generate a consumed value (because
     upon ending the borrow we consumed a value).
     Otherwise we ignore it. *)
  [%ltrace
    "Projecting abs_regions: "
    ^ T.region_set_to_string abs_regions
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

let translate_mprojection_elem span (pe : S.mprojection_elem) : mprojection_elem
    =
  let type_id = translate_type_id span pe.type_ref in
  { type_id; variant_id = pe.variant_id; field_id = pe.field_id }

(** Translate a "meta"-place *)
let rec translate_mplace span type_infos (p : S.mplace) : mplace =
  match p with
  | PlaceLocal bv -> PlaceLocal (bv.index, bv.name)
  | PlaceGlobal { id; generics } ->
      let global_generics =
        translate_fwd_generic_args span type_infos generics
      in
      PlaceGlobal { global_id = id; global_generics }
  | PlaceProjection (p, pe) ->
      let p = translate_mplace span type_infos p in
      let pe = translate_mprojection_elem span pe in
      PlaceProjection (p, pe)

let translate_opt_mplace span type_infos (p : S.mplace option) : mplace option =
  match p with
  | None -> None
  | Some p -> Some (translate_mplace span type_infos p)

type borrow_or_symbolic_id =
  | Borrow of V.BorrowId.id
  | Symbolic of V.SymbolicValueId.id
[@@deriving show, ord]

(** Introduce a pattern for a symbolic value given back by a backward function.

    - [consumed]: the expression which was consumed by the backward function (it
      uses the forward representation): we use it as the default value (see
      [bs_ctx.var_id_to_default]).
    - [ty]: the type of the symbolic value. *)
let given_back_symbolic_value_to_pat (ctx : bs_ctx) (mp : mplace option)
    (given_back : V.symbolic_value) (consumed : texpr) (ty : T.ty) :
    bs_ctx * tpat option =
  if not (ty_has_different_back_repr ctx ty) then
    (* Return the meta-value *)
    let ctx, var = fresh_var_for_symbolic_value given_back ctx in
    let pat = mk_tpat_from_fvar mp var in
    (* Register the default value *)
    let ctx =
      {
        ctx with
        var_id_to_default = FVarId.Map.add var.id consumed ctx.var_id_to_default;
      }
    in
    (ctx, Some pat)
  else
    (* The backward function gives back a value which uses the backward
       representation (e.g., a value of type [T] for a symbolic value of
       type [&mut T]): we introduce a variable with the backward
       representation, and map the given back symbolic value to the
       expression which converts this variable to the forward
       representation (e.g., [MutBorrow.mk x]). *)
    let back_ty = translate_back_repr_ty ctx ty in
    let ctx, var = fresh_var None back_ty ctx in
    let pat = mk_tpat_from_fvar mp var in
    let var_e = mk_texpr_from_fvar var in
    let ctx =
      {
        ctx with
        sv_to_expr =
          V.SymbolicValueId.Map.add given_back.sv_id
            (back_to_fwd_repr_texpr ctx ty var_e)
            ctx.sv_to_expr;
        var_id_to_default =
          FVarId.Map.add var.id
            (fwd_to_back_repr_texpr ctx ty consumed)
            ctx.var_id_to_default;
      }
    in
    (ctx, Some pat)

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
let rec tavalue_to_given_back_aux ~(filter : bool) (abs_regions : T.region_set)
    (abs_level : abs_level) (current_level : abs_level) (mp : mplace option)
    (av : V.tavalue) (ctx : bs_ctx) : bs_ctx * tpat option =
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
          let ty = translate_back_repr_ty ctx av.ty in
          (ctx, Some (mk_ignored_pat ty))
  in
  (* Sanity checks - Rk.: we do this at every recursive call, which is a bit
   * expansive... *)
  (match value with
  | None -> ()
  | Some value -> type_check_pat ctx value);
  (* Return *)
  (ctx, value)

and adt_avalue_to_given_back_aux ~(filter : bool) (abs_regions : T.region_set)
    (abs_level : abs_level) (current_level : abs_level) (av : V.tavalue)
    (adt_v : V.adt_avalue) (ctx : bs_ctx) : bs_ctx * tpat option =
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
      mk_simpl_tuple_pat (mk_wrapper_pat WBox)
      (fun (v : V.tavalue) -> v.ty)
      (back_to_fwd_repr_pat ctx) ~filter ~variant_id:adt_v.variant_id ctx av
      av.ty adt_v.fields
  in
  (ctx, Option.map snd out)

and aloan_content_to_given_back_aux ~(filter : bool)
    (abs_regions : T.region_set) (abs_level : abs_level)
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
    (abs_regions : T.region_set) (abs_level : abs_level)
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
      (* Using the projection type as the type of the symbolic value - it
         doesn't really matter *)
      let consumed_sv : V.symbolic_value =
        { sv_id = mv.consumed; sv_ty = ty }
      in
      let consumed = symbolic_value_to_texpr ctx consumed_sv in
      given_back_symbolic_value_to_pat ctx mp mv.given_back consumed ty
  | AEmpty | AProjLoans _ | AProjBorrows _ -> [%craise] ctx.span "Unreachable"

let tavalue_to_given_back (abs_regions : T.region_set) (abs_level : abs_level)
    (mp : mplace option) (v : V.tavalue) (ctx : bs_ctx) : bs_ctx * tpat option =
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
