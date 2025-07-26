open Types
open Values
open Contexts
open ValuesUtils
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterBorrows
open Errors

(** The local logger *)
let log = Logging.abs_log

let convert_value_to_abstractions (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(destructure_shared_values : bool) (ctx : eval_ctx)
    (v : typed_value) : abs list =
  log#ltrace (lazy (__FUNCTION__ ^ ": " ^ typed_value_to_string ctx v));
  (* Convert the value to a list of avalues *)
  let absl = ref [] in
  let push_abs (r_id : RegionId.id) (avalues : typed_avalue list) : unit =
    if avalues = [] then ()
    else begin
      (* Create the abs - note that we keep the order of the avalues as it is
         (unlike the environments) *)
      log#ldebug
        (lazy
          (__FUNCTION__ ^ ": push_abs: avalues:\n"
          ^ String.concat "\n"
              (List.map
                 (fun (v : typed_avalue) ->
                   typed_avalue_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
                 avalues)));
      let abs =
        {
          abs_id = fresh_abstraction_id ();
          kind = abs_kind;
          can_end;
          parents = AbstractionId.Set.empty;
          original_parents = [];
          regions = { owned = RegionId.Set.singleton r_id };
          avalues;
        }
      in
      log#ldebug
        (lazy
          (__FUNCTION__ ^ ": push_abs: abs:\n" ^ abs_to_string span ctx abs));
      Invariants.opt_type_check_abs span ctx abs;
      (* Add to the list of abstractions *)
      absl := abs :: !absl
    end
  in

  (* [group]: group in one abstraction (because we dived into a borrow/loan)

     We return one typed-value for the shared values: when we encounter a shared
     loan, we need to compute the value which will be shared. If [destructure_shared_values]
     is [true], this shared value will be stripped of its shared loans.
  *)
  let rec to_avalues ~(allow_borrows : bool) ~(inside_borrowed : bool)
      ~(group : bool) (r_id : RegionId.id) (v : typed_value) :
      typed_avalue list * typed_value =
    (* Debug *)
    log#ldebug
      (lazy
        (__FUNCTION__ ^ ": to_avalues:\n- value: "
        ^ typed_value_to_string ~span:(Some span) ctx v));

    let ty = v.ty in
    match v.value with
    | VLiteral _ -> ([], v)
    | VBottom ->
        (* Can happen: we *do* convert dummy values to abstractions, and dummy
           values can contain bottoms *)
        ([], v)
    | VAdt adt ->
        (* Two cases, depending on whether we have to group all the borrows/loans
           inside one abstraction or not *)
        let avl, field_values =
          if group then
            (* Convert to avalues, and transmit to the parent *)
            let avl, field_values =
              List.split
                (List.map
                   (to_avalues ~allow_borrows ~inside_borrowed ~group r_id)
                   adt.field_values)
            in
            (List.concat avl, field_values)
          else
            (* Create one abstraction per field, and transmit nothing to the parent *)
            let field_values =
              List.map
                (fun fv ->
                  let r_id = fresh_region_id () in
                  let avl, fv =
                    to_avalues ~allow_borrows ~inside_borrowed ~group r_id fv
                  in
                  push_abs r_id avl;
                  fv)
                (* Slightly tricky: pay attention to the order in which the
                   abstractions are pushed (i.e.: the [List.rev] is important
                   to get a "good" environment, and a nice translation) *)
                (List.rev adt.field_values)
            in
            ([], field_values)
        in
        let adt = { adt with field_values } in
        (avl, { v with value = VAdt adt })
    | VBorrow bc -> (
        let _, ref_ty, kind = ty_as_ref ty in
        cassert __FILE__ __LINE__ (ty_no_regions ref_ty) span
          "Nested borrows are not supported yet";
        (* Sanity check *)
        sanity_check __FILE__ __LINE__ allow_borrows span;
        (* Convert the borrow content *)
        match bc with
        | VSharedBorrow bid ->
            cassert __FILE__ __LINE__ (ty_no_regions ref_ty) span
              "Nested borrows are not supported yet";
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let value = ABorrow (ASharedBorrow (PNone, bid)) in
            ([ { value; ty } ], v)
        | VMutBorrow (bid, bv) ->
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not (value_has_borrows (Some span) ctx bv.value))
              span "Nested borrows are not supported yet";
            (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let ignored = mk_aignored span ref_ty None in
            let av = ABorrow (AMutBorrow (PNone, bid, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let avl, bv =
              to_avalues ~allow_borrows:false ~inside_borrowed:true ~group:true
                r_id bv
            in
            let value = { v with value = VBorrow (VMutBorrow (bid, bv)) } in
            (av :: avl, value)
        | VReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            craise __FILE__ __LINE__ span "Unexpected")
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let r_id = if group then r_id else fresh_region_id () in
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not (value_has_borrows (Some span) ctx sv.value))
              span "Nested borrows are not supported yet";
            (* Push the avalue *)
            cassert __FILE__ __LINE__ (ty_no_regions ty) span
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty None in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RShared in
            (* Rem.: the shared value might contain loans *)
            let avl, sv =
              to_avalues ~allow_borrows:false ~inside_borrowed:true ~group:true
                r_id sv
            in
            let av = ALoan (ASharedLoan (PNone, bids, sv, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let value : value =
              if destructure_shared_values then sv.value
              else VLoan (VSharedLoan (bids, sv))
            in
            let value = { v with value } in
            (av :: avl, value)
        | VMutLoan bid ->
            (* Push the avalue *)
            cassert __FILE__ __LINE__ (ty_no_regions ty) span
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RMut in
            let av = ALoan (AMutLoan (PNone, bid, ignored None)) in
            let av = { value = av; ty } in
            ([ av ], v))
    | VSymbolic sv ->
        (* Check that there are no nested borrows in the symbolic value -
           we don't support this case yet *)
        cassert __FILE__ __LINE__
          (not
             (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
          span "Nested borrows are not supported yet";

        (* If we don't need to group the borrows into one region (because the
           symbolic value is inside a mutable borrow for instance) check that
           none of the regions used by the symbolic value have ended. *)
        sanity_check __FILE__ __LINE__
          (group || not (symbolic_value_has_ended_regions ctx.ended_regions sv))
          span;

        (* If we group the borrows: simply introduce a projector.
           Otherwise, introduce one abstraction per region *)
        if group then
          (* Check if the type contains regions: if not, simply ignore
             it (there are no projections to introduce) *)
          if TypesUtils.ty_no_regions sv.sv_ty then ([], v)
          else
            (* Substitute the regions in the type *)
            let visitor =
              object
                inherit [_] map_ty

                method! visit_RVar _ var =
                  match var with
                  | Free _ -> RVar (Free r_id)
                  | Bound _ -> internal_error __FILE__ __LINE__ span
              end
            in
            let ty = visitor#visit_ty () sv.sv_ty in
            let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty = ty } in
            let nv = ASymbolic (PNone, AProjBorrows { proj; loans = [] }) in
            let nv : typed_avalue = { value = nv; ty } in
            ([ nv ], v)
        else
          (* Introduce one abstraction per live region *)
          let regions, ty = refresh_live_regions_in_ty span ctx sv.sv_ty in
          RegionId.Map.iter
            (fun _ rid ->
              let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty = ty } in
              let nv = ASymbolic (PNone, AProjBorrows { proj; loans = [] }) in
              let nv : typed_avalue = { value = nv; ty } in
              push_abs rid [ nv ])
            regions;
          ([], v)
  in

  (* Generate the avalues *)
  let r_id = fresh_region_id () in
  let values, _ =
    to_avalues ~allow_borrows:true ~inside_borrowed:false ~group:false r_id v
  in
  (* Introduce an abstraction for the returned values *)
  push_abs r_id values;
  (* Return *)
  List.rev !absl

type 'a borrow_or_loan = Borrow of 'a | Loan of 'a

type g_loan_content_with_ty =
  (ety * loan_content, rty * aloan_content) concrete_or_abs

type g_borrow_content_with_ty =
  (ety * borrow_content, rty * aborrow_content) concrete_or_abs

type merge_abstraction_info = {
  loans : MarkedBorrowId.Set.t;
  borrows : MarkedBorrowId.Set.t;
  loan_projs : MarkedNormSymbProj.Set.t;
  borrow_projs : MarkedNormSymbProj.Set.t;
  borrows_loans : marked_borrow_id borrow_or_loan list;
  borrow_loan_projs : marked_norm_symb_proj borrow_or_loan list;
      (** We use a list to preserve the order in which the borrows were found *)
  loan_to_content : g_loan_content_with_ty MarkedBorrowId.Map.t;
  borrow_to_content : g_borrow_content_with_ty MarkedBorrowId.Map.t;
  loan_proj_to_content : (ty * proj_marker * aproj) MarkedNormSymbProj.Map.t;
  borrow_proj_to_content : (ty * proj_marker * aproj) MarkedNormSymbProj.Map.t;
}

(** Small utility to help merging abstractions.

    We compute the list of loan/borrow contents, maps from borrow/loan ids to
    borrow/loan contents, etc.

    Note that this function is very specific to [merge_into_first_abstraction]:
    we have strong assumptions about the shape of the abstraction, and in
    particular that:
    - its values don't contain nested borrows
    - all the borrows are destructured (for instance, shared loans can't contain
      shared loans). *)
let compute_merge_abstraction_info (span : Meta.span) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : typed_avalue list) :
    merge_abstraction_info =
  let loans : MarkedBorrowId.Set.t ref = ref MarkedBorrowId.Set.empty in
  let borrows : MarkedBorrowId.Set.t ref = ref MarkedBorrowId.Set.empty in
  let loan_projs = ref MarkedNormSymbProj.Set.empty in
  let borrow_projs = ref MarkedNormSymbProj.Set.empty in
  let borrows_loans : marked_borrow_id borrow_or_loan list ref = ref [] in
  let borrow_loan_projs = ref [] in
  let loan_to_content : g_loan_content_with_ty MarkedBorrowId.Map.t ref =
    ref MarkedBorrowId.Map.empty
  in
  let borrow_to_content : g_borrow_content_with_ty MarkedBorrowId.Map.t ref =
    ref MarkedBorrowId.Map.empty
  in
  let loan_proj_to_content = ref MarkedNormSymbProj.Map.empty in
  let borrow_proj_to_content = ref MarkedNormSymbProj.Map.empty in

  let module Push
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt) =
  struct
    let push (set : Set.t ref) (content : 'a) (to_content : 'a Map.t ref)
        (is_borrow : bool) (borrows_loans : Set.elt borrow_or_loan list ref)
        (marked : Set.elt) : unit =
      sanity_check __FILE__ __LINE__ (not (Set.mem marked !set)) span;
      set := Set.add marked !set;
      sanity_check __FILE__ __LINE__ (not (Map.mem marked !to_content)) span;
      to_content := Map.add marked content !to_content;
      borrows_loans :=
        (if is_borrow then Borrow marked else Loan marked) :: !borrows_loans
  end in
  let module PushConcrete = Push (MarkedBorrowId.Set) (MarkedBorrowId.Map) in
  let push_loan pm id (lc : g_loan_content_with_ty) =
    PushConcrete.push loans lc loan_to_content false borrows_loans (pm, id)
  in
  let push_loans pm ids lc : unit =
    BorrowId.Set.iter (fun id -> push_loan pm id lc) ids
  in
  let push_borrow pm id (bc : g_borrow_content_with_ty) =
    PushConcrete.push borrows bc borrow_to_content true borrows_loans (pm, id)
  in

  let module PushSymbolic =
    Push (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
  in
  let push_loan_proj pm (proj : symbolic_proj) lc =
    let norm_proj_ty = normalize_proj_ty owned_regions proj.proj_ty in
    let proj = { pm; sv_id = proj.sv_id; norm_proj_ty } in
    PushSymbolic.push loan_projs lc loan_proj_to_content false borrow_loan_projs
      proj
  in
  let push_borrow_proj pm (proj : symbolic_proj) bc =
    let norm_proj_ty = normalize_proj_ty owned_regions proj.proj_ty in
    let proj = { pm; sv_id = proj.sv_id; norm_proj_ty } in
    PushSymbolic.push borrow_projs bc borrow_proj_to_content true
      borrow_loan_projs proj
  in

  let iter_avalues =
    object
      inherit [_] iter_typed_avalue as super

      (** We redefine this to track the types *)
      method! visit_typed_avalue _ v =
        super#visit_typed_avalue (Some (Abstract v.ty)) v

      (** We redefine this to track the types *)
      method! visit_typed_value _ (v : typed_value) =
        super#visit_typed_value (Some (Concrete v.ty)) v

      method! visit_loan_content _ _ =
        (* Could happen if we explore shared values whose sub-values are
           reborrowed. We use the fact that we destructure the nested shared
           loans before reducing a context or computing a join. *)
        craise __FILE__ __LINE__ span "Unreachable"

      method! visit_borrow_content _ _ =
        (* Can happen if we explore shared values which contain borrows -
           i.e., if we have nested borrows (we forbid this for now) *)
        craise __FILE__ __LINE__ span "Unreachable"

      method! visit_aloan_content env lc =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        (* Register the loans *)
        (match lc with
        | ASharedLoan (pm, bids, _, _) -> push_loans pm bids (Abstract (ty, lc))
        | AMutLoan (pm, bid, _) -> push_loan pm bid (Abstract (ty, lc))
        | AEndedMutLoan _
        | AEndedSharedLoan _
        | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _
        | AIgnoredSharedLoan _ ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            craise __FILE__ __LINE__ span "Unreachable");
        (* Continue *)
        super#visit_aloan_content env lc

      method! visit_aborrow_content env bc =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        (* Explore the borrow content *)
        (match bc with
        | AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid) ->
            push_borrow pm bid (Abstract (ty, bc))
        | AProjSharedBorrow asb ->
            let register asb =
              match asb with
              | AsbBorrow bid -> push_borrow PNone bid (Abstract (ty, bc))
              | AsbProjReborrows _ ->
                  (* Can only happen if the symbolic value (potentially) contains
                     borrows - i.e., we have nested borrows *)
                  craise __FILE__ __LINE__ span "Unreachable"
            in
            List.iter register asb
        | AIgnoredMutBorrow _
        | AEndedIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            craise __FILE__ __LINE__ span "Unreachable");
        super#visit_aborrow_content env bc

      method! visit_symbolic_value _ sv =
        (* Sanity check: no borrows *)
        sanity_check __FILE__ __LINE__
          (not (symbolic_value_has_borrows (Some span) ctx sv))
          span

      method! visit_ASymbolic env pm proj =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        match proj with
        | AProjLoans { proj = proj'; consumed; borrows } ->
            sanity_check __FILE__ __LINE__ (consumed = []) span;
            sanity_check __FILE__ __LINE__ (borrows = []) span;
            push_loan_proj pm proj' (ty, pm, proj)
        | AProjBorrows { proj = proj'; loans } ->
            sanity_check __FILE__ __LINE__ (loans = []) span;
            push_borrow_proj pm proj' (ty, pm, proj)
        | AEndedProjLoans _ | AEndedProjBorrows _ ->
            craise __FILE__ __LINE__ span "Unreachable"
        | AEmpty -> ()
    end
  in

  List.iter (iter_avalues#visit_typed_avalue None) avalues;

  {
    loans = !loans;
    borrows = !borrows;
    borrows_loans = List.rev !borrows_loans;
    loan_to_content = !loan_to_content;
    borrow_to_content = !borrow_to_content;
    loan_projs = !loan_projs;
    borrow_projs = !borrow_projs;
    borrow_loan_projs = List.rev !borrow_loan_projs;
    loan_proj_to_content = !loan_proj_to_content;
    borrow_proj_to_content = !borrow_proj_to_content;
  }

type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_borrows :
    borrow_id -> rty -> proj_marker -> rty -> proj_marker -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [ty1]
          - [pm1] *)
  merge_amut_loans :
    loan_id ->
    rty ->
    proj_marker ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_loans :
    loan_id_set ->
    rty ->
    proj_marker ->
    typed_value ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_value ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [pm0]
          - [sv0]
          - [child0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [child1] *)
  merge_aborrow_projs :
    ty ->
    proj_marker ->
    aproj_borrows ->
    ty ->
    proj_marker ->
    aproj_borrows ->
    typed_avalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [loans0]
          - [ty1]
          - [pm1]
          - [proj1]
          - [loans1] *)
  merge_aloan_projs :
    ty ->
    proj_marker ->
    aproj_loans ->
    ty ->
    proj_marker ->
    aproj_loans ->
    typed_avalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [consumed0]
          - [borrows0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [proj_ty1]
          - [children1] *)
}

(** Small utility: if a value doesn't have any marker, split it into two values
    with complementary markers. We use this for {!merge_abstractions}.

    We assume the value has been destructured (there are no nested loans, adts,
    the children are ignored, etc.). *)
let typed_avalue_split_marker (span : Meta.span) (ctx : eval_ctx)
    (av : typed_avalue) : typed_avalue list =
  let mk_split mk_value = [ mk_value PLeft; mk_value PRight ] in
  let mk_opt_split pm mk_value =
    if pm = PNone then mk_split mk_value else [ av ]
  in
  match av.value with
  | AAdt _ | ABottom | AIgnored _ -> internal_error __FILE__ __LINE__ span
  | ABorrow bc -> (
      match bc with
      | AMutBorrow (pm, bid, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          let mk_value pm =
            { av with value = ABorrow (AMutBorrow (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedBorrow (pm, bid) ->
          let mk_value pm =
            { av with value = ABorrow (ASharedBorrow (pm, bid)) }
          in
          mk_opt_split pm mk_value
      | _ -> internal_error __FILE__ __LINE__ span)
  | ALoan lc -> (
      match lc with
      | AMutLoan (pm, bid, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          let mk_value pm =
            { av with value = ALoan (AMutLoan (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedLoan (pm, bids, sv, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          sanity_check __FILE__ __LINE__
            (not (value_has_borrows (Some span) ctx sv.value))
            span;
          let mk_value pm =
            { av with value = ALoan (ASharedLoan (pm, bids, sv, child)) }
          in
          mk_opt_split pm mk_value
      | _ -> internal_error __FILE__ __LINE__ span)
  | ASymbolic (pm, proj) -> (
      if pm <> PNone then [ av ]
      else
        match proj with
        | AProjBorrows { proj = _; loans } ->
            sanity_check __FILE__ __LINE__ (loans = []) span;
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AProjLoans { proj = _; consumed; borrows } ->
            sanity_check __FILE__ __LINE__ (consumed = []) span;
            sanity_check __FILE__ __LINE__ (borrows = []) span;
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            internal_error __FILE__ __LINE__ span)

let abs_split_markers (span : Meta.span) (ctx : eval_ctx) (abs : abs) : abs =
  {
    abs with
    avalues =
      List.concat (List.map (typed_avalue_split_marker span ctx) abs.avalues);
  }

(** Auxiliary function for {!merge_abstractions}.

    Phase 1 of the merge: we simplify all loan/borrow pairs, if a loan is in the
    left abstraction and its corresponding borrow is in the right abstraction.

    Important: this is asymmetric (the loan must be in the left abstraction).

    Example:
    {[
      abs0 { ML l0, MB l1 } |><| abs1 { MB l0 }
          ~~> abs1 { MB l1 }
    ]}

    But:
    {[
      abs1 { MB l0 } |><| abs0 { ML l0, MB l1 }
          ~~> abs1 { MB l0, ML l0, MB l1 }
    ]}

    We return the list of merged values. *)
let merge_abstractions_merge_loan_borrow_pairs (span : Meta.span)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : typed_avalue list =
  log#ltrace (lazy __FUNCTION__);

  (* Split the markers inside the abstractions (if we allow using markers).

     We do so because it enables simplification later when we are in the following case:
     {[
       abs0 { ML l0 } |><| abs1 { |MB l0|, MB l1 }
     ]}

     If we split before merging we get:
     {[
       abs0 { |ML l0|, ︙ML l0︙ } |><| abs1 { |MB l0|, |MB l1|, ︙MB l1︙ }
           ~~> merge
       abs2 { ︙ML l0︙, |MB l1|, ︙MB l1︙ }
           ~~> simplify the complementary markers
       abs2 { ︙ML l0︙, MB l1 }
     ]}
  *)
  let abs0, abs1 =
    if merge_funs = None then (abs0, abs1)
    else (abs_split_markers span ctx abs0, abs_split_markers span ctx abs1)
  in

  (* Compute the relevant information *)
  let {
    loans = loans0;
    borrows = borrows0;
    loan_projs = loan_projs0;
    borrow_projs = borrow_projs0;
    borrows_loans = borrows_loans0;
    borrow_loan_projs = borrow_loan_projs0;
    loan_to_content = loan_to_content0;
    loan_proj_to_content = loan_proj_to_content0;
    borrow_to_content = borrow_to_content0;
    borrow_proj_to_content = borrow_proj_to_content0;
  } =
    compute_merge_abstraction_info span ctx abs0.regions.owned abs0.avalues
  in

  let {
    loans = loans1;
    borrows = borrows1;
    loan_projs = loan_projs1;
    borrow_projs = borrow_projs1;
    borrows_loans = borrows_loans1;
    borrow_loan_projs = borrow_loan_projs1;
    loan_to_content = loan_to_content1;
    loan_proj_to_content = loan_proj_to_content1;
    borrow_to_content = borrow_to_content1;
    borrow_proj_to_content = borrow_proj_to_content1;
  } =
    compute_merge_abstraction_info span ctx abs1.regions.owned abs1.avalues
  in

  (* Sanity check: no markers appear unless we allow merging duplicates.
     Also, the borrows must be disjoint, and the loans must be disjoint.
  *)
  if merge_funs = None then (
    sanity_check __FILE__ __LINE__
      (List.for_all
         (function
           | Loan (pm, _) | Borrow (pm, _) -> pm = PNone)
         (borrows_loans0 @ borrows_loans1))
      span;
    sanity_check __FILE__ __LINE__
      (List.for_all
         (function
           | Loan proj | Borrow proj -> proj.pm = PNone)
         (borrow_loan_projs0 @ borrow_loan_projs1))
      span;
    sanity_check __FILE__ __LINE__
      (MarkedBorrowId.Set.disjoint borrows0 borrows1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedBorrowId.Set.disjoint loans0 loans1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedNormSymbProj.Set.disjoint borrow_projs0 borrow_projs1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedNormSymbProj.Set.disjoint loan_projs0 loan_projs1)
      span);

  (* Merge.
     There are several cases:
     - if a borrow/loan is only in one abstraction, we simply check if we need
       to filter it (because its associated loan/borrow is in the other
       abstraction).
     - if a borrow/loan is present in both abstractions, we need to merge its
       content.

     Note that we may need to merge strictly more than two avalues, because of
     shared loans. For instance, if we have:
     {[
       abs'0 { shared_loan { l0, l1 } ... }
       abs'1 { shared_loan { l0 } ..., shared_loan { l1 } ... }
     ]}

     We ignore this case for now: we check that whenever we merge two shared loans,
     then their sets of ids are equal, and fail if it is not the case.
     Remark: a way of solving this problem would be to destructure shared loans
     so that they always have exactly one id.
  *)
  let merged_borrows = ref MarkedBorrowId.Set.empty in
  let merged_borrow_projs = ref MarkedNormSymbProj.Set.empty in
  let merged_loans = ref MarkedBorrowId.Set.empty in
  let merged_loan_projs = ref MarkedNormSymbProj.Set.empty in
  let borrow_avalues = ref [] in
  let loan_avalues = ref [] in
  let push_borrow_avalue av =
    log#ltrace
      (lazy
        (__FUNCTION__ ^ ": push_borrow_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    borrow_avalues := av :: !borrow_avalues
  in
  let push_loan_avalue av =
    log#ltrace
      (lazy
        (__FUNCTION__ ^ ": push_loan_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    loan_avalues := av :: !loan_avalues
  in

  (* Compute the intersection of:
     - the loans coming from the left abstraction
     - the borrows coming from the right abstraction
     We will need to filter those (because the loan from the left will cancel
     out with the borrow from the right)
  *)
  let intersect_concrete = MarkedBorrowId.Set.inter loans0 borrows1 in
  let intersect_symbolic =
    MarkedNormSymbProj.Set.inter loan_projs0 borrow_projs1
  in

  (* This function is called when handling shared loans: we have to apply a projection
     marker to a set of borrow ids. *)
  let filter_bids (pm : proj_marker) (bids : BorrowId.Set.t) : BorrowId.Set.t =
    let bids =
      BorrowId.Set.to_seq bids
      |> Seq.map (fun x -> (pm, x))
      |> MarkedBorrowId.Set.of_seq
    in
    let bids = MarkedBorrowId.Set.diff bids intersect_concrete in
    sanity_check __FILE__ __LINE__ (not (MarkedBorrowId.Set.is_empty bids)) span;
    MarkedBorrowId.Set.to_seq bids |> Seq.map snd |> BorrowId.Set.of_seq
  in
  let filter_concrete (bid : marked_borrow_id) : bool =
    MarkedBorrowId.Set.mem bid intersect_concrete
  in
  let filter_symbolic (marked : marked_norm_symb_proj) : bool =
    MarkedNormSymbProj.Set.mem marked intersect_symbolic
  in

  let borrow_is_merged id = MarkedBorrowId.Set.mem id !merged_borrows in
  let borrow_proj_is_merged id =
    MarkedNormSymbProj.Set.mem id !merged_borrow_projs
  in
  let set_borrow_as_merged id =
    merged_borrows := MarkedBorrowId.Set.add id !merged_borrows
  in
  let set_borrow_proj_as_merged id =
    merged_borrow_projs := MarkedNormSymbProj.Set.add id !merged_borrow_projs
  in
  let loan_is_merged id = MarkedBorrowId.Set.mem id !merged_loans in
  let loan_proj_is_merged id =
    MarkedNormSymbProj.Set.mem id !merged_loan_projs
  in
  let set_loan_as_merged id =
    merged_loans := MarkedBorrowId.Set.add id !merged_loans
  in
  let set_loan_proj_as_merged id =
    merged_loan_projs := MarkedNormSymbProj.Set.add id !merged_loan_projs
  in

  let module Merge
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt)
      (Marked : sig
        type borrow_content
        type loan_content

        val to_string : Set.elt -> string
        val borrow_is_merged : Set.elt -> bool
        val loan_is_merged : Set.elt -> bool
        val filter_marked : Set.elt -> bool
        val set_borrow_as_merged : Set.elt -> unit
        val set_loan_as_merged : Set.elt -> unit
        val make_borrow_value : Set.elt -> borrow_content -> typed_avalue

        (** Return the list of marked values to mark as merged - this is
            important for shared loans: the loan itself is identified by a
            single loan id, but we need to mark *all* the loan ids contained in
            the set as merged. *)
        val make_loan_value :
          Set.elt -> loan_content -> Set.elt list * typed_avalue
      end) =
  struct
    (* Iterate over all the borrows/loans found in the abstractions and merge them *)
    let merge (borrow_to_content0 : Marked.borrow_content Map.t)
        (borrow_to_content1 : Marked.borrow_content Map.t)
        (loan_to_content0 : Marked.loan_content Map.t)
        (loan_to_content1 : Marked.loan_content Map.t)
        (borrows_loans : Set.elt borrow_or_loan list) : unit =
      List.iter
        (function
          | Borrow marked ->
              log#ltrace
                (lazy
                  (__FUNCTION__ ^ ": merging borrow: " ^ Marked.to_string marked));

              (* Check if the borrow has already been merged - this can happen
                 because we go through all the borrows/loans in [abs0] *then*
                 all the borrows/loans in [abs1], and there may be duplicates
                 between the two *)
              if Marked.borrow_is_merged marked then ()
              else (
                Marked.set_borrow_as_merged marked;
                (* Check if we need to filter it *)
                if Marked.filter_marked marked then ()
                else
                  (* Lookup the contents *)
                  let bc0 = Map.find_opt marked borrow_to_content0 in
                  let bc1 = Map.find_opt marked borrow_to_content1 in
                  (* Merge *)
                  let av : typed_avalue =
                    match (bc0, bc1) with
                    | None, Some bc | Some bc, None ->
                        Marked.make_borrow_value marked bc
                    | Some _, Some _ ->
                        (* Because of markers, the case where the same borrow is duplicated should
                           be unreachable. Note, this is due to all shared borrows currently
                           taking different ids, this will not be the case anymore when shared loans
                           will take a unique id instead of a set *)
                        craise __FILE__ __LINE__ span "Unreachable"
                    | None, None -> craise __FILE__ __LINE__ span "Unreachable"
                  in
                  push_borrow_avalue av)
          | Loan marked ->
              if
                (* Check if the loan has already been treated - it can happen
                   for the same reason as for borrows, and also because shared
                   loans contain sets of borrows (meaning that when taking care
                   of one loan, we can merge several other loans at once).
                *)
                Marked.loan_is_merged marked
              then ()
              else (
                (* Do not set the loans as merged yet *)
                log#ltrace
                  (lazy
                    (__FUNCTION__ ^ ": merging loan: " ^ Marked.to_string marked));
                (* Check if we need to filter it *)
                if Marked.filter_marked marked then ()
                else
                  (* Lookup the contents *)
                  let lc0 = Map.find_opt marked loan_to_content0 in
                  let lc1 = Map.find_opt marked loan_to_content1 in
                  (* Merge *)
                  let ml, av =
                    match (lc0, lc1) with
                    | None, Some lc | Some lc, None ->
                        Marked.make_loan_value marked lc
                    | Some _, Some _ ->
                        (* With projection markers, shared loans should not be duplicated *)
                        craise __FILE__ __LINE__ span "Unreachable"
                    | None, None -> craise __FILE__ __LINE__ span "Unreachable"
                  in
                  List.iter Marked.set_loan_as_merged ml;
                  push_loan_avalue av))
        borrows_loans
  end in
  (* First merge the concrete borrows/loans *)
  let module MergeConcrete =
    Merge (MarkedBorrowId.Set) (MarkedBorrowId.Map)
      (struct
        type borrow_content =
          ( ty * Values.borrow_content,
            ty * Values.aborrow_content )
          concrete_or_abs

        type loan_content =
          (ty * Values.loan_content, ty * Values.aloan_content) concrete_or_abs

        let to_string = MarkedBorrowId.to_string
        let borrow_is_merged = borrow_is_merged
        let loan_is_merged = loan_is_merged
        let filter_marked = filter_concrete
        let set_borrow_as_merged = set_borrow_as_merged
        let set_loan_as_merged = set_loan_as_merged

        let make_borrow_value _ bc : typed_avalue =
          match bc with
          | Concrete _ ->
              (* This can happen only in case of nested borrows - a concrete
                 borrow can only happen inside a shared loan *)
              craise __FILE__ __LINE__ span "Unreachable"
          | Abstract (ty, bc) -> { value = ABorrow bc; ty }

        let make_loan_value _ lc : marked_borrow_id list * typed_avalue =
          match lc with
          | Concrete _ ->
              (* This shouldn't happen because the avalues should
                 have been destructured. *)
              craise __FILE__ __LINE__ span "Unreachable"
          | Abstract (ty, lc) -> (
              match lc with
              | ASharedLoan (pm, bids, sv, child) ->
                  let bids = filter_bids pm bids in
                  sanity_check __FILE__ __LINE__
                    (not (BorrowId.Set.is_empty bids))
                    span;
                  sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
                  sanity_check __FILE__ __LINE__
                    (not (value_has_loans_or_borrows (Some span) ctx sv.value))
                    span;
                  let marked_bids =
                    List.map (fun bid -> (pm, bid)) (BorrowId.Set.elements bids)
                  in
                  let lc = ASharedLoan (pm, bids, sv, child) in
                  (marked_bids, { value = ALoan lc; ty })
              | AMutLoan (pm, bid, _) ->
                  ([ (pm, bid) ], { value = ALoan lc; ty })
              | AEndedMutLoan _
              | AEndedSharedLoan _
              | AIgnoredMutLoan _
              | AEndedIgnoredMutLoan _
              | AIgnoredSharedLoan _ ->
                  (* The abstraction has been destructured, so those shouldn't appear *)
                  craise __FILE__ __LINE__ span "Unreachable")
      end)
  in
  (* Note that we first explore the borrows/loans of [abs0], because we
     want to merge *into* this abstraction, and as a consequence we want to
     preserve its structure as much as we can *)
  let borrows_loans = List.append borrows_loans0 borrows_loans1 in
  MergeConcrete.merge borrow_to_content0 borrow_to_content1 loan_to_content0
    loan_to_content1 borrows_loans;

  (* Do the same for the symbolic projections *)
  let borrows_loans = List.append borrow_loan_projs0 borrow_loan_projs1 in
  (* First merge the concrete borrows/loans *)
  let module MergeSymbolic =
    Merge (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
      (struct
        type borrow_content = ty * proj_marker * aproj
        type loan_content = ty * proj_marker * aproj

        let to_string = marked_norm_symb_proj_to_string ctx
        let borrow_is_merged = borrow_proj_is_merged
        let loan_is_merged = loan_proj_is_merged
        let filter_marked = filter_symbolic
        let set_borrow_as_merged = set_borrow_proj_as_merged
        let set_loan_as_merged = set_loan_proj_as_merged

        let make_borrow_value _ (ty, pm, proj) =
          { value = ASymbolic (pm, proj); ty }

        let make_loan_value marked (ty, pm, proj) =
          ([ marked ], { value = ASymbolic (pm, proj); ty })
      end)
  in
  MergeSymbolic.merge borrow_proj_to_content0 borrow_proj_to_content1
    loan_proj_to_content0 loan_proj_to_content1 borrows_loans;

  (* Reverse the avalues (we visited the loans/borrows in order, but pushed
     new values at the beggining of the stack of avalues). Also note that we
     put the borrows, then the loans. *)
  List.rev !borrow_avalues @ List.rev !loan_avalues

(** Auxiliary function for {!merge_abstractions}.

    Phase 2 of the merge: we remove markers, by merging pairs of the same
    element with different markers into one element without markers.

    Example:
    {[
      |MB l0|, MB l1, ︙MB l0︙
           ~~>
      MB l0, MB l1
    ]} *)
let merge_abstractions_merge_markers (span : Meta.span)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : typed_avalue list) :
    typed_avalue list =
  log#ltrace
    (lazy
      (__FUNCTION__ ^ ":\n- avalues:\n"
      ^ String.concat ", " (List.map (typed_avalue_to_string ctx) avalues)));

  (* We linearly traverse the list of avalues created through the first phase. *)

  (* Compute some relevant information *)
  let {
    loans = _;
    borrows = _;
    borrows_loans;
    loan_to_content;
    borrow_to_content;
    loan_projs = _;
    borrow_projs = _;
    borrow_loan_projs;
    loan_proj_to_content;
    borrow_proj_to_content;
  } =
    compute_merge_abstraction_info span ctx owned_regions avalues
  in

  (* Utilities to accumulate the list of values resulting from the merge *)
  let avalues = ref [] in
  let push_avalue av =
    log#ltrace
      (lazy
        (__FUNCTION__ ^ ": push_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    avalues := av :: !avalues
  in

  (* We will merge elements with the same borrow/loan id, but with different markers.
     Hence, we only keep track of the id here: if [Borrow PLeft bid] has been merged
     and we see [Borrow PRight bid], we should ignore [Borrow PRight bid] (because
     when seeing [Borrow PLeft bid] we stored [Borrow PNone bid] into the list
     of values to insert in the resulting abstraction). *)
  let merged_borrows = ref BorrowId.Set.empty in
  let merged_loans = ref BorrowId.Set.empty in
  let merged_borrow_projs = ref NormSymbProj.Set.empty in
  let merged_loan_projs = ref NormSymbProj.Set.empty in

  let borrow_is_merged id = BorrowId.Set.mem id !merged_borrows in
  let set_borrow_as_merged id =
    merged_borrows := BorrowId.Set.add id !merged_borrows
  in

  let borrow_proj_is_merged m =
    NormSymbProj.Set.mem
      (marked_norm_symb_proj_to_unmarked m)
      !merged_borrow_projs
  in
  let set_borrow_proj_as_merged m =
    merged_borrow_projs :=
      NormSymbProj.Set.add
        (marked_norm_symb_proj_to_unmarked m)
        !merged_borrow_projs
  in

  let loan_is_merged id = BorrowId.Set.mem id !merged_loans in
  let set_loan_as_merged id =
    merged_loans := BorrowId.Set.add id !merged_loans
  in
  let set_loans_as_merged ids = BorrowId.Set.iter set_loan_as_merged ids in

  let loan_proj_is_merged m =
    NormSymbProj.Set.mem
      (marked_norm_symb_proj_to_unmarked m)
      !merged_loan_projs
  in
  let set_loan_proj_as_merged m =
    merged_loan_projs :=
      NormSymbProj.Set.add
        (marked_norm_symb_proj_to_unmarked m)
        !merged_loan_projs
  in

  (* Recreates an avalue from a borrow_content. *)
  let avalue_from_bc = function
    | Concrete (_, _) ->
        (* This can happen only in case of nested borrows, and should have been filtered during phase 1 *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty, bc) -> { value = ABorrow bc; ty }
  in

  (* Recreates an avalue from a loan_content, and adds the set of loan ids as merged.
     See the comment in the loop below for a detailed explanation *)
  let avalue_from_lc = function
    | Concrete (_, _) ->
        (* This can happen only in case of nested borrows, and should have been filtered
           during phase 1 *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty, bc) ->
        (match bc with
        | AMutLoan (_, id, _) -> set_loan_as_merged id
        | ASharedLoan (_, ids, _, _) -> set_loans_as_merged ids
        | _ -> craise __FILE__ __LINE__ span "Unreachable");
        { value = ALoan bc; ty }
  in

  (* Recreates an avalue from a borrow projector. *)
  let avalue_from_borrow_proj ((ty, pm, proj) : ty * proj_marker * aproj) :
      typed_avalue =
    { value = ASymbolic (pm, proj); ty }
  in

  (* Recreates an avalue from a loan_content, and adds the set of loan ids as merged.
     See the comment in the loop below for a detailed explanation *)
  let avalue_from_loan_proj ((ty, pm, proj) : ty * proj_marker * aproj) :
      typed_avalue =
    { value = ASymbolic (pm, proj); ty }
  in

  let complementary_markers pm0 pm1 =
    (pm0 = PLeft && pm1 = PRight) || (pm0 = PRight && pm1 = PLeft)
  in

  (* Some utility functions *)
  (* Merge two aborrow contents - note that those contents must have the same id *)
  let merge_aborrow_contents (ty0 : rty) (bc0 : aborrow_content) (ty1 : rty)
      (bc1 : aborrow_content) : typed_avalue =
    match (bc0, bc1) with
    | AMutBorrow (pm0, id0, child0), AMutBorrow (pm1, id1, child1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (Option.get merge_funs).merge_amut_borrows id0 ty0 pm0 child0 ty1 pm1
          child1
    | ASharedBorrow (pm0, id0), ASharedBorrow (pm1, id1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (Option.get merge_funs).merge_ashared_borrows id0 ty0 pm0 ty1 pm1
    | AProjSharedBorrow _, AProjSharedBorrow _ ->
        (* Unreachable because requires nested borrows *)
        craise __FILE__ __LINE__ span "Unreachable"
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_g_borrow_contents (bc0 : g_borrow_content_with_ty)
      (bc1 : g_borrow_content_with_ty) : typed_avalue =
    match (bc0, bc1) with
    | Concrete _, Concrete _ ->
        (* This can happen only in case of nested borrows - the borrow has
           to appear inside a shared loan. *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty0, bc0), Abstract (ty1, bc1) ->
        merge_aborrow_contents ty0 bc0 ty1 bc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let loan_content_to_ids (lc : g_loan_content_with_ty) : BorrowId.Set.t =
    match lc with
    | Abstract (_, lc) -> (
        match lc with
        | AMutLoan (_, id, _) -> BorrowId.Set.singleton id
        | ASharedLoan (_, ids, _, _) -> ids
        | _ ->
            (* Unreachable because those cases are ignored (ended/ignored borrows)
               or inconsistent *)
            craise __FILE__ __LINE__ span "Unreachable")
    | Concrete _ ->
        (* Can only happen with nested borrows *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_aloan_contents (ty0 : rty) (lc0 : aloan_content) (ty1 : rty)
      (lc1 : aloan_content) : typed_avalue =
    match (lc0, lc1) with
    | AMutLoan (pm0, id0, child0), AMutLoan (pm1, id1, child1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (* Merge *)
        (Option.get merge_funs).merge_amut_loans id0 ty0 pm0 child0 ty1 pm1
          child1
    | ASharedLoan (pm0, ids0, sv0, child0), ASharedLoan (pm1, ids1, sv1, child1)
      ->
        (* Check that the sets of ids are the same - if it is not the case, it
           means we actually need to merge more than 2 avalues: we ignore this
           case for now *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (BorrowId.Set.equal ids0 ids1) span;
        let ids = ids0 in
        (* Merge *)
        (Option.get merge_funs).merge_ashared_loans ids ty0 pm0 sv0 child0 ty1
          pm1 sv1 child1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  (* Note that because we may filter ids from a set of id, this function has
     to register the merged loan ids: the caller doesn't do it (contrary to
     the borrow case) *)
  let merge_g_loan_contents (lc0 : g_loan_content_with_ty)
      (lc1 : g_loan_content_with_ty) : typed_avalue =
    match (lc0, lc1) with
    | Concrete _, Concrete _ ->
        (* This can not happen: the values should have been destructured *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty0, lc0), Abstract (ty1, lc1) ->
        merge_aloan_contents ty0 lc0 ty1 lc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_borrow_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : typed_avalue =
    sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
    match (proj0, proj1) with
    | AProjBorrows proj0, AProjBorrows proj1 ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__
          (proj0.proj.sv_id = proj1.proj.sv_id)
          span;
        (* Merge *)
        (Option.get merge_funs).merge_aborrow_projs ty0 pm0 proj0 ty1 pm1 proj1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_loan_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : typed_avalue =
    sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
    match (proj0, proj1) with
    | AProjLoans proj0, AProjLoans proj1 ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__
          (proj0.proj.sv_id = proj1.proj.sv_id)
          span;
        (* Merge *)
        (Option.get merge_funs).merge_aloan_projs ty0 pm0 proj0 ty1 pm1 proj1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let invert_proj_marker = function
    | PNone -> craise __FILE__ __LINE__ span "Unreachable"
    | PLeft -> PRight
    | PRight -> PLeft
  in

  (* We now iter over all the accumulated elements. For each element with a marker
     (i.e., not [PNone]), we attempt to find the dual element in the rest of the list. If so,
     we remove both elements, and insert the same element but with no marker.

     Importantly, attempting the merge when first seeing a marked element allows us to preserve
     the structure of the abstraction we are merging into (i.e., abs0). Note that during phase 1,
     we traversed the borrow/loans of the abs 0 first, and hence these elements are at the top of
     the list. *)
  let module Merge
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt)
      (Marked : sig
        type borrow_content
        type loan_content
        type loan_id_set

        val get_marker : Set.elt -> proj_marker
        val invert_marker : Set.elt -> Set.elt
        val borrow_is_merged : Set.elt -> bool
        val loan_is_merged : Set.elt -> bool
        val set_borrow_as_merged : Set.elt -> unit
        val set_loans_as_merged : loan_id_set -> unit
        val loan_content_to_ids : loan_content -> loan_id_set
        val avalue_from_bc : borrow_content -> typed_avalue
        val avalue_from_lc : loan_content -> typed_avalue

        val merge_borrow_contents :
          borrow_content -> borrow_content -> typed_avalue

        val merge_loan_contents : loan_content -> loan_content -> typed_avalue
      end) =
  struct
    let merge (borrow_to_content : Marked.borrow_content Map.t)
        (loan_to_content : Marked.loan_content Map.t) borrows_loans =
      List.iter
        (function
          | Borrow marked ->
              (* Case disjunction: no marker/marker *)
              if Marked.get_marker marked = PNone then begin
                sanity_check __FILE__ __LINE__
                  (not (Marked.borrow_is_merged marked))
                  span;
                (* This element has no marker. We do not filter it, hence we retrieve the
                   contents and inject it into the avalues list *)
                let bc = Map.find marked borrow_to_content in
                push_avalue (Marked.avalue_from_bc bc);
                (* Setting the borrow as merged is not really necessary but we do it
                   for consistency, and this allows us to do some sanity checks. *)
                Marked.set_borrow_as_merged marked
              end
              else if
                (* Check if the borrow has already been merged. If so, it means we already
                   added the merged value to the avalues list, and we can thus skip it *)
                Marked.borrow_is_merged marked
              then ()
              else (
                (* Not merged: set it as merged *)
                Marked.set_borrow_as_merged marked;
                (* Lookup the content of the borrow *)
                let bc0 = Map.find marked borrow_to_content in
                (* Check if there exists the same borrow but with the complementary marker *)
                let obc1 =
                  Map.find_opt (Marked.invert_marker marked) borrow_to_content
                in
                match obc1 with
                | None ->
                    (* No dual element found, we keep the current one in the list of avalues,
                       with the same marker *)
                    push_avalue (Marked.avalue_from_bc bc0)
                | Some bc1 ->
                    (* We have borrows with left and right markers in the environment.
                       We merge their values, and push the result to the list of avalues.
                       The merge will also remove the projection marker *)
                    push_avalue (Marked.merge_borrow_contents bc0 bc1))
          | Loan marked -> (
              if
                (* Case disjunction: no marker/marker *)
                Marked.get_marker marked = PNone
              then (
                if
                  (* Since we currently have a set of loan ids associated to a shared_borrow, we can
                     have several loan ids associated to the same element. Hence, we need to ensure
                     that we did not previously add the corresponding element.

                     To do so, we use the loan id merged set for both marked and unmarked values.
                     The assumption is that we should not have the same loan id for both an unmarked
                     element and a marked element. It might be better to sanity-check this.

                     Adding the loan id to the merged set will be done inside avalue_from_lc.

                     Remark: Once we move to a single loan id per shared_loan, this should not
                     be needed anymore.
                  *)
                  Marked.loan_is_merged marked
                then ()
                else
                  let lc = Map.find marked loan_to_content in
                  push_avalue (Marked.avalue_from_lc lc);
                  (* Mark as merged *)
                  let ids = Marked.loan_content_to_ids lc in
                  Marked.set_loans_as_merged ids)
              else if
                (* Check if the loan has already been merged. If so, we skip it. *)
                Marked.loan_is_merged marked
              then ()
              else
                let lc0 = Map.find marked loan_to_content in
                let olc1 =
                  Map.find_opt (Marked.invert_marker marked) loan_to_content
                in
                (* Mark as merged *)
                let ids0 = Marked.loan_content_to_ids lc0 in
                Marked.set_loans_as_merged ids0;
                match olc1 with
                | None ->
                    (* No dual element found, we keep the current one with the same marker *)
                    push_avalue (Marked.avalue_from_lc lc0)
                | Some lc1 ->
                    push_avalue (Marked.merge_loan_contents lc0 lc1);
                    (* Mark as merged *)
                    let ids1 = Marked.loan_content_to_ids lc1 in
                    Marked.set_loans_as_merged ids1))
        borrows_loans
  end in
  (* Merge the concrete borrows/loans *)
  let module MergeConcrete =
    Merge (MarkedBorrowId.Set) (MarkedBorrowId.Map)
      (struct
        type borrow_content = g_borrow_content_with_ty
        type loan_content = g_loan_content_with_ty
        type loan_id_set = Values.loan_id_set

        let get_marker (pm, _) = pm
        let invert_marker (pm, bid) = (invert_proj_marker pm, bid)
        let borrow_is_merged (_, bid) = borrow_is_merged bid
        let loan_is_merged (_, bid) = loan_is_merged bid
        let set_borrow_as_merged (_, bid) = set_borrow_as_merged bid
        let set_loans_as_merged bids = set_loans_as_merged bids
        let loan_content_to_ids = loan_content_to_ids
        let avalue_from_bc = avalue_from_bc
        let avalue_from_lc = avalue_from_lc
        let merge_borrow_contents = merge_g_borrow_contents
        let merge_loan_contents = merge_g_loan_contents
      end)
  in
  MergeConcrete.merge borrow_to_content loan_to_content borrows_loans;

  (* Merge the symbolic borrows/loans *)
  let module MergeSymbolic =
    Merge (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
      (struct
        type borrow_content = ty * proj_marker * aproj
        type loan_content = ty * proj_marker * aproj
        type loan_id_set = marked_norm_symb_proj

        let get_marker marked = marked.pm

        let invert_marker marked =
          { marked with pm = invert_proj_marker marked.pm }

        let borrow_is_merged marked = borrow_proj_is_merged marked
        let loan_is_merged marked = loan_proj_is_merged marked
        let set_borrow_as_merged marked = set_borrow_proj_as_merged marked
        let set_loans_as_merged bids = set_loan_proj_as_merged bids

        let loan_content_to_ids ((_, pm, proj) : ty * proj_marker * aproj) :
            marked_norm_symb_proj =
          match proj with
          | AProjLoans { proj; _ } ->
              let norm_proj_ty = normalize_proj_ty owned_regions proj.proj_ty in
              { pm; sv_id = proj.sv_id; norm_proj_ty }
          | _ -> internal_error __FILE__ __LINE__ span

        let avalue_from_bc = avalue_from_borrow_proj
        let avalue_from_lc = avalue_from_loan_proj
        let merge_borrow_contents = merge_borrow_projs
        let merge_loan_contents = merge_loan_projs
      end)
  in
  MergeSymbolic.merge borrow_proj_to_content loan_proj_to_content
    borrow_loan_projs;

  (* Reorder the avalues. We want the avalues to have the borrows first, then
     the loans (this structure is more stable when we merge abstractions together,
     meaning it is easier to find fixed points).
  *)
  let avalues = List.rev !avalues in
  let is_borrow (av : typed_avalue) : bool =
    match av.value with
    | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
    | ALoan _ | ASymbolic (_, AProjLoans _) -> false
    | _ -> craise __FILE__ __LINE__ span "Unexpected"
  in
  let aborrows, aloans = List.partition is_borrow avalues in
  List.append aborrows aloans

(** Auxiliary function.

    Merge two abstractions into one, without updating the context. *)
let merge_abstractions (span : Meta.span) (abs_kind : abs_kind) (can_end : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : abs =
  log#ltrace
    (lazy
      ("merge_abstractions:\n- abs0:\n"
      ^ abs_to_string span ctx abs0
      ^ "\n\n- abs1:\n"
      ^ abs_to_string span ctx abs1));
  (* Sanity check: we can't merge an abstraction with itself *)
  sanity_check __FILE__ __LINE__ (abs0.abs_id <> abs1.abs_id) span;

  (* Check that the abstractions are destructured (i.e., there are no nested
     values, etc.) *)
  if !Config.sanity_checks then (
    let destructure_shared_values = true in
    sanity_check __FILE__ __LINE__
      (abs_is_destructured span destructure_shared_values ctx abs0)
      span;
    sanity_check __FILE__ __LINE__
      (abs_is_destructured span destructure_shared_values ctx abs1)
      span);

  (* Compute the ancestor regions, owned regions, etc.
     Note that one of the two abstractions might a parent of the other *)
  let parents =
    AbstractionId.Set.diff
      (AbstractionId.Set.union abs0.parents abs1.parents)
      (AbstractionId.Set.of_list [ abs0.abs_id; abs1.abs_id ])
  in
  let original_parents = AbstractionId.Set.elements parents in
  let regions =
    let owned = RegionId.Set.union abs0.regions.owned abs1.regions.owned in
    { owned }
  in

  (* Phase 1: simplify the loans coming from the left abstraction with
     the borrows coming from the right abstraction. *)
  let avalues =
    merge_abstractions_merge_loan_borrow_pairs span merge_funs ctx abs0 abs1
  in

  (* Phase 2: we now remove markers, by merging pairs of the same element with
     different markers into one element. To do so, we linearly traverse the list
     of avalues created through the first phase. *)
  let avalues =
    merge_abstractions_merge_markers span merge_funs ctx regions.owned avalues
  in

  (* Create the new abstraction *)
  let abs_id = fresh_abstraction_id () in
  let abs =
    {
      abs_id;
      kind = abs_kind;
      can_end;
      parents;
      original_parents;
      regions;
      avalues;
    }
  in

  (* Sanity check *)
  sanity_check __FILE__ __LINE__ (abs_is_destructured span true ctx abs) span;
  (* Return *)
  abs

(** Merge the regions in a context to a single region *)
let ctx_merge_regions (ctx : eval_ctx) (rid : RegionId.id)
    (rids : RegionId.Set.t) : eval_ctx =
  let rsubst x = if RegionId.Set.mem x rids then rid else x in
  let env = Substitute.env_subst_rids rsubst ctx.env in
  { ctx with env }

let merge_into_first_abstraction (span : Meta.span) (abs_kind : abs_kind)
    (can_end : bool) (merge_funs : merge_duplicates_funcs option)
    (ctx : eval_ctx) (abs_id0 : AbstractionId.id) (abs_id1 : AbstractionId.id) :
    eval_ctx * AbstractionId.id =
  (* Small sanity check *)
  sanity_check __FILE__ __LINE__ (abs_id0 <> abs_id1) span;

  (* Lookup the abstractions *)
  let abs0 = ctx_lookup_abs ctx abs_id0 in
  let abs1 = ctx_lookup_abs ctx abs_id1 in

  (* Merge them *)
  let nabs =
    merge_abstractions span abs_kind can_end merge_funs ctx abs0 abs1
  in
  Invariants.opt_type_check_abs span ctx nabs;

  (* Update the environment: replace the abstraction 0 with the result of the merge,
     remove the abstraction 1 *)
  let ctx = fst (ctx_subst_abs span ctx abs_id0 nabs) in
  let ctx = fst (ctx_remove_abs span ctx abs_id1) in

  (* Merge all the regions from the abstraction into one (the first - i.e., the
     one with the smallest id). Note that we need to do this in the whole
     environment, as those regions may be referenced as ancestor regions by
     the other abstractions, and may be present in symbolic values, etc. (this
     is not the case if there are no nested borrows, but we anticipate).
  *)
  let ctx =
    let regions = nabs.regions.owned in
    (* Pick the first region id (this is the smallest) *)
    let rid = RegionId.Set.min_elt regions in
    (* If there is only one region, do nothing *)
    if RegionId.Set.cardinal regions = 1 then ctx
    else
      let rids = RegionId.Set.remove rid regions in
      ctx_merge_regions ctx rid rids
  in

  (* Return *)
  (ctx, nabs.abs_id)

(** Reorder the loans and borrows inside the fresh abstractions.

    See {!reorder_fresh_abs}. *)
let reorder_loans_borrows_in_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let reorder_in_fresh_abs (abs : abs) : abs =
    (* Split between the loans and borrows, and between the concrete
       and symbolic values. *)
    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
      | ALoan _ | ASymbolic (_, AProjLoans _) -> false
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let is_concrete (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ALoan _ -> true
      | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> false
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let aborrows, aloans = List.partition is_borrow abs.avalues in
    let aborrows, borrow_projs = List.partition is_concrete aborrows in
    let aloans, loan_projs = List.partition is_concrete aloans in

    (* Reoder the borrows, and the loans.

       After experimenting, it seems that a good way of reordering the loans
       and the borrows to find fixed points is simply to sort them by increasing
       order of id (taking the smallest id of a set of ids, in case of sets).

       This is actually not as arbitrary as it might seem, because the ids give
       us the order in which we introduced those borrows/loans.

       We do the same thing for the symbolic values: we use the symbolic ids.
       The final order is:
         borrows, borrow projectors, loans, loan projectors
       (all sorted by increasing id)
    *)
    let get_borrow_id (av : typed_avalue) : BorrowId.id =
      match av.value with
      | ABorrow (AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          bid
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let get_loan_id (av : typed_avalue) : BorrowId.id =
      match av.value with
      | ALoan (AMutLoan (pm, lid, _)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          lid
      | ALoan (ASharedLoan (pm, lids, _, _)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          BorrowId.Set.min_elt lids
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let get_symbolic_id (av : typed_avalue) : SymbolicValueId.id =
      match av.value with
      | ASymbolic (pm, aproj) -> begin
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          match aproj with
          | AProjLoans { proj; _ } | AProjBorrows { proj; _ } -> proj.sv_id
          | _ -> craise __FILE__ __LINE__ span "Unexpected"
        end
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let compare_pair :
        'a. ('a -> 'a -> int) -> 'a * typed_avalue -> 'a * typed_avalue -> int =
     fun compare_id x y ->
      let fst = compare_id (fst x) (fst y) in
      cassert __FILE__ __LINE__ (fst <> 0) span
        ("Unexpected: can't compare: '"
        ^ typed_avalue_to_string ctx (snd x)
        ^ "' with '"
        ^ typed_avalue_to_string ctx (snd y)
        ^ "'");
      fst
    in
    (* We use ordered maps to reorder the borrows and loans *)
    let reorder :
        'a.
        (typed_avalue -> 'a) ->
        ('a -> 'a -> int) ->
        typed_avalue list ->
        typed_avalue list =
     fun get_id compare_id values ->
      let values = List.map (fun v -> (get_id v, v)) values in
      List.map snd (List.stable_sort (compare_pair compare_id) values)
    in
    let aborrows = reorder get_borrow_id compare_borrow_id aborrows in
    let borrow_projs =
      reorder get_symbolic_id compare_symbolic_value_id borrow_projs
    in
    let aloans = reorder get_loan_id compare_borrow_id aloans in
    let loan_projs =
      reorder get_symbolic_id compare_symbolic_value_id loan_projs
    in
    let avalues = List.concat [ aborrows; borrow_projs; aloans; loan_projs ] in
    { abs with avalues }
  in

  let reorder_in_abs (abs : abs) =
    if AbstractionId.Set.mem abs.abs_id old_abs_ids then abs
    else reorder_in_fresh_abs abs
  in

  let env = env_map_abs reorder_in_abs ctx.env in

  { ctx with env }

type typed_avalue_list = typed_avalue list [@@deriving ord, show]

module OrderedTypedAvalueList :
  Collections.OrderedType with type t = typed_avalue list = struct
  type t = typed_avalue_list

  let compare x y = compare_typed_avalue_list x y
  let to_string x = show_typed_avalue_list x
  let pp_t fmt x = Format.pp_print_string fmt (show_typed_avalue_list x)
  let show_t x = show_typed_avalue_list x
end

let reorder_fresh_abs_aux (span : Meta.span) (old_abs_ids : AbstractionId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  (* Split between the fresh abstractions and the rest of the context *)
  let env, fresh_abs =
    List.partition
      (function
        | EAbs abs -> AbstractionId.Set.mem abs.abs_id old_abs_ids
        | _ -> true)
      ctx.env
  in

  (* Reorder the fresh abstractions.

     We use the content of the abstractions to reorder them.
     In practice, this allows us to reorder the abstractions by using the ids
     of the loans, borrows and symbolic values. This is far from perfect, but
     allows us to have a quite simple matching algorithm for now, to compute
     the joins as well as to check whether two environments are equivalent.
     We may want to make this algorithm more general in the future.
  *)
  let cmp abs0 abs1 =
    match (abs0, abs1) with
    | EAbs abs0, EAbs abs1 ->
        compare_typed_avalue_list abs0.avalues abs1.avalues
    | _ -> internal_error __FILE__ __LINE__ span
  in
  let fresh_abs = List.sort cmp fresh_abs |> List.rev in

  (* Reconstruct the environment *)
  let env = fresh_abs @ env in

  { ctx with env }

let reorder_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  reorder_loans_borrows_in_fresh_abs span allow_markers old_abs_ids ctx
  |> reorder_fresh_abs_aux span old_abs_ids
