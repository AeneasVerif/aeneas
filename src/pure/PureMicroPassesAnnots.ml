open Pure
open PureUtils
open TranslateCore
open PureMicroPassesBase

(** Introduce type annotations.

    See [add_type_annotations].

    Note that we use the context only for printing. *)
let add_type_annotations_to_fun_decl (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation FunDeclId.Map.t)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl TypeDeclId.Map.t) (def : fun_decl) : fun_decl =
  let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
  [%ldebug PrintPure.fun_decl_to_string fmt def];
  let span = def.item_meta.span in
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
  let texpr_to_string (x : texpr) : string =
    PrintPure.texpr_to_string fmt false "" "  " x
  in
  let ty_to_string (x : ty) : string = PrintPure.ty_to_string fmt false x in
  let generic_params_to_string (generics : generic_params) : string =
    "["
    ^ String.concat ", " (PrintPure.generic_params_to_strings fmt generics)
    ^ "]"
  in
  let generic_args_to_string (generics : generic_args) : string =
    "["
    ^ String.concat ", " (PrintPure.generic_args_to_strings fmt false generics)
    ^ "]"
  in
  let fun_sig_to_string (sg : fun_sig) : string =
    PrintPure.fun_sig_to_string fmt sg
  in

  (* The map visitor tracks each sub-expression's "expected type" as a type
     possibly containing holes — unknown positions encoded as [TVar (Free id)]
     with a negative id. [-1] is the "universal" hole. Negative ids strictly
     less than [-1] are "fresh tags" allocated per call to the visitor: they
     mark which type parameter of the callee a hole came from, which lets us
     unify against the args' actual types to recover the callee's type-
     parameter substitution (used for sibling propagation between args and
     for the application-level annotation decision).

     When the expected type at a sub-expression still has holes that prevent
     the elaborator from determining a callee's implicit type parameter, we
     introduce a type annotation. *)
  let hole : ty = TVar (T.Free (TypeVarId.of_int (-1))) in
  let cg_hole : const_generic =
    CgVar (T.Free (ConstGenericVarId.of_int (-1)))
  in

  let fresh_hole_counter = ref (-2) in
  let alloc_fresh_ty_id () : TypeVarId.id =
    let id = TypeVarId.of_int !fresh_hole_counter in
    decr fresh_hole_counter;
    id
  in
  let alloc_fresh_cg_id () : ConstGenericVarId.id =
    let id = ConstGenericVarId.of_int !fresh_hole_counter in
    decr fresh_hole_counter;
    id
  in
  let is_fresh_ty_id (id : TypeVarId.id) : bool = TypeVarId.to_int id < -1 in
  let is_fresh_cg_id (id : ConstGenericVarId.id) : bool =
    ConstGenericVarId.to_int id < -1
  in

  (* Check whether a type or const generic contains the universal hole [-1]. *)
  let cg_is_universal_hole (cg : const_generic) : bool =
    match cg with
    | CgVar (T.Free id) -> ConstGenericVarId.to_int id = -1
    | _ -> false
  in
  let rec ty_has_hole (t : ty) : bool =
    match t with
    | TVar (T.Free id) -> TypeVarId.to_int id = -1
    | TVar (T.Bound _) -> false
    | TLiteral _ | TNever | TError -> false
    | TAdt (_, generics) -> generics_has_hole generics
    | TArrow (t1, t2) -> ty_has_hole t1 || ty_has_hole t2
    | TTraitType _ | TDynTrait _ -> false
  and generics_has_hole (g : generic_args) : bool =
    List.exists ty_has_hole g.types
    || List.exists cg_is_universal_hole g.const_generics
  in

  (* Fresh-tag substitution: maps fresh tag IDs to the concrete types/cgs
     they have been resolved to. Tags are allocated per call and never
     reused, so the substitution can safely grow across the whole pass. *)
  let ty_subst = ref TypeVarId.Map.empty in
  let cg_subst = ref ConstGenericVarId.Map.empty in

  (* Apply the current substitution: replace resolved fresh tags with their
     value; replace unresolved fresh tags with the universal hole. *)
  let rec apply_subst (t : ty) : ty =
    match t with
    | TVar (T.Free id) when is_fresh_ty_id id -> (
        match TypeVarId.Map.find_opt id !ty_subst with
        | Some t' -> apply_subst t'
        | None -> hole)
    | TAdt (id, g) -> TAdt (id, apply_subst_generics g)
    | TArrow (t1, t2) -> TArrow (apply_subst t1, apply_subst t2)
    | _ -> t
  and apply_subst_cg (cg : const_generic) : const_generic =
    match cg with
    | CgVar (T.Free id) when is_fresh_cg_id id -> (
        match ConstGenericVarId.Map.find_opt id !cg_subst with
        | Some cg' -> apply_subst_cg cg'
        | None -> cg_hole)
    | _ -> cg
  and apply_subst_generics (g : generic_args) : generic_args =
    {
      g with
      types = List.map apply_subst g.types;
      const_generics = List.map apply_subst_cg g.const_generics;
    }
  in

  (* Unify a template (possibly containing fresh tags) against an actual
     (concrete) type, recording the implied tag -> ty bindings. We never
     learn a binding to a value containing a hole. *)
  let rec unify_against (template : ty) (actual : ty) : unit =
    match (template, actual) with
    | TVar (T.Free id), _ when is_fresh_ty_id id ->
        if (not (TypeVarId.Map.mem id !ty_subst)) && not (ty_has_hole actual)
        then ty_subst := TypeVarId.Map.add id actual !ty_subst
    | TAdt (id1, g1), TAdt (id2, g2) when id1 = id2 ->
        if List.length g1.types = List.length g2.types then
          List.iter2 unify_against g1.types g2.types;
        if List.length g1.const_generics = List.length g2.const_generics then
          List.iter2 unify_cg_against g1.const_generics g2.const_generics
    | TArrow (t1a, t2a), TArrow (t1b, t2b) ->
        unify_against t1a t1b;
        unify_against t2a t2b
    | _ -> ()
  and unify_cg_against (template : const_generic) (actual : const_generic) :
      unit =
    match template with
    | CgVar (T.Free id) when is_fresh_cg_id id ->
        if
          (not (ConstGenericVarId.Map.mem id !cg_subst))
          && not (cg_is_universal_hole actual)
        then cg_subst := ConstGenericVarId.Map.add id actual !cg_subst
    | _ -> ()
  in

  (* Small helper to add a type annotation *)
  let mk_type_annot (e : texpr) : texpr =
    { e = Meta (TypeAnnot, e); ty = e.ty }
  in

  let rec visit (ty : ty) (e : texpr) : texpr =
    [%ldebug "visit:\n- ty: " ^ ty_to_string ty ^ "\n- e: " ^ texpr_to_string e];
    match e.e with
    | FVar _ | CVar _ | Const _ | EError _ -> e
    | Qualif q -> begin
        match q.id with
        | AdtCons adt_cons_id ->
            (* A bare ADT constructor is a 0-arg application; the same
               annotation logic as for [App] applies. *)
            visit_adt_cons_app ty e [] adt_cons_id q.generics
        | FunOrOp _
        | Global _
        | Proj _
        | ScalarValProj _
        | TraitConst _
        | MkDynTrait _
        | LoopOp -> e
      end
    | BVar _ -> [%internal_error] span
    | App _ -> visit_App ty e
    | Lambda (pat, e') ->
        (* Decompose the type *)
        let ty' =
          match ty with
          | TArrow (_, ty) -> ty
          | _ -> hole
        in
        { e with e = Lambda (pat, visit ty' e') }
    | Let (monadic, pat, bound, next) ->
        (* Pass the bound's actual type as the expected type. This lets
           sibling propagation skip annotating constructors when context
           already fully determines their type (e.g. match arms whose
           result type is fixed by the surrounding [let ←]). *)
        let bound = visit bound.ty bound in
        let next = visit ty next in
        { e with e = Let (monadic, pat, bound, next) }
    | Switch (discr, body) ->
        let discr = visit discr.ty discr in
        let body = visit_switch_body ty body in
        { e with e = Switch (discr, body) }
    | Loop _ ->
        (* Loops should have been eliminated *)
        [%internal_error] span
    | StructUpdate supd ->
        [%ldebug "exploring: " ^ texpr_to_string e];
        (* Some backends need a type annotation here if we create a new structure
           and if the type is unknown.
           TODO: actually we may change the type of the structure by changing
           one of its fields (it happens when we do an unsized cast in Rust).
           We ignore this case here. *)
        let ty =
          match supd.init with
          | None -> ty
          | Some _ ->
              (* We update a structure (we do not create a new one): we consider that the type is known *)
              e.ty
        in
        begin
          match ty with
          | TAdt (adt_id, generics) ->
              (* The type is known: let's compute the type of the fields and recurse *)
              let field_tys =
                (* There are two cases: the ADT may be an array (it happens when
                   initializing an array) *)
                match adt_id with
                | TBuiltin TArray ->
                    [%sanity_check] span (List.length generics.types = 1);
                    Collections.List.repeat (List.length supd.updates)
                      (List.nth generics.types 0)
                | _ ->
                    PureTypeCheck.get_adt_field_types span type_decls adt_id
                      None generics
              in
              [%ldebug
                "- ty: " ^ ty_to_string ty ^ "\n- field_tys:\n"
                ^ String.concat "\n" (List.map ty_to_string field_tys)
                ^ "\n- supd.update:\n"
                ^ String.concat "\n"
                    (List.map
                       (fun (fid, f) ->
                         FieldId.to_string fid ^ " -> " ^ texpr_to_string f)
                       supd.updates)];
              (* Update the fields *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpr) ->
                    match FieldId.nth_opt field_tys fid with
                    | None -> [%internal_error] span
                    | Some field_ty -> (fid, visit field_ty fe))
                  supd.updates
              in
              { e with e = StructUpdate { supd with updates } }
          | _ ->
              (* The type of the structure is unknown: we add a type annotation.
                 From there, the type of the field updates is known *)
              let updates =
                List.map
                  (fun ((fid, fe) : _ * texpr) -> (fid, visit fe.ty fe))
                  supd.updates
              in
              let e = { e with e = StructUpdate { supd with updates } } in
              (* Add the type annotation, if the backend is Lean *)
              if Config.backend () = Lean then mk_type_annot e else e
        end
    | Meta (meta, e') ->
        let ty = if meta = TypeAnnot then e'.ty else ty in
        { e with e = Meta (meta, visit ty e') }
  and visit_App (ty : ty) (e : texpr) : texpr =
    [%ldebug
      "visit_App:\n- ty: " ^ ty_to_string ty ^ "\n- e: " ^ texpr_to_string e];
    (* Deconstruct the app *)
    let f, args = destruct_apps e in
    (* AdtCons applications go through a separate path which propagates type
       info between sibling args and decides annotation at the App level. *)
    match f.e with
    | Qualif { id = AdtCons adt_cons_id; generics = q_generics } ->
        visit_adt_cons_app ty f args adt_cons_id q_generics
    | _ -> visit_App_other ty e f args
  and visit_App_other (ty : ty) (_e : texpr) (f : texpr) (args : texpr list) :
      texpr =
    (* Compute the types of the arguments: it depends on the function *)
    let mk_holes () = List.map (fun _ -> hole) args in
    let mk_known () = List.map (fun (e : texpr) -> e.ty) args in
    let known_f_ty, known_args_tys =
      let rec compute_known_tys known_ty args =
        match args with
        | [] -> (known_ty, [])
        | _ :: args -> (
            match known_ty with
            | TArrow (ty0, ty1) ->
                let fty, args_tys = compute_known_tys ty1 args in
                (fty, ty0 :: args_tys)
            | _ ->
                let fty, args_tys = compute_known_tys hole args in
                (fty, hole :: args_tys))
      in
      compute_known_tys ty args
    in
    (* evaluate to: (function type, arguments types, needs annotations) *)
    let compute_known_tys_from_fun_id (qualif : qualif) (fid : fun_id) :
        ty * ty list * bool =
      [%ldebug "fid: " ^ PrintPure.regular_fun_id_to_string fmt fid];
      match fid with
      | Pure fid -> begin
          match fid with
          | Return | ToResult -> begin
              match known_args_tys with
              | [ ty ] ->
                  if ty = hole && Config.backend () = Lean then
                    (hole, mk_holes (), false)
                  else (known_f_ty, known_args_tys, false)
              | _ -> (known_f_ty, known_args_tys, false)
            end
          | Loop _ | RecLoopCall _ -> (hole, mk_holes (), true)
          | Discriminant -> (hole, mk_holes (), false)
          | Fail | Assert | FuelDecrease | FuelEqZero ->
              (f.ty, mk_known (), false)
          | UpdateAtIndex _ -> (known_f_ty, known_args_tys, false)
          | ResultUnwrapMut -> (hole, mk_holes (), false)
          | GetTarget -> (f.ty, mk_known (), false)
        end
      | FromLlbc (fid, lp_id) -> begin
          (* Lookup the signature *)
          let sg =
            match fid with
            | FunId (FRegular fid) ->
                let trans_fun =
                  [%silent_unwrap] span
                    (LlbcAst.FunDeclId.Map.find_opt fid trans_funs)
                in
                let trans_fun =
                  match lp_id with
                  | None -> trans_fun.f
                  | Some (lp_id, true) -> Pure.LoopId.nth trans_fun.bodies lp_id
                  | Some (lp_id, false) -> Pure.LoopId.nth trans_fun.loops lp_id
                in
                [%ldebug "function name: " ^ trans_fun.name];
                trans_fun.signature
            | TraitMethod (tref, method_id, method_decl_id) ->
                [%ldebug
                  "method name: "
                  ^ Charon.GAstUtils.get_method_name trans_ctx.crate
                      tref.trait_decl_ref.trait_decl_id method_id];
                if Option.is_some lp_id then
                  [%craise] span
                    "Trying to get a loop subfunction from a method call";
                let method_sig =
                  [%silent_unwrap] span
                    (Charon.Substitute.lookup_flat_method_sig trans_ctx.crate
                       tref.trait_decl_ref.trait_decl_id method_id)
                in
                (* TODO: we shouldn't call `SymbolicToPure` here, there should
                   be a way to translate these signatures earlier. *)
                SymbolicToPureTypes.translate_fun_sig trans_ctx
                  (FRegular method_decl_id) method_sig
                  (List.map (fun _ -> None) method_sig.item_binder_value.inputs)
            | FunId (FBuiltin aid) ->
                Builtin.BuiltinFunIdMap.find aid builtin_sigs
          in
          [%ldebug "signature: " ^ fun_sig_to_string sg];
          (* In case this is a trait method, we need to concatenate the generics
             args of the trait ref with the generics args of the method call itself *)
          let generics =
            match fid with
            | TraitMethod (trait_ref, _, _) ->
                append_generic_args trait_ref.trait_decl_ref.decl_generics
                  qualif.generics
            | _ -> qualif.generics
          in
          let tr_self =
            match fid with
            | TraitMethod (trait_ref, _, _) -> trait_ref.trait_id
            (* Dummy, won't be used since we're not substituting for a trait. *)
            | _ -> UnknownTrait "add_type_annotations_to_fun_decl"
          in
          (* Replace all the unknown implicit type variables with holes.
             Note that we assume that all the trait refs are there, meaning
             we can use them to infer some implicit variables.
          *)
          (* Replace each "unknown" type/const-generic argument with a fresh
             tag (rather than the universal hole). This lets us learn its
             value via unification with concrete sibling arg types — which is
             what enables [List.Cons 3#i32 List.Nil]-style sibling
             propagation to skip unnecessary annotations on [List.Nil]. *)
          let known = sg.known_from_trait_refs in
          let types =
            List.map
              (fun (known, ty) ->
                match known with
                | Known -> ty
                | Unknown -> TVar (T.Free (alloc_fresh_ty_id ())))
              (List.combine known.known_types generics.types)
          in
          let const_generics =
            List.map
              (fun (known, cg) ->
                match known with
                | Known -> cg
                | Unknown -> CgVar (T.Free (alloc_fresh_cg_id ())))
              (List.combine known.known_const_generics generics.const_generics)
          in
          let generics = { qualif.generics with types; const_generics } in
          (* Compute the types of the arguments *)
          [%ldebug
            "- sg.generics: "
            ^ generic_params_to_string sg.generics
            ^ "\n- generics: "
            ^ generic_args_to_string generics];
          let subst =
            make_subst_from_generics_for_trait sg.generics tr_self generics
          in
          let sg = fun_sig_substitute subst sg in
          (known_f_ty, sg.inputs, false)
        end
    in
    let f_ty, args_tys, need_annot =
      match f.e with
      | Qualif qualif -> begin
          match qualif.id with
          | FunOrOp fop -> begin
              match fop with
              | Fun fid -> begin compute_known_tys_from_fun_id qualif fid end
              | Unop unop -> begin
                  match unop with
                  | Not _ | Neg _ | Cast _ | ArrayToSlice ->
                      (known_f_ty, known_args_tys, false)
                end
              | Binop _ -> (known_f_ty, known_args_tys, false)
            end
          | Global _ -> (f.ty, mk_known (), false)
          | AdtCons _ ->
              (* AdtCons applications are handled earlier in [visit_App] via
                 [visit_adt_cons_app], so this branch is unreachable. *)
              [%internal_error] span
          | MkDynTrait _ ->
              (* The type is statically known because of the trait ref *)
              [%sanity_check] span (List.length known_args_tys = 1);
              (known_f_ty, known_args_tys, false)
          | Proj _ | ScalarValProj _ | TraitConst _ ->
              (* Being conservative here *)
              (hole, mk_holes (), false)
          | LoopOp -> (hole, mk_holes (), false)
        end
      | FVar _ ->
          (* We consider that the full type of the function should be known,
             so the type of the arguments should be known *)
          (f.ty, mk_known (), false)
      | BVar _ -> [%internal_error] span
      | _ ->
          (* Being conservative: the type is unknown (we actually shouldn't
             get here) *)
          (hole, mk_holes (), false)
    in
    (* The application may be partial *)
    let num_args = List.length args in
    [%sanity_check] span (num_args <= List.length args_tys);
    let args_tys = Collections.List.prefix num_args args_tys in
    (* Sibling propagation: as we recurse on each arg, refine the remaining
       expected types using what we learned from already-processed siblings.
       For args_tys without fresh tags this collapses to the old behavior. *)
    let args =
      List.map2
        (fun template arg ->
          let expected = apply_subst template in
          let visited = visit expected arg in
          unify_against template visited.ty;
          visited)
        args_tys args
    in
    let f = visit f_ty f in
    let e = [%add_loc] mk_apps span f args in
    if need_annot then mk_type_annot e else e
  and visit_adt_cons_app (ty : ty) (f : texpr) (args : texpr list)
      (adt_cons_id : adt_cons_id) (q_generics : generic_args) : texpr =
    (* Process an application of an ADT constructor (possibly 0-ary) per the
       design principle: if any of the constructor's type parameters cannot
       be inferred from the args we passed AND the expected outer type still
       has holes, annotate the whole application.

       To compute "inferable from args" precisely (so we don't over-annotate
       e.g. [List.Cons 3#i32 List.Nil] where Lean infers [T = i32] from the
       first arg), we tag the constructor's type parameters with fresh IDs,
       propagate concrete types between siblings via unification, and check
       at the end which tags remain unresolved. *)
    match adt_cons_id.adt_id with
    | TBuiltin (TArray | TSlice) ->
        (* Arrays/slices: keep the legacy conservative behavior — no
           sibling propagation, no constructor-level annotation. *)
        let args = List.map (visit hole) args in
        [%add_loc] mk_apps span f args
    | _ ->
        let fresh_ty_ids =
          List.map (fun _ -> alloc_fresh_ty_id ()) q_generics.types
        in
        let fresh_cg_ids =
          List.map (fun _ -> alloc_fresh_cg_id ()) q_generics.const_generics
        in
        let fresh_generics =
          {
            types = List.map (fun id -> TVar (T.Free id)) fresh_ty_ids;
            const_generics = List.map (fun id -> CgVar (T.Free id)) fresh_cg_ids;
            trait_refs = [];
          }
        in
        let template_field_tys =
          PureTypeCheck.get_adt_field_types span type_decls adt_cons_id.adt_id
            adt_cons_id.variant_id fresh_generics
        in
        (* Pre-seed substitution from the expected outer type when it matches
           and provides concrete info at some positions. *)
        (match ty with
        | TAdt (id, g)
          when id = adt_cons_id.adt_id
               && List.length g.types = List.length fresh_ty_ids
               && List.length g.const_generics = List.length fresh_cg_ids ->
            List.iter2
              (fun fid concrete ->
                if not (ty_has_hole concrete) then
                  ty_subst := TypeVarId.Map.add fid concrete !ty_subst)
              fresh_ty_ids g.types;
            List.iter2
              (fun fid concrete ->
                if not (cg_is_universal_hole concrete) then
                  cg_subst := ConstGenericVarId.Map.add fid concrete !cg_subst)
              fresh_cg_ids g.const_generics
        | _ -> ());
        (* Iterate args left-to-right, propagating concrete info from
           already-processed siblings. *)
        let num_args = List.length args in
        if num_args > List.length template_field_tys then [%internal_error] span;
        let template_prefix =
          Collections.List.prefix num_args template_field_tys
        in
        let visited_args =
          List.map2
            (fun template arg ->
              let expected = apply_subst template in
              let visited = visit expected arg in
              unify_against template visited.ty;
              visited)
            template_prefix args
        in
        let e' = [%add_loc] mk_apps span f visited_args in
        let some_ty_param_unconstrained =
          List.exists
            (fun id -> not (TypeVarId.Map.mem id !ty_subst))
            fresh_ty_ids
        in
        let some_cg_param_unconstrained =
          List.exists
            (fun id -> not (ConstGenericVarId.Map.mem id !cg_subst))
            fresh_cg_ids
        in
        if
          Config.backend () = Lean
          && (some_ty_param_unconstrained || some_cg_param_unconstrained)
          && ty_has_hole ty
        then mk_type_annot e'
        else e'
  and visit_switch_body (ty : ty) (body : switch_body) : switch_body =
    match body with
    | If (e1, e2) -> If (visit ty e1, visit ty e2)
    | Match branches ->
        let branches =
          List.map
            (fun (b : match_branch) -> { b with branch = visit ty b.branch })
            branches
        in
        Match branches
  in

  (* Update the body *)
  map_open_all_fun_decl_body_expr fresh_fvar_id
    (fun (body : texpr) -> visit body.ty body)
    def

(** Introduce type annotations.

    See [add_type_annotations]

    We need to do this in some backends in particular for the expressions which
    create structures, as the target structure may be ambiguous from the
    context.

    Note that we use the context only for printing. *)
let add_type_annotations (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation list)
    (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl TypeDeclId.Map.t) : pure_fun_translation list =
  let trans_funs_map =
    FunDeclId.Map.of_list
      (List.map
         (fun (fl : pure_fun_translation) -> (fl.f.def_id, fl))
         trans_funs)
  in
  let add_annot (decl : fun_decl) =
    try
      [%ltrace
        let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
        "About to add type annotations to:\n\n"
        ^ PrintPure.fun_decl_to_string fmt decl];
      let decl =
        add_type_annotations_to_fun_decl trans_ctx trans_funs_map builtin_sigs
          type_decls decl
      in
      [%ltrace
        let fmt = trans_ctx_to_pure_fmt_env trans_ctx in
        "After adding type annotations:\n\n"
        ^ PrintPure.fun_decl_to_string fmt decl];
      decl
    with Errors.CFailure error ->
      let name = name_to_string trans_ctx decl.item_meta.name in
      let name_pattern =
        try
          name_to_pattern_string (Some decl.item_meta.span) trans_ctx
            decl.item_meta.name
        with Errors.CFailure _ ->
          "(could not compute the name pattern due to a different error)"
      in
      [%warn_opt_span] error.span
        ("Could not add type annotations to the fun declaration '" ^ name
       ^ " because of previous error\nName pattern: '" ^ name_pattern
       ^ "'.\n\
         \ We will generate code without annotations but it may not type-check."
        );
      (* Keep the unchanged decl *)
      decl
  in
  List.map
    (fun (fl : pure_fun_translation) ->
      let f = add_annot fl.f in
      let loops = List.map add_annot fl.loops in
      let bodies = List.map add_annot fl.bodies in
      { f; loops; bodies })
    trans_funs
