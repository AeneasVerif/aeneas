open Pure
open PureUtils
open TranslateCore
open PureMicroPassesBase

(** A type parameter or a const generic parameter of an ADT, by position *)
type adt_param = TyParam of int | CgParam of int

(** Introduce type annotations.

    See [add_type_annotations].

    Note that we use the context only for printing. *)
let add_type_annotations_to_fun_decl (trans_ctx : trans_ctx)
    (trans_funs : pure_fun_translation FunDeclId.Map.t)
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

  (* The map visitor.

     For every sub-expression we track a "type with holes", where the holes
     are types which are not explicitly known (either because we can't directly
     know the type from the context, or because some type variables are implicit).

     If at some point the type is not known and the type of the expression is
     ambiguous, we introduce a type annotation.

     We encode types with holes in a simple manner: the unknown holes are type
     variables with id = -1.
  *)
  let hole : ty = TVar (T.Free (TypeVarId.of_int (-1))) in
  (* The const generic holes are not really useful, but while we're at it we
     can keep track of them *)
  let cg_hole : const_generic =
    CgVar (T.Free (ConstGenericVarId.of_int (-1)))
  in

  (* Small helper to add a type annotation *)
  let mk_type_annot (e : texpr) : texpr =
    { e = Meta (TypeAnnot, e); ty = e.ty }
  in

  (* Collect the type variables and the const generic variables which appear
     in a list of types *)
  let collect_vars (tys : ty list) : TypeVarId.Set.t * ConstGenericVarId.Set.t =
    let ty_vars = ref TypeVarId.Set.empty in
    let cg_vars = ref ConstGenericVarId.Set.empty in
    let visitor =
      object
        inherit [_] iter_ty

        method! visit_type_var_id _ id =
          ty_vars := TypeVarId.Set.add id !ty_vars

        method! visit_const_generic_var_id _ id =
          cg_vars := ConstGenericVarId.Set.add id !cg_vars
      end
    in
    List.iter (visitor#visit_ty ()) tys;
    (!ty_vars, !cg_vars)
  in
  let hole_id = TypeVarId.of_int (-1) in
  let is_known (ty : ty) : bool =
    not (TypeVarId.Set.mem hole_id (fst (collect_vars [ ty ])))
  in

  (* Pair the elements of two lists, stopping at the end of the shorter one
     (applications may be partial) *)
  let rec zip_prefix l0 l1 =
    match (l0, l1) with
    | x0 :: l0, x1 :: l1 -> (x0, x1) :: zip_prefix l0 l1
    | _ -> []
  in

  (* In Lean, the type parameters and the const generics of an ADT are
     implicit parameters of its constructors. Given the fields of a value of
     the ADT, as pairs of a field index and an expression, compute the
     parameters which Lean can't infer from those fields. A parameter can be
     inferred if it appears in the type of a field whose value has a type that
     Lean can infer by itself. *)
  let rec undetermined_params (adt_id : type_id)
      (variant_id : VariantId.id option) (generics : generic_args)
      (fields : (int * texpr) list) : adt_param list =
    (* Instantiate the fields with markers to find out which parameters they
       use *)
    let ty_marker i = TypeVarId.of_int (-2 - i) in
    let cg_marker i = ConstGenericVarId.of_int (-2 - i) in
    let markers =
      {
        generics with
        types =
          List.mapi (fun i _ -> TVar (T.Free (ty_marker i))) generics.types;
        const_generics =
          List.mapi
            (fun i _ -> CgVar (T.Free (cg_marker i)))
            generics.const_generics;
      }
    in
    let field_tys =
      PureTypeCheck.get_adt_field_types span type_decls adt_id variant_id
        markers
    in
    let ty_vars, cg_vars =
      collect_vars
        (List.filter_map
           (fun (i, field) ->
             if synthesizable field then List.nth_opt field_tys i else None)
           fields)
    in
    let indices l = List.init (List.length l) (fun i -> i) in
    List.filter_map
      (fun i ->
        if TypeVarId.Set.mem (ty_marker i) ty_vars then None
        else Some (TyParam i))
      (indices generics.types)
    @ List.filter_map
        (fun i ->
          if ConstGenericVarId.Set.mem (cg_marker i) cg_vars then None
          else Some (CgParam i))
        (indices generics.const_generics)
  (* The undetermined parameters of the application of a constructor, or
     [None] for the kinds of ADTs we don't handle *)
  and cons_undetermined_params (e : texpr) (adt_cons_id : adt_cons_id)
      (args : texpr list) : adt_param list option =
    match (adt_cons_id.adt_id, e.ty) with
    | TAdtId _, TAdt (adt_id, generics) when adt_id = adt_cons_id.adt_id ->
        Some
          (undetermined_params adt_id adt_cons_id.variant_id generics
             (List.mapi (fun i arg -> (i, arg)) args))
    | _ -> None
  (* The undetermined parameters of a structure built from its fields, or
     [None] for the kinds of ADTs we don't handle *)
  and struct_undetermined_params (e : texpr) (supd : struct_update) :
      adt_param list option =
    match (supd.init, e.ty) with
    | None, TAdt ((TAdtId _ as adt_id), generics) ->
        Some
          (undetermined_params adt_id None generics
             (List.map
                (fun (fid, field) -> (FieldId.to_int fid, field))
                supd.updates))
    | _ -> None
  (* Whether Lean can infer the type of an expression without any information
     from the context. This is an approximation: we only return [false] for
     the values of ADTs with parameters which are not determined by their
     fields (in particular the ones we annotate), and for the tuples which
     contain such values. *)
  and synthesizable (e : texpr) : bool =
    match e.e with
    | Meta (TypeAnnot, _) -> true
    | Meta (_, e') -> synthesizable e'
    | StructUpdate supd -> begin
        match struct_undetermined_params e supd with
        | None -> true
        | Some undetermined -> undetermined = []
      end
    | Qualif _ | App _ -> begin
        let f, args = destruct_apps e in
        match f.e with
        | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ } ->
            List.for_all synthesizable args
        | Qualif { id = AdtCons adt_cons_id; _ } -> begin
            match cons_undetermined_params e adt_cons_id args with
            | None -> true
            | Some undetermined -> undetermined = []
          end
        | _ -> true
      end
    | _ -> true
  in

  (* Lean needs a type annotation on a value of an ADT when one of the
     parameters of the ADT is neither determined by the fields nor known from
     the context. This happens for instance with [None], or with [Ok x] when
     the error type is unknown. *)
  let needs_annot (ty : ty) (adt_id : type_id)
      (undetermined : adt_param list option) : bool =
    Config.backend () = Lean
    &&
    match undetermined with
    | None -> false
    | Some undetermined ->
        let known_from_context (p : adt_param) : bool =
          match ty with
          | TAdt (adt_id', generics) when adt_id' = adt_id -> begin
              match p with
              | TyParam i -> is_known (List.nth generics.types i)
              | CgParam i -> List.nth generics.const_generics i <> cg_hole
            end
          | _ -> false
        in
        List.exists (fun p -> not (known_from_context p)) undetermined
  in

  let rec visit (ty : ty) (e : texpr) : texpr =
    [%ldebug "visit:\n- ty: " ^ ty_to_string ty ^ "\n- e: " ^ texpr_to_string e];
    match e.e with
    | Qualif { id = AdtCons _; _ } ->
        (* A constructor without arguments, like [None], may need a type
           annotation *)
        visit_App ty e
    | FVar _ | CVar _ | Const _ | EError _ | Qualif _ -> e
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
        (* The type of the bound expression is considered as unknown *)
        let bound = visit hole bound in
        let next = visit ty next in
        { e with e = Let (monadic, pat, bound, next) }
    | Switch (discr, body) ->
        (* We consider that the type of the discriminant is unknown *)
        let discr = visit hole discr in
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
              (* In Lean, if some parameters of a new structure are neither
                 determined by its fields nor known from the context, we add a
                 type annotation. Either way, the full type of the structure,
                 and thus the type of its fields, is then known. *)
              let undetermined = struct_undetermined_params e supd in
              let annot = needs_annot ty adt_id undetermined in
              let generics =
                match e.ty with
                | TAdt (_, generics')
                  when Config.backend () = Lean && Option.is_some undetermined
                  -> generics'
                | _ -> generics
              in
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
              let e = { e with e = StructUpdate { supd with updates } } in
              if annot then mk_type_annot e else e
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
          | IndexAtIndex kind | IndexMutAtIndex kind ->
              let collection_ty =
                let id, const_generics =
                  match kind with
                  | Array -> (TArray, [ cg_hole ])
                  | Slice -> (TSlice, [])
                in
                TAdt
                  ( TBuiltin id,
                    { types = [ hole ]; const_generics; trait_refs = [] } )
              in
              (known_f_ty, [ collection_ty; TLiteral (TUInt Usize) ], false)
          | ResultUnwrapMut -> (hole, mk_holes (), false)
          | GetTarget -> (f.ty, mk_known (), false)
          | TargetFeatureEnabled -> (f.ty, mk_known (), false)
        end
      | FromLlbc (fid, lp_id) -> begin
          (* Lookup the signature *)
          let sg =
            match fid with
            | FunId fid ->
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
            | TraitMethod (tref, method_id) ->
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
                SymbolicToPureTypes.translate_fun_sig trans_ctx fid method_sig
                  (List.map (fun _ -> None) method_sig.item_binder_value.inputs)
          in
          [%ldebug "signature: " ^ fun_sig_to_string sg];
          (* In case this is a trait method, we need to concatenate the generics
             args of the trait ref with the generics args of the method call itself *)
          let generics =
            match fid with
            | TraitMethod (trait_ref, _) ->
                append_generic_args trait_ref.trait_decl_ref.decl_generics
                  qualif.generics
            | _ -> qualif.generics
          in
          let tr_self =
            match fid with
            | TraitMethod (trait_ref, _) -> trait_ref.trait_id
            (* Dummy, won't be used since we're not substituting for a trait. *)
            | _ -> UnknownTrait "add_type_annotations_to_fun_decl"
          in
          (* Replace all the unknown implicit type variables with holes.
             Note that we assume that all the trait refs are there, meaning
             we can use them to infer some implicit variables.
             In Lean, an implicit type variable is also known if it appears
             in the type of an argument whose type Lean can infer by itself.
          *)
          let known = sg.known_from_trait_refs in
          let determined_tys, determined_cgs =
            if Config.backend () = Lean then
              collect_vars
                (List.filter_map
                   (fun (input_ty, arg) ->
                     if synthesizable arg then Some input_ty else None)
                   (zip_prefix sg.inputs args))
            else (TypeVarId.Set.empty, ConstGenericVarId.Set.empty)
          in
          let types =
            List.map
              (fun ((known, ty), (param : type_param)) ->
                match known with
                | Known -> ty
                | Unknown ->
                    if TypeVarId.Set.mem param.index determined_tys then ty
                    else hole)
              (List.combine
                 (List.combine known.known_types generics.types)
                 sg.generics.types)
          in
          let const_generics =
            List.map
              (fun ((known, cg), (param : const_generic_param)) ->
                match known with
                | Known -> cg
                | Unknown ->
                    if ConstGenericVarId.Set.mem param.index determined_cgs then
                      cg
                    else cg_hole)
              (List.combine
                 (List.combine known.known_const_generics
                    generics.const_generics)
                 sg.generics.const_generics)
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
          | AdtCons adt_cons_id -> begin
              (* In Lean, the full type of the constructor of a regular ADT
                 is known: its type parameters are known from the context or
                 determined by the arguments, otherwise we add a type
                 annotation. The types of the fields are thus known. *)
              let lean_field_tys =
                match (adt_cons_id.adt_id, e.ty) with
                | TAdtId _, TAdt (adt_id, generics)
                  when Config.backend () = Lean && adt_id = adt_cons_id.adt_id
                  ->
                    Some
                      (PureTypeCheck.get_adt_field_types span type_decls adt_id
                         adt_cons_id.variant_id generics)
                | _ -> None
              in
              (* We extract the type of the arguments from the known type *)
              match ty with
              | _ when Option.is_some lean_field_tys ->
                  ( hole,
                    Option.get lean_field_tys,
                    needs_annot ty adt_cons_id.adt_id
                      (cons_undetermined_params e adt_cons_id args) )
              | TAdt (TBuiltin (TArray | TSlice), _) ->
                  (hole, mk_holes (), false)
              | TAdt (adt_id, generics)
              (* TODO: there are type-checking errors that we need to take into account (otherwise
                 [get_adt_field_types] sometimes crashes) *)
                when adt_id = adt_cons_id.adt_id ->
                  (* The type is known: let's compute the type of the fields and recurse *)
                  let field_tys =
                    PureTypeCheck.get_adt_field_types span type_decls adt_id
                      adt_cons_id.variant_id generics
                  in
                  (* We shouldn't need to know the type of the constructor - just leaving
                     a hole for now *)
                  (hole, field_tys, false)
              | _ ->
                  (* The type is unknown, but if the constructor is an enumeration
                     constructor, we can retrieve information from it *)
                  if Option.is_some adt_cons_id.variant_id then
                    let args_tys =
                      match e.ty with
                      | TAdt (adt_id, generics) ->
                          (* Replace the generic arguments with holes *)
                          let generics =
                            {
                              generics with
                              types = List.map (fun _ -> hole) generics.types;
                              const_generics =
                                List.map
                                  (fun _ -> cg_hole)
                                  generics.const_generics;
                            }
                          in
                          PureTypeCheck.get_adt_field_types span type_decls
                            adt_id adt_cons_id.variant_id generics
                      | _ -> mk_holes ()
                    in
                    (hole, args_tys, false)
                  else (hole, mk_holes (), false)
            end
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
    let args =
      List.map (fun (ty, arg) -> visit ty arg) (List.combine args_tys args)
    in
    (* The function itself is left unchanged if it is a qualified identifier:
       this avoids looping on constructors, which [visit] sends back here *)
    let f =
      match f.e with
      | Qualif _ -> f
      | _ -> visit f_ty f
    in
    let e = [%add_loc] mk_apps span f args in
    if need_annot then mk_type_annot e else e
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
        add_type_annotations_to_fun_decl trans_ctx trans_funs_map type_decls
          decl
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
