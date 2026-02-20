open Pure
open PureUtils
open TranslateCore
open PureMicroPassesAnnots
open PureMicroPassesBase
open PureMicroPassesGeneral
open PureMicroPassesLoops
open PureMicroPassesPrettyNames

(* TODO: reorder the branches of the matches/switche
   TODO: we might want to leverage more the assignment meta-data, for
   aggregates for instance. *)
let passes :
    ((unit -> bool) option * string * (ctx -> fun_decl -> fun_decl)) list =
  [
    (* Find informative names for the unnamed variables *)
    (None, "compute_pretty_names", compute_pretty_names);
    (* Remove the meta-information (it's only useful to compute the pretty names).

       Remark: some passes below use the fact that we removed the meta-data
       (otherwise we would have to "unmeta" expressions before matching) *)
    (None, "remove_meta_def", remove_meta);
    (* Convert the unit variables to [()] if they are used as right-values or
     * [_] if they are used as left values. *)
    (None, "unit_vars_to_unit", unit_vars_to_unit);
    (* Introduce [massert] - we do this early because it makes the AST nicer to
       read by removing indentation. *)
    (Some (fun _ -> !Config.intro_massert), "intro_massert", intro_massert);
    (* Simplify the let-bindings which bind the fields of ADTs
       which only have one variant (i.e., enumerations with one variant
       and structures). *)
    (None, "simplify_decompose_struct", simplify_decompose_struct);
    (* Introduce the special structure create/update expressions *)
    (None, "intro_struct_updates", intro_struct_updates);
    (* Simplify the lambdas *)
    (None, "simplify_lambdas", simplify_lambdas);
    (* Simplify the let-bindings *)
    (None, "simplify_let_bindings", simplify_let_bindings);
    (* Inline the useless variable reassignments *)
    ( None,
      "inline_useless_var_assignments",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:false );
    (* Simplify the lambdas by applying beta-reduction *)
    (None, "apply_beta_reduction", apply_beta_reduction);
    (* Eliminate the box functions - note that the "box" types were eliminated
       during the symbolic to pure phase: see the comments for [eliminate_box_functions] *)
    (None, "eliminate_box_functions", eliminate_box_functions);
    (* Simplify some traits like [Clone::clone] for type [Box] *)
    (None, "simplify_trait_calls", simplify_trait_calls);
    (* Remove the duplicated function calls *)
    (None, "simplify_duplicate_calls", simplify_duplicate_calls);
    (* Merge let bindings which bind an expression then decompose a tuple *)
    ( Some (fun _ -> !Config.merge_let_app_decompose_tuple),
      "merge_let_app_then_decompose_tuple",
      merge_let_app_then_decompose_tuple );
    (* Filter the useless variables, assignments, function calls, etc. *)
    (None, "filter_useless", filter_useless);
    (* Do the following kind of transformations (note that such expressions
       are frequently introduced when joining the contexts after a branching
       expression):

       {[
         let (b', x) := if b then (true, 1) else (false, 0) in
         ...

           ~~>

         let x := if b then 1 else 0 in
         let b' := b in // inlined afterwards by [inline_useless_var_assignments]
         ...
       ]}
    *)
    (None, "simplify_let_branching", simplify_let_branching);
    (* Simplify the lets immediately followed by a return.

       Ex.:
       {[
         x <-- f y;
         Return x

           ~~>

         f y
       ]}
    *)
    (None, "simplify_let_then_ok", simplify_let_then_ok ~ignore_loops:true);
    (* Simplify the lambdas again: this simplification might have been unlocked
       by [simplify_let_then_ok], and is useful for [filter_loop_useless_inputs_outputs] *)
    (None, "simplify_lambdas (pass 2)", simplify_lambdas);
    (* Decompose the loop outputs if they have the type tuple.

       We do so to make it simpler to analyze the relationship between inputs
       and outputs and that we need to do in [simplify_loop_output_conts],
       [filter_loop_useless_inputs_outputs], etc. Importantly, the passes below
       will not be correct (they might crash) if we don't do this here first.
    *)
    (None, "decompose_loop_outputs", decompose_loop_outputs);
    (* Simplify and filter the loop outputs.

       Note that calling [simplify_loop_output_conts] *before*
       [filter_loop_useless_inputs_outputs] leads to better code. In particular,
       [simplify_loop_output_conts] inlines some values inside the loop, which
       thus become necessary inputs and do not get eliminated by [simplify_loop_output_conts]
       in case we extract the loops to recursive functions (or simply introduce auxiliary
       functions for the loops). If those inputs get eliminated, we introduce binders back
       when actually introducing the auxiliary loop functions, but then the order of the
       inputs is not preserved anymore.
    *)
    (None, "simplify_loop_output_conts", simplify_loop_output_conts);
    (* [simplify_loop_output_conts] also introduces simplification opportunities
       for those 2 passes.
       TODO: it would be good to do both at once. *)
    (None, "apply_beta_reduction (pass 3)", apply_beta_reduction);
    ( None,
      "inline_useless_var_assignments (pass 3)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:true );
    (* Filter the useless loop inputs and outputs.

       For now we do not filter the constant inputs: we will do this after
       (optionally) introducing auxiliary definitions for the loops: this allows
       us to make sure we preserve the order of the constant inputs. *)
    ( None,
      "filter_loop_useless_inputs_outputs",
      filter_loop_useless_inputs_outputs ~filter_constant_inputs:false );
    (* [filter_loop_useless_inputs_outputs] might have triggered simplification
       opportunities for [apply_beta_reduction] and [inline_useless_var_assignments].

       In particular, it often introduces expressions of the shape:
       {[
         let x = (fun y -> y) v in
         ...
       ]}
    *)
    (None, "apply_beta_reduction (pass 2)", apply_beta_reduction);
    ( None,
      "inline_useless_var_assignments (pass 2)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:true ~inline_identity:true ~inline_loop_back_calls:false );
    (* Reorder some of the loop outputs to permit [loops_to_recursive] to succeed *)
    (None, "reorder_loop_outputs", reorder_loop_outputs);
    (* Change the structure of the loops if we can simplify their backward
       functions. This is in preparation of [decompose_loops], which introduces
       auxiliary (and potentially recursive) functions. *)
    (None, "loops_to_recursive", loops_to_recursive);
    (* Introduce match expressions where let-bindings need to open enumerations *)
    (None, "let_to_match", let_to_match);
    (None, "flatten_struct_updates", flatten_struct_updates);
    (* Simplify the aggregated ADTs.

       Ex.:
       {[
         (* type struct = { f0 : nat; f1 : nat; f2 : nat } *)

         Mkstruct x.f0 x.f1 x.f2                 ~~> x
         { f0 := x.f0; f1 := x.f1; f2 := x.f2 }  ~~> x
         { f0 := x.f0; f1 := x.f1; f2 := v }     ~~> { x with f2 = v }
       ]}
    *)
    (None, "simplify_aggregates", simplify_aggregates);
    (* Simplify the aggregated ADTs further. *)
    ( None,
      "simplify_aggregates_unchanged_fields",
      simplify_aggregates_unchanged_fields );
    (* Simplify the lambdas again *)
    (None, "simplify_lambdas (pass 2)", simplify_lambdas);
    (* Simplify the let-bindings - some simplifications may have been unlocked by
       the pass above (for instance, the lambda simplification) *)
    (None, "simplify_let_bindings (pass 2)", simplify_let_bindings);
    (* Inline the useless vars again *)
    ( None,
      "inline_useless_var_assignments (pass 4)",
      inline_useless_var_assignments ~inline_named:true ~inline_const:true
        ~inline_pure:false ~inline_identity:true ~inline_loop_back_calls:false
    );
    (* Filter the useless variables again *)
    (None, "filter_useless (pass 2)", filter_useless);
    (* Simplify the let-then return again (the lambda simplification may have
       unlocked more simplifications here) *)
    ( None,
      "simplify_let_then_ok (pass 2)",
      simplify_let_then_ok ~ignore_loops:false );
    (* Simplify the array/slice manipulations by introducing calls to [array_update]
       [slice_update] *)
    (None, "simplify_array_slice_update", simplify_array_slice_update);
    (* Simplify the let-then return again (the array simplification may have
       unlocked more simplifications here) *)
    ( None,
      "simplify_let_then_ok (pass 3)",
      simplify_let_then_ok ~ignore_loops:false );
    (* Decompose the monadic let-bindings - used by Coq *)
    ( Some (fun _ -> !Config.decompose_monadic_let_bindings),
      "decompose_monadic_let_bindings",
      decompose_monadic_let_bindings );
    (* Decompose nested let-patterns *)
    ( Some (fun _ -> !Config.decompose_nested_let_patterns),
      "decompose_nested_let_patterns",
      decompose_nested_let_patterns );
    (* Unfold the monadic let-bindings *)
    ( Some (fun _ -> !Config.unfold_monadic_let_bindings),
      "unfold_monadic_let_bindings",
      unfold_monadic_let_bindings );
    (* Introduce calls to [toResult] to lift pure function calls to monadic
       function calls *)
    ( Some (fun _ -> !Config.lift_pure_function_calls),
      "lift_pure_function_calls",
      lift_pure_function_calls );
    (* Update the matches over [isize] and [usize] *)
    (None, "update_match_over_isize_usize", update_match_over_isize_usize);
  ]

(** Apply all the micro-passes to a function. *)
let apply_passes_to_def (ctx : ctx) (def : fun_decl) : fun_decl =
  List.fold_left
    (fun def (option, pass_name, pass) ->
      let apply =
        match option with
        | None -> true
        | Some option -> option ()
      in

      if apply then (
        [%ltrace "About to apply: '" ^ pass_name ^ "'"];
        let def' = pass ctx def in
        let updated = string_of_bool (def' <> def) in
        [%ltrace
          "After applying '" ^ pass_name ^ "'" ^ "(updated:" ^ updated
          ^ "):\n\n"
          ^ fun_decl_to_string ctx def'];
        def')
      else (
        [%ltrace "Ignoring " ^ pass_name ^ " due to the configuration\n"];
        def))
    def passes

(** Update the [reducible] attribute.

    For now we mark a function as reducible when its body is only a call to a
    loop function. This situation often happens for simple functions whose body
    contains a loop: we introduce an intermediate function for the loop body,
    and the translation of the function itself simply calls the loop body. By
    marking the function as reducible, we allow tactics like [simp] or
    [progress] to see through the definition. *)
let compute_reducible (_ctx : ctx) (transl : pure_fun_translation list) :
    pure_fun_translation list =
  let update_one (trans : pure_fun_translation) : pure_fun_translation =
    match trans.f.body with
    | None -> trans
    | Some body -> (
        let app, _ = destruct_apps body.body in
        match app.e with
        | Qualif
            {
              id = FunOrOp (Fun (FromLlbc (FunId fid, Some _lp_id)));
              generics = _;
            }
          when fid = FRegular trans.f.def_id ->
            let f =
              { trans.f with backend_attributes = { reducible = true } }
            in
            { trans with f }
        | _ -> trans)
  in
  List.map update_one transl

(** Apply the micro-passes to a list of forward/backward translations.

    This function also extracts the loop definitions from the function body (see
    {!decompose_loops}).

    It also returns a boolean indicating whether the forward function should be
    kept or not at extraction time ([true] means we need to keep the forward
    function).

    Note that we don't "filter" the forward function and return a boolean
    instead, because this function contains useful information to extract the
    backward functions. Note that here, keeping the forward function it is not
    *necessary* but convenient. *)
let apply_passes_to_pure_fun_translations (crate : LlbcAst.crate)
    (trans_ctx : trans_ctx) (builtin_sigs : fun_sig Builtin.BuiltinFunIdMap.t)
    (type_decls : type_decl list) (trait_impls : trait_impl list)
    (transl : fun_decl list) : pure_fun_translation list =
  let fun_decls =
    FunDeclId.Map.of_list
      (List.map (fun (f : fun_decl) -> (f.def_id, f)) transl)
  in
  let type_decls =
    TypeDeclId.Map.of_list
      (List.map (fun (d : type_decl) -> (d.def_id, d)) type_decls)
  in
  let trait_impls =
    TraitImplId.Map.of_list
      (List.map (fun (d : trait_impl) -> (d.def_id, d)) trait_impls)
  in

  let fvar_id_generator, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let refresh_fvar_id_generator () =
    fvar_id_generator := FVarId.generator_zero
  in
  let ctx =
    { crate; trans_ctx; type_decls; trait_impls; fun_decls; fresh_fvar_id }
  in

  (* Apply the micro-passes *)
  let apply (f : fun_decl) : pure_fun_translation =
    (* Apply the micro-passes *)
    let f = apply_passes_to_def ctx f in

    (* Decompose the loops *)
    [%ltrace "About to apply: 'decompose_loops':\n" ^ fun_decl_to_string ctx f];
    refresh_fvar_id_generator ();
    let f, loops = decompose_loops ctx f in
    [%ltrace
      "After applying: 'decompose_loops':\n"
      ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) (f :: loops))];

    (* Filter the constant *inputs¨ in the loops to simplify the calls to the loop
       fixed-point operators *)
    let simplify f =
      [%ltrace
        "About to apply: 'filter_loop_useless_inputs':\n"
        ^ fun_decl_to_string ctx f];
      refresh_fvar_id_generator ();
      let f = filter_loop_useless_inputs ctx f in
      [%ltrace
        "After applying 'filter_loop_useless_inputs':\n"
        ^ fun_decl_to_string ctx f];
      f
    in
    let f = simplify f in
    let loops = List.map simplify loops in

    (* Convert the loop nodes to calls to the loop fixed-point operator *)
    let update f =
      [%ltrace "About to apply: 'loops_to_fixed_points'"];
      refresh_fvar_id_generator ();
      let f = loops_to_fixed_points ctx f in
      [%ltrace
        "After applying 'loops_to_fixed_points':\n" ^ fun_decl_to_string ctx f];
      f
    in
    let f = update f in
    let loops = List.map update loops in

    (* Decomposing the loops and filtering the inputs might have introduced
       expressions of the shape:
       [let (x, y) = e in ok (x, y)]
       We need to resimplify those. *)
    let simplify f =
      [%ltrace "About to apply: 'simplify_let_then_ok (final pass)'"];
      refresh_fvar_id_generator ();
      let f = simplify_let_then_ok ~ignore_loops:false ctx f in
      [%ltrace
        "After applying 'simplify_let_then_ok (final pass)':\n"
        ^ fun_decl_to_string ctx f];
      f
    in
    let f = simplify f in
    let loops = List.map simplify loops in

    [%ltrace
      let funs = f :: loops in
      "After decomposing loops:\n\n"
      ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) funs)];

    let trans : pure_fun_translation = { f; loops } in

    (* Introduce the fuel and the state, if necessary.

       We do this last, because some other passes need to manipulate the
       functions *wihout* fuel and state (otherwise it messes up the
       parameter manipulations). *)
    refresh_fvar_id_generator ();
    let trans = if !Config.use_fuel then add_fuel ctx trans else trans in

    trans
  in
  let transl =
    (* Partition the opaque and transparent functions *)
    let opaque, transparent =
      List.partition
        (fun (f : pure_fun_translation_no_loops) -> Option.is_none f.body)
        transl
    in

    let process (kind : string) (transl : pure_fun_translation_no_loops list) =
      let num_decls = List.length transl in
      ProgressBar.with_parallel_reporter num_decls
        ("Post-processed translated " ^ kind ^ " functions: ")
        (fun report ->
          Parallel.parallel_map
            (fun x ->
              let x = apply x in
              report 1;
              x)
            transl)
    in

    let opaque = process "opaque" opaque in
    let transparent = process "transparent" transparent in
    opaque @ transparent
  in

  (* Add the type annotations - we add those only now because we need
     to use the final types of the functions (in particular, we introduce
     loop functions and modify their types above).

     TODO: move
  *)
  let transl = add_type_annotations trans_ctx transl builtin_sigs type_decls in

  (* Update the "reducible" attribute *)
  refresh_fvar_id_generator ();
  compute_reducible ctx transl
