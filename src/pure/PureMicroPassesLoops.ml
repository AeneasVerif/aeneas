open Pure
open PureUtils
open PureMicroPassesBase

(** Helper for [decompose_loops]: for the case when we convert a loop to a
    recursive function, update the occurrences of continue and break. *)
let update_rec_continue_breaks (ctx : ctx) (def : fun_decl) (loop_func : texpr)
    (constant_inputs : texpr list) (e : texpr) : texpr =
  let span = def.item_meta.span in

  let rec update (e : texpr) : texpr =
    [%ldebug "e:\n" ^ texpr_to_string ctx e];
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ -> e
    | App _ | Qualif _ -> (
        (* Check if this is a continue, break, or a recLoopCall *)
        match
          opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:true
            ~opened_vars:false e
        with
        | Some ({ variant_id; args; break_ty; _ }, rebind) ->
            if variant_id = loop_result_continue_id then (
              [%ldebug "continue expression: introducing a recursive call"];
              [%ldebug
                "- loop_func: "
                ^ texpr_to_string ctx loop_func
                ^ "\n- loop_func.ty: "
                ^ ty_to_string ctx loop_func.ty
                ^ "\n- num args: "
                ^ string_of_int (List.length args)
                ^ "\n- args:\n"
                ^ String.concat "\n\n" (List.map (texpr_to_string ctx) args)];
              let args = constant_inputs @ args in
              rebind ([%add_loc] mk_apps span loop_func args))
            else if variant_id = loop_result_break_id then (
              [%ldebug "break expression: introducing an ok expression"];
              let arg = mk_simpl_tuple_texpr span args in
              rebind (mk_result_ok_texpr span arg))
            else if variant_id = loop_result_fail_id then
              let arg = mk_simpl_tuple_texpr span args in
              rebind (mk_result_fail_texpr span arg break_ty)
            else [%internal_error] span
        | _ -> (
            (* Not a continue or a break: might be a recLoopCall *)
            match opt_destruct_rec_loop_call span e with
            | Some { args; _ } ->
                let args = constant_inputs @ args in
                [%add_loc] mk_apps span loop_func args
            | None -> e))
    | Lambda (pat, body) ->
        let body = update body in
        mk_opened_lambda span pat body
    | Let (monadic, pat, bound, next) ->
        let bound = update bound in
        let next = update next in
        mk_opened_let monadic pat bound next
    | Switch (scrut, body) ->
        let scrut = update scrut in
        let body, ty =
          match body with
          | If (e0, e1) ->
              let e0 = update e0 in
              let e1 = update e1 in
              (If (e0, e1), e0.ty)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    { pat; branch = update branch })
                  branches
              in
              let ty =
                match branches with
                | [] -> [%internal_error] span
                | { branch = b; _ } :: _ -> b.ty
              in
              (Match branches, ty)
        in
        { e = Switch (scrut, body); ty }
    | Loop _ -> [%internal_error] span
    | StructUpdate { struct_id; init; updates } ->
        let init = Option.map update init in
        let updates = List.map (fun (fid, e) -> (fid, update e)) updates in
        { e with e = StructUpdate { struct_id; init; updates } }
    | Meta (m, e) -> mk_emeta m (update e)
    | EError _ ->
        let ty =
          match try_unwrap_loop_result e.ty with
          | None -> e.ty
          | Some (_, break) -> mk_result_ty break
        in
        { e with ty }
  in
  update e

(** Helper for [decompose_loops]: for the case when we convert a loop to a call
    to a fixed point operator, update the occurrences of continue and break, in
    particular to wrap them into [Result]. *)
let update_non_rec_continue_breaks (ctx : ctx) (def : fun_decl) (input_ty : ty)
    (output_ty : ty) (e : texpr) : texpr =
  let span = def.item_meta.span in

  let rec update (e : texpr) : texpr =
    [%ldebug "e:\n" ^ texpr_to_string ctx e];
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ -> e
    | App _ | Qualif _ -> (
        (* Check if this is a continue, break, or a recLoopCall *)
        match
          opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:true
            ~opened_vars:true e
        with
        | Some ({ variant_id; args; break_ty; _ }, rebind) ->
            if variant_id = loop_result_continue_id then (
              [%ldebug "continue expression: introducing an ok expression"];
              let arg = mk_simpl_tuple_texpr span args in
              rebind
                (mk_result_ok_texpr span (mk_continue_texpr span arg output_ty)))
            else if variant_id = loop_result_break_id then (
              [%ldebug "break expression: introducing an ok expression"];
              let arg = mk_simpl_tuple_texpr span args in
              rebind
                (mk_result_ok_texpr span (mk_break_texpr span input_ty arg)))
            else if variant_id = loop_result_fail_id then
              let arg = mk_simpl_tuple_texpr span args in
              rebind (mk_result_fail_texpr span arg break_ty)
            else [%internal_error] span
        | _ -> e)
    | Lambda (pat, body) ->
        let body = update body in
        mk_opened_lambda span pat body
    | Let (monadic, pat, bound, next) ->
        let bound = update bound in
        let next = update next in
        mk_opened_let monadic pat bound next
    | Switch (scrut, body) ->
        let scrut = update scrut in
        let body, ty =
          match body with
          | If (e0, e1) ->
              let e0 = update e0 in
              let e1 = update e1 in
              (If (e0, e1), e0.ty)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    { pat; branch = update branch })
                  branches
              in
              let ty =
                match branches with
                | [] -> [%internal_error] span
                | { branch = b; _ } :: _ -> b.ty
              in
              (Match branches, ty)
        in
        { e = Switch (scrut, body); ty }
    | Loop _ -> [%internal_error] span
    | StructUpdate { struct_id; init; updates } ->
        let init = Option.map update init in
        let updates = List.map (fun (fid, e) -> (fid, update e)) updates in
        { e with e = StructUpdate { struct_id; init; updates } }
    | Meta (m, e) -> mk_emeta m (update e)
    | EError _ ->
        let ty =
          match try_unwrap_loop_result e.ty with
          | None -> e.ty
          | Some (_, break) -> mk_result_ty break
        in
        { e with ty }
  in
  update e

(** Returns true if the continuations listed in [loop_conts] are used in a
    chained manner.

    For instance, given [loop_conts = {f0, f1}], they are in:
    {[
      let x1 = f0 x0 in
      f1 x1
    ]}
    but not in:
    {[
      f0 x0, f1 x1
    ]}

    We do this by doing a (slightly imprecise) control-flow analysis. *)
let expr_chains_loop_conts span (ctx : ctx) (loop_vars : FVarId.Set.t)
    (e : texpr) : bool =
  let flatten_set_list (s : FVarId.Set.t list) : FVarId.Set.t =
    List.fold_left (fun s0 s1 -> FVarId.Set.union s0 s1) FVarId.Set.empty s
  in
  let flatten_set_list_opt (sl : FVarId.Set.t list option) : FVarId.Set.t =
    match sl with
    | None -> FVarId.Set.empty
    | Some sl -> flatten_set_list sl
  in
  let flatten_set_list_opt_list (sl : FVarId.Set.t list option list) :
      FVarId.Set.t =
    let sl = List.flatten (List.filter_map (fun x -> x) sl) in
    flatten_set_list sl
  in
  let merge_sets_lists (sl : FVarId.Set.t list list) : FVarId.Set.t list =
    (* Attempt to combine the sets if the lists all have the same length,
       otherwise group everything in a single set *)
    match sl with
    | [] -> [ FVarId.Set.empty ]
    | s :: sl ->
        let n = List.length s in
        if List.for_all (fun s -> List.length s = n) sl then
          let rec merge sl =
            match sl with
            | [] -> s
            | s :: sl ->
                let s' = merge sl in
                List.map
                  (fun (s, s') -> FVarId.Set.union s s')
                  (List.combine s s')
          in
          merge sl
        else [ flatten_set_list (List.flatten (s :: sl)) ]
  in
  let merge_sets_opt_lists (sl : FVarId.Set.t list option list) :
      FVarId.Set.t list option =
    let sl = List.filter_map (fun x -> x) sl in
    if sl = [] then None else Some (merge_sets_lists sl)
  in
  let extend_env (env : FVarId.Set.t FVarId.Map.t) (pat : tpat)
      (deps : FVarId.Set.t) : FVarId.Set.t FVarId.Map.t =
    let fvars = tpat_get_fvars pat in
    FVarId.Map.add_list
      (List.map (fun fid -> (fid, deps)) (FVarId.Set.elements fvars))
      env
  in
  let rec check (env : FVarId.Set.t FVarId.Map.t) (e : texpr) :
      FVarId.Set.t list option =
    match e.e with
    | FVar fid -> (
        if FVarId.Set.mem fid loop_vars then Some [ FVarId.Set.singleton fid ]
        else
          match FVarId.Map.find_opt fid env with
          | None -> Some [ FVarId.Set.empty ]
          | Some deps -> Some [ deps ])
    | BVar _ -> [%internal_error] span
    | CVar _ | Const _ | Qualif _ | EError _ -> Some [ FVarId.Set.empty ]
    | App _ -> (
        (* Ignore the continues, pay attention to structures *)
        let f, args = destruct_apps e in
        match f.e with
        | Qualif
            {
              id =
                AdtCons { adt_id = TBuiltin TLoopResult; variant_id = Some id };
              _;
            }
          when id = loop_result_continue_id -> None
        | Qualif { id = AdtCons { adt_id = _; variant_id = None }; _ } ->
            let args = List.map (check env) args in
            if List.for_all Option.is_some args then
              Some (List.map (fun x -> flatten_set_list (Option.get x)) args)
            else Some [ flatten_set_list_opt_list args ]
        | _ ->
            let f = check env f in
            let args = List.map (check env) args in
            Some [ flatten_set_list_opt_list (f :: args) ])
    | Lambda _ ->
        let _, _, body = open_lambdas ctx span e in
        check env body
    | Let (_, pat, bound, next) ->
        let bound = flatten_set_list_opt (check env bound) in
        let _, pat, next = open_binder ctx span pat next in
        (* Update the environment - this is not very precise *)
        let env = extend_env env pat bound in
        check env next
    | Switch (scrut, switch) -> (
        let scrut = flatten_set_list_opt (check env scrut) in
        match switch with
        | If (e0, e1) ->
            let e0 = check env e0 in
            let e1 = check env e1 in
            merge_sets_opt_lists [ e0; e1 ]
        | Match branches ->
            let branches =
              List.map
                (fun ({ pat; branch } : match_branch) ->
                  let _, pat, branch = open_binder ctx span pat branch in
                  let env = extend_env env pat scrut in
                  check env branch)
                branches
            in
            merge_sets_opt_lists branches)
    | Loop { inputs; loop_body = { inputs = input_pats; loop_body }; _ } ->
        let inputs = List.map (check env) inputs in
        let _, input_pats, loop_body =
          open_binders ctx span input_pats loop_body
        in
        let env =
          List.fold_left2
            (fun env pat bound ->
              match bound with
              | None -> env
              | Some bound -> extend_env env pat (flatten_set_list bound))
            env input_pats inputs
        in
        check env loop_body
    | StructUpdate { struct_id = _; init; updates } ->
        let init =
          match init with
          | None -> None
          | Some init -> check env init
        in
        let updates = List.map (fun (_, x) -> check env x) updates in
        Some [ flatten_set_list_opt_list (init :: updates) ]
    | Meta (_, e) -> check env e
  in
  let outputs = check FVarId.Map.empty e in
  match outputs with
  | None -> false
  | Some outputs -> List.for_all (fun s -> FVarId.Set.cardinal s > 1) outputs

(** Simplify the outputs of a loop. *)
let simplify_loop_output_conts (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Small helper to update the expression *after* the loop while detecting
     which simplifications should be done on the outputs.

     Returns the updated expression and a map from the freshly introduced
     fvar ids to their expressions. Those fresh fvars are continuations that
     should be added to the loop output.

     For now we do something simple and we don't check whether we're introducing
     continuations which collide each other: this is sound, but doesn't lead to
     the best output in the presence of branching after the loop.
  *)
  let simplify_in (before_loop_vars : FVarId.Set.t) (loop_vars : FVarId.Set.t)
      (loop_conts : FVarId.Set.t) (e : texpr) :
      (FVarId.id * texpr) list * (FVarId.id * texpr) list * texpr =
    let all_loop_outputs = FVarId.Set.union loop_vars loop_conts in
    let all_vars = FVarId.Set.union before_loop_vars all_loop_outputs in
    let fresh_values = ref [] in
    let fresh_conts = ref [] in
    let fresh_output_var ~(is_value : bool) (e : texpr) : texpr =
      let fid = ctx.fresh_fvar_id () in
      let fv : texpr = { e = FVar fid; ty = e.ty } in
      let fresh = if is_value then fresh_values else fresh_conts in
      fresh := (fid, e) :: !fresh;
      fv
    in
    let rec simplify (e : texpr) : texpr =
      match e.e with
      | FVar _
      | BVar _
      | CVar _
      | Const _
      | EError _
      | StructUpdate _
      | Qualif _
      | Switch _ (* let's ignore those for now *)
      | Loop _ -> e
      | Let (monadic, pat, bound, next) ->
          let bound = simplify bound in
          let _, pat, next = open_binder ctx span pat next in
          let next = simplify next in
          mk_closed_let span monadic pat bound next
      | Meta (m, e) -> mk_emeta m (simplify e)
      | Lambda _ ->
          (* One of the important cases: this might be the composition of a
             backward function. We check if all the free variables appearing
             in its body are loop outputs: if yes, it is likely a backward
             function which composes loop outputs

             We also check whether it's worth merging the outputs.
             For instance, if we have something like this:
             {[
               let (..., y, back0, back1) <- loop ...
               let back := fun x ->
                 back1 (Cons (y, back0 x))
               ...
             ]}
             then we introduce an output for [back] because it allows merging
             [back0], [back1] and [y] in a single output.

             However, if we have something like this:
             {[
               let (..., back0, back1) <- loop ...
               let back := fun (x, y) ->
                 (back0 x, back1 y)
               ...
             ]}
             then we don't merge anything, because it would only group
             several backward functions into a single backward functions,
             potentially limiting further optimizations like in
             [loop_to_recursive].

             We detect this by doing a flow analysis.
          *)
          if expr_chains_loop_conts span ctx all_loop_outputs e then (
            (* It is a subset: introduce a fresh output var *)
            [%ldebug
              "Simplifying output:\n" ^ texpr_to_string ctx e ^ "\n- ty: "
              ^ ty_to_string ctx e.ty];
            fresh_output_var ~is_value:false e)
          else
            (* No: dive into the lambda as there might be sub-expressions we can isolate *)
            let _, patl, body = open_lambdas ctx span e in
            let body = simplify body in
            close_lambdas span patl body
      | App _ -> (
          (* Other important case: try to simplify calls to backward functions *)
          let f, args = destruct_apps e in
          (* Is it a call to a backward function? *)
          match f.e with
          | FVar fid when FVarId.Set.mem fid loop_conts ->
              (* Check if all the free variables which appear in the call
                 are loop outputs or were introduced before the loop: if yes,
                 simplify. *)
              let fvars = texpr_get_fvars e in
              if FVarId.Set.subset fvars all_vars then (
                (* Simplify: introduce a fresh output var *)
                [%ldebug
                  "Simplifying call to backward function:\n"
                  ^ texpr_to_string ctx e ^ "\n- ty: " ^ ty_to_string ctx e.ty];
                fresh_output_var ~is_value:true e)
              else [%add_loc] mk_apps span (simplify f) (List.map simplify args)
          | _ -> [%add_loc] mk_apps span (simplify f) (List.map simplify args))
    in
    let e = simplify e in
    (List.rev !fresh_values, List.rev !fresh_conts, e)
  in

  let update_loop_body (num_filtered_outputs : int)
      (keep_outputs : (bool * FVarId.id option) list)
      (fresh_output_values : texpr list) (fresh_output_conts : texpr list)
      (continue_ty : ty) (break_ty : ty) (body : loop_body) : loop_body =
    let _, body = open_loop_body ctx span body in

    (* Introduce an intermediate let-binding for a loop.

       TODO: is this really useful? Can it happen that we find an loop
       which is not bound by a let-binding? If useful, we should also use
       it elsewhere.
    *)
    let rebind_loop (loop : loop) : texpr =
      let fvars = List.map (mk_fresh_fvar ctx) loop.output_tys in
      let pats = List.map (mk_tpat_from_fvar None) fvars in
      let pat = mk_simpl_tuple_pat pats in
      let outputs = List.map mk_texpr_from_fvar fvars in
      let output = mk_simpl_tuple_texpr span outputs in
      let bound : texpr = { e = Loop loop; ty = mk_result_ty output.ty } in
      mk_closed_let span true pat bound (mk_break_texpr span continue_ty output)
    in

    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ ->
          (* Shouldn't happen *)
          [%internal_error] span
      | Loop loop ->
          (* Introduce a let-binding and simplify (the simplification is implemented
             for the App case, below). *)
          update (rebind_loop loop)
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true ~opened_vars:false e
            with
            | None -> e
            | Some ({ variant_id; args = outputs; _ }, rebind) ->
                if variant_id = loop_result_break_id then
                  (* Filter while computing the map from output var index to output expression *)
                  let outputs, map =
                    List.split
                      (List.map
                         (fun (o, (keep, fid)) ->
                           let b =
                             match fid with
                             | Some fid -> Some (fid, o)
                             | None -> None
                           in
                           let o = if keep then Some o else None in
                           (o, b))
                         (List.combine outputs keep_outputs))
                  in
                  let outputs = List.filter_map (fun x -> x) outputs in
                  let output_values, output_conts =
                    Collections.List.split_at outputs num_filtered_outputs
                  in

                  (* Compute the additional outputs: we need to update the free variables which
                     appear in the continuation (and are output by the loop) with their actual
                     expression. *)
                  let map =
                    FVarId.Map.of_list (List.filter_map (fun x -> x) map)
                  in
                  let visitor =
                    object
                      inherit [_] map_expr

                      method! visit_FVar _ fid =
                        match FVarId.Map.find_opt fid map with
                        | None -> FVar fid
                        | Some e -> e.e
                    end
                  in
                  let fresh_output_values =
                    List.map (visitor#visit_texpr ()) fresh_output_values
                  in
                  let fresh_output_conts =
                    List.map (visitor#visit_texpr ()) fresh_output_conts
                  in

                  let outputs =
                    mk_simpl_tuple_texpr span
                      (output_values @ fresh_output_values @ output_conts
                     @ fresh_output_conts)
                  in
                  rebind (mk_break_texpr span continue_ty outputs)
                else if variant_id = loop_result_continue_id then
                  (* We leave the expression unchanged but have to modify its type *)
                  rebind
                    (mk_continue_texpr span
                       (mk_simpl_tuple_texpr span outputs)
                       break_ty)
                else (
                  [%sanity_check] span (variant_id = loop_result_fail_id);
                  let arg = mk_simpl_tuple_texpr span outputs in
                  rebind
                    (mk_loop_result_fail_texpr span continue_ty break_ty arg))
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let body = { body with loop_body = update body.loop_body } in
    close_loop_body span body
  in

  let fvarset_union (vars : FVarId.Set.t) (vars' : fvar FVarId.Map.t) :
      FVarId.Set.t =
    FVarId.Set.union vars (FVarId.Set.of_list (FVarId.Map.keys vars'))
  in

  let rec update (vars : FVarId.Set.t) (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Lambda _ ->
        let vars', pats, body = open_lambdas ctx span e in
        let vars = fvarset_union vars vars' in
        let body = update vars body in
        mk_closed_lambdas span pats body
    | Meta (meta, inner) -> mk_emeta meta (update vars inner)
    | Switch (scrut, switch) ->
        let scrut = update vars scrut in
        let switch, ty =
          match switch with
          | If (e0, e1) ->
              let e0 = update vars e0 in
              let e1 = update vars e1 in
              (If (e0, e1), e0.ty)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    let vars', pat, branch = open_binder ctx span pat branch in
                    let vars = fvarset_union vars vars' in
                    let branch = update vars branch in
                    let pat, branch = close_binder span pat branch in
                    { pat; branch })
                  branches
              in
              let ty = (List.hd branches).branch.ty in
              (Match branches, ty)
        in
        { e = Switch (scrut, switch); ty }
    | Let (monadic, pat, bound, next) -> (
        [%ldebug "About to simplify the outputs of:\n" ^ texpr_to_string ctx e];
        let vars', pat, next = open_binder ctx span pat next in
        let vars = fvarset_union vars vars' in
        [%ldebug
          "After opening the binders in the let:\n"
          ^ texpr_to_string ctx { e with e = Let (monadic, pat, bound, next) }];
        (* Check if we are binding a loop *)
        match bound.e with
        | Loop loop ->
            (* The output should be a tuple containing first the output values,
               then the output continuations *)
            let pats = try_destruct_tuple_tpat span pat in
            let as_pat_open_or_ignored (pat : tpat) : fvar option =
              match pat.pat with
              | POpen (fv, _) -> Some fv
              | PIgnored -> None
              | _ -> [%internal_error] span
            in
            let pvars = List.map as_pat_open_or_ignored pats in
            let to_set pvars =
              FVarId.Set.of_list
                (List.filter_map (Option.map (fun (v : fvar) -> v.id)) pvars)
            in
            let loop_varset = to_set pvars in
            [%ldebug
              "\n- loop.num_output_values: "
              ^ string_of_int loop.num_output_values
              ^ "- pats: "
              ^ Print.list_to_string (tpat_to_string ctx) pats];
            [%sanity_check] span (loop.num_output_values <= List.length pvars);
            let loop_conts =
              to_set (Collections.List.drop loop.num_output_values pvars)
            in

            (* Analyze the next expression to detect potential simplifications *)
            let fresh_output_values, fresh_output_conts, next =
              simplify_in vars loop_varset loop_conts next
            in
            let fresh_outputs = fresh_output_values @ fresh_output_conts in
            [%ldebug
              "After calling simplify_in:" ^ "\n- fresh_output_values:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                  (List.map snd fresh_output_values)
              ^ "\n- fresh_output_conts:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                  (List.map snd fresh_output_conts)];

            (* Filter the output variables which are now useless *)
            let used_vars = texpr_get_fvars next in
            let keep_varsl =
              List.map
                (fun (v : fvar option) ->
                  match v with
                  | None -> (false, None)
                  | Some v ->
                      let keep = FVarId.Set.mem v.id used_vars in
                      (keep, Some v.id))
                pvars
            in

            (* Update the loop body *)
            let continue_ty =
              mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) loop.inputs)
            in
            let filter outputs =
              List.filter_map
                (fun (keep, ty) -> if keep then Some ty else None)
                outputs
            in
            let output_value_tys, output_conts_tys =
              Collections.List.split_at
                (List.combine (List.map fst keep_varsl) loop.output_tys)
                loop.num_output_values
            in
            let filt_output_value_tys = filter output_value_tys in
            let output_tys =
              let tys =
                filt_output_value_tys
                @ List.map
                    (fun ((_, e) : _ * texpr) -> e.ty)
                    fresh_output_values
                @ filter output_conts_tys
                @ List.map (fun ((_, e) : _ * texpr) -> e.ty) fresh_output_conts
              in
              (* There may be only one remaining output, which has type tuple:
                 if it is the case we need to simplify it *)
              match tys with
              | [ ty ] -> try_destruct_tuple span ty
              | _ -> tys
            in

            let break_ty = mk_simpl_tuple_ty output_tys in
            let loop_body =
              let num_filtered_outputs = List.length filt_output_value_tys in
              let fresh_output_values = List.map snd fresh_output_values in
              let fresh_output_conts = List.map snd fresh_output_conts in
              [%ldebug
                "About to update the loop body:" ^ "\n- keep_varsl: "
                ^ Print.list_to_string
                    (Print.pair_to_string Print.bool_to_string
                       (Print.option_to_string FVarId.to_string))
                    keep_varsl
                ^ "\n- fresh_output_values:\n"
                ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                    fresh_output_values
                ^ "\n- fresh_output_conts:\n"
                ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx)
                    fresh_output_conts];
              update_loop_body num_filtered_outputs keep_varsl
                fresh_output_values fresh_output_conts continue_ty break_ty
                loop.loop_body
            in

            (* Update the signature *)
            let num_output_values =
              List.length
                (List.filter fst
                   (Collections.List.prefix loop.num_output_values keep_varsl))
            in
            let loop = { loop with num_output_values; output_tys; loop_body } in
            let loop : texpr =
              { e = Loop loop; ty = mk_loop_result_ty continue_ty break_ty }
            in

            (* Reconstruct the let-binding *)
            let filtered_pats =
              List.filter_map
                (fun ((keep, _), pat) -> if keep then Some pat else None)
                (List.combine keep_varsl pats)
            in
            let new_pats =
              List.map
                (fun ((id, e) : _ * texpr) ->
                  ({ id; basename = Some "back"; ty = e.ty } : fvar))
                fresh_outputs
            in
            let new_pats = List.map (mk_tpat_from_fvar None) new_pats in
            let pats = filtered_pats @ new_pats in
            let pat = mk_simpl_tuple_pat pats in
            mk_closed_let span monadic pat loop next
        | _ ->
            (* No need to update the bound expression *)
            let next = update vars next in
            mk_closed_let span monadic pat bound next)
  in
  let body =
    Option.map
      (fun body ->
        let fvars, body = open_fun_body ctx span body in
        let fvars = FVarId.Set.of_list (FVarId.Map.keys fvars) in
        let body = { body with body = update fvars body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

type loop_rel = {
  inputs : texpr list list;
  outputs : texpr list list;
  used_fvars : FVarId.Set.t;
      (** The set of fvars which are actually used by the loop (not simply
          transmitted to the continues *)
  smaller_than_input : int FVarId.Map.t;
      (** The set of variables that are structurally smaller than an input
          variable. We use this to compute whether the loop is structurally
          terminating because it "dives" into a recursive data-structure: this
          is one of the criteria we use to decide whether we should extract it
          to a recursive function or not.

          This is a map from a variable id to the index (that is, the position)
          of the input the variable is smaller than. *)
  equal_to_input : int FVarId.Map.t;
      (** The set of variables that are equal to an input.

          This is a map for the same reasons as [smaller_than_input]. *)
}

let loop_rel_to_string (ctx : ctx) (rel : loop_rel) : string =
  let { inputs; outputs; used_fvars; smaller_than_input; equal_to_input } =
    rel
  in
  "{\n  inputs = "
  ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) inputs
  ^ ";\n  outputs = "
  ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) outputs
  ^ ";\n  used_fvars = "
  ^ FVarId.Set.to_string None used_fvars
  ^ ";\n  smaller_than_input = "
  ^ FVarId.Map.to_string None string_of_int smaller_than_input
  ^ ";\n  equal_to_input = "
  ^ FVarId.Map.to_string None string_of_int equal_to_input
  ^ "\n}"

(** Analyze a loop body to compute the relationship between its input and its
    outputs.

    Remark: we expect the loop body to have been opened (only the *inputs* of
    the loop body, it is fine if the other variables are bound). *)
let compute_loop_input_output_rel (span : Meta.span) (ctx : ctx) (loop : loop) :
    loop_rel =
  [%sanity_check] span (List.for_all tpat_is_open loop.loop_body.inputs);

  let body = loop.loop_body in
  let inputs = List.map (fun _ -> ref []) body.inputs in
  let input_fvars =
    List.map
      (fun (p : tpat) ->
        match p.pat with
        | POpen (fv, _) -> Some fv
        | PIgnored -> None
        | _ -> [%internal_error] span)
      body.inputs
  in
  let outputs = List.map (fun _ -> ref []) loop.output_tys in
  let used_fvars = ref FVarId.Set.empty in
  let inputs_fvars = tpats_get_fvars body.inputs in

  (* The variables which are an input or equal (because of a let-binding) to an input.
     This is a map from the variable id to the index (i.e., position) of the input
     to which the variable is equal to. *)
  let equal_to_input =
    ref
      (FVarId.Map.of_list
         (List.mapi
            (fun i (x : fvar) -> (x.id, i))
            (List.filter_map (fun x -> x) input_fvars)))
  in
  (* The variables which are stricly smaller than an input.
     This is a map for the same reason as [input_or_eq]. *)
  let smaller_than_input = ref FVarId.Map.empty in

  let is_smaller_than_or_equal_to_input (fid : FVarId.id) : int option =
    match FVarId.Map.find_opt fid !equal_to_input with
    | Some i -> Some i
    | None -> FVarId.Map.find_opt fid !smaller_than_input
  in

  (* Register than [tgt] is equal to [src] *)
  let register_equal (tgt : fvar) (src : FVarId.id) : unit =
    (* Equality *)
    Option.iter
      (fun input_id ->
        equal_to_input := FVarId.Map.add tgt.id input_id !equal_to_input)
      (FVarId.Map.find_opt src !equal_to_input);
    (* Smaller than *)
    Option.iter
      (fun input_id ->
        smaller_than_input := FVarId.Map.add tgt.id input_id !smaller_than_input)
      (FVarId.Map.find_opt src !smaller_than_input)
  in
  let register_smaller (fid : FVarId.id) (input_id : int) : unit =
    smaller_than_input := FVarId.Map.add fid input_id !smaller_than_input
  in

  let marked_as_used_visitor =
    object
      inherit [_] iter_expr
      method! visit_fvar_id _ fid = used_fvars := FVarId.Set.add fid !used_fvars
    end
  in

  let visitor =
    object (self)
      inherit [_] iter_expr as super

      method! visit_Loop env loop =
        (* We do not visit the inner loops *)
        List.iter (self#visit_texpr env) loop.inputs

      method visit_app_texpr env (e : texpr) =
        [%ldebug
          "- e.ty: " ^ ty_to_string ctx e.ty ^ "\n- e:\n"
          ^ texpr_to_string ctx e];
        match
          opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:false
            ~opened_vars:true e
        with
        | None ->
            (* We need to visit the sub-expressions *)
            super#visit_texpr env e
        | Some ({ variant_id; args; _ }, _) ->
            [%ldebug
              "- outputs:\n"
              ^ Print.list_to_string ~sep:"\n"
                  (fun el -> Print.list_to_string (texpr_to_string ctx) !el)
                  outputs
              ^ "\n\n- args:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];

            if variant_id = loop_result_break_id then (
              [%sanity_check] span (List.length outputs = List.length args);
              (* Update the output map *)
              List.iter
                (fun (l, arg) -> l := arg :: !l)
                (List.combine outputs args);
              (* Also visit the arguments: we want to register the used variables *)
              List.iter (self#visit_texpr env) args)
            else if variant_id = loop_result_continue_id then (
              [%ldebug
                "- inputs:\n"
                ^ Print.list_to_string ~sep:"\n"
                    (fun el -> Print.list_to_string (texpr_to_string ctx) !el)
                    inputs
                ^ "\n\n- args:\n"
                ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];

              (* There is a special case if the loop has a single input of type
                     unit *)
              match loop.inputs with
              | [ input ] when input.ty = mk_unit_ty ->
                  List.iter (fun l -> l := mk_unit_texpr :: !l) inputs
              | _ ->
                  [%sanity_check] span (List.length inputs = List.length args);
                  (* Update the input map *)
                  Collections.List.iter
                    (fun ((l, input, arg) : _ * fvar option * _) ->
                      (* Register the output *)
                      l := arg :: !l;
                      (* Also check whether the output is exactly the input:
                             if it is not the case, we mark the variables which appear
                             in the output as used. *)
                      match (input, arg.e) with
                      | Some fvar, FVar fid when fid = fvar.id -> ()
                      | _ -> marked_as_used_visitor#visit_texpr () arg)
                    (Collections.List.combine3 inputs input_fvars args))
            else (
              [%sanity_check] span (variant_id = loop_result_fail_id);
              (* Also visit the arguments: we want to register the used variables *)
              List.iter (self#visit_texpr env) args)

      (* We match on the expr to simplify handling of the app case *)
      method! visit_texpr env e =
        match e.e with
        | App _ -> self#visit_app_texpr env e
        | _ -> super#visit_texpr env e

      method! visit_Let env monadic pat bound next =
        (* Register the equality *)
        (match (pat.pat, bound.e) with
        | POpen (tgt, _), FVar src_id -> register_equal tgt src_id
        | _ -> ());
        super#visit_Let env monadic pat bound next

      method! visit_Switch env scrut switch =
        match switch with
        | If _ -> super#visit_Switch env scrut switch
        | Match branches -> (
            (* If the scrutinee is a variable derived from the input (either equal
               or smaller than an input) register that all the variables introduced
               here are smaller *)
            match scrut.e with
            | FVar scrut_id -> (
                match is_smaller_than_or_equal_to_input scrut_id with
                | None -> super#visit_Switch env scrut switch
                | Some i ->
                    (* Explore the scrutinee to register all the free variables there as used *)
                    self#visit_texpr env scrut;
                    (* Explore the branches *)
                    let visitor =
                      object
                        inherit [_] iter_expr
                        method! visit_fvar_id _ fid = register_smaller fid i
                      end
                    in
                    List.iter
                      (fun ({ pat; branch } : match_branch) ->
                        (* Register all the fvar ids appearing in the branch pattern
                           as being smaller than the input *)
                        visitor#visit_tpat () pat;
                        (* Explore the branch expressions themselves *)
                        self#visit_texpr env branch)
                      branches)
            | _ -> super#visit_Switch env scrut switch)

      method! visit_fvar_id _ fid = used_fvars := FVarId.Set.add fid !used_fvars
    end
  in
  visitor#visit_texpr () body.loop_body;

  let inputs = List.map (fun l -> List.rev !l) inputs in
  let outputs = List.map (fun l -> List.rev !l) outputs in
  [%ldebug
    "About to explore inputs/outputs to compute the used variables:"
    ^ "\n- inputs: "
    ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) inputs
    ^ "\n- outputs: "
    ^ Print.list_to_string (Print.list_to_string (texpr_to_string ctx)) outputs];

  (* Filter the used variables to only preserve the inputs *)
  let used_fvars =
    FVarId.Set.filter (fun fid -> FVarId.Set.mem fid inputs_fvars) !used_fvars
  in

  (* *)
  {
    inputs;
    outputs;
    used_fvars;
    equal_to_input = !equal_to_input;
    smaller_than_input = !smaller_than_input;
  }

(** Small helper: decompose a pattern if it is a variable or an ignored pattern
    of type tuple. Returns an optional substitution (if the pattern was a
    variable) *)
let decompose_tuple_pat span (ctx : ctx) (pat : tpat) :
    bool * tpat * (FVarId.id * texpr) option =
  if (is_pat_open pat || is_ignored_pat pat) && is_tuple_ty pat.ty then
    (* Decompose the pattern *)
    let pat, subst =
      let tys = [%add_loc] as_tuple_ty span pat.ty in
      if is_pat_open pat then
        (* Introduce auxiliary variables *)
        let fv, _ = [%add_loc] as_pat_open span pat in
        let fvars = List.map (mk_fresh_fvar ctx) tys in
        let pat =
          mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) fvars)
        in
        let tuple =
          mk_simpl_tuple_texpr span (List.map mk_texpr_from_fvar fvars)
        in
        (pat, Some (fv.id, tuple))
      else
        (* Simply decompose into a tuple of ignored patterns *)
        (mk_simpl_tuple_pat (List.map mk_ignored_pat tys), None)
    in
    (true, pat, subst)
  else (false, pat, None)

let decompose_loop_outputs (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  let visitor =
    object (self)
      inherit [_] map_expr as super

      method! visit_Let env monadic pat bound next =
        match bound.e with
        | Loop _ ->
            (* Attempt to decompose the pattern *)
            let decompose, pat, subst = decompose_tuple_pat span ctx pat in
            if decompose then
              (* Update the bound expression first *)
              let bound = self#visit_texpr env bound in
              (* Register the substitution *)
              let env =
                match subst with
                | None -> env
                | Some (fid, tuple) -> FVarId.Map.add fid tuple env
              in
              (* Update the next expression *)
              let next = self#visit_texpr env next in
              (* Recreate the let-binding *)
              (mk_opened_let monadic pat bound next).e
            else super#visit_Let env monadic pat bound next
        | _ -> super#visit_Let env monadic pat bound next

      method! visit_FVar env fid =
        match FVarId.Map.find_opt fid env with
        | None -> FVar fid
        | Some e -> e.e
    end
  in

  let body =
    Option.map
      (fun body ->
        let _, body = open_all_fun_body ctx span body in
        let body =
          { body with body = visitor#visit_texpr FVarId.Map.empty body.body }
        in
        close_all_fun_body span body)
      def.body
  in
  { def with body }

(** Helper to filter the useless loop inputs/outputs: update the continue/breaks
    in a loop body by filtering the useless arguments.

    [opened_vars]: if [true], all the bound variables should have been opened,
    otherwise we open/close them on the fly. *)
let filter_loop_useless_inputs_outputs_update_continue_break (span : Meta.span)
    (ctx : ctx) ~(opened_vars : bool) (keep_outputs : bool list)
    (keep_inputs : bool list) (continue_ty : ty) (break_ty : ty)
    (body : loop_body) : loop_body =
  let opt_open_binder pat next =
    if opened_vars then (pat, next)
    else
      let _, pat, next = open_binder ctx span pat next in
      (pat, next)
  in
  let opt_close_binder pat next =
    if opened_vars then (pat, next) else close_binder span pat next
  in
  let mk_let monadic pat bound next =
    if opened_vars then mk_opened_let monadic pat bound next
    else mk_closed_let span monadic pat bound next
  in
  let rec update (e : texpr) : texpr =
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _ ->
        (* Shouldn't happen *)
        [%internal_error] span
    | EError _ -> e
    | App _ | Qualif _ ->
        (* This might be a break or a continue *)
        begin
          match
            opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:true
              ~opened_vars e
          with
          | None -> e
          | Some ({ variant_id; args = outputs; _ }, rebind) ->
              let filter keep el =
                let el =
                  (* There is a special case if the loop has a single input of type unit *)
                  match body.inputs with
                  | [ pat ] when pat.ty = mk_unit_ty -> []
                  | _ ->
                      [%sanity_check] span (List.length keep = List.length el);
                      List.filter_map
                        (fun (keep, x) -> if keep then Some x else None)
                        (List.combine keep el)
                in
                mk_simpl_tuple_texpr span el
              in
              if variant_id = loop_result_break_id then
                (* Filter *)
                let outputs = filter keep_outputs outputs in
                rebind (mk_break_texpr span continue_ty outputs)
              else if variant_id = loop_result_continue_id then
                (* We leave the expression unchanged but have to modify its type *)
                let inputs = filter keep_inputs outputs in
                rebind (mk_continue_texpr span inputs break_ty)
              else (
                [%sanity_check] span (variant_id = loop_result_fail_id);
                let arg = mk_simpl_tuple_texpr span outputs in
                rebind (mk_loop_result_fail_texpr span continue_ty break_ty arg))
        end
    | Let (monadic, pat, bound, next) ->
        (* No need to update the bound expression *)
        let pat, next = opt_open_binder pat next in
        let next = update next in
        mk_let monadic pat bound next
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (update e0, update e1)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    let pat, branch = opt_open_binder pat branch in
                    let branch = update branch in
                    let pat, branch = opt_close_binder pat branch in
                    { pat; branch })
                  branches
              in
              Match branches
        in
        [%add_loc] mk_switch span scrut switch
    | Meta (m, e) -> mk_emeta m (update e)
  in

  let inputs =
    List.filter_map
      (fun (keep, input) -> if keep then Some input else None)
      (List.combine keep_inputs body.inputs)
  in
  { inputs; loop_body = update body.loop_body }

(** Small helper: given a loop_rel, compute the set of inputs which:
    - are not used inside the loop
    - remain constant throughout the loop execution (if [filter_constant_inputs]
      is true)

    We output:
    - the set of constant inputs
    - the list of inputs to keep (this is a list of booleans, [true] means
      [keep]) *)
let compute_loop_useless_inputs (span : Meta.span) (ctx : ctx)
    ~(filter_constant_inputs : bool) (loop : loop) (rel : loop_rel) :
    FVarId.Set.t * bool list =
  let body = loop.loop_body in
  let input_vars =
    List.map
      (fun (p : tpat) ->
        match p.pat with
        | POpen (v, _) -> Some v
        | PIgnored -> None
        | _ -> [%internal_error] span)
      body.inputs
  in

  (* First, the inputs *)
  let non_constant_inputs =
    List.map
      (fun ((fv, el) : fvar option * texpr list) ->
        (* Check if all the expressions are actually exactly the
           input expression *)
        match fv with
        | None -> false
        | Some fv ->
            not
              (List.for_all
                 (fun (e : texpr) ->
                   match e.e with
                   | FVar fid -> fid = fv.id
                   | _ -> false)
                 el))
      (List.combine input_vars rel.inputs)
  in
  let used_inputs =
    List.map
      (fun (fv : fvar option) ->
        match fv with
        | None -> false
        | Some fv -> FVarId.Set.mem fv.id rel.used_fvars)
      input_vars
  in
  let constant_inputs_set =
    FVarId.Set.of_list
      (List.filter_map
         (fun ((keep, fv) : _ * fvar option) ->
           if keep then None
           else
             match fv with
             | None -> None
             | Some fv -> Some fv.id)
         (List.combine non_constant_inputs input_vars))
  in

  (* We preserve the inputs if:
     - they are modified throughout the loop and are used inside it
     - they are are used within the loop *and* we extract auxiliary
       functions for the loops (we want to preserve the order of the
       input). *)
  let constant_inputs = List.map (fun b -> not b) non_constant_inputs in
  let unit_or_ignored_inputs =
    List.map
      (fun (p : tpat) -> p.ty = mk_unit_ty || is_ignored_pat p)
      body.inputs
  in
  [%ldebug
    let bool_list_to_string = Print.list_to_string ~sep:"; " string_of_bool in
    "- inputs: "
    ^ Print.list_to_string ~sep:"; " (tpat_to_string ctx) body.inputs
    ^ "\n- constant_inputs: "
    ^ bool_list_to_string constant_inputs
    ^ "\n- used: "
    ^ bool_list_to_string used_inputs
    ^ "\n- unit_or_ignored: "
    ^ bool_list_to_string unit_or_ignored_inputs];
  let filter =
    Collections.List.map3
      (fun constant used unit_or_ignored ->
        (* Constant inputs: filter them if it is allowed or if
           the input is not used *)
        (constant && (filter_constant_inputs || not used))
        (* We filter all inputs which have unit type or are
           the ignored pattern *)
        || unit_or_ignored)
      constant_inputs used_inputs unit_or_ignored_inputs
  in

  (* Revert: we want to know which inputs to *keep* *)
  let keep = List.map (fun b -> not b) filter in

  (* *)
  (constant_inputs_set, keep)

(** Small helper to filter the useless inputs/outputs of a loop: update a loop
    body bound in a let-binding *)
let filter_loop_useless_inputs_outputs_update_loop_body (span : Meta.span)
    (ctx : ctx) ~(filter_constant_inputs : bool) (pat : tpat) (loop : loop)
    (next : texpr) : tpat * loop * texpr =
  let body = loop.loop_body in

  (* Analyze the body *)
  let rel = compute_loop_input_output_rel span ctx loop in

  [%ldebug
    "- used_inputs: "
    ^ FVarId.Set.to_string None rel.used_fvars
    ^ "\n- pat: " ^ tpat_to_string ctx pat ^ "\n- loop:\n"
    ^ loop_to_string ctx loop ^ "\n- next:\n" ^ texpr_to_string ctx next];

  (* We need to decompose the pattern, if it is a tuple, before attempting
       to destruct it below. *)
  let pat, next =
    let _, pat, subst = decompose_tuple_pat span ctx pat in
    let next =
      match subst with
      | None -> next
      | Some (fid, e) ->
          (* We need to update the next expression *)
          let visitor =
            object
              inherit [_] map_expr
              method! visit_FVar _ fid' = if fid' = fid then e.e else FVar fid'
            end
          in
          visitor#visit_texpr () next
    in
    (pat, next)
  in

  (* We go through the inputs and identify those which are
     mapped to exactly themselves (i.e., remain unchanged throughout
     the loop). If [filter_constant_inputs] is [true] we filter them.
     Otherwise, we filter only the inputs which are actually not used
     within the loop (and are just passed throughout the recursive calls).

     We then go through the outputs: for a given output, if all the expressions
     it is mapped to are actually the same, and this expression doesn't
     contain variables which are locally bound in the loop, it means that
     this output can be computed from the inputs of the loop only. If
     those inputs were filtered above, it means they are left unchanged
     throughout the loop and so that the output can be computed from
     the *initial* input. We thus filter it.
  *)
  [%ldebug tpat_to_string ctx pat];
  let output_vars = try_destruct_tuple_or_ignored_tpat span pat in
  let output_vars =
    List.map
      (fun (p : tpat) ->
        match p.pat with
        | POpen (v, _) -> Some v
        | PIgnored -> None
        | _ -> [%craise] span "Not an open binder or an ignored pattern")
      output_vars
  in
  let input_vars =
    List.map
      (fun (p : tpat) ->
        match p.pat with
        | POpen (v, _) -> Some v
        | PIgnored -> None
        | _ -> [%internal_error] span)
      body.inputs
  in
  let input_var_ids =
    List.map (Option.map (fun (fv : fvar) -> fv.id)) input_vars
  in

  (* Compute the set of constant inputs, and the list of inputs to keep *)
  let constant_inputs_set, keep_inputs =
    compute_loop_useless_inputs span ctx ~filter_constant_inputs loop rel
  in

  (* Then, the outputs.

     Check if the output can be computed statically from the
     initial inputs. *)
  let output_known_statically (el : texpr list) : bool =
    (* The output is known statically only if it contains:
       - free variables (those were introduced *before* the loop)
       - locally bound vars (those can appear in expressions like [fun x => x])

       The non-locally bound vars are bound in the loop body: if the
       expression contains such variables we have to preserve it, because
       it means its value depends on what happens inside the loop.

       We check the presence of non-locally bound vars in a simple
       way: we simply open all the variables bound in the body,
       and check if there are remaining bound variables - those must
       be bound elsewhere.
     *)
    (* Check if there are bound vars *)
    let have_bvars =
      List.exists
        (fun x -> x)
        (List.map (fun e -> texpr_has_bvars (open_all_texpr ctx span e)) el)
    in
    if have_bvars then false
    else
      match el with
      | [] ->
          (* Could happen with infinite loops, for now we forbid them *)
          [%internal_error] span
      | e :: el ->
          if List.for_all (fun e' -> e = e') el then
            (* All the expressions are the same: now check
               if all the free variables are filtered inputs *)
            let fvars = texpr_get_fvars e in
            FVarId.Set.subset fvars constant_inputs_set
          else false
  in
  let keep_outputs =
    let known_statically = List.map output_known_statically rel.outputs in
    List.map
      (fun (known, x) -> (not known) && Option.is_some x)
      (List.combine known_statically output_vars)
  in

  [%ldebug
    "- keep_inputs: "
    ^ Print.list_to_string Print.bool_to_string keep_inputs
    ^ "\n- keep_outputs: "
    ^ Print.list_to_string Print.bool_to_string keep_outputs];

  (* We need to compute the new expressions for the outputs we filter,
     by substituting the free variables which appear in their expressions
     (which are inputs bound locally in the loop) with the initial inputs
     with which the loop is "called". We can then introduce the let-bindings. *)
  let to_initial_input =
    FVarId.Map.of_list
      (List.filter_map
         (fun (fv, v) ->
           match fv with
           | None -> None
           | Some fv -> Some (fv, v))
         (List.combine input_var_ids loop.inputs))
  in
  let update_initial_inputs (e : texpr) : texpr =
    let visitor =
      object
        inherit [_] map_expr

        method! visit_FVar _ fid =
          match FVarId.Map.find_opt fid to_initial_input with
          | None -> FVar fid
          | Some e -> e.e
      end
    in
    visitor#visit_texpr () e
  in
  let updt_outputs =
    List.filter_map
      (fun (keep, output_var, el) ->
        match el with
        | [] -> [%internal_error] span
        | e :: _ ->
            if keep || output_var = None then None
            else Some (update_initial_inputs e))
      (Collections.List.combine3 keep_outputs output_vars rel.outputs)
  in

  (* Update the loop body *)
  let continue_ty =
    let tys =
      List.filter_map
        (fun ((keep, input) : _ * texpr) ->
          if keep then Some input.ty else None)
        (List.combine keep_inputs loop.inputs)
    in
    mk_simpl_tuple_ty tys
  in
  let break_ty =
    let tys =
      List.filter_map
        (fun ((keep, x) : _ * fvar option) ->
          match (keep, x) with
          | true, Some x -> Some x.ty
          | _ -> None)
        (List.combine keep_outputs output_vars)
    in
    (* There may be only one output, which has type tuple: if it is
         the case we need to simplify it *)
    let tys =
      match tys with
      | [ ty ] -> try_destruct_tuple span ty
      | _ -> tys
    in
    mk_simpl_tuple_ty tys
  in

  [%ldebug
    "- continue_ty: "
    ^ ty_to_string ctx continue_ty
    ^ "\n- break_ty: " ^ ty_to_string ctx break_ty];

  (* Substitute the unchanged variables with their (constant) values in the loop body *)
  let body =
    [%sanity_check] span (List.length input_vars = List.length loop.inputs);
    let bindings = List.combine input_vars loop.inputs in
    let bindings =
      List.filter_map
        (fun ((keep, (fv, v)) : _ * (fvar option * _)) ->
          if keep then None
          else
            match fv with
            | None -> None
            | Some fv -> Some (fv.id, v))
        (List.combine keep_inputs bindings)
    in
    let subst = FVarId.Map.of_list bindings in

    let visitor =
      object
        inherit [_] map_expr

        method! visit_FVar _ fid =
          match FVarId.Map.find_opt fid subst with
          | None -> FVar fid
          | Some e -> e.e
      end
    in
    visitor#visit_loop_body () body
  in

  (* Filter the arguments of the continue/breaks *)
  let body =
    filter_loop_useless_inputs_outputs_update_continue_break span ctx
      ~opened_vars:false keep_outputs keep_inputs continue_ty break_ty body
  in
  let filter keep xl =
    List.filter_map
      (fun (keep, x) -> if keep then Some x else None)
      (List.combine keep xl)
  in
  let compute_num keep n =
    List.length (List.filter (fun b -> b) (Collections.List.prefix n keep))
  in
  let loop =
    {
      loop with
      output_tys = filter keep_outputs loop.output_tys;
      num_output_values = compute_num keep_outputs loop.num_output_values;
      inputs = filter keep_inputs loop.inputs;
      num_input_conts = compute_num keep_inputs loop.num_input_conts;
      loop_body = body;
    }
  in
  [%ldebug
    "- output_tys: "
    ^ Print.list_to_string (ty_to_string ctx) loop.output_tys
    ^ "\n- num_output_values: "
    ^ string_of_int loop.num_output_values
    ^ "\n- inputs: "
    ^ Print.list_to_string (texpr_to_string ctx) loop.inputs
    ^ "\n- num_input_conts: "
    ^ string_of_int loop.num_input_conts];

  (* Introduce the loop outputs we filtered by adding let-bindings
     afterwards (they're not output by the loop anymore) *)
  let kept_output_vars, filt_output_vars =
    List.partition fst (List.combine keep_outputs output_vars)
  in
  let kept_output_vars = List.filter_map snd kept_output_vars in
  let filt_output_vars = List.filter_map snd filt_output_vars in
  let filt_output_vars = List.map (mk_tpat_from_fvar None) filt_output_vars in
  [%ldebug
    "- filt_output_vars:\n"
    ^ String.concat "\n" (List.map (tpat_to_string ctx) filt_output_vars)
    ^ "\n- updt_outputs:\n"
    ^ String.concat "\n" (List.map (texpr_to_string ctx) updt_outputs)];

  (* We split the outputs in two:
     - the outputs which are variables, that we directly inline
     - the others, for which we introduce let-bindings
   *)
  let lets = List.combine filt_output_vars updt_outputs in
  let to_inline, to_let = List.partition (fun (_, e) -> is_fvar e) lets in
  let to_inline =
    FVarId.Map.of_list
      (List.map
         (fun (p, e) -> ((fst ([%add_loc] as_pat_open span p)).id, e))
         to_inline)
  in
  let next =
    let visitor =
      object
        inherit [_] map_expr

        method! visit_FVar _ fid =
          match FVarId.Map.find_opt fid to_inline with
          | None -> FVar fid
          | Some e -> e.e
      end
    in
    visitor#visit_texpr () next
  in
  let next = mk_closed_lets span false to_let next in

  (* *)
  let pat =
    mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) kept_output_vars)
  in

  (* *)
  (pat, loop, next)

(** We do several things.

    1. We filter the loop outputs which are not used.

    2. We filter the loop outputs which are actually equal to some of its
    inputs, while filtering the inputs which are equal throughout the execution
    of the loop (we do the latter only if [filter_constant_inputs] is [true] or
    if the input is actually not used within the loop body - we have this option
    because we want to filter those inputs *after* introducing auxiliary
    functions, if there are) or are not used outside of the recursive calls.

    For instance:
    {[
      let (i, y) =
        loop (fun i x ->
          if i < n then continue ((i + 1), y)
          else break (i, y)) i0 y0
      in
      ...

        ~>

      let i =
        loop (fun i x ->
          if i < n then continue (i + 1)
          else break i) i0
      in
      let y = y0 in
      ...
    ]}

    3. We filter the loop output backward functions which are the identity. *)
let filter_loop_useless_inputs_outputs (ctx : ctx)
    ~(filter_constant_inputs : bool) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Small helper: filter the variables which appear in [pat] and not in [next] *)
  let filter_useless (next : texpr) (pat : tpat) : tpat =
    let fvars = texpr_get_fvars next in

    let visitor =
      object
        inherit [_] map_tpat

        method! visit_POpen _ v mp =
          if FVarId.Set.mem v.id fvars then POpen (v, mp) else PIgnored

        method! visit_PBound _ _ _ = [%internal_error] span
      end
    in
    visitor#visit_tpat () pat
  in

  let rec update (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | Lambda _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Meta (m, e) -> mk_emeta m (update e)
    | Let (monadic, pat, bound, next) -> (
        let _, pat, next = open_binder ctx span pat next in

        (* Update the next expression first - there may be loops in there *)
        let next = update next in

        (* Filter the useless variables which appear in [pat] (some currently
           used variables may have been eliminated by simplifying the loops in
           next) *)
        let pat = filter_useless next pat in

        (* Check if the bound expression is a loop *)
        match bound.e with
        | Loop loop ->
            let _, body = open_loop_body ctx span loop.loop_body in

            (* First explore the loop body: we want to simplify the inner loops *)
            let body = { body with loop_body = update body.loop_body } in
            let loop = { loop with loop_body = body } in

            let update_loop =
              filter_loop_useless_inputs_outputs_update_loop_body span ctx
                ~filter_constant_inputs
            in

            (* Update the loop itself *)
            let pat, loop, next = update_loop pat loop next in

            let pat, loop, next =
              if not filter_constant_inputs then
                (* Because we use [filter_constant_inputs = false], the first application of
                   [update_loop] filters all the outputs that need to be filtered, but may
                   leave some unused inputs (which became unused because they were used in
                   some outputs which got filtered). We thus have to call it again. *)
                update_loop pat loop next
              else (pat, loop, next)
            in

            let loop =
              { loop with loop_body = close_loop_body span loop.loop_body }
            in

            let loop : texpr =
              {
                e = Loop loop;
                ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys);
              }
            in

            (* Bind the loop *)
            mk_closed_let span monadic pat loop next
        | _ ->
            (* No need to update the bound expression *)
            mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (update e0, update e1)
          | Match bl ->
              Match
                (List.map
                   (fun ({ pat; branch } : match_branch) ->
                     let _, pat, branch = open_binder ctx span pat branch in
                     let branch = update branch in
                     let pat, branch = close_binder span pat branch in
                     { pat; branch })
                   bl)
        in
        [%add_loc] mk_switch span scrut switch
  in
  let body =
    Option.map
      (fun body ->
        let _, body = open_fun_body ctx span body in
        let body = { body with body = update body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

(** Reorder the outputs of loops, in particular to trigger simplifications with
    [loops_to_recursive].

    There are several issues linked to [loops_to_recursive]:
    {ul
     {- in order for [loops_to_recursive] to be triggered, it needs the backward
        functions to be used in the *output* in exactly the same order as they
        are received as input (the main reason is that it makes the code of
        [loops_to_recursive] slightly easier).
     }
     {- it can happen that some output *value* is actually a call to a loop
        backward function, while [loops_to_recursive] will only analyse the loop
        output backward functions, not the loop output values.

        For instance, we sometimes generate code like this:
        {[
          def loop (back : ...) (l : List a) :=
            match l with
            | Nil => ok (back ...) (* HERE *)
            | Cons ... => ...
        ]}
        where in [ok (back ...)], the expression [back ...] is tagged as an
        output value.

        This micro-pass changes the order of the output values and updates the
        split between values and backward functions so that [loops_to_recursive]
        can trigger. Of course we could do everything inside of
        [loops_to_recursive], but that would make the code quite complex.
     }
    }

    In case we do not reorder the outputs for [loops_to_recursive], this
    micro-pass will try to reorder the outputs to solve the following case:
    {[
      def foo ... :=
        let (x, y) <- loop (fun ... ->
         ok (x, y))
        ok (y, x)

         ~~>

      def foo ... :=
        loop (fun ... ->
         ok (y, x))
    ]} *)
let reorder_loop_outputs (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Helper to update the breaks in a loop body. *)
  let update_and_close_loop_body (explore : texpr -> texpr)
      (output_indices : int list) (num_output_backs : int) (loop : loop) : texpr
      =
    let continue_ty =
      mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) loop.inputs)
    in
    let rec update (e : texpr) : texpr =
      match e.e with
      | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _
        ->
          (* Shouldn't happen *)
          [%internal_error] span
      | EError _ -> e
      | App _ | Qualif _ ->
          (* This might be a break or a continue *)
          begin
            match
              opt_destruct_loop_result_decompose_outputs ctx span
                ~intro_let:true ~opened_vars:false e
            with
            | None -> e
            | Some ({ variant_id; args; _ }, rebind) ->
                if variant_id = loop_result_break_id then (
                  (* Reorder the outputs *)
                  [%sanity_check] span
                    (List.length args = List.length output_indices);
                  let args =
                    List.map
                      (fun i -> Collections.List.nth args i)
                      output_indices
                  in
                  let args = mk_simpl_tuple_texpr span args in
                  rebind (mk_break_texpr span continue_ty args))
                else
                  (* Nothing to do *)
                  e
          end
      | Let (monadic, pat, bound, next) ->
          (* No need to update the bound expression *)
          let _, pat, next = open_binder ctx span pat next in
          let next = update next in
          mk_closed_let span monadic pat bound next
      | Switch (scrut, switch) ->
          (* No need to update the scrutinee *)
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun ({ pat; branch } : match_branch) ->
                      let _, pat, branch = open_binder ctx span pat branch in
                      let branch = update branch in
                      let pat, branch = close_binder span pat branch in
                      { pat; branch })
                    branches
                in
                Match branches
          in
          [%add_loc] mk_switch span scrut switch
      | Meta (m, e) -> mk_emeta m (update e)
    in

    let body = loop.loop_body in
    let body = { body with loop_body = update body.loop_body } in

    (* Recursively explore the loop body *)
    let body = { body with loop_body = explore body.loop_body } in

    (* Close the loop body *)
    let body = close_loop_body span body in

    (* Rebuild the loop *)
    let num_outputs = List.length loop.output_tys in
    let num_output_values = num_outputs - num_output_backs in
    let output_tys =
      List.map (fun i -> Collections.List.nth loop.output_tys i) output_indices
    in
    let loop =
      {
        loop with
        output_tys;
        num_output_values;
        inputs = loop.inputs;
        num_input_conts = loop.num_input_conts;
        loop_body = body;
      }
    in

    let loop : texpr =
      { e = Loop loop; ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys) }
    in
    [%ldebug "loop:\n" ^ texpr_to_string ctx loop];

    loop
  in

  (* Small helper: update a let-binding binding a loop, after we reordred the
     outputs *inside* the loop (i.e., the arguments given to the breaks) *)
  let update_let (monadic : bool) (pat : tpat) (loop : texpr) (next : texpr)
      (output_indices : int list) : texpr =
    (* Decompose the pattern, which should be a tuple *)
    let patl = try_destruct_tuple_or_ignored_tpat span pat in

    (* Reorder *)
    let patl = List.map (fun i -> Collections.List.nth patl i) output_indices in
    let pat = mk_simpl_tuple_pat patl in

    (* Create the let-binding *)
    mk_closed_let span monadic pat loop next
  in

  (* Small helper: attempt to compute a new order which would be useful for
     [loops_to_recursive] *)
  let compute_outputs_indices_to_reorder_backs (loop : loop) :
      (int list * int) option =
    (* Analyze the body *)
    let rel = compute_loop_input_output_rel span ctx loop in

    (* Go through all the outputs, check if some of them are actually
       calls to input backward functions *)
    (* Helper: is a continuation exactly a call to an input backward function? *)
    let input_conts_fvids_to_index =
      FVarId.Map.of_list
        (List.filter_map
           (fun x -> x)
           (List.mapi
              (fun i (p : tpat) ->
                match p.pat with
                | PIgnored -> None
                | POpen (fvar, _) -> Some (fvar.id, i)
                | _ -> [%internal_error] span)
              (Collections.List.prefix loop.num_input_conts
                 loop.loop_body.inputs)))
    in
    [%ldebug
      "- input_conts_fvids_to_index: "
      ^ FVarId.Map.to_string None string_of_int input_conts_fvids_to_index
      ^ "\n- num_input_conts: "
      ^ string_of_int loop.num_input_conts
      ^ "\n- num_output_values: "
      ^ string_of_int loop.num_output_values];

    let is_call_to_input (x : texpr) : int option =
      let _pats, body = raw_destruct_lambdas x in
      let _, body = raw_destruct_lets body in
      let f, _args = destruct_apps body in
      match f.e with
      | FVar fid -> FVarId.Map.find_opt fid input_conts_fvids_to_index
      | _ -> None
    in
    let { outputs; _ } : loop_rel = rel in
    [%ldebug "loop_rel:\n" ^ loop_rel_to_string ctx rel];
    let outputs_call_inputs =
      List.filter_map
        (fun (i, xl) ->
          match List.find_opt Option.is_some xl with
          | None -> None
          | Some x ->
              let x = Option.get x in
              if List.for_all (fun x' -> x' = Some x) xl then Some (i, x)
              else None)
        (List.mapi
           (fun i x -> (i, x))
           (List.map (List.map is_call_to_input) outputs))
    in
    [%ldebug
      "outputs_call_inputs:\n"
      ^ Print.list_to_string
          (fun (x, i) -> string_of_int x ^ " -> " ^ string_of_int i)
          outputs_call_inputs];

    (* We reorder only if every input backward function has a corresponding
       output. We first compute the map from input backward function (refered
       to by its index) to output index.

       TODO: it would be good to generalize, but it's unclear what we should do,
       so it should be driven by examples. *)
    let input_to_output =
      ref
        (Collections.IntMap.of_list
           (List.init loop.num_input_conts (fun i -> (i, []))))
    in
    List.iter
      (fun (output_index, input_index) ->
        input_to_output :=
          Collections.IntMap.add_to_list input_index output_index
            !input_to_output)
      outputs_call_inputs;
    let input_to_output = !input_to_output in

    (* Check that every input backward function maps to exactly one output *)
    let reorder =
      Collections.IntMap.for_all
        (fun _ x ->
          match x with
          | [ _ ] -> true
          | _ -> false)
        input_to_output
      && not (Collections.IntMap.is_empty input_to_output)
    in
    [%ldebug "reorder: " ^ string_of_bool reorder];

    if not reorder then None
    else
      (* First, simplify the map from input index to output index so that
         it maps to a single index (rather than a list of indices) *)
      let input_to_output =
        Collections.IntMap.map (fun xl -> List.hd xl) input_to_output
      in

      (* Then, compute the indices of the outputs to reorder - we need this
         to partition the outputs between those we put in front and the others *)
      let outputs_to_reorder =
        Collections.IntSet.of_list (Collections.IntMap.values input_to_output)
      in

      (* Finally, compute the list of the indices to use for the outputs.
         e.g., if we want the output to follow the order:
         output at index 2, output at index 0, then output at index 1,
         the list is [2; 0; 1] *)
      let num_outputs = List.length loop.output_tys in
      let output_indices =
        (* The prefix: the values which are not considered to be continuations *)
        List.filter_map
          (fun out_i ->
            (* We simply remove the outputs that will be moved to the end,
               because they are continuations that we want to reorder *)
            if Collections.IntSet.mem out_i outputs_to_reorder then None
            else Some out_i)
          (List.init num_outputs (fun i -> i))
        (* The suffix: the reordered continuations. *)
        @ Collections.IntMap.values input_to_output
      in
      [%sanity_check] span (List.length output_indices = num_outputs);

      Some (output_indices, Collections.IntMap.cardinal input_to_output)
  in

  (* Small helper: analyze the next expression to check if it is exactly
     [ok ...] or [break ...] called on the loop outputs, but in a different
     order.
   *)
  let compute_outputs_indices_if_followed_by_ok (loop : loop) (pat : tpat)
      (next : texpr) =
    (* Check if the next expression is [ok (...)] or [break (...)],
       and reorder the outputs accordingly. *)
    (* Deconstruct the pattern and check that it is a tuple of free variables *)
    [%ldebug "pat: " ^ tpat_to_string ctx pat];
    let patl = try_destruct_tuple_or_ignored_or_open_tpat span pat in
    let patl_fvars =
      List.map
        (fun (p : tpat) ->
          match p.pat with
          | POpen (fv, _) -> Some fv
          | _ -> None)
        patl
    in
    if not (List.for_all Option.is_some patl_fvars) then None
    else
      let patl_fvars = List.map Option.get patl_fvars in
      [%ldebug
        "patl_fvars: " ^ Print.list_to_string (fvar_to_string ctx) patl_fvars];

      (* Deconstruct the [next] expression *)
      let f, args = destruct_apps next in
      let is_ok_or_break =
        match f.e with
        | Qualif
            {
              id =
                AdtCons { adt_id = TBuiltin tid; variant_id = Some variant_id };
              _;
            } -> (
            match tid with
            | TResult when variant_id = result_ok_id -> true
            | TLoopResult when variant_id = loop_result_break_id -> true
            | _ -> false)
        | _ -> false
      in
      [%ldebug "is_ok_or_break: " ^ Print.bool_to_string is_ok_or_break];

      if (not is_ok_or_break) || List.length args <> 1 then None
      else
        (* Analyze the arguments to check if they are all variables,
           and if they are exactly the variables introduced by [patl]
           but in a different order. *)
        let args = try_destruct_tuple_texpr span (List.hd args) in
        let args_fvars =
          List.map
            (fun (a : texpr) ->
              match a.e with
              | FVar fid -> Some fid
              | _ -> None)
            args
        in
        [%ldebug
          "args_fvars: "
          ^ Print.list_to_string
              (Print.option_to_string FVarId.to_string)
              args_fvars];

        if not (List.for_all Option.is_some args_fvars) then None
        else
          let args_fvars = List.map Option.get args_fvars in
          [%ldebug
            "args_fvars: " ^ Print.list_to_string FVarId.to_string args_fvars];

          (* Check that the arguments are exactly the fvars bound by the let-binding
             but in a different order *)
          (* First, compute a map from pattern fvar id to index (which gives the position) *)
          let pat_fvar_to_index =
            FVarId.Map.of_list
              (List.mapi (fun i (fv : fvar) -> (fv.id, i)) patl_fvars)
          in
          [%ldebug
            "pat_fvar_to_index: "
            ^ FVarId.Map.to_string None string_of_int pat_fvar_to_index];

          (* Map every argument to the index of the fvar it uses, if it uses an fvar
             bound in the let *)
          let arg_to_index =
            List.mapi
              (fun arg_i fid ->
                match FVarId.Map.find_opt fid pat_fvar_to_index with
                | None -> None
                | Some pat_index -> Some (arg_i, pat_index))
              args_fvars
          in
          [%ldebug
            "arg_to_index: "
            ^ Print.list_to_string
                (Print.option_to_string
                   (Print.pair_to_string string_of_int string_of_int))
                arg_to_index];

          (* Check that we could map all the arguments to some input, and that
             the order is not respected *)
          if not (List.for_all Option.is_some arg_to_index) then None
          else
            let arg_to_index = List.map Option.get arg_to_index in
            if List.for_all (fun (i, i') -> i = i') arg_to_index then
              (* Order is the same: no need to reorder *)
              None
            else
              (* Order is not the same: we need to reorder *)
              let output_indices = List.map snd arg_to_index in
              (* Computing the number of output continuations is slightly annoying.
                 We do something approximate: we compute the length of the longest
                 suffix of the reordered outputs made of only continuations. *)
              let num_outputs = List.length loop.output_tys in
              let num_output_conts =
                match
                  List.find_index
                    (fun i -> i < loop.num_output_values)
                    (List.rev output_indices)
                with
                | Some i -> i
                | None -> num_outputs
              in
              Some (output_indices, num_output_conts)
  in

  let rec explore (e : texpr) : texpr =
    match e.e with
    | FVar _
    | BVar _
    | CVar _
    | Const _
    | Lambda _
    | App _
    | Qualif _
    | StructUpdate _
    | EError _ -> e
    | Loop _ ->
        (* A loop should always be bound by a let *)
        [%internal_error] span
    | Meta (m, e) -> mk_emeta m (explore e)
    | Let (monadic, pat, bound, next) -> (
        let _, pat, next = open_binder ctx span pat next in

        (* Check if the bound expression is a loop *)
        match bound.e with
        | Loop loop -> (
            let _, body = open_loop_body ctx span loop.loop_body in
            [%ldebug "body:\n" ^ loop_body_to_string ctx body];

            let loop = { loop with loop_body = body } in

            (* Check if we should reorder the output in an attempt to trigger the simplification
               implemented by [loops_to_recursive] *)
            match compute_outputs_indices_to_reorder_backs loop with
            | Some (output_indices, num_output_backs) ->
                (* Apply the update to the loop body - note that this *closes* the loop body *)
                let loop =
                  update_and_close_loop_body explore output_indices
                    num_output_backs loop
                in

                (* Apply the let-binding (we need to reorder the variables in the pattern) *)
                let next = explore next in
                let e = update_let monadic pat loop next output_indices in
                [%ldebug "let-expression:\n" ^ texpr_to_string ctx e];
                e
            | None -> (
                match
                  compute_outputs_indices_if_followed_by_ok loop pat next
                with
                | Some (output_indices, num_output_backs) ->
                    (* Apply the update to the loop body - note that this *closes* the loop body *)
                    let loop =
                      update_and_close_loop_body explore output_indices
                        num_output_backs loop
                    in

                    (* Apply the let-binding (we need to reorder the variables in the pattern) *)
                    let next = explore next in
                    let e = update_let monadic pat loop next output_indices in
                    [%ldebug "let-expression:\n" ^ texpr_to_string ctx e];
                    e
                | None ->
                    (* Do not reorder the output but recursively explore the loop body *)
                    let loop_body =
                      {
                        loop.loop_body with
                        loop_body = explore loop.loop_body.loop_body;
                      }
                    in
                    let loop =
                      { loop with loop_body = close_loop_body span loop_body }
                    in
                    let bound = { bound with e = Loop loop } in
                    let next = explore next in
                    mk_closed_let span monadic pat bound next))
        | _ ->
            (* No need to update the bound expression *)
            let next = explore next in
            mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (explore e0, explore e1)
          | Match bl ->
              Match
                (List.map
                   (fun ({ pat; branch } : match_branch) ->
                     let _, pat, branch = open_binder ctx span pat branch in
                     let branch = explore branch in
                     let pat, branch = close_binder span pat branch in
                     { pat; branch })
                   bl)
        in
        [%add_loc] mk_switch span scrut switch
  in
  let body =
    Option.map
      (fun body ->
        let _, body = open_fun_body ctx span body in
        let body = { body with body = explore body.body } in
        close_fun_body span body)
      def.body
  in
  { def with body }

(** Return [true] if the input/output relation implies that the loop has a
    termination measure.

    We explore all the recursive inputs (the inputs at the [continue]s). If
    there is an index i such that the input at index i decreases for all
    occurrences of [continue], we have a termination measure. *)
let loop_rel_has_termination_measure (rel : loop_rel) : bool =
  let input_decreases (index : int) (input : texpr) : bool =
    (* We consider two cases:
       - the input is a free variable, in which case it needs to be smaller
         than the original input at the same position
       - the input is a structure projection, in which case the structure
         must be a free variable, which should be smaller than the input at
         the same position
    *)
    let smaller (fid : FVarId.id) =
      match FVarId.Map.find_opt fid rel.smaller_than_input with
      | None -> false
      | Some index' ->
          (* We need to be smaller than the input at the same position *)
          index = index'
    in
    match input.e with
    | FVar fid | App ({ e = Qualif { id = Proj _; _ }; _ }, { e = FVar fid; _ })
      -> smaller fid
    | _ -> false
  in
  List.exists
    (fun x -> x)
    (List.mapi (fun i -> List.for_all (input_decreases i)) rel.inputs)

(** Given a loop input/output relation, does the loop satisfy the criteria to be
    turned into a recursive function?

    The criteria are:
    - all input continuations are the identity
    - all the output continuations, and the input continuations given to the
      recursive calls, are exactly calls to an input continuation
    - there is a structural termination measure

    Remark: we used to require that there is at least one input continuation,
    but replaced this with the need for termination measure (the latter case is
    more natural, and it is to be noted that there are cases where we have a
    termination measure but no input continuation, and cases where we have an
    input continuation but no termination measure). *)
let loop_satisfies_recursive_criteria_aux (ctx : ctx) (def : fun_decl)
    (loop : loop) (rel : loop_rel) : bool =
  let span = def.item_meta.span in
  let input_conts = Collections.List.prefix loop.num_input_conts loop.inputs in
  let body = loop.loop_body in
  (* Helper: is a continuation exactly the identity? *)
  let is_identity (x : texpr) : bool =
    let pats, body = raw_destruct_lambdas x in
    match (pats, body.e) with
    | [ { pat = POpen (fv, _); _ } ], FVar fid -> fv.id = fid
    | _ -> false
  in
  let all_inputs_are_id = List.for_all is_identity input_conts in

  (* Helper: is a continuation exactly a call to an input backward function? *)
  let input_conts_fvids =
    tpats_get_fvars (Collections.List.prefix loop.num_input_conts body.inputs)
  in
  let input_conts_fvids_to_index =
    FVarId.Map.of_list
      (List.filter_map
         (fun x -> x)
         (List.mapi
            (fun i (p : tpat) ->
              match p.pat with
              | PIgnored -> None
              | POpen (fvar, _) -> Some (fvar.id, i)
              | _ ->
                  [%craise] span ("Unexpected pattern: " ^ tpat_to_string ctx p))
            (Collections.List.prefix loop.num_input_conts body.inputs)))
  in
  [%ldebug
    "input_conts_fvids: "
    ^ FVarId.Set.to_string None input_conts_fvids
    ^ "\n- input_conts_fvids_to_index: "
    ^ FVarId.Map.to_string None string_of_int input_conts_fvids_to_index
    ^ "\n- num_input_conts: "
    ^ string_of_int loop.num_input_conts
    ^ "\n- num_output_values: "
    ^ string_of_int loop.num_output_values];
  let is_call_to_input (i : int) (x : texpr) : bool =
    [%ldebug "- index: " ^ string_of_int i ^ "\n- x:\n" ^ texpr_to_string ctx x];
    let _pats, body = raw_destruct_lambdas x in
    let _, body = raw_destruct_lets body in
    let f, _args = destruct_apps body in
    (* TODO: we also need to check that the input backward functions
       are not used elsewhere. We do this after the fact, through
       a sanity check (we check that after we performed the transformation,
       no use of the input backward functions remains), but it would be
       better to do it before) *)
    match f.e with
    | FVar fid ->
        FVarId.Set.mem fid input_conts_fvids
        (* Also check that the order is correct - TODO: the first check
           is subsumed by the second one *)
        && FVarId.Map.find_opt fid input_conts_fvids_to_index = Some i
    | _ -> false
  in
  let { inputs; outputs; _ } : loop_rel = rel in
  [%ldebug "loop_rel:\n" ^ loop_rel_to_string ctx rel];
  let input_conts = Collections.List.prefix loop.num_input_conts inputs in
  let output_conts = Collections.List.drop loop.num_output_values outputs in
  [%ldebug
    "- input_conts:"
    ^ Print.list_to_string ~sep:"\n"
        (Print.list_to_string (texpr_to_string ctx))
        input_conts
    ^ "\n- output_conts:"
    ^ Print.list_to_string ~sep:"\n"
        (Print.list_to_string (texpr_to_string ctx))
        output_conts];
  let inputs_are_calls_to_inputs =
    List.mapi (fun i -> List.map (is_call_to_input i)) input_conts
  in
  let outputs_are_calls_to_inputs =
    List.mapi (fun i -> List.map (is_call_to_input i)) output_conts
  in

  (* Check whether we can find a termination measure *)
  let has_termination_measure = loop_rel_has_termination_measure rel in

  [%ldebug
    "- has_termination_measure: "
    ^ string_of_bool has_termination_measure
    ^ "\n- all_inputs_are_id: "
    ^ string_of_bool all_inputs_are_id
    ^ "\n- inputs_are_calls_to_inputs: "
    ^ Print.list_to_string ~sep:"\n"
        (Print.list_to_string string_of_bool)
        inputs_are_calls_to_inputs
    ^ "\n- outputs_are_calls_to_inputs: "
    ^ Print.list_to_string ~sep:"\n"
        (Print.list_to_string string_of_bool)
        outputs_are_calls_to_inputs];

  (* *)
  let for_all = List.for_all (List.for_all (fun x -> x)) in
  has_termination_measure && all_inputs_are_id
  && for_all inputs_are_calls_to_inputs
  && for_all outputs_are_calls_to_inputs
  && List.length input_conts = List.length output_conts
  && not !Config.no_recursive_loops

let loop_satisfies_recursive_criteria (ctx : ctx) (def : fun_decl) (loop : loop)
    (rel : loop_rel) : bool =
  if !Config.no_recursive_loops then false
  else loop_satisfies_recursive_criteria_aux ctx def loop rel

(** Helper for [loops_to_recursive]: actually update the continue/breaks in a
    loop body to introduce the (fake) recursive call (we use the [RecLoopCall]
    special function, as we introduce the recursive function for the loop only
    in a later pass). *)
let loops_to_recursive_update_loop_body (ctx : ctx) (def : fun_decl)
    (input_conts_fids : FVarId.Set.t) (num_input_conts : int)
    (num_output_values : int) (output_conts_inputs : fvar list list)
    (break_outputs : fvar list) (continue_ty : ty) (break_ty : ty)
    (body : loop_body) : loop_body =
  let span = def.item_meta.span in
  let rec update (e : texpr) : texpr =
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ | Lambda _ | StructUpdate _ | Loop _ ->
        (* Shouldn't happen *)
        [%internal_error] span
    | EError _ -> e
    | App _ | Qualif _ ->
        (* This might be a break or a continue *)
        update_app_or_qualif e
    | Let (monadic, pat, bound, next) ->
        (* No need to update the bound expression *)
        let next = update next in
        mk_opened_let monadic pat bound next
    | Switch (scrut, switch) ->
        (* No need to update the scrutinee *)
        let switch =
          match switch with
          | If (e0, e1) -> If (update e0, update e1)
          | Match branches ->
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    let branch = update branch in
                    { pat; branch })
                  branches
              in
              Match branches
        in
        [%add_loc] mk_switch span scrut switch
    | Meta (m, e) -> mk_emeta m (update e)
  and update_app_or_qualif (e : texpr) : texpr =
    (* This might be a break or a continue *)
    match
      opt_destruct_loop_result_decompose_outputs ctx span ~intro_let:true
        ~opened_vars:true e
    with
    | None -> e
    | Some ({ variant_id; args = outputs; _ }, rebind) ->
        update_loop_break_continue variant_id outputs rebind
  and update_loop_break_continue (variant_id : variant_id)
      (outputs : texpr list) (rebind : texpr -> texpr) : texpr =
    if variant_id = loop_result_break_id then
      (* Update the backward functions.

           We simply remove the call to the input backward function. *)
      let update_back (e : texpr) =
        [%ldebug "- e:\n" ^ texpr_to_string ctx e];
        (* It can happen that we directly call the backward function,
             which is thus not a lambda. If this happens, we update it
             so that it matches the more general case.

             TODO: this will not work once we add support for
             function pointers and closures. *)
        let e =
          if is_fvar e then
            let arg_ty, _ = destruct_arrow span e.ty in
            let fv = mk_fresh_fvar ctx arg_ty in
            let arg = mk_texpr_from_fvar fv in
            let pat = mk_tpat_from_fvar None fv in
            let app = [%add_loc] mk_app span e arg in
            mk_opened_lambda span pat app
          else e
        in
        let lam_pats, body = raw_destruct_lambdas e in
        let lets, body = raw_destruct_lets body in
        let _, args = destruct_apps body in
        match args with
        | [ arg ] ->
            mk_opened_lambdas span lam_pats
              (mk_opened_heterogeneous_lets lets arg)
        | _ -> [%internal_error] span
      in
      let values, backl = Collections.List.split_at outputs num_output_values in
      let backl = List.map update_back backl in
      let outputs = mk_simpl_tuple_texpr span (values @ backl) in
      rebind (mk_break_texpr span continue_ty outputs)
    else if variant_id = loop_result_continue_id then (
      (* Remove the continuations *)
      let input_backl, input_values =
        Collections.List.split_at outputs num_input_conts
      in
      let inputs = mk_simpl_tuple_texpr span input_values in
      (* Replace the [continue] with a call to RecLoopCall *)
      let call = [%add_loc] mk_rec_loop_call_texpr span inputs break_ty in
      (* Bind the outputs *)
      let output_values, output_backl =
        Collections.List.split_at break_outputs num_output_values
      in

      [%ldebug
        let el_to_string el =
          String.concat "\n" (List.map (texpr_to_string ctx) el)
        in
        let fv_to_string el =
          String.concat "\n" (List.map (fvar_to_string ctx) el)
        in
        "- input_values:\n" ^ el_to_string input_values ^ "\n- input_backl:\n"
        ^ el_to_string input_backl ^ "\n- output_values:\n"
        ^ fv_to_string output_values ^ "\n- output_backl:\n"
        ^ fv_to_string output_backl];

      (* Introduce the backward functions *)
      [%sanity_check] span (List.length input_backl = List.length output_backl);
      let update_back (input : texpr) (back : fvar) (back_inputs : fvar list) :
          texpr =
        [%ldebug
          "- input: " ^ texpr_to_string ctx input ^ "\n- back: "
          ^ fvar_to_string ctx back ^ "\n- back_inputs: "
          ^ Print.list_to_string (fvar_to_string ctx) back_inputs];
        let lam_pats, body = raw_destruct_lambdas input in
        let let_pats, body = raw_destruct_lets body in
        let f, args = destruct_apps body in
        match (f.e, lam_pats, args) with
        | FVar _, [ pat ], [ arg ] ->
            let back_inputs_el = List.map mk_texpr_from_fvar back_inputs in
            let back = mk_texpr_from_fvar back in
            let e = mk_opened_heterogeneous_lets let_pats arg in
            let e =
              mk_opened_let false pat
                ([%add_loc] mk_apps span back back_inputs_el)
                e
            in
            let back_inputs = List.map (mk_tpat_from_fvar None) back_inputs in
            mk_opened_lambdas span back_inputs e
        | _ -> [%internal_error] span
      in

      [%ldebug
        let el_to_string el =
          String.concat "\n" (List.map (texpr_to_string ctx) el)
        in
        let fv_to_string el =
          String.concat "\n" (List.map (fvar_to_string ctx) el)
        in
        "- input_backl (length: "
        ^ string_of_int (List.length input_backl)
        ^ "):\n" ^ el_to_string input_backl ^ "\n- output_backl (length: "
        ^ string_of_int (List.length output_backl)
        ^ "):\n" ^ fv_to_string output_backl
        ^ "\n- output_conts_inputs (length: "
        ^ string_of_int (List.length output_conts_inputs)
        ^ "):\n"
        ^ Print.list_to_string
            (Print.list_to_string (fvar_to_string ctx))
            output_conts_inputs];

      let updated_backl =
        Collections.List.map3 update_back input_backl output_backl
          output_conts_inputs
      in
      let backl =
        List.map
          (fun (e : texpr) ->
            let id = ctx.fresh_fvar_id () in
            let fv : fvar = { id; ty = e.ty; basename = Some "back" } in
            fv)
          updated_backl
      in
      let outputs =
        mk_simpl_tuple_texpr span
          (List.map mk_texpr_from_fvar (output_values @ backl))
      in
      let output = rebind (mk_break_texpr span continue_ty outputs) in
      let e =
        mk_opened_lets false
          (List.combine (List.map (mk_tpat_from_fvar None) backl) updated_backl)
          output
      in
      let e =
        mk_opened_let true
          (mk_simpl_tuple_pat (List.map (mk_tpat_from_fvar None) break_outputs))
          call e
      in
      e)
    else (
      [%sanity_check] span (variant_id = loop_result_fail_id);
      let arg = mk_simpl_tuple_texpr span outputs in
      mk_loop_result_fail_texpr span continue_ty break_ty arg)
  in

  let inputs = Collections.List.drop num_input_conts body.inputs in
  let body = { inputs; loop_body = update body.loop_body } in
  (* Check that all the input continuations disappeared from the loop body *)
  let fids = texpr_get_fvars body.loop_body in
  [%sanity_check] span
    (FVarId.Set.is_empty (FVarId.Set.inter fids input_conts_fids));
  (* *)
  body

(** Attempts to transform loops to recursive functions which receive no backward
    functions as inputs and only *output* backward functions.

    We *can* do so if the output backward functions perform a terminal call to
    the input backward functions, and the input backward functions are the
    identiy.

    For instance:
    {[
      let list_nth_mut {T : Type} (ls : List T) (i : U32) : T × (T → List T) :=
        let (x, back) ← loop (fun back ls i =>
          match ls with
          | Cons x tl =>
            if i = 0 then break (x, fun y => back (Cons y tl))
            else
              let i1 ← i - 1
              let back' := fun l => back (Cons x l) (* Performs a terminal call to back *)
              continue back' tl i1
          | Nil => panic) (fun x -> x) ls i (* input back fun is the identity *)
       pure (x, back)

        ~>

      let list_nth_mut {T : Type} (ls : List T) (i : U32) : T × (T → List T) :=
        let (x, back) ← loop (fun ls i =>
          match ls with
          | Cons x tl =>
            if i = 0 then
              let back := fun y => Cons y tl (* Removed the call to the backward function *)
              break (x, back)
            else
              let i1 ← i - 1
              let x, back ← recLoopCall tl i1
              let back' := fun y =>
                let l := back y (* l is the original input of the continuation *)
                Cons x l
              break (x, back')
          | Nil => panic) ls i
       ok (x, back)
    ]}

    Note that we do not introduce recursive definitions for the loops *yet*: we
    first use the [RecLoopCall] function, and introduce the auxiliary
    definitions in [decompose_loops].

    Moreover, we do so *only* if we can find a structural termination measure
    for the loop (i.e., we dive deeper into a recursive data structure whenever
    we reach a continue). If this happens, it means it is natural to translate
    the loop to a recursive function. Otherwise it is not. *)
let loops_to_recursive_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr as super

    method! visit_Loop _ _ =
      (* A loop should always be bound by a let *)
      [%internal_error] span

    method! visit_Let env monadic pat bound next =
      match bound.e with
      | Loop loop -> (self#update_let_loop monadic pat bound loop next).e
      | _ -> super#visit_Let env monadic pat bound next

    method update_let_loop (monadic : bool) (pat : tpat) (bound : texpr)
        (loop : loop) (next : texpr) : texpr =
      [%ldebug "loop:\n" ^ loop_to_string ctx loop];
      (* Explore the loop body: we want to simplify the inner loops *)
      let loop = self#visit_loop () loop in

      (* Analyze the body to check whether we should turn the loop to a recursive function *)
      let rel = compute_loop_input_output_rel span ctx loop in
      let loop_to_rec = loop_satisfies_recursive_criteria ctx def loop rel in

      if loop_to_rec then (
        (* Transform the loop to introduce recursive calls and simplify
         the backward functions *)
        let break_ty = mk_simpl_tuple_ty loop.output_tys in
        (* TODO: names for the outputs *)
        let break_outputs =
          List.mapi
            (fun i ty ->
              let id = ctx.fresh_fvar_id () in
              let basename =
                if i < loop.num_output_values then None else Some "back"
              in
              ({ id; basename; ty } : fvar))
            loop.output_tys
        in
        let inputs = Collections.List.drop loop.num_input_conts loop.inputs in
        let continue_ty =
          mk_simpl_tuple_ty (List.map (fun (e : texpr) -> e.ty) inputs)
        in
        let output_conts_inputs =
          List.map
            (fun el ->
              match el with
              | e :: _ ->
                  (* The function may have been simplified: if it is the case,
                      we need to reintroduce lambdas *)
                  if is_fvar e then
                    (* TODO: this will not work once we add support for
                     function pointers and closures. *)
                    let tys, _ = destruct_arrows e.ty in
                    List.map (mk_fresh_fvar ctx) tys
                  else
                    (* Destruct the lambdas *)
                    let pats, _ = raw_destruct_lambdas e in
                    List.map (fun x -> fst ([%add_loc] as_pat_open span x)) pats
              | _ -> [%internal_error] span)
            (Collections.List.drop loop.num_output_values rel.outputs)
        in

        [%ldebug
          "output_conts_inputs:\n"
          ^ String.concat ",\n"
              (List.map
                 (Print.list_to_string (fvar_to_string ctx))
                 output_conts_inputs)];

        let input_conts_fvids =
          tpats_get_fvars
            (Collections.List.prefix loop.num_input_conts loop.loop_body.inputs)
        in

        let body =
          loops_to_recursive_update_loop_body ctx def input_conts_fvids
            loop.num_input_conts loop.num_output_values output_conts_inputs
            break_outputs continue_ty break_ty loop.loop_body
        in

        (* Check that the body doesn't contain uses of the input continuations anymore *)
        [%sanity_check] span
          (let fvars = texpr_get_fvars body.loop_body in
           FVarId.Set.disjoint input_conts_fvids fvars);

        let loop =
          {
            loop with
            output_tys = loop.output_tys;
            num_output_values = loop.num_output_values;
            inputs = Collections.List.drop loop.num_input_conts loop.inputs;
            num_input_conts = 0;
            loop_body = body;
            to_rec = true;
          }
        in

        let loop : texpr =
          {
            e = Loop loop;
            ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys);
          }
        in

        [%ldebug "loop:\n" ^ texpr_to_string ctx loop];

        (* Bind the loop *)
        mk_opened_let monadic pat loop next)
      else (* Do not apply any transformation *)
        mk_opened_let monadic pat { bound with e = Loop loop } next
  end

let loops_to_recursive = lift_expr_map_visitor loops_to_recursive_visitor

(** Retrieve the loop definitions from the function definition.

    Introduce auxiliary definitions for the loops. *)
let decompose_loops_aux (ctx : ctx) (def : fun_decl) (body : fun_body) :
    fun_decl * fun_decl list =
  let span = def.item_meta.span in

  let fvars, body = open_all_fun_body ctx span body in

  (* Count the number of loops and compute the relative position of each loop *)
  let loops = ref LoopId.Set.empty in
  let loop_pos = ref [ 0 ] in
  let loop_id_to_pos = ref LoopId.Map.empty in
  let expr_visitor =
    object
      inherit [_] iter_expr as super

      method! visit_Loop env loop =
        [%sanity_check] span (not (LoopId.Set.mem loop.loop_id !loops));
        loops := LoopId.Set.add loop.loop_id !loops;
        loop_id_to_pos :=
          LoopId.Map.add loop.loop_id (List.rev !loop_pos) !loop_id_to_pos;
        (* Push a position index *)
        loop_pos := 0 :: !loop_pos;
        super#visit_Loop env loop;
        (* Pop the last position index and increment the current position *)
        match !loop_pos with
        | _ :: current :: prefix -> loop_pos := (current + 1) :: prefix
        | _ -> [%internal_error] span
    end
  in
  expr_visitor#visit_texpr () body.body;
  let num_loops = LoopId.Set.cardinal !loops in

  (* Store the loops here *)
  let loops = ref LoopId.Map.empty in

  let compute_loop_fun_expr (loop : loop) (generics_filter : generics_filter)
      (constant_inputs : ty list) : texpr =
    let generic_args = generic_args_of_params def.signature.generics in
    let { types; const_generics; trait_refs } : generic_args = generic_args in
    let types =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.types types)
    in
    let const_generics =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.const_generics const_generics)
    in
    let trait_refs =
      List.filter_map
        (fun (b, x) -> if b then Some x else None)
        (List.combine generics_filter.trait_clauses trait_refs)
    in
    let generics : generic_args = { types; const_generics; trait_refs } in

    let output_ty = mk_result_ty (mk_simpl_tuple_ty loop.output_tys) in
    let input_tys = List.map (fun (e : texpr) -> e.ty) loop.inputs in
    let input_tys = constant_inputs @ input_tys in
    let func_ty = mk_arrows input_tys output_ty in
    let func =
      Qualif
        {
          id =
            FunOrOp
              (Fun (FromLlbc (FunId (FRegular def.def_id), Some loop.loop_id)));
          generics;
        }
    in
    { e = func; ty = func_ty }
  in

  (* Generate a function declaration from a loop body.

     We return:
     - the new declaration for the loop
     - the additional constant inputs (constants refered to by the loop but not
       bound by the loop body)
     - the expression representing a call to the loop function (without any arguments)
  *)
  let generate_loop_def (loop : loop) : fun_decl * fvar list * texpr =
    (* Should we introduce a recursive definition or use a fixed-point operator? *)
    let to_rec = !Config.loops_to_recursive_functions || loop.to_rec in

    (* *)
    let ({ output_tys; loop_body; _ } : loop) = loop in
    let output_ty = mk_simpl_tuple_ty output_tys in

    (* Compute the list of *constant* inputs: those are variables used
       by the loop but not bound by the loop itself (because they are
       not modified through the loop iterations).

       TODO: we shouldn't need to do this because we took care to preserve the
       constant loop inputs until now, in particular to preserve their order
       when introducing the auxiliary functions (because when introducing the
       auxiliary functions, we need to bind all inputs). We filter the loop constant
       inputs only after we introduced the auxiliary functions.
    *)
    let constant_inputs =
      let used_in_body = texpr_get_fvars loop_body.loop_body in
      let bound_in_body = loop_body_get_bound_fvars loop_body in
      let constant_inputs =
        List.filter_map
          (fun fid ->
            if FVarId.Set.mem fid bound_in_body then None
            else Some (FVarId.Map.find fid fvars))
          (FVarId.Set.elements used_in_body)
      in
      [%ldebug
        "- body:\n"
        ^ loop_body_to_string ctx loop_body
        ^ "\n\n- used_in_body: "
        ^ FVarId.Set.to_string None used_in_body
        ^ "\n- bound_in_body: "
        ^ FVarId.Set.to_string None bound_in_body
        ^ "\n- constant_inputs: "
        ^ Print.list_to_string (fvar_to_string ctx) constant_inputs];
      constant_inputs
    in
    let constant_input_tys =
      List.map (fun (e : fvar) -> e.ty) constant_inputs
    in

    (* Compute the generic params - note that the indices are not updated,
       meaning we do not need to update those in the body *)
    let generics, generics_filter =
      filter_generic_params_used_in_texpr def.signature.generics
        loop_body.loop_body
    in
    [%ldebug
      "- generic_params:\n"
      ^ generic_params_to_string ctx generics
      ^ "\n- generics_filter:\n"
      ^ show_generics_filter generics_filter];
    let loop_func =
      compute_loop_fun_expr loop generics_filter constant_input_tys
    in

    (* Update the loop body to:
       - either introduce recursive calls
       - or introduce a call to the loop fixed point operator
    *)
    let body =
      if to_rec then
        let body =
          update_rec_continue_breaks ctx def loop_func
            (List.map mk_texpr_from_fvar constant_inputs)
            loop_body.loop_body
        in
        body
      else
        (* We need to update the inputs to use the variables we bind at the
           level of the function body. *)
        let loop_body' = close_loop_body span loop.loop_body in
        let inputs =
          List.map
            (fun (pat : tpat) ->
              match pat.pat with
              | POpen (fvar, _) -> { e = FVar fvar.id; ty = pat.ty }
              | _ -> [%internal_error] span)
            loop_body.inputs
        in
        let loop = { loop with loop_body = loop_body'; inputs } in
        ({ e = Loop loop; ty = mk_result_ty output_ty } : texpr)
    in

    (* Update the inputs and close the function body *)
    let fun_body =
      let inputs =
        List.map (mk_tpat_from_fvar None) constant_inputs @ loop_body.inputs
      in
      let body : fun_body = { inputs; body } in
      [%ldebug
        "body before closing the free variables:\n"
        ^ fun_body_to_string ctx body];
      close_all_fun_body loop.span body
    in
    [%ldebug
      "body after closing the free variables:\n"
      ^ fun_body_to_string ctx fun_body];
    if !Config.sanity_checks then
      [%sanity_check] span (not (texpr_has_fvars fun_body.body));

    (* *)
    let fun_sig = def.signature in
    let fwd_info = fun_sig.fwd_info in
    let fwd_effect_info = fwd_info.effect_info in
    let ignore_output = fwd_info.ignore_output in

    (* Generate the loop definition *)
    let loop_fwd_effect_info = { fwd_effect_info with is_rec = to_rec } in

    let loop_fwd_sig_info : fun_sig_info =
      { effect_info = loop_fwd_effect_info; ignore_output }
    in

    (* Note that the loop body already binds the "constant" inputs: we don't
       need to add them anymore *)
    let input_tys = List.map (fun (v : tpat) -> v.ty) fun_body.inputs in
    let output = output_ty in

    let llbc_generics : T.generic_params =
      let { types; const_generics; trait_clauses; _ } : T.generic_params =
        fun_sig.llbc_generics
      in
      let types =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.types types)
      in
      let const_generics =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.const_generics const_generics)
      in
      let trait_clauses =
        List.filter_map
          (fun (b, x) -> if b then Some x else None)
          (List.combine generics_filter.trait_clauses trait_clauses)
      in
      {
        types;
        const_generics;
        trait_clauses;
        regions = [];
        regions_outlive = [];
        types_outlive = [];
        trait_type_constraints = [];
      }
    in

    let explicit_info = compute_explicit_info generics input_tys in
    let known_from_trait_refs = compute_known_info explicit_info generics in
    let loop_sig : fun_sig =
      {
        generics;
        explicit_info;
        known_from_trait_refs;
        llbc_generics;
        preds = { trait_type_constraints = [] };
        inputs = input_tys;
        output = mk_result_ty output;
        fwd_info = loop_fwd_sig_info;
        back_effect_info = fun_sig.back_effect_info;
      }
    in

    (* We retrieve the meta information from the parent function
     *but* replace its span with the span of the loop *)
    let item_meta = { def.item_meta with span = loop.span } in

    [%sanity_check] def.item_meta.span (def.builtin_info = None);

    let loop_pos =
      [%unwrap_with_span] span
        (LoopId.Map.find_opt loop.loop_id !loop_id_to_pos)
        "Internal error: please file an issue"
    in

    let loop_def : fun_decl =
      {
        def_id = def.def_id;
        item_meta;
        builtin_info = def.builtin_info;
        src = def.src;
        backend_attributes = def.backend_attributes;
        num_loops;
        loop_id = Some loop.loop_id;
        loop_pos;
        name = def.name;
        signature = loop_sig;
        is_global_decl_body = def.is_global_decl_body;
        body = Some fun_body;
      }
    in
    [%sanity_check] span
      (List.length loop_def.signature.inputs = List.length fun_body.inputs);

    (loop_def, constant_inputs, loop_func)
  in

  let decompose_visitor =
    object (self)
      inherit [_] map_expr

      (* In order to properly analyze the loops, and in particular filter
         their inputs/outputs, we make sure loops are always bound by a let-binding *)
      method! visit_Loop env loop =
        (* First, decompose the inner loops *)
        let loop = self#visit_loop env loop in

        (* Update the definition *)
        let loop_def, constant_inputs, func = generate_loop_def loop in

        (* Store the loop definition *)
        loops := LoopId.Map.add_strict loop.loop_id loop_def !loops;

        let inputs =
          List.map mk_texpr_from_fvar constant_inputs @ loop.inputs
        in
        let loop = [%add_loc] mk_apps span func inputs in
        loop.e
    end
  in

  let body_expr = decompose_visitor#visit_texpr () body.body in
  [%ldebug
    "Resulting body:\n" ^ fun_body_to_string ctx { body with body = body_expr }];
  let body = close_all_fun_body span { body with body = body_expr } in
  let def = { def with body = Some body; num_loops } in
  let loops = List.map snd (LoopId.Map.bindings !loops) in
  (def, loops)

let decompose_loops (ctx : ctx) (def : fun_decl) =
  match def.body with
  | None -> (def, [])
  | Some body -> decompose_loops_aux ctx def body

let loops_to_fixed_points_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expr

    method! visit_Loop _ loop =
      [%ldebug
        "loop before introducing the fixed point:\n" ^ loop_to_string ctx loop];

      let ({ output_tys; loop_body; _ } : loop) = loop in
      let output_ty = mk_simpl_tuple_ty output_tys in

      let input_ty =
        mk_simpl_tuple_ty
          (List.map (fun (pat : tpat) -> pat.ty) loop_body.inputs)
      in
      let body =
        update_non_rec_continue_breaks ctx def input_ty output_ty
          loop_body.loop_body
      in
      let input_pats = mk_simpl_tuple_pat loop_body.inputs in
      let body = mk_opened_lambda span input_pats body in
      let loop_op : texpr =
        let qualif =
          {
            id = LoopOp;
            generics = mk_generic_args_from_types [ input_ty; output_ty ];
          }
        in
        {
          e = Qualif qualif;
          ty = mk_arrows [ body.ty; input_pats.ty ] (mk_result_ty output_ty);
        }
      in
      let loop =
        [%add_loc] mk_apps span loop_op
          [ body; mk_simpl_tuple_texpr span loop.inputs ]
      in

      [%ldebug
        "loop after introducing the fixed point:\n" ^ texpr_to_string ctx loop];

      loop.e
  end

(** Convert the [Loop] nodes to calls to the loop fixed-point operator *)
let loops_to_fixed_points = lift_expr_map_visitor loops_to_fixed_points_visitor

let filter_loop_useless_inputs_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expr

    method! visit_Loop _ loop =
      [%ldebug
        "loop before filtering the useless inputs:\n" ^ loop_to_string ctx loop];

      let rel = compute_loop_input_output_rel span ctx loop in
      let _, keep_inputs =
        compute_loop_useless_inputs span ctx ~filter_constant_inputs:true loop
          rel
      in
      [%ldebug
        "keep_inputs: " ^ Print.list_to_string string_of_bool keep_inputs];

      let {
        loop_id;
        span;
        output_tys;
        num_output_values;
        inputs;
        num_input_conts;
        loop_body;
        to_rec;
      } =
        loop
      in

      let input_vars =
        List.map
          (fun (p : tpat) ->
            match p.pat with
            | POpen (v, _) -> Some v
            | PIgnored -> None
            | _ -> [%internal_error] span)
          loop_body.inputs
      in

      (* Substitute the unchanged variables with their (constant) values in the loop body *)
      let loop_body =
        [%sanity_check] span (List.length input_vars = List.length loop.inputs);
        let bindings = List.combine input_vars loop.inputs in
        let bindings =
          List.filter_map
            (fun ((keep, (fv, v)) : _ * (fvar option * _)) ->
              if keep then None
              else
                match fv with
                | None -> None
                | Some fv -> Some (fv.id, v))
            (List.combine keep_inputs bindings)
        in
        let subst = FVarId.Map.of_list bindings in

        let visitor =
          object
            inherit [_] map_expr

            method! visit_FVar _ fid =
              match FVarId.Map.find_opt fid subst with
              | None -> FVar fid
              | Some e -> e.e
          end
        in
        visitor#visit_loop_body () loop_body
      in

      (* Update the continue/breaks *)
      [%sanity_check] span (List.length keep_inputs = List.length inputs);
      let inputs =
        List.filter_map
          (fun (keep, input) -> if keep then Some input else None)
          (List.combine keep_inputs inputs)
      in
      let num_input_conts =
        List.length
          (List.filter
             (fun x -> x)
             (Collections.List.prefix num_input_conts keep_inputs))
      in
      let continue_ty =
        List.map (fun (input : texpr) -> input.ty) inputs |> mk_simpl_tuple_ty
      in
      let break_ty = mk_simpl_tuple_ty output_tys in
      let keep_outputs = List.map (fun _ -> true) output_tys in

      let loop_body =
        filter_loop_useless_inputs_outputs_update_continue_break span ctx
          ~opened_vars:true keep_outputs keep_inputs continue_ty break_ty
          loop_body
      in
      let loop : loop =
        {
          loop_id;
          span;
          output_tys;
          num_output_values;
          inputs;
          num_input_conts;
          loop_body;
          to_rec;
        }
      in

      [%ldebug
        "loop after filtering the useless inputs:\n" ^ loop_to_string ctx loop];

      Loop loop
  end

let filter_loop_useless_inputs =
  lift_expr_map_visitor filter_loop_useless_inputs_visitor
