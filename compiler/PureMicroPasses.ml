(** The following module defines micro-passes which operate on the pure AST *)

open Pure
open PureUtils
open TranslateCore
open Errors

(** The local logger *)
let log = Logging.pure_micro_passes_log

let fun_decl_to_string (ctx : trans_ctx) (def : Pure.fun_decl) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_decl_to_string fmt def

let fun_sig_to_string (ctx : trans_ctx) (sg : Pure.fun_sig) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx in
  PrintPure.fun_sig_to_string fmt sg

let var_to_string (ctx : trans_ctx) (v : var) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx in
  PrintPure.var_to_string fmt v

let texpression_to_string (ctx : trans_ctx) (x : texpression) : string =
  let fmt = trans_ctx_to_pure_fmt_env ctx in
  PrintPure.texpression_to_string fmt false "" "  " x

(** Small utility.

    We sometimes have to insert new fresh variables in a function body, in which
    case we need to make their indices greater than the indices of all the variables
    in the body.
    TODO: things would be simpler if we used a better representation of the
    variables indices...
 *)
let get_body_min_var_counter (body : fun_body) : VarId.generator =
  (* Find the max id in the input variables - some of them may have been
   * filtered from the body *)
  let min_input_id =
    List.fold_left
      (fun id (var : var) -> VarId.max id var.id)
      VarId.zero body.inputs
  in
  let obj =
    object
      inherit [_] reduce_expression
      method zero _ = min_input_id
      method plus id0 id1 _ = VarId.max (id0 ()) (id1 ())
      (* Get the maximum *)

      (** For the patterns *)
      method! visit_var _ v _ = v.id

      (** For the rvalues *)
      method! visit_Var _ vid _ = vid
    end
  in
  (* Find the max counter in the body *)
  let id = obj#visit_expression () body.body.e () in
  VarId.generator_from_incr_id id

(** "Pretty-Name context": see {!compute_pretty_names} *)
type pn_ctx = {
  pure_vars : string VarId.Map.t;
      (** Information about the pure variables used in the synthesized program *)
  llbc_vars : string E.VarId.Map.t;
      (** Information about the LLBC variables used in the original program *)
}

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "span"-place information in the AST to generate naming
    constraints, and then uses those to compute the names.
    
    The way it works is as follows:
    - we only modify the names of the unnamed variables
    - whenever we see an rvalue/pattern which is exactly an unnamed variable,
      and this value is linked to some span-place information which contains
      a name and an empty path, we consider we should use this name
    - we try to propagate naming constraints on the pure variables use in the
      synthesized programs, and also on the LLBC variables from the original
      program (information about the LLBC variables is stored in the span-places)
      
      
    Something important is that, for every variable we find, the name of this
    variable can be influenced by the information we find *below* in the AST.

    For instance, the following situations happen:
    
    - let's say we evaluate:
      {[
        match (ls : List<T>) {
          List::Cons(x, hd) => {
            ...
          }
        }
      ]}
      
      Actually, in MIR, we get:
      {[
        tmp := discriminant(ls);
        switch tmp {
          0 => {
            x := (ls as Cons).0; // (i)
            hd := (ls as Cons).1; // (ii)
            ...
          }
        }
      ]}
      If [ls] maps to a symbolic value [s0] upon evaluating the match in symbolic
      mode, we expand this value upon evaluating [tmp = discriminant(ls)].
      However, at this point, we don't know which should be the names of
      the symbolic values we introduce for the fields of [Cons]!

      Let's imagine we have (for the [Cons] branch): [s0 ~~> Cons s1 s2].
      The assigments at (i) and (ii) lead to the following binding in the
      evaluation context:
      {[
        x -> s1
        hd -> s2
      ]}
      
      When generating the symbolic AST, we save as span-information that we
      assign [s1] to the place [x] and [s2] to the place [hd]. This way,
      we learn we can use the names [x] and [hd] for the variables which are
      introduced by the match:
      {[
        match ls with
        | Cons x hd -> ...
        | ...
      ]}
   - Assignments:
     [let x [@mplace=lp] = v [@mplace = rp] in ...]
     
     We propagate naming information across the assignments. This is important
     because many reassignments using temporary, anonymous variables are
     introduced during desugaring.
   
   - Given back values (introduced by backward functions):
     Let's say we have the following Rust code:
     {[
       let py = id(&mut x);
       *py = 2;
       assert!(x = 2);
     ]}
     
     After desugaring, we get the following MIR:
     {[
       ^0 = &mut x; // anonymous variable
       py = id(move ^0);
       *py += 2;
       assert!(x = 2);
     ]}
     
     We want this to be translated as:
     {[
       let py = id_fwd x in
       let py1 = py + 2 in
       let x1 = id_back x py1 in // <-- x1 is "given back": doesn't appear in the original MIR
       assert(x1 = 2);
     ]}

     We want to notice that the value given back by [id_back] is given back for "x",
     so we should use "x" as the basename (hence the resulting name "x1"). However,
     this is non-trivial, because after desugaring the input argument given to [id]
     is not [&mut x] but [move ^0] (i.e., it comes from a temporary, anonymous
     variable). For this reason, we use the span-place [&mut x] as the span-place
     for the given back value (this is done during the synthesis), and propagate
     naming information *also* on the LLBC variables (which are referenced by the
     span-places).

     This way, because of [^0 = &mut x], we can propagate the name "x" to the place
     [^0], then to the given back variable across the function call.
   
 *)
let compute_pretty_names (def : fun_decl) : fun_decl =
  (* Small helpers *)
  (* 
   * When we do branchings, we need to merge (the constraints saved in) the
   * contexts returned by the different branches.
   *
   * Note that by doing so, some mappings from var id to name
   * in one context may be overriden by the ones in the other context.
   *
   * This should be ok because:
   * - generally, the overriden variables should have been introduced *inside*
   *   the branches, in which case we don't care
   * - or they were introduced before, in which case the naming should generally
   *   be consistent? In the worse case, it isn't, but it leads only to less
   *   readable code, not to unsoundness. This case should be pretty rare,
   *   also.
   *)
  let merge_ctxs (ctx0 : pn_ctx) (ctx1 : pn_ctx) : pn_ctx =
    let pure_vars =
      VarId.Map.fold
        (fun id name ctx -> VarId.Map.add id name ctx)
        ctx0.pure_vars ctx1.pure_vars
    in
    let llbc_vars =
      E.VarId.Map.fold
        (fun id name ctx -> E.VarId.Map.add id name ctx)
        ctx0.llbc_vars ctx1.llbc_vars
    in
    { pure_vars; llbc_vars }
  in
  let empty_ctx =
    { pure_vars = VarId.Map.empty; llbc_vars = E.VarId.Map.empty }
  in
  let merge_ctxs_ls (ctxs : pn_ctx list) : pn_ctx =
    List.fold_left (fun ctx0 ctx1 -> merge_ctxs ctx0 ctx1) empty_ctx ctxs
  in

  (*
   * The way we do is as follows:
   * - we explore the expressions
   * - we register the variables introduced by the let-bindings
   * - we use the naming information we find (through the variables and the
   *   span-places) to update our context (i.e., maps from variable ids to
   *   names)
   * - we use this information to update the names of the variables used in the
   *   expressions
   *)

  (* Register a variable for constraints propagation - used when an variable is
   * introduced (left-hand side of a left binding) *)
  let register_var (ctx : pn_ctx) (v : var) : pn_ctx =
    sanity_check __FILE__ __LINE__
      (not (VarId.Map.mem v.id ctx.pure_vars))
      def.item_meta.span;
    match v.basename with
    | None -> ctx
    | Some name ->
        let pure_vars = VarId.Map.add v.id name ctx.pure_vars in
        { ctx with pure_vars }
  in
  (* Update a variable - used to update an expression after we computed constraints *)
  let update_var (ctx : pn_ctx) (v : var) (mp : mplace option) : var =
    match v.basename with
    | Some _ -> v
    | None -> (
        match VarId.Map.find_opt v.id ctx.pure_vars with
        | Some basename -> { v with basename = Some basename }
        | None ->
            if Option.is_some mp then
              match
                E.VarId.Map.find_opt (Option.get mp).var_id ctx.llbc_vars
              with
              | None -> v
              | Some basename -> { v with basename = Some basename }
            else v)
  in
  (* Update an pattern - used to update an expression after we computed constraints *)
  let update_typed_pattern ctx (lv : typed_pattern) : typed_pattern =
    let obj =
      object
        inherit [_] map_typed_pattern
        method! visit_PatVar _ v mp = PatVar (update_var ctx v mp, mp)
      end
    in
    obj#visit_typed_pattern () lv
  in

  (* Register an mplace the first time we find one *)
  let register_mplace (mp : mplace) (ctx : pn_ctx) : pn_ctx =
    match (E.VarId.Map.find_opt mp.var_id ctx.llbc_vars, mp.name) with
    | None, Some name ->
        let llbc_vars = E.VarId.Map.add mp.var_id name ctx.llbc_vars in
        { ctx with llbc_vars }
    | _ -> ctx
  in

  (* Register the fact that [name] can be used for the pure variable identified
   * by [var_id] (will add this name in the map if the variable is anonymous) *)
  let add_pure_var_constraint (var_id : VarId.id) (name : string) (ctx : pn_ctx)
      : pn_ctx =
    let pure_vars =
      if VarId.Map.mem var_id ctx.pure_vars then ctx.pure_vars
      else VarId.Map.add var_id name ctx.pure_vars
    in
    { ctx with pure_vars }
  in
  (* Similar to [add_pure_var_constraint], but for LLBC variables *)
  let add_llbc_var_constraint (var_id : E.VarId.id) (name : string)
      (ctx : pn_ctx) : pn_ctx =
    let llbc_vars =
      if E.VarId.Map.mem var_id ctx.llbc_vars then ctx.llbc_vars
      else E.VarId.Map.add var_id name ctx.llbc_vars
    in
    { ctx with llbc_vars }
  in
  (* Add a constraint: given a variable id and an associated span-place, try to
   * extract naming information from the span-place and save it *)
  let add_constraint (mp : mplace) (var_id : VarId.id) (ctx : pn_ctx) : pn_ctx =
    (* Register the place *)
    let ctx = register_mplace mp ctx in
    (* Update the variable name *)
    match (mp.name, mp.projection) with
    | Some name, [] ->
        (* Check if the variable already has a name - if not: insert the new name *)
        let ctx = add_pure_var_constraint var_id name ctx in
        let ctx = add_llbc_var_constraint mp.var_id name ctx in
        ctx
    | _ -> ctx
  in
  (* Specific case of constraint on rvalues *)
  let add_right_constraint (mp : mplace) (rv : texpression) (ctx : pn_ctx) :
      pn_ctx =
    (* Register the place *)
    let ctx = register_mplace mp ctx in
    (* Add the constraint *)
    match (unspan rv).e with
    | Var vid -> add_constraint mp vid ctx
    | _ -> ctx
  in
  let add_pure_var_value_constraint (var_id : VarId.id) (rv : texpression)
      (ctx : pn_ctx) : pn_ctx =
    (* Add the constraint *)
    match (unspan rv).e with
    | Var vid -> (
        (* Try to find a name for the vid *)
        match VarId.Map.find_opt vid ctx.pure_vars with
        | None -> ctx
        | Some name -> add_pure_var_constraint var_id name ctx)
    | _ -> ctx
  in
  (* Specific case of constraint on left values *)
  let add_left_constraint (lv : typed_pattern) (ctx : pn_ctx) : pn_ctx =
    let obj =
      object (self)
        inherit [_] reduce_typed_pattern
        method zero _ = empty_ctx
        method plus ctx0 ctx1 _ = merge_ctxs (ctx0 ()) (ctx1 ())

        method! visit_PatVar _ v mp () =
          (* Register the variable *)
          let ctx = register_var (self#zero ()) v in
          (* Register the mplace information if there is such information *)
          match mp with
          | Some mp -> add_constraint mp v.id ctx
          | None -> ctx
      end
    in
    let ctx1 = obj#visit_typed_pattern () lv () in
    merge_ctxs ctx ctx1
  in
  (* If we have [x = y] where x and y are variables, add a constraint linking
     the names of x and y *)
  let add_eq_var_constraint (lv : typed_pattern) (re : texpression)
      (ctx : pn_ctx) : pn_ctx =
    match (lv.value, re.e) with
    | PatVar (lv, _), Var rv when Option.is_some lv.basename ->
        add_pure_var_constraint rv (Option.get lv.basename) ctx
    | _ -> ctx
  in

  (* This is used to propagate constraint information about places in case of
   * variable reassignments: we try to propagate the information from the
   * rvalue to the left *)
  let add_left_right_constraint (lv : typed_pattern) (re : texpression)
      (ctx : pn_ctx) : pn_ctx =
    (* We propagate constraints across variable reassignments: [^0 = x],
     * if the destination doesn't have naming information *)
    match lv.value with
    | PatVar (({ id = _; basename = None; ty = _ } as lvar), lmp) ->
        if
          (* Check that there is not already a name for the variable *)
          VarId.Map.mem lvar.id ctx.pure_vars
        then ctx
        else
          (* We ignore the left span-place information: it should have been taken
           * care of by [add_left_constraint]. We try to use the right span-place
           * information *)
          let add (name : string) (ctx : pn_ctx) : pn_ctx =
            (* Add the constraint for the pure variable *)
            let ctx = add_pure_var_constraint lvar.id name ctx in
            (* Add the constraint for the LLBC variable *)
            match lmp with
            | None -> ctx
            | Some lmp -> add_llbc_var_constraint lmp.var_id name ctx
          in
          (* We try to use the right-place information *)
          let rmp, re = opt_unspan_mplace re in
          let ctx =
            match rmp with
            | Some { var_id; name; projection = [] } -> (
                if Option.is_some name then add (Option.get name) ctx
                else
                  match E.VarId.Map.find_opt var_id ctx.llbc_vars with
                  | None -> ctx
                  | Some name -> add name ctx)
            | _ -> ctx
          in
          (* We try to use the rvalue information, if it is a variable *)
          let ctx =
            match (unspan re).e with
            | Var rvar_id -> (
                match VarId.Map.find_opt rvar_id ctx.pure_vars with
                | None -> ctx
                | Some name -> add name ctx)
            | _ -> ctx
          in
          ctx
    | _ -> ctx
  in

  (* *)
  let rec update_texpression (e : texpression) (ctx : pn_ctx) :
      pn_ctx * texpression =
    let ty = e.ty in
    let ctx, e =
      match e.e with
      | Var _ | CVar _ | Const _ -> (* Nothing to do *) (ctx, e.e)
      | App (app, arg) ->
          let ctx, app = update_texpression app ctx in
          let ctx, arg = update_texpression arg ctx in
          let e = App (app, arg) in
          (ctx, e)
      | Qualif _ -> (* nothing to do *) (ctx, e.e)
      | Let (monadic, lb, re, e) -> update_let monadic lb re e ctx
      | Switch (scrut, body) -> update_switch_body scrut body ctx
      | Loop loop -> update_loop loop ctx
      | StructUpdate supd -> update_struct_update supd ctx
      | Lambda (lb, e) -> update_lambda lb e ctx
      | Meta (span, e) -> update_espan span e ctx
      | EError (span, msg) -> (ctx, EError (span, msg))
    in
    (ctx, { e; ty })
  (* *)
  and update_lambda (x : typed_pattern) (e : texpression) (ctx : pn_ctx) :
      pn_ctx * expression =
    (* We first add the left-constraint *)
    let ctx = add_left_constraint x ctx in
    (* Update the expression, and add additional constraints *)
    let ctx, e = update_texpression e ctx in
    (* Update the abstracted value *)
    let x = update_typed_pattern ctx x in
    (* Put together *)
    (ctx, Lambda (x, e))
  (* *)
  and update_let (monadic : bool) (lv : typed_pattern) (re : texpression)
      (e : texpression) (ctx : pn_ctx) : pn_ctx * expression =
    (* We first add the left-constraint *)
    let ctx = add_left_constraint lv ctx in
    (* Then we try to propagate the right-constraints to the left, in case
     * the left constraints didn't give naming information *)
    let ctx = add_left_right_constraint lv re ctx in
    let ctx, re = update_texpression re ctx in
    let ctx, e = update_texpression e ctx in
    let lv = update_typed_pattern ctx lv in
    let ctx = add_eq_var_constraint lv re ctx in
    (ctx, Let (monadic, lv, re, e))
  (* *)
  and update_switch_body (scrut : texpression) (body : switch_body)
      (ctx : pn_ctx) : pn_ctx * expression =
    let ctx, scrut = update_texpression scrut ctx in

    let ctx, body =
      match body with
      | If (e_true, e_false) ->
          let ctx1, e_true = update_texpression e_true ctx in
          let ctx2, e_false = update_texpression e_false ctx in
          let ctx = merge_ctxs ctx1 ctx2 in
          (ctx, If (e_true, e_false))
      | Match branches ->
          let ctx_branches_ls =
            List.map
              (fun br ->
                let ctx = add_left_constraint br.pat ctx in
                let ctx, branch = update_texpression br.branch ctx in
                let pat = update_typed_pattern ctx br.pat in
                (ctx, { pat; branch }))
              branches
          in
          let ctxs, branches = List.split ctx_branches_ls in
          let ctx = merge_ctxs_ls ctxs in
          (ctx, Match branches)
    in
    (ctx, Switch (scrut, body))
  (* *)
  and update_loop (loop : loop) (ctx : pn_ctx) : pn_ctx * expression =
    let {
      fun_end;
      loop_id;
      span;
      fuel0;
      fuel;
      input_state;
      inputs;
      inputs_lvs;
      output_ty;
      loop_body;
    } =
      loop
    in
    let ctx, fun_end = update_texpression fun_end ctx in
    let ctx, loop_body = update_texpression loop_body ctx in
    let inputs = List.map (fun v -> update_var ctx v None) inputs in
    let inputs_lvs = List.map (update_typed_pattern ctx) inputs_lvs in
    let loop =
      {
        fun_end;
        loop_id;
        span;
        fuel0;
        fuel;
        input_state;
        inputs;
        inputs_lvs;
        output_ty;
        loop_body;
      }
    in
    (ctx, Loop loop)
  and update_struct_update (supd : struct_update) (ctx : pn_ctx) :
      pn_ctx * expression =
    let { struct_id; init; updates } = supd in
    let ctx, updates =
      List.fold_left_map
        (fun ctx (fid, fe) ->
          let ctx, fe = update_texpression fe ctx in
          (ctx, (fid, fe)))
        ctx updates
    in
    let supd = { struct_id; init; updates } in
    (ctx, StructUpdate supd)
  (* *)
  and update_espan (span : espan) (e : texpression) (ctx : pn_ctx) :
      pn_ctx * expression =
    let ctx =
      match span with
      | Assignment (mp, rvalue, rmp) ->
          let ctx = add_right_constraint mp rvalue ctx in
          let ctx =
            match (mp.projection, rmp) with
            | [], Some { var_id; name; projection = [] } -> (
                let name =
                  match name with
                  | Some name -> Some name
                  | None -> E.VarId.Map.find_opt var_id ctx.llbc_vars
                in
                match name with
                | None -> ctx
                | Some name -> add_llbc_var_constraint mp.var_id name ctx)
            | _ -> ctx
          in
          ctx
      | SymbolicAssignments infos ->
          List.fold_left
            (fun ctx (var_id, rvalue) ->
              add_pure_var_value_constraint var_id rvalue ctx)
            ctx infos
      | SymbolicPlaces infos ->
          List.fold_left
            (fun ctx (var_id, name) -> add_pure_var_constraint var_id name ctx)
            ctx infos
      | MPlace mp -> add_right_constraint mp e ctx
      | Tag _ -> ctx
    in
    let ctx, e = update_texpression e ctx in
    let e = mk_espan span e in
    (ctx, e.e)
  in

  let body =
    match def.body with
    | None -> None
    | Some body ->
        let input_names =
          List.filter_map
            (fun (v : var) ->
              match v.basename with
              | None -> None
              | Some name -> Some (v.id, name))
            body.inputs
        in
        let ctx =
          {
            pure_vars = VarId.Map.of_list input_names;
            llbc_vars = E.VarId.Map.empty;
          }
        in
        let _, body_exp = update_texpression body.body ctx in
        Some { body with body = body_exp }
  in
  { def with body }

(** Remove the span-information *)
let remove_span (def : fun_decl) : fun_decl =
  match def.body with
  | None -> def
  | Some body ->
      let body = { body with body = PureUtils.remove_span body.body } in
      { def with body = Some body }

(** Introduce the special structure create/update expressions.

    Upon generating the pure code, we introduce structure values by using
    the structure constructors:
    {[
      Cons x0 ... xn
    ]}

    This micro-pass turns those into expressions which use structure syntax:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 y ~~> { x with f2 = y }
    ]}

    Note however that we do not apply this transformation if the
    structure is to be extracted as a tuple.
 *)
let intro_struct_updates (ctx : trans_ctx) (def : fun_decl) : fun_decl =
  let obj =
    object (self)
      inherit [_] map_expression as super

      method! visit_texpression env (e : texpression) =
        match e.e with
        | App _ -> (
            let app, args = destruct_apps e in
            let ignore () =
              mk_apps def.item_meta.span
                (self#visit_texpression env app)
                (List.map (self#visit_texpression env) args)
            in
            match app.e with
            | Qualif
                {
                  id = AdtCons { adt_id = TAdtId adt_id; variant_id = None };
                  generics = _;
                } ->
                (* Lookup the def *)
                let decl = TypeDeclId.Map.find adt_id ctx.type_ctx.type_decls in
                (* Check if the def will be extracted as a tuple *)
                if
                  TypesUtils.type_decl_from_decl_id_is_tuple_struct
                    ctx.type_ctx.type_infos adt_id
                then ignore ()
                else
                  (* Check that there are as many arguments as there are fields - note
                     that the def should have a body (otherwise we couldn't use the
                     constructor) *)
                  let fields = TypesUtils.type_decl_get_fields decl None in
                  if List.length fields = List.length args then
                    (* Check if the definition is recursive *)
                    let is_rec =
                      match
                        TypeDeclId.Map.find adt_id
                          ctx.type_ctx.type_decls_groups
                      with
                      | NonRecGroup _ -> false
                      | RecGroup _ -> true
                    in
                    (* Convert, if possible - note that for now for Lean and Coq
                       we don't support the structure syntax on recursive structures *)
                    if
                      (Config.backend () <> Lean && Config.backend () <> Coq)
                      || not is_rec
                    then
                      let struct_id = TAdtId adt_id in
                      let init = None in
                      let updates =
                        FieldId.mapi
                          (fun fid fe -> (fid, self#visit_texpression env fe))
                          args
                      in
                      let ne = { struct_id; init; updates } in
                      let nty = e.ty in
                      { e = StructUpdate ne; ty = nty }
                    else ignore ()
                  else ignore ()
            | _ -> ignore ())
        | _ -> super#visit_texpression env e
    end
  in
  match def.body with
  | None -> def
  | Some body ->
      let body = { body with body = obj#visit_texpression () body.body } in
      { def with body = Some body }

(** Simplify the let-bindings by performing the following rewritings:

    Move inner let-bindings outside. This is especially useful to simplify
    the backward expressions, when we merge the forward/backward functions.
    Note that the rule is also applied with monadic let-bindings.
    {[
      let x :=
        let y := ... in
        e

        ~~>

      let y := ... in
      let x := e
    ]}

    Simplify panics and returns:
    {[
      let x ← fail
      ...
        ~~>
      fail

      let x ← return y
      ...
        ~~>
      let x := y
      ...
    ]}

    Simplify tuples:
    {[
      let (y0, y1) := (x0, x1) in
      ...
        ~~>
      let y0 = x0 in
      let y1 = x1 in
      ...
    ]}

    Simplify arrows:
    {[
      let f := fun x => g x in
      ...
        ~~>
      let f := g in
      ...
    ]}
 *)
let simplify_let_bindings (_ctx : trans_ctx) (def : fun_decl) : fun_decl =
  let obj =
    object (self)
      inherit [_] map_expression as super

      method! visit_Let env monadic lv rv next =
        match rv.e with
        | Let (rmonadic, rlv, rrv, rnext) ->
            (* Case 1: move the inner let outside then re-visit *)
            let rnext1 = Let (monadic, lv, rnext, next) in
            let rnext1 = { ty = next.ty; e = rnext1 } in
            self#visit_Let env rmonadic rlv rrv rnext1
        | App
            ( {
                e =
                  Qualif
                    {
                      id =
                        AdtCons
                          {
                            adt_id = TAssumed TResult;
                            variant_id = Some variant_id;
                          };
                      generics = _;
                    };
                ty = _;
              },
              x ) ->
            (* return/fail case *)
            if variant_id = result_ok_id then
              (* Return case - note that the simplification we just perform
                 might have unlocked the tuple simplification below *)
              self#visit_Let env false lv x next
            else if variant_id = result_fail_id then
              (* Fail case *)
              self#visit_expression env rv.e
            else craise __FILE__ __LINE__ def.item_meta.span "Unexpected"
        | App _ ->
            (* This might be the tuple case *)
            if not monadic then
              match
                (opt_dest_struct_pattern lv, opt_dest_tuple_texpression rv)
              with
              | Some pats, Some vals ->
                  (* Tuple case *)
                  let pat_vals = List.combine pats vals in
                  let e =
                    List.fold_right
                      (fun (pat, v) next -> mk_let false pat v next)
                      pat_vals next
                  in
                  super#visit_expression env e.e
              | _ -> super#visit_Let env monadic lv rv next
            else super#visit_Let env monadic lv rv next
        | Lambda _ ->
            if not monadic then
              (* Arrow case *)
              let pats, e = destruct_lambdas rv in
              let g, args = destruct_apps e in
              if List.length pats = List.length args then
                (* Check if the arguments are exactly the lambdas *)
                let check_pat_arg ((pat, arg) : typed_pattern * texpression) =
                  match (pat.value, arg.e) with
                  | PatVar (v, _), Var vid -> v.id = vid
                  | _ -> false
                in
                if List.for_all check_pat_arg (List.combine pats args) then
                  self#visit_Let env monadic lv g next
                else super#visit_Let env monadic lv rv next
              else super#visit_Let env monadic lv rv next
            else super#visit_Let env monadic lv rv next
        | _ -> super#visit_Let env monadic lv rv next
    end
  in
  match def.body with
  | None -> def
  | Some body ->
      let body = { body with body = obj#visit_texpression () body.body } in
      { def with body = Some body }

(** Inline the useless variable (re-)assignments:

    A lot of intermediate variable assignments are introduced through the
    compilation to MIR and by the translation itself (and the variable used
    on the left is often unnamed).

    Note that many of them are just variable "reassignments": [let x = y in ...].
    Some others come from ??
    
    TODO: how do we call that when we introduce intermediate variable assignments
    for the arguments of a function call?

    [inline_named]: if [true], inline all the assignments of the form
    [let VAR = VAR in ...], otherwise inline only the ones where the variable
    on the left is anonymous.
    
    [inline_pure]: if [true], inline all the pure assignments where the variable
    on the left is anonymous, but the assignments where the r-expression is
    a non-primitive function call (i.e.: inline the binops, ADT constructions,
    etc.).

    TODO: we have a smallish issue which is that rvalues should be merged with
    expressions... For now, this forces us to substitute whenever we can, but
    leave the let-bindings where they are, and eliminated them in a subsequent
    pass (if they are useless).
 *)
let inline_useless_var_reassignments (ctx : trans_ctx) ~(inline_named : bool)
    ~(inline_const : bool) ~(inline_pure : bool) (def : fun_decl) : fun_decl =
  let obj =
    object (self)
      inherit [_] map_expression as super

      (** Visit the let-bindings to filter the useless ones (and update
          the substitution map while doing so *)
      method! visit_Let (env : texpression VarId.Map.t) monadic lv re e =
        (* In order to filter, we need to check first that:
           - the let-binding is not monadic
           - the left-value is a variable

           We also inline if the binding decomposes a structure that is to be
           extracted as a tuple, and the right value is a variable.
        *)
        match (monadic, lv.value) with
        | false, PatVar (lv_var, _) ->
            (* We can filter if: *)
            (* 1. the left variable is unnamed or [inline_named] is true *)
            let filter_left =
              match (inline_named, lv_var.basename) with
              | true, _ | _, None -> true
              | _ -> false
            in
            (* And either:
               2.1 the right-expression is a variable, a global or a const generic var *)
            let var_or_global = is_var re || is_cvar re || is_global re in
            (* Or:
               2.2 the right-expression is a constant-value and we inline constant values,
                   *or* it is a qualif with no arguments (we consider this as a const) *)
            let const_re =
              inline_const
              &&
              let is_const_adt =
                let app, args = destruct_apps re in
                if args = [] then
                  match app.e with
                  | Qualif _ -> true
                  | StructUpdate upd -> upd.updates = []
                  | _ -> false
                else false
              in
              is_const re || is_const_adt
            in
            (* Or:
               2.3 the right-expression is an ADT value, a projection or a
                   primitive function call *and* the flag [inline_pure] is set *)
            let pure_re =
              inline_pure
              &&
              let app, _ = destruct_apps re in
              match app.e with
              | Qualif qualif -> (
                  match qualif.id with
                  | AdtCons _ -> true (* ADT constructor *)
                  | Proj _ -> true (* Projector *)
                  | FunOrOp (Unop _ | Binop _) ->
                      true (* primitive function call *)
                  | FunOrOp (Fun _) -> false (* non-primitive function call *)
                  | _ -> false)
              | StructUpdate _ -> true (* ADT constructor *)
              | _ -> false
            in
            let filter =
              filter_left && (var_or_global || const_re || pure_re)
            in

            (* Update the rhs (we may perform substitutions inside, and it is
             * better to do them *before* we inline it *)
            let re = self#visit_texpression env re in
            (* Update the substitution environment *)
            let env = if filter then VarId.Map.add lv_var.id re env else env in
            (* Update the next expression *)
            let e = self#visit_texpression env e in
            (* Reconstruct the [let], only if the binding is not filtered *)
            if filter then e.e else Let (monadic, lv, re, e)
        | ( false,
            PatAdt
              {
                variant_id = None;
                field_values = [ { value = PatVar (lv_var, _); ty = _ } ];
              } ) ->
            (* Second case: we deconstruct a structure with one field that we will
               extract as tuple. *)
            let adt_id, _ = PureUtils.ty_as_adt def.item_meta.span re.ty in
            (* Update the rhs (we may perform substitutions inside, and it is
             * better to do them *before* we inline it *)
            let re = self#visit_texpression env re in
            if
              PureUtils.is_var re
              && type_decl_from_type_id_is_tuple_struct ctx.type_ctx.type_infos
                   adt_id
            then
              (* Update the substitution environment *)
              let env = VarId.Map.add lv_var.id re env in
              (* Update the next expression *)
              let e = self#visit_texpression env e in
              (* We filter the [let], and thus do not reconstruct it *)
              e.e
            else (* Nothing to do *)
              super#visit_Let env monadic lv re e
        | _ -> super#visit_Let env monadic lv re e

      (** Substitute the variables *)
      method! visit_Var (env : texpression VarId.Map.t) (vid : VarId.id) =
        match VarId.Map.find_opt vid env with
        | None -> (* No substitution *) super#visit_Var env vid
        | Some ne ->
            (* Substitute - note that we need to reexplore, because
             * there may be stacked substitutions, if we have:
             * var0 --> var1
             * var1 --> var2.
             *)
            self#visit_expression env ne.e
    end
  in
  match def.body with
  | None -> def
  | Some body ->
      let body =
        { body with body = obj#visit_texpression VarId.Map.empty body.body }
      in
      { def with body = Some body }

(** Filter the useless assignments (removes the useless variables, filters
    the function calls) *)
let filter_useless (_ctx : trans_ctx) (def : fun_decl) : fun_decl =
  (* We first need a transformation on *left-values*, which filters the useless
   * variables and tells us whether the value contains any variable which has
   * not been replaced by [_] (in which case we need to keep the assignment,
   * etc.).
   * 
   * This is implemented as a map-reduce.
   *
   * Returns: ( filtered_left_value, *all_dummies* )
   *
   * [all_dummies]:
   * If the returned boolean is true, it means that all the variables appearing
   * in the filtered left-value are *dummies* (meaning that if this left-value
   * appears at the left of a let-binding, this binding might potentially be
   * removed).
   *)
  let lv_visitor =
    object
      inherit [_] mapreduce_typed_pattern
      method zero _ = true
      method plus b0 b1 _ = b0 () && b1 ()

      method! visit_PatVar env v mp =
        if VarId.Set.mem v.id env then (PatVar (v, mp), fun _ -> false)
        else (PatDummy, fun _ -> true)
    end
  in
  let filter_typed_pattern (used_vars : VarId.Set.t) (lv : typed_pattern) :
      typed_pattern * bool =
    let lv, all_dummies = lv_visitor#visit_typed_pattern used_vars lv in
    (lv, all_dummies ())
  in

  (* We then implement the transformation on *expressions* through a mapreduce.
   * Note that the transformation is bottom-up.
   * The map filters the useless assignments, the reduce computes the set of
   * used variables.
   *)
  let expr_visitor =
    object (self)
      inherit [_] mapreduce_expression as super
      method zero _ = VarId.Set.empty
      method plus s0 s1 _ = VarId.Set.union (s0 ()) (s1 ())

      (** Whenever we visit a variable, we need to register the used variable *)
      method! visit_Var _ vid = (Var vid, fun _ -> VarId.Set.singleton vid)

      method! visit_expression env e =
        match e with
        | Var _ | CVar _ | Const _ | App _ | Qualif _
        | Meta (_, _)
        | StructUpdate _ | Lambda _
        | EError (_, _) -> super#visit_expression env e
        | Switch (scrut, switch) -> (
            match switch with
            | If (_, _) -> super#visit_expression env e
            | Match branches ->
                (* Simplify the branches *)
                let simplify_branch (br : match_branch) =
                  (* Compute the set of values used inside the branch *)
                  let branch, used = self#visit_texpression env br.branch in
                  (* Simplify the pattern *)
                  let pat, _ = filter_typed_pattern (used ()) br.pat in
                  { pat; branch }
                in
                super#visit_expression env
                  (Switch (scrut, Match (List.map simplify_branch branches))))
        | Let (monadic, lv, re, e) ->
            (* Compute the set of values used in the next expression *)
            let e, used = self#visit_texpression env e in
            let used = used () in
            (* Filter the left values *)
            let lv, all_dummies = filter_typed_pattern used lv in
            (* Small utility - called if we can't filter the let-binding *)
            let dont_filter () =
              let re, used_re = self#visit_texpression env re in
              let used = VarId.Set.union used (used_re ()) in
              (* Simplify the left pattern if it only contains dummy variables *)
              let lv =
                if all_dummies then
                  let ty = lv.ty in
                  let value = PatDummy in
                  { value; ty }
                else lv
              in
              (Let (monadic, lv, re, e), fun _ -> used)
            in
            (* Potentially filter the let-binding *)
            if all_dummies then
              if not monadic then
                (* Not a monadic let-binding: simple case *)
                (e.e, fun _ -> used)
              else (* Monadic let-binding: can't filter *)
                dont_filter ()
            else (* There are used variables: don't filter *)
              dont_filter ()
        | Loop loop ->
            (* We take care to ignore the varset computed on the *loop body* *)
            let fun_end, s = self#visit_texpression () loop.fun_end in
            let loop_body, _ = self#visit_texpression () loop.loop_body in
            (Loop { loop with fun_end; loop_body }, s)
    end
  in
  (* We filter only inside of transparent (i.e., non-opaque) definitions *)
  match def.body with
  | None -> def
  | Some body ->
      (* Visit the body *)
      let body_exp, used_vars = expr_visitor#visit_texpression () body.body in
      (* Visit the parameters - TODO: update: we can filter only if the definition
       * is not recursive (otherwise it might mess up with the decrease clauses:
       * the decrease clauses uses all the inputs given to the function, if some
       * inputs are replaced by '_' we can't give it to the function used in the
       * decreases clause).
       * For now we deactivate the filtering. *)
      let used_vars = used_vars () in
      let inputs_lvs =
        if false then
          List.map
            (fun lv -> fst (filter_typed_pattern used_vars lv))
            body.inputs_lvs
        else body.inputs_lvs
      in
      (* Return *)
      let body = { body with body = body_exp; inputs_lvs } in
      { def with body = Some body }

(** Simplify the lets immediately followed by an ok.

    Ex.:
    {[
      x <-- f y;
      Ok x

        ~~>

      f y
    ]}
 *)
let simplify_let_then_ok _ctx (def : fun_decl) =
  (* Match a pattern and an expression: evaluates to [true] if the expression
     is actually exactly the pattern *)
  let rec match_pattern_and_expr (pat : typed_pattern) (e : texpression) : bool
      =
    match (pat.value, e.e) with
    | PatConstant plit, Const lit -> plit = lit
    | PatVar (pv, _), Var vid -> pv.id = vid
    | PatDummy, _ ->
        (* It is ok only if we ignore the unit value *)
        pat.ty = mk_unit_ty && e = mk_unit_rvalue
    | PatAdt padt, _ -> (
        let qualif, args = destruct_apps e in
        match qualif.e with
        | Qualif { id = AdtCons cons_id; generics = _ } ->
            if
              pat.ty = e.ty
              && padt.variant_id = cons_id.variant_id
              && List.length padt.field_values = List.length args
            then
              List.for_all
                (fun (p, e) -> match_pattern_and_expr p e)
                (List.combine padt.field_values args)
            else false
        | _ -> false)
    | _ -> false
  in

  let expr_visitor =
    object (self)
      inherit [_] map_expression

      method! visit_Let env monadic lv rv next_e =
        (* We do a bottom up traversal (simplifying in the children nodes
           can allow to simplify in the parent nodes) *)
        let rv = self#visit_texpression env rv in
        let next_e = self#visit_texpression env next_e in
        let not_simpl_e = Let (monadic, lv, rv, next_e) in
        match next_e.e with
        | Switch _ | Loop _ | Let _ ->
            (* Small shortcut to avoid doing the check on every let-binding *)
            not_simpl_e
        | _ -> (
            if (* Do the check *)
               monadic then
              (* The first let-binding is monadic *)
              match opt_destruct_ret next_e with
              | Some e ->
                  if match_pattern_and_expr lv e then rv.e else not_simpl_e
              | None -> not_simpl_e
            else
              (* The first let-binding is not monadic *)
              match opt_destruct_ret next_e with
              | Some e ->
                  if match_pattern_and_expr lv e then
                    (* We need to wrap the right-value in a ret *)
                    (mk_result_ok_texpression def.item_meta.span rv).e
                  else not_simpl_e
              | None ->
                  if match_pattern_and_expr lv next_e then rv.e else not_simpl_e
            )
    end
  in

  match def.body with
  | None -> def
  | Some body ->
      (* Visit the body *)
      let body_exp = expr_visitor#visit_texpression () body.body in
      (* Return *)
      let body = { body with body = body_exp } in
      { def with body = Some body }

(** Simplify the aggregated ADTs.
    Ex.:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 x.f2 ~~> x
    ]}
 *)
let simplify_aggregates (ctx : trans_ctx) (def : fun_decl) : fun_decl =
  let expr_visitor =
    object
      inherit [_] map_expression as super

      (* Look for a type constructor applied to arguments *)
      method! visit_texpression env e =
        match e.e with
        | App _ -> (
            (* TODO: we should remove this case, which dates from before the
               introduction of [StructUpdate] *)
            let app, args = destruct_apps e in
            match app.e with
            | Qualif
                {
                  id = AdtCons { adt_id = TAdtId adt_id; variant_id = None };
                  generics;
                } ->
                (* This is a struct *)
                (* Retrieve the definiton, to find how many fields there are *)
                let adt_decl =
                  TypeDeclId.Map.find adt_id ctx.type_ctx.type_decls
                in
                let fields =
                  match adt_decl.kind with
                  | Enum _ | Alias _ | Opaque | Error _ ->
                      craise __FILE__ __LINE__ def.item_meta.span "Unreachable"
                  | Union _ ->
                      craise __FILE__ __LINE__ def.item_meta.span
                        "Unions are not supported"
                  | Struct fields -> fields
                in
                let num_fields = List.length fields in
                (* In order to simplify, there must be as many arguments as
                 * there are fields *)
                sanity_check __FILE__ __LINE__ (num_fields > 0)
                  def.item_meta.span;
                if num_fields = List.length args then
                  (* We now need to check that all the arguments are of the form:
                   * [x.field] for some variable [x], and where the projection
                   * is for the proper ADT *)
                  let to_var_proj (i : int) (arg : texpression) :
                      (generic_args * var_id) option =
                    match arg.e with
                    | App (proj, x) -> (
                        match (proj.e, x.e) with
                        | ( Qualif
                              {
                                id =
                                  Proj { adt_id = TAdtId proj_adt_id; field_id };
                                generics = proj_generics;
                              },
                            Var v ) ->
                            (* We check that this is the proper ADT, and the proper field *)
                            if
                              proj_adt_id = adt_id
                              && FieldId.to_int field_id = i
                            then Some (proj_generics, v)
                            else None
                        | _ -> None)
                    | _ -> None
                  in
                  let args = List.mapi to_var_proj args in
                  let args = List.filter_map (fun x -> x) args in
                  (* Check that all the arguments are of the expected form *)
                  if List.length args = num_fields then
                    (* Check that this is the same variable we project from -
                     * note that we checked above that there is at least one field *)
                    let (_, x), end_args = Collections.List.pop args in
                    if List.for_all (fun (_, y) -> y = x) end_args then (
                      (* We can substitute *)
                      (* Sanity check: all types correct *)
                      sanity_check __FILE__ __LINE__
                        (List.for_all
                           (fun (generics1, _) -> generics1 = generics)
                           args)
                        def.item_meta.span;
                      { e with e = Var x })
                    else super#visit_texpression env e
                  else super#visit_texpression env e
                else super#visit_texpression env e
            | _ -> super#visit_texpression env e)
        | StructUpdate { struct_id; init = None; updates } ->
            let adt_ty = e.ty in
            (* Attempt to convert all the field updates to projections
               of fields from an ADT with the same type *)
            let to_var_proj ((fid, arg) : FieldId.id * texpression) :
                var_id option =
              match arg.e with
              | App (proj, x) -> (
                  match (proj.e, x.e) with
                  | ( Qualif
                        {
                          id = Proj { adt_id = TAdtId proj_adt_id; field_id };
                          generics = _;
                        },
                      Var v ) ->
                      (* We check that this is the proper ADT, and the proper field *)
                      if
                        TAdtId proj_adt_id = struct_id
                        && field_id = fid && x.ty = adt_ty
                      then Some v
                      else None
                  | _ -> None)
              | _ -> None
            in
            let var_projs = List.map to_var_proj updates in
            let filt_var_projs = List.filter_map (fun x -> x) var_projs in
            if filt_var_projs = [] then super#visit_texpression env e
            else
              (* If all the projections are from the same variable [x], we
                 simply replace the whole expression with [x] *)
              let x = List.hd filt_var_projs in
              if
                List.length filt_var_projs = List.length updates
                && List.for_all (fun y -> y = x) filt_var_projs
              then { e with e = Var x }
              else if
                (* Attempt to create an "update" expression (i.e., of
                   the shape [{ x with f := v }]).

                   This is not supported by Coq *)
                Config.backend () <> Coq
              then (
                (* Compute the number of occurrences of each variable *)
                let occurs = ref VarId.Map.empty in
                List.iter
                  (fun x ->
                    let num =
                      match VarId.Map.find_opt x !occurs with
                      | None -> 1
                      | Some n -> n + 1
                    in
                    occurs := VarId.Map.add x num !occurs)
                  filt_var_projs;
                (* Find the max - note that we can initialize the max at 0,
                   because there is at least one variable *)
                let max = ref 0 in
                let x = ref x in
                List.iter
                  (fun (y, n) ->
                    if n > !max then (
                      max := n;
                      x := y))
                  (VarId.Map.bindings !occurs);
                (* Create the update expression *)
                let updates =
                  List.filter_map
                    (fun ((fid, fe), y_opt) ->
                      if y_opt = Some !x then None else Some (fid, fe))
                    (List.combine updates var_projs)
                in
                let supd =
                  StructUpdate { struct_id; init = Some !x; updates }
                in
                let e = { e with e = supd } in
                super#visit_texpression env e)
              else super#visit_texpression env e
        | _ -> super#visit_texpression env e
    end
  in
  match def.body with
  | None -> def
  | Some body ->
      (* Visit the body *)
      let body_exp = expr_visitor#visit_texpression () body.body in
      (* Return *)
      let body = { body with body = body_exp } in
      { def with body = Some body }

(** Retrieve the loop definitions from the function definition.

    {!SymbolicToPure} generates an AST in which the loop bodies are part of
    the function body (see the {!Pure.Loop} node). This function extracts
    those function bodies into independent definitions while removing
    occurrences of the {!Pure.Loop} node.
 *)
let decompose_loops (_ctx : trans_ctx) (def : fun_decl) :
    fun_decl * fun_decl list =
  match def.body with
  | None -> (def, [])
  | Some body ->
      (* Count the number of loops *)
      let loops = ref LoopId.Set.empty in
      let expr_visitor =
        object
          inherit [_] iter_expression as super

          method! visit_Loop env loop =
            loops := LoopId.Set.add loop.loop_id !loops;
            super#visit_Loop env loop
        end
      in
      expr_visitor#visit_texpression () body.body;
      let num_loops = LoopId.Set.cardinal !loops in

      (* Store the loops here *)
      let loops = ref LoopId.Map.empty in
      let expr_visitor =
        object (self)
          inherit [_] map_expression

          method! visit_Loop env loop =
            let fun_sig = def.signature in
            let fwd_info = fun_sig.fwd_info in
            let fwd_effect_info = fwd_info.effect_info in
            let ignore_output = fwd_info.ignore_output in

            (* Generate the loop definition *)
            let loop_fwd_effect_info = fwd_effect_info in

            let loop_fwd_sig_info : fun_sig_info =
              let fuel = if !Config.use_fuel then 1 else 0 in
              let num_inputs = List.length loop.inputs in
              let fwd_info : inputs_info =
                let info = fwd_info.fwd_info in
                let fwd_state =
                  info.num_inputs_with_fuel_with_state
                  - info.num_inputs_with_fuel_no_state
                in
                {
                  has_fuel = !Config.use_fuel;
                  num_inputs_no_fuel_no_state = num_inputs;
                  num_inputs_with_fuel_no_state = num_inputs + fuel;
                  num_inputs_with_fuel_with_state =
                    num_inputs + fuel + fwd_state;
                }
              in

              { fwd_info; effect_info = loop_fwd_effect_info; ignore_output }
            in
            sanity_check __FILE__ __LINE__
              (fun_sig_info_is_wf loop_fwd_sig_info)
              def.item_meta.span;

            let inputs_tys =
              let fuel = if !Config.use_fuel then [ mk_fuel_ty ] else [] in
              let fwd_inputs = List.map (fun (v : var) -> v.ty) loop.inputs in
              let info = fwd_info.fwd_info in
              let fwd_state =
                Collections.List.subslice fun_sig.inputs
                  info.num_inputs_with_fuel_no_state
                  info.num_inputs_with_fuel_with_state
              in
              List.concat [ fuel; fwd_inputs; fwd_state ]
            in

            let output = loop.output_ty in

            let loop_sig =
              {
                generics = fun_sig.generics;
                explicit_info = fun_sig.explicit_info;
                llbc_generics = fun_sig.llbc_generics;
                preds = fun_sig.preds;
                inputs = inputs_tys;
                output;
                fwd_info = loop_fwd_sig_info;
                back_effect_info = fun_sig.back_effect_info;
              }
            in

            let fuel_vars, inputs, inputs_lvs =
              (* Introduce the fuel input *)
              let fuel_vars, fuel0_var, fuel_lvs =
                if !Config.use_fuel then
                  let fuel0_var = mk_fuel_var loop.fuel0 in
                  let fuel_lvs = mk_typed_pattern_from_var fuel0_var None in
                  (Some (loop.fuel0, loop.fuel), [ fuel0_var ], [ fuel_lvs ])
                else (None, [], [])
              in

              (* Introduce the forward input state *)
              let fwd_state_var, fwd_state_lvs =
                sanity_check __FILE__ __LINE__
                  (loop_fwd_effect_info.stateful
                  = Option.is_some loop.input_state)
                  def.item_meta.span;
                match loop.input_state with
                | None -> ([], [])
                | Some input_state ->
                    let state_var = mk_state_var input_state in
                    let state_lvs = mk_typed_pattern_from_var state_var None in
                    ([ state_var ], [ state_lvs ])
              in

              (* Introduce the additional backward inputs, if necessary *)
              let fun_body = Option.get def.body in
              let info = fwd_info.fwd_info in
              let _, back_inputs =
                Collections.List.split_at fun_body.inputs
                  info.num_inputs_with_fuel_with_state
              in
              let _, back_inputs_lvs =
                Collections.List.split_at fun_body.inputs_lvs
                  info.num_inputs_with_fuel_with_state
              in

              let inputs =
                List.concat
                  [ fuel0_var; fwd_state_var; loop.inputs; back_inputs ]
              in
              let inputs_lvs =
                List.concat
                  [ fuel_lvs; fwd_state_lvs; loop.inputs_lvs; back_inputs_lvs ]
              in
              (fuel_vars, inputs, inputs_lvs)
            in

            (* Wrap the loop body in a match over the fuel *)
            let loop_body =
              match fuel_vars with
              | None -> loop.loop_body
              | Some (fuel0, fuel) ->
                  SymbolicToPure.wrap_in_match_fuel def.item_meta.span fuel0
                    fuel loop.loop_body
            in

            let loop_body = { inputs; inputs_lvs; body = loop_body } in
            (* We retrieve the meta information from the parent function
               *but* replace its span with the span of the loop *)
            let item_meta = { def.item_meta with span = loop.span } in

            let loop_def : fun_decl =
              {
                def_id = def.def_id;
                item_meta;
                kind = def.kind;
                backend_attributes = def.backend_attributes;
                num_loops;
                loop_id = Some loop.loop_id;
                name = def.name;
                signature = loop_sig;
                is_global_decl_body = def.is_global_decl_body;
                body = Some loop_body;
              }
            in
            (* Store the loop definition *)
            loops := LoopId.Map.add_strict loop.loop_id loop_def !loops;

            (* Update the current expression to remove the [Loop] node, and continue *)
            (self#visit_texpression env loop.fun_end).e
        end
      in

      let body_expr = expr_visitor#visit_texpression () body.body in
      let body = { body with body = body_expr } in
      let def = { def with body = Some body; num_loops } in
      let loops = List.map snd (LoopId.Map.bindings !loops) in
      (def, loops)

(** Convert the unit variables to [()] if they are used as right-values or
    [_] if they are used as left values in patterns. *)
let unit_vars_to_unit (def : fun_decl) : fun_decl =
  (* The map visitor *)
  let obj =
    object
      inherit [_] map_expression as super

      (** Replace in patterns *)
      method! visit_PatVar _ v mp =
        if v.ty = mk_unit_ty then PatDummy else PatVar (v, mp)

      (** Replace in "regular" expressions - note that we could limit ourselves
          to variables, but this is more powerful
       *)
      method! visit_texpression env e =
        if e.ty = mk_unit_ty then mk_unit_rvalue
        else super#visit_texpression env e
    end
  in
  (* Update the body *)
  match def.body with
  | None -> def
  | Some body ->
      let body_exp = obj#visit_texpression () body.body in
      (* Update the input parameters *)
      let inputs_lvs = List.map (obj#visit_typed_pattern ()) body.inputs_lvs in
      (* Return *)
      let body = Some { body with body = body_exp; inputs_lvs } in
      { def with body }

(** Eliminate the box functions like [Box::new] (which is translated to the
    identity) and [Box::free] (which is translated to [()]).

    Note that the box types have already been eliminated during the translation
    from symbolic to pure.
    The reason why we don't eliminate the box functions at the same time is
    that we would need to eliminate them in two different places: when translating
    function calls, and when translating end abstractions. Here, we can do
    something simpler, in one micro-pass.
 *)
let eliminate_box_functions (_ctx : trans_ctx) (def : fun_decl) : fun_decl =
  (* The map visitor *)
  let obj =
    object
      inherit [_] map_expression as super

      method! visit_texpression env e =
        match opt_destruct_function_call e with
        | Some (fun_id, _tys, args) -> (
            (* Below, when dealing with the arguments: we consider the very
             * general case, where functions could be boxed (meaning we
             * could have: [box_new f x])
             * *)
            match fun_id with
            | Fun (FromLlbc (FunId (FAssumed aid), _lp_id)) -> (
                match aid with
                | BoxNew ->
                    let arg, args = Collections.List.pop args in
                    mk_apps def.item_meta.span arg args
                | Index _ | ArrayToSliceShared | ArrayToSliceMut | ArrayRepeat
                  -> super#visit_texpression env e)
            | _ -> super#visit_texpression env e)
        | _ -> super#visit_texpression env e
    end
  in
  (* Update the body *)
  match def.body with
  | None -> def
  | Some body ->
      let body = Some { body with body = obj#visit_texpression () body.body } in
      { def with body }

(** Decompose let-bindings by introducing intermediate let-bindings.

    This is a utility function: see {!decompose_monadic_let_bindings} and
    {!decompose_nested_let_patterns}.

    [decompose_monadic]: always decompose a monadic let-binding
    [decompose_nested_pats]: decompose the nested patterns
 *)
let decompose_let_bindings (decompose_monadic : bool)
    (decompose_nested_pats : bool) (_ctx : trans_ctx) (def : fun_decl) :
    fun_decl =
  match def.body with
  | None -> def
  | Some body ->
      (* Set up the var id generator *)
      let cnt = get_body_min_var_counter body in
      let _, fresh_id = VarId.mk_stateful_generator cnt in
      let mk_fresh (ty : ty) : typed_pattern * texpression =
        let vid = fresh_id () in
        let tmp : var = { id = vid; basename = None; ty } in
        let ltmp = mk_typed_pattern_from_var tmp None in
        let rtmp = mk_texpression_from_var tmp in
        (ltmp, rtmp)
      in

      (* Utility function - returns the patterns to introduce, from the last to
         the first.

         For instance, if it returns:
         {[
           ([
              ((x3, x4), x1);
              ((x1, x2), tmp)
            ],
            (x0, tmp))
         ]}
         then we need to introduce:
         {[
           let (x0, tmp) = original_term in
           let (x1, x2) = tmp in
           let (x3, x4) = x1 in
           ...
         }]
      *)
      let decompose_pat (lv : typed_pattern) :
          (typed_pattern * texpression) list * typed_pattern =
        let patterns = ref [] in

        (* We decompose patterns *inside* other patterns.
           The boolean [inside] allows us to remember if we dived into a
           pattern already *)
        let visit_pats =
          object
            inherit [_] map_typed_pattern as super

            method! visit_typed_pattern (inside : bool) (pat : typed_pattern)
                : typed_pattern =
              match pat.value with
              | PatConstant _ | PatVar _ | PatDummy -> pat
              | PatAdt _ ->
                  if not inside then super#visit_typed_pattern true pat
                  else
                    let ltmp, rtmp = mk_fresh pat.ty in
                    let pat = super#visit_typed_pattern false pat in
                    patterns := (pat, rtmp) :: !patterns;
                    ltmp
          end
        in

        let inside = false in
        let lv = visit_pats#visit_typed_pattern inside lv in
        (!patterns, lv)
      in

      (* It is a very simple map *)
      let visit_lets =
        object (self)
          inherit [_] map_expression as super

          method! visit_Let env monadic lv re next_e =
            (* Decompose the monadic let-bindings *)
            let monadic, lv, re, next_e =
              if (not monadic) || not decompose_monadic then
                (monadic, lv, re, next_e)
              else
                (* If monadic, we need to check if the left-value is a variable:
                 * - if yes, don't decompose
                 * - if not, make the decomposition in two steps
                 *)
                match lv.value with
                | PatVar _ | PatDummy ->
                    (* Variable: nothing to do *)
                    (monadic, lv, re, next_e)
                | _ ->
                    (* Not a variable: decompose if required *)
                    (* Introduce a temporary variable to receive the value of the
                     * monadic binding *)
                    let ltmp, rtmp = mk_fresh lv.ty in
                    (* Visit the next expression *)
                    let next_e = self#visit_texpression env next_e in
                    (* Create the let-bindings *)
                    (monadic, ltmp, re, mk_let false lv rtmp next_e)
            in
            (* Decompose the nested let-patterns *)
            let lv, next_e =
              if not decompose_nested_pats then (lv, next_e)
              else
                let pats, first_pat = decompose_pat lv in
                let e =
                  List.fold_left
                    (fun next_e (lpat, rv) -> mk_let false lpat rv next_e)
                    next_e pats
                in
                (first_pat, e)
            in
            (* Continue *)
            super#visit_Let env monadic lv re next_e
        end
      in
      (* Update the body *)
      let body =
        Some { body with body = visit_lets#visit_texpression () body.body }
      in
      (* Return *)
      { def with body }

(** Decompose monadic let-bindings.

    See the explanations in {!val:Config.decompose_monadic_let_bindings}
 *)
let decompose_monadic_let_bindings (ctx : trans_ctx) (def : fun_decl) : fun_decl
    =
  decompose_let_bindings true false ctx def

(** Decompose the nested let patterns.

    See the explanations in {!val:Config.decompose_nested_let_patterns}
 *)
let decompose_nested_let_patterns (ctx : trans_ctx) (def : fun_decl) : fun_decl
    =
  decompose_let_bindings false true ctx def

(** Unfold the monadic let-bindings to explicit matches. *)
let unfold_monadic_let_bindings (_ctx : trans_ctx) (def : fun_decl) : fun_decl =
  match def.body with
  | None -> def
  | Some body ->
      let cnt = get_body_min_var_counter body in
      let _, fresh_id = VarId.mk_stateful_generator cnt in

      (* It is a very simple map *)
      let obj =
        object (_self)
          inherit [_] map_expression as super

          method! visit_Let env monadic lv re e =
            (* We simply do the following transformation:
               {[
                 pat <-- re; e

                     ~~>

                 match re with
                 | Fail err -> Fail err
                 | Return pat -> e
               ]}
            *)
            (* TODO: we should use a monad "kind" instead of a boolean *)
            if not monadic then super#visit_Let env monadic lv re e
            else
              (* We don't do the same thing if we use a state-error monad or simply
                 an error monad.
                 Note that some functions always live in the error monad (arithmetic
                 operations, for instance).
              *)
              (* TODO: this information should be computed in SymbolicToPure and
               * store in an enum ("monadic" should be an enum, not a bool). *)
              let re_ty =
                Option.get (opt_destruct_result def.item_meta.span re.ty)
              in
              sanity_check __FILE__ __LINE__ (lv.ty = re_ty) def.item_meta.span;
              let err_vid = fresh_id () in
              let err_var : var =
                {
                  id = err_vid;
                  basename = Some ConstStrings.error_basename;
                  ty = mk_error_ty;
                }
              in
              let err_pat = mk_typed_pattern_from_var err_var None in
              let fail_pat = mk_result_fail_pattern err_pat.value lv.ty in
              let err_v = mk_texpression_from_var err_var in
              let fail_value =
                mk_result_fail_texpression def.item_meta.span err_v e.ty
              in
              let fail_branch = { pat = fail_pat; branch = fail_value } in
              let success_pat = mk_result_ok_pattern lv in
              let success_branch = { pat = success_pat; branch = e } in
              let switch_body = Match [ fail_branch; success_branch ] in
              let e = Switch (re, switch_body) in
              (* Continue *)
              super#visit_expression env e
        end
      in
      (* Update the body *)
      let body_e = obj#visit_texpression () body.body in
      let body = { body with body = body_e } in
      (* Return *)
      { def with body = Some body }

(** Auxiliary function for {!apply_passes_to_def} *)
let apply_end_passes_to_def (ctx : trans_ctx) (def : fun_decl) : fun_decl =
  (* Convert the unit variables to [()] if they are used as right-values or
   * [_] if they are used as left values. *)
  let def = unit_vars_to_unit def in
  log#ldebug
    (lazy ("unit_vars_to_unit:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Introduce the special structure create/update expressions *)
  let def = intro_struct_updates ctx def in
  log#ldebug
    (lazy ("intro_struct_updates:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Simplify the let-bindings *)
  let def = simplify_let_bindings ctx def in
  log#ldebug
    (lazy ("simplify_let_bindings:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Inline the useless variable reassignments *)
  let def =
    inline_useless_var_reassignments ctx ~inline_named:true ~inline_const:true
      ~inline_pure:true def
  in
  log#ldebug
    (lazy
      ("inline_useless_var_assignments:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Eliminate the box functions - note that the "box" types were eliminated
   * during the symbolic to pure phase: see the comments for [eliminate_box_functions] *)
  let def = eliminate_box_functions ctx def in
  log#ldebug
    (lazy ("eliminate_box_functions:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Filter the useless variables, assignments, function calls, etc. *)
  let def = filter_useless ctx def in
  log#ldebug (lazy ("filter_useless:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Simplify the lets immediately followed by a return.

     Ex.:
     {[
       x <-- f y;
       Return x

         ~~>

       f y
     ]}
  *)
  let def = simplify_let_then_ok ctx def in
  log#ldebug
    (lazy ("simplify_let_then_ok:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Simplify the aggregated ADTs.

     Ex.:
     {[
       (* type struct = { f0 : nat; f1 : nat; f2 : nat } *)

       Mkstruct x.f0 x.f1 x.f2                 ~~> x
       { f0 := x.f0; f1 := x.f1; f2 := x.f2 }  ~~> x
       { f0 := x.f0; f1 := x.f1; f2 := v }     ~~> { x with f2 = v }
     ]}
  *)
  let def = simplify_aggregates ctx def in
  log#ldebug
    (lazy ("simplify_aggregates:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Simplify the let-bindings - some simplifications may have been unlocked by
     the pass above (for instance, the lambda simplification) *)
  let def = simplify_let_bindings ctx def in
  log#ldebug
    (lazy
      ("simplify_let_bindings (pass 2):\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Inline the useless vars again *)
  let def =
    inline_useless_var_reassignments ctx ~inline_named:true ~inline_const:true
      ~inline_pure:false def
  in
  log#ldebug
    (lazy
      ("inline_useless_var_assignments (pass 2):\n\n"
     ^ fun_decl_to_string ctx def ^ "\n"));

  (* Simplify the let-then return again (the lambda simplification may have
     unlocked more simplifications here) *)
  let def = simplify_let_then_ok ctx def in
  log#ldebug
    (lazy
      ("simplify_let_then_ok (pass 2):\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Decompose the monadic let-bindings - used by Coq *)
  let def =
    if !Config.decompose_monadic_let_bindings then (
      let def = decompose_monadic_let_bindings ctx def in
      log#ldebug
        (lazy
          ("decompose_monadic_let_bindings:\n\n" ^ fun_decl_to_string ctx def
         ^ "\n"));
      def)
    else (
      log#ldebug
        (lazy
          "ignoring decompose_monadic_let_bindings due to the configuration\n");
      def)
  in

  (* Decompose nested let-patterns *)
  let def =
    if !Config.decompose_nested_let_patterns then (
      let def = decompose_nested_let_patterns ctx def in
      log#ldebug
        (lazy
          ("decompose_nested_let_patterns:\n\n" ^ fun_decl_to_string ctx def
         ^ "\n"));
      def)
    else (
      log#ldebug
        (lazy
          "ignoring decompose_nested_let_patterns due to the configuration\n");
      def)
  in

  (* Unfold the monadic let-bindings *)
  let def =
    if !Config.unfold_monadic_let_bindings then (
      let def = unfold_monadic_let_bindings ctx def in
      log#ldebug
        (lazy
          ("unfold_monadic_let_bindings:\n\n" ^ fun_decl_to_string ctx def
         ^ "\n"));
      def)
    else (
      log#ldebug
        (lazy "ignoring unfold_monadic_let_bindings due to the configuration\n");
      def)
  in

  (* We are done *)
  def

(** Small utility for {!filter_loop_inputs} *)
let filter_prefix (keep : bool list) (ls : 'a list) : 'a list =
  let ls0, ls1 = Collections.List.split_at ls (List.length keep) in
  let ls0 =
    List.filter_map
      (fun (b, x) -> if b then Some x else None)
      (List.combine keep ls0)
  in
  List.append ls0 ls1

type fun_loop_id = A.fun_id * LoopId.id option [@@deriving show, ord]

module FunLoopIdOrderedType = struct
  type t = fun_loop_id

  let compare = compare_fun_loop_id
  let to_string = show_fun_loop_id
  let pp_t = pp_fun_loop_id
  let show_t = show_fun_loop_id
end

module FunLoopIdMap = Collections.MakeMap (FunLoopIdOrderedType)

(** Filter the useless loop input parameters. *)
let filter_loop_inputs (ctx : trans_ctx) (transl : pure_fun_translation list) :
    pure_fun_translation list =
  (* We need to explore groups of mutually recursive functions. In order
     to compute which parameters are useless, we need to explore the
     functions by groups of mutually recursive definitions.

     Because every Rust function is translated to a list of functions (forward
     function, backward functions, loop functions, etc.), and those functions
     might depend on each others in different ways, we recompute the SCCs of
     the whole module.

     Rem.: we also redo this computation, on a smaller scale, in {!Translate}.
     Maybe we can factor out the two.
  *)
  let all_decls =
    List.concat
      (List.concat (List.map (fun { f; loops } -> [ f :: loops ]) transl))
  in
  let subgroups = ReorderDecls.group_reorder_fun_decls all_decls in

  log#ldebug
    (lazy
      ("filter_loop_inputs: all_decls:\n\n"
      ^ String.concat "\n\n" (List.map (fun_decl_to_string ctx) all_decls)
      ^ "\n"));

  (* Explore the subgroups one by one.

     For now, we only filter the parameters of loop functions which are simply
     recursive.

     Rem.: there is a bit of redundancy in computing the useless parameters
     for the loop forward *and* the loop backward functions.
  *)
  (* The [filtered] map: maps function identifiers to filtering information. *)
  let used_map = ref FunLoopIdMap.empty in

  (* We start by computing the filtering information, for each function *)
  let compute_one_filter_info (decl : fun_decl) =
    (* There should be a body *)
    let body = Option.get decl.body in
    (* We only look at the forward inputs, without the state *)
    let inputs_prefix, _ =
      Collections.List.split_at body.inputs
        decl.signature.fwd_info.fwd_info.num_inputs_with_fuel_no_state
    in
    let used = ref (List.map (fun v -> (var_get_id v, false)) inputs_prefix) in
    let inputs_prefix_length = List.length inputs_prefix in
    let inputs =
      List.map
        (fun v -> (var_get_id v, mk_texpression_from_var v))
        inputs_prefix
    in
    log#ldebug
      (lazy
        ("inputs:\n"
        ^ String.concat ", " (List.map (var_to_string ctx) inputs_prefix)
        ^ "\n"));
    let inputs_set = VarId.Set.of_list (List.map var_get_id inputs_prefix) in
    sanity_check __FILE__ __LINE__
      (Option.is_some decl.loop_id)
      decl.item_meta.span;

    let fun_id = (E.FRegular decl.def_id, decl.loop_id) in

    let set_used vid =
      used := List.map (fun (vid', b) -> (vid', b || vid = vid')) !used
    in

    (* Set the fuel as used *)
    let sg_info = decl.signature.fwd_info in
    if sg_info.fwd_info.has_fuel then
      set_used (fst (Collections.List.nth inputs 0));

    let visitor =
      object (self : 'self)
        inherit [_] iter_expression as super

        (** Override the expression visitor, to look for loop function calls *)
        method! visit_texpression env e =
          match e.e with
          | App _ -> (
              (* If this is an app: destruct all the arguments, and check if
                 the leftmost expression is the loop function call *)
              let e_app, args = destruct_apps e in
              match e_app.e with
              | Qualif qualif -> (
                  match qualif.id with
                  | FunOrOp (Fun (FromLlbc (FunId fun_id', loop_id'))) ->
                      if (fun_id', loop_id') = fun_id then (
                        (* For each argument, check if it is exactly the original
                           input parameter. Note that there shouldn't be partial
                           applications of loop functions: the number of arguments
                           should be exactly the number of input parameters (i.e.,
                           we can use [combine])
                        *)
                        let beg_args, end_args =
                          Collections.List.split_at args inputs_prefix_length
                        in
                        log#ldebug
                          (lazy
                            ("beg_args:\n"
                            ^ String.concat ", "
                                (List.map (texpression_to_string ctx) beg_args)
                            ^ "\n"));
                        let used_args = List.combine inputs beg_args in
                        List.iter
                          (fun ((vid, var), arg) ->
                            if var <> arg then (
                              self#visit_texpression env arg;
                              set_used vid))
                          used_args;
                        List.iter (self#visit_texpression env) end_args)
                      else super#visit_texpression env e
                  | _ -> super#visit_texpression env e)
              | _ -> super#visit_texpression env e)
          | _ -> super#visit_texpression env e

        (** If we visit a variable which is actually an input parameter, we
            set it as used. Note that we take care of ignoring some of those
            input parameters given in [visit_texpression].
          *)
        method! visit_var_id _ id =
          if VarId.Set.mem id inputs_set then set_used id
      end
    in
    visitor#visit_texpression () body.body;

    log#ldebug
      (lazy
        ("\n- used variables: "
        ^ String.concat ", "
            (List.map
               (Print.pair_to_string VarId.to_string string_of_bool)
               !used)
        ^ "\n"));

    (* Save the filtering information, if there is anything to filter *)
    if List.exists (fun (_, b) -> not b) !used then
      let used = List.map snd !used in
      let used =
        match FunLoopIdMap.find_opt fun_id !used_map with
        | None -> used
        | Some used0 ->
            List.map (fun (b0, b1) -> b0 || b1) (List.combine used0 used)
      in
      used_map := FunLoopIdMap.add fun_id used !used_map
  in
  List.iter
    (fun (_, fl) ->
      match fl with
      | [ f ] ->
          (* Group made of one function: check if it is a loop. If it is the
             case, explore it. *)
          log#ldebug
            (lazy
              ("filter_loop_inputs: singleton:\n\n" ^ fun_decl_to_string ctx f
             ^ "\n"));

          if Option.is_some f.loop_id then compute_one_filter_info f else ()
      | _ ->
          (* Group of mutually recursive functions: ignore for now *)
          ())
    subgroups;

  (* We then apply the filtering to all the function definitions at once *)
  let filter_in_one (decl : fun_decl) : fun_decl =
    (* Filter the function signature *)
    let fun_id = (E.FRegular decl.def_id, decl.loop_id) in
    let decl =
      match FunLoopIdMap.find_opt fun_id !used_map with
      | None -> (* Nothing to filter *) decl
      | Some used_info ->
          let num_filtered =
            List.length (List.filter (fun b -> not b) used_info)
          in
          let {
            generics;
            explicit_info = _;
            llbc_generics;
            preds;
            inputs;
            output;
            fwd_info;
            back_effect_info;
          } =
            decl.signature
          in
          let { fwd_info; effect_info; ignore_output } = fwd_info in

          let {
            has_fuel;
            num_inputs_no_fuel_no_state;
            num_inputs_with_fuel_no_state;
            num_inputs_with_fuel_with_state;
          } =
            fwd_info
          in

          let inputs = filter_prefix used_info inputs in

          let fwd_info =
            {
              has_fuel;
              num_inputs_no_fuel_no_state =
                num_inputs_no_fuel_no_state - num_filtered;
              num_inputs_with_fuel_no_state =
                num_inputs_with_fuel_no_state - num_filtered;
              num_inputs_with_fuel_with_state =
                num_inputs_with_fuel_with_state - num_filtered;
            }
          in

          let fwd_info = { fwd_info; effect_info; ignore_output } in
          sanity_check __FILE__ __LINE__
            (fun_sig_info_is_wf fwd_info)
            decl.item_meta.span;
          let signature =
            {
              generics;
              explicit_info =
                SymbolicToPure.compute_explicit_info generics inputs;
              llbc_generics;
              preds;
              inputs;
              output;
              fwd_info;
              back_effect_info;
            }
          in

          { decl with signature }
    in

    (* Filter the function body *)
    let body =
      match decl.body with
      | None -> None
      | Some body ->
          (* Update the list of vars *)
          let { inputs; inputs_lvs; body } = body in

          let inputs, inputs_lvs =
            match FunLoopIdMap.find_opt fun_id !used_map with
            | None -> (* Nothing to filter *) (inputs, inputs_lvs)
            | Some used_info ->
                let inputs = filter_prefix used_info inputs in
                let inputs_lvs = filter_prefix used_info inputs_lvs in
                (inputs, inputs_lvs)
          in

          (* Update the body expression *)
          let visitor =
            object (self)
              inherit [_] map_expression as super

              method! visit_texpression env e =
                match e.e with
                | App _ -> (
                    let e_app, args = destruct_apps e in
                    match e_app.e with
                    | Qualif qualif -> (
                        match qualif.id with
                        | FunOrOp (Fun (FromLlbc (FunId fun_id, loop_id))) -> (
                            match
                              FunLoopIdMap.find_opt (fun_id, loop_id) !used_map
                            with
                            | None -> super#visit_texpression env e
                            | Some used_info ->
                                (* Filter the types in the arrow type *)
                                let tys, ret_ty = destruct_arrows e_app.ty in
                                let tys = filter_prefix used_info tys in
                                let ty = mk_arrows tys ret_ty in
                                let e_app = { e_app with ty } in

                                (* Filter the arguments *)
                                let args = filter_prefix used_info args in

                                (* Explore the arguments *)
                                let args =
                                  List.map (self#visit_texpression env) args
                                in

                                (* Rebuild *)
                                mk_apps decl.item_meta.span e_app args)
                        | _ ->
                            let e_app = self#visit_texpression env e_app in
                            let args =
                              List.map (self#visit_texpression env) args
                            in
                            mk_apps decl.item_meta.span e_app args)
                    | _ ->
                        let e_app = self#visit_texpression env e_app in
                        let args = List.map (self#visit_texpression env) args in
                        mk_apps decl.item_meta.span e_app args)
                | _ -> super#visit_texpression env e
            end
          in
          let body = visitor#visit_texpression () body in
          Some { inputs; inputs_lvs; body }
    in
    { decl with body }
  in
  let transl =
    List.map
      (fun f ->
        { f = filter_in_one f.f; loops = List.map filter_in_one f.loops })
      transl
  in

  (* Return *)
  transl

(** Update the [reducible] attribute.

    For now we mark a function as reducible when its body is only a call to a loop
    function. This situation often happens for simple functions whose body contains
    a loop: we introduce an intermediate function for the loop body, and the
    translation of the function itself simply calls the loop body. By marking
    the function as reducible, we allow tactics like [simp] or [progress] to
    see through the definition.
 *)
let compute_reducible (_ctx : trans_ctx) (transl : pure_fun_translation list) :
    pure_fun_translation list =
  let update_one (trans : pure_fun_translation) : pure_fun_translation =
    match trans.f.body with
    | None -> trans
    | Some body -> (
        (* Check if the body is exactly a call to a loop function.
           Note that we check that the arguments are exactly the input
           variables - otherwise we may not want the call to be reducible;
           for instance when using the [progress] tactic we might want to
           use a more specialized specification theorem. *)
        let app, args = destruct_apps body.body in
        match app.e with
        | Qualif
            {
              id = FunOrOp (Fun (FromLlbc (FunId fid, Some _lp_id)));
              generics = _;
            }
          when fid = FRegular trans.f.def_id ->
            if
              List.length body.inputs = List.length args
              && List.for_all
                   (fun ((var, arg) : var * texpression) ->
                     match arg.e with
                     | Var var_id -> var_id = var.id
                     | _ -> false)
                   (List.combine body.inputs args)
            then
              let f =
                { trans.f with backend_attributes = { reducible = true } }
              in
              { trans with f }
            else trans
        | _ -> trans)
  in
  List.map update_one transl

(** Apply all the micro-passes to a function.

    As loops are initially directly integrated into the function definition,
    {!apply_passes_to_def} extracts those loops definitions from the body;
    it thus returns the pair: (function def, loop defs). See {!decompose_loops}
    for more information.

    [ctx]: used only for printing.
 *)
let apply_passes_to_def (ctx : trans_ctx) (def : fun_decl) : fun_and_loops =
  (* Debug *)
  log#ldebug (lazy ("PureMicroPasses.apply_passes_to_def: " ^ def.name));

  log#ldebug (lazy ("original decl:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* First, find names for the variables which are unnamed *)
  let def = compute_pretty_names def in
  log#ldebug
    (lazy ("compute_pretty_name:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* TODO: we might want to leverage more the assignment span-data, for
   * aggregates for instance. *)

  (* TODO: reorder the branches of the matches/switches *)

  (* The span-information is now useless: remove it.
   * Rk.: some passes below use the fact that we removed the span-data
   * (otherwise we would have to "unspan" expressions before matching) *)
  let def = remove_span def in
  log#ldebug (lazy ("remove_span:\n\n" ^ fun_decl_to_string ctx def ^ "\n"));

  (* Extract the loop definitions by removing the {!Loop} node *)
  let def, loops = decompose_loops ctx def in

  (* Apply the remaining passes *)
  let f = apply_end_passes_to_def ctx def in
  let loops = List.map (apply_end_passes_to_def ctx) loops in
  { f; loops }

(** Apply the micro-passes to a list of forward/backward translations.

    This function also extracts the loop definitions from the function body
    (see {!decompose_loops}).

    It also returns a boolean indicating whether the forward function should be kept
    or not at extraction time ([true] means we need to keep the forward function).

    Note that we don't "filter" the forward function and return a boolean instead,
    because this function contains useful information to extract the backward
    functions. Note that here, keeping the forward function it is not *necessary*
    but convenient.
 *)
let apply_passes_to_pure_fun_translations (ctx : trans_ctx)
    (transl : fun_decl list) : pure_fun_translation list =
  (* Apply the micro-passes *)
  let transl = List.map (apply_passes_to_def ctx) transl in

  (* Filter the useless inputs in the loop functions (loops are initially
     parameterized by *all* the symbolic values in the context, because
     they may access any of them). *)
  let transl = filter_loop_inputs ctx transl in

  (* Update the "reducible" attribute *)
  compute_reducible ctx transl
