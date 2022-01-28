(** The following module defines micro-passes which operate on the pure AST *)

open Errors
open Pure

type pn_ctx = string VarId.Map.t
(** "pretty-name context": see [compute_pretty_names] *)

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "meta"-place information in the AST to generate naming
    constraints.
    
    The way it works is as follows:
    - we only modify the names of the unnamed variables
    - whenever we see an rvalue/lvalue which is exactly an unnamed variable,
      and this value is linked to some meta-place information which contains
      a name and an empty path, we consider we should use this name
      
    Something important is that, for every variable we find, the name of this
    variable is influenced by the information we find *below* in the AST.

    For instance, the following situations happen:
    
    - let's say we evaluate:
      ```
      match (ls : List<T>) {
        List::Cons(x, hd) => {
          ...
        }
      }
      ```
      
      Actually, in MIR, we get:
      ```
      tmp := discriminant(ls);
      switch tmp {
        0 => {
          x := (ls as Cons).0;
          hd := (ls as Cons).1;
          ...
        }
      }
      ```
      If `ls` maps to a symbolic value `s0` upon evaluating the match in symbolic
      mode, we expand this value upon evaluating `tmp = discriminant(ls)`.
      However, at this point, we don't know which should be the names of
      the symbolic values we introduce for the fields of `Cons`!
      Let's imagine we have (for the `Cons` branch): `s0 ~~> Cons s1 s2`.
      The assigments lead to the following binding in the evaluation context:
      ```
      x -> s1
      hd -> s2
      ```
      
      When generating the symbolic AST, we save as meta-information that we
      assign `s1` to the place `x` and `s2` to the place `hd`. This way,
      we learn we can use the names `x` and `hd` for the variables which are
      introduced by the match:
      ```
      match ls with
      | Cons x hd -> ...
      | ...
      ```
   - If we write the following in Rust:
     ```
     let x = y + z;
     ```
     
     We get the following MIR:
     ```
     let tmp = y + z;
     ```
     TODO: finish...
   - If we write the following in Rust:
     ```
     let px = &mut x;
     f(px);
     ```
     
     Rustc generates the following MIR:
     ```
     px := &mut x;
     tmp := &mut ( *px ); // "tmp" is actually an anonymous variable
     f(move tmp);
     ```

     As borrows and dereferencements are ignored in the pure paths we generate
     (because they are extracted to the identity), we save as meta-data that
     at some point we assign the value of `px` to `tmp`.
     
     TODO: actually useless, because `tmp` later gets inlined.
   - TODO: inputs and end abstraction...
 *)
let compute_pretty_names (def : fun_def) : fun_def =
  (* Small helpers *)
  let add_var (ctx : pn_ctx) (v : var) : pn_ctx =
    assert (not (VarId.Map.mem v.id ctx));
    match v.basename with
    | None -> ctx
    | Some name -> VarId.Map.add v.id name ctx
  in
  let add_var_or_dummy (ctx : pn_ctx) (v : var_or_dummy) : pn_ctx =
    match v with Dummy -> ctx | Var v -> add_var ctx v
  in
  let add_var_or_dummy_list ctx ls = List.fold_left add_var_or_dummy ctx ls in
  let update_var (ctx : pn_ctx) (v : var) : var =
    match v.basename with
    | Some _ -> v
    | None -> (
        match VarId.Map.find_opt v.id ctx with
        | None -> v
        | Some basename -> { v with basename = Some basename })
  in
  let update_var_or_dummy (ctx : pn_ctx) (v : var_or_dummy) : var_or_dummy =
    match v with Dummy -> Dummy | Var v -> Var (update_var ctx v)
  in
  let update_var_or_dummy_list ctx = List.map (update_var_or_dummy ctx) in
  let update_typed_lvalue ctx (lv : typed_lvalue) =
    let value =
      match lv.value with
      | LvVar v -> LvVar (update_var_or_dummy ctx v)
      | v -> v
    in
    { lv with value }
  in

  let add_constraint (mp : mplace) (var_id : VarId.id) (ctx : pn_ctx) : pn_ctx =
    match (mp.name, mp.projection) with
    | Some name, [] ->
        (* Check if the variable already has a name - if not: insert the new name *)
        if VarId.Map.mem var_id ctx then ctx else VarId.Map.add var_id name ctx
    | _ -> ctx
  in
  let add_right_constraint (mp : mplace) (rv : typed_rvalue) (ctx : pn_ctx) :
      pn_ctx =
    match rv.value with
    | RvPlace { var = var_id; projection = [] } -> add_constraint mp var_id ctx
    | _ -> ctx
  in
  let add_opt_right_constraint (mp : mplace option) (rv : typed_rvalue)
      (ctx : pn_ctx) : pn_ctx =
    match mp with None -> ctx | Some mp -> add_right_constraint mp rv ctx
  in
  let add_opt_right_constraint_list ctx rvs =
    List.fold_left
      (fun ctx (mp, rv) -> add_opt_right_constraint mp rv ctx)
      ctx rvs
  in
  let add_left_constraint_var_or_dummy (mp : mplace option) (v : var_or_dummy)
      (ctx : pn_ctx) : pn_ctx =
    let ctx = add_var_or_dummy ctx v in
    match (v, mp) with Var v, Some mp -> add_constraint mp v.id ctx | _ -> ctx
  in
  let add_left_constraint_typed_value (mp : mplace option) (lv : typed_lvalue)
      (ctx : pn_ctx) : pn_ctx =
    match lv.value with
    | LvTuple _ | LvVar Dummy -> ctx
    | LvVar v -> add_left_constraint_var_or_dummy mp v ctx
  in
  let add_left_constraint_var_or_dummy_list ctx lvs =
    List.fold_left
      (fun ctx (v, mp) -> add_left_constraint_var_or_dummy mp v ctx)
      ctx lvs
  in
  let add_left_constraint_typed_value_list ctx lvs =
    List.fold_left
      (fun ctx (v, mp) -> add_left_constraint_typed_value mp v ctx)
      ctx lvs
  in

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
    VarId.Map.fold (fun id name ctx -> VarId.Map.add id name ctx) ctx0 ctx1
  in
  let merge_ctxs_ls (ctxs : pn_ctx list) : pn_ctx =
    List.fold_left (fun ctx0 ctx1 -> merge_ctxs ctx0 ctx1) VarId.Map.empty ctxs
  in

  (* *)
  let rec update_expression (e : expression) (ctx : pn_ctx) :
      pn_ctx * expression =
    match e with
    | Return _ | Fail -> (ctx, e)
    | Let (lb, e) -> update_let lb e ctx
    | Switch (scrut, mp, body) -> update_switch_body scrut mp body ctx
    | Meta (meta, e) -> update_meta meta e ctx
  (* *)
  and update_let (lb : let_bindings) (e : expression) (ctx : pn_ctx) :
      pn_ctx * expression =
    match lb with
    | Call (lvs, call) ->
        let ctx =
          add_opt_right_constraint_list ctx
            (List.combine call.args_mplaces call.args)
        in
        let ctx = add_left_constraint_typed_value_list ctx lvs in
        let ctx, e = update_expression e ctx in
        let lvs =
          List.map (fun (v, mp) -> (update_typed_lvalue ctx v, mp)) lvs
        in
        (ctx, Let (Call (lvs, call), e))
    | Assign (lv, lmp, rv, rmp) -> raise Unimplemented
    | Deconstruct (lvs, opt_variant_id, rv, rmp) -> raise Unimplemented
  (* *)
  and update_switch_body (scrut : typed_rvalue) (mp : mplace option)
      (body : switch_body) (ctx : pn_ctx) : pn_ctx * expression =
    let ctx = add_opt_right_constraint mp scrut ctx in

    let ctx, body =
      match body with
      | If (e_true, e_false) ->
          let ctx1, e_true = update_expression e_true ctx in
          let ctx2, e_false = update_expression e_false ctx in
          let ctx = merge_ctxs ctx1 ctx2 in
          (ctx, If (e_true, e_false))
      | SwitchInt (int_ty, branches, otherwise) ->
          let ctx_branches_ls =
            List.map
              (fun (v, br) ->
                let ctx, br = update_expression br ctx in
                (ctx, (v, br)))
              branches
          in
          let ctx, otherwise = update_expression otherwise ctx in
          let ctxs, branches = List.split ctx_branches_ls in
          let ctxs = merge_ctxs_ls ctxs in
          let ctx = merge_ctxs ctx ctxs in
          (ctx, SwitchInt (int_ty, branches, otherwise))
      | Match branches ->
          let ctx_branches_ls =
            List.map
              (fun br ->
                let ctx = add_var_or_dummy_list ctx br.vars in
                let ctx, branch = update_expression br.branch ctx in
                let vars = update_var_or_dummy_list ctx br.vars in
                (ctx, { br with branch; vars }))
              branches
          in
          let ctxs, branches = List.split ctx_branches_ls in
          let ctx = merge_ctxs_ls ctxs in
          (ctx, Match branches)
    in
    (ctx, Switch (scrut, mp, body))
  (* *)
  and update_meta (meta : meta) (e : expression) (ctx : pn_ctx) :
      pn_ctx * expression =
    match meta with
    | Assignment (mp, rvalue) ->
        let ctx = add_right_constraint mp rvalue ctx in
        update_expression e ctx
  in

  let input_names =
    List.filter_map
      (fun (v : var) ->
        match v.basename with None -> None | Some name -> Some (v.id, name))
      def.inputs
  in
  let ctx = VarId.Map.of_list input_names in
  let _, body = update_expression def.body ctx in
  { def with body }

(** Remove the meta-information *)
let remove_meta (def : fun_def) : fun_def =
  let obj =
    object
      inherit [_] map_expression as super

      method! visit_Meta env meta e = super#visit_expression env e
    end
  in
  let body = obj#visit_expression () def.body in
  { def with body }
