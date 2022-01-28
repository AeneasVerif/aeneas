(** The following module defines micro-passes which operate on the pure AST *)

open Errors
open Pure
open TranslateCore

(** The local logger *)
let log = L.pure_micro_passes_log

(** Small utility.

    We sometimes have to insert new fresh variables in a function body, in which
    case we need to make their indices greater than the indices of all the variables
    in the body.
    TODO: things would be simpler if we used a better representation of the
    variables indices...
 *)
let get_expression_min_var_counter (e : expression) : VarId.generator =
  let obj =
    object
      inherit [_] reduce_expression

      method zero _ _ = VarId.zero

      (* TODO: why 2 parameters??? I don't understand what's going on... *)
      method plus id0 id1 _ _ = VarId.max (id0 () ()) (id1 () ())
      (* Get the maximum *)

      method! visit_var _ v mp () = v.id
    end
  in
  let id = obj#visit_expression () e () () in
  VarId.generator_from_incr_id id

type pn_ctx = string VarId.Map.t
(** "pretty-name context": see [compute_pretty_names] *)

(** This function computes pretty names for the variables in the pure AST. It
    relies on the "meta"-place information in the AST to generate naming
    constraints, and then uses those to compute the names.
    
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
   - TODO: inputs and end abstraction...
 *)
let compute_pretty_names (def : fun_def) : fun_def =
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
    VarId.Map.fold (fun id name ctx -> VarId.Map.add id name ctx) ctx0 ctx1
  in
  let merge_ctxs_ls (ctxs : pn_ctx list) : pn_ctx =
    List.fold_left (fun ctx0 ctx1 -> merge_ctxs ctx0 ctx1) VarId.Map.empty ctxs
  in

  let add_var (ctx : pn_ctx) (v : var) : pn_ctx =
    assert (not (VarId.Map.mem v.id ctx));
    match v.basename with
    | None -> ctx
    | Some name -> VarId.Map.add v.id name ctx
  in
  let update_var (ctx : pn_ctx) (v : var) : var =
    match v.basename with
    | Some _ -> v
    | None -> (
        match VarId.Map.find_opt v.id ctx with
        | None -> v
        | Some basename -> { v with basename = Some basename })
  in
  let update_typed_lvalue ctx (lv : typed_lvalue) : typed_lvalue =
    let obj =
      object
        inherit [_] map_typed_lvalue

        method! visit_var _ v = update_var ctx v
      end
    in
    obj#visit_typed_lvalue () lv
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
  let add_left_constraint (lv : typed_lvalue) (ctx : pn_ctx) : pn_ctx =
    let obj =
      object (self)
        inherit [_] reduce_typed_lvalue

        method zero _ = VarId.Map.empty

        method plus ctx0 ctx1 _ = merge_ctxs (ctx0 ()) (ctx1 ())

        method! visit_var _ v () = add_var (self#zero ()) v
      end
    in
    let ctx1 = obj#visit_typed_lvalue () lv () in
    merge_ctxs ctx ctx1
  in

  (* *)
  let rec update_expression (e : expression) (ctx : pn_ctx) :
      pn_ctx * expression =
    match e with
    | Value (v, mp) -> update_value v mp ctx
    | Call call -> update_call call ctx
    | Let (monadic, lb, re, e) -> update_let monadic lb re e ctx
    | Switch (scrut, mp, body) -> update_switch_body scrut mp body ctx
    | Meta (meta, e) -> update_meta meta e ctx
  (* *)
  and update_value (v : typed_rvalue) (mp : mplace option) (ctx : pn_ctx) :
      pn_ctx * expression =
    let ctx = add_opt_right_constraint mp v ctx in
    (ctx, Value (v, mp))
  (* *)
  and update_call (call : call) (ctx : pn_ctx) : pn_ctx * expression =
    let ctx, args =
      List.fold_left_map
        (fun ctx arg -> update_expression arg ctx)
        ctx call.args
    in
    let call = { call with args } in
    (ctx, Call call)
  (* *)
  and update_let (monadic : bool) (lv : typed_lvalue) (re : expression)
      (e : expression) (ctx : pn_ctx) : pn_ctx * expression =
    let ctx = add_left_constraint lv ctx in
    let ctx, re = update_expression re ctx in
    let ctx, e = update_expression e ctx in
    let lv = update_typed_lvalue ctx lv in
    (ctx, Let (monadic, lv, re, e))
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
                let ctx = add_left_constraint br.pat ctx in
                let ctx, branch = update_expression br.branch ctx in
                let pat = update_typed_lvalue ctx br.pat in
                (ctx, { pat; branch }))
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

      method! visit_Meta env _ e = super#visit_expression env e
    end
  in
  let body = obj#visit_expression () def.body in
  { def with body }

(** Inline the useless variable reassignments (a lot of variable assignments
    like `let x = y in ...ÿ` are introduced through the compilation to MIR
    and by the translation, and the variable used on the left is often unnamed *)
let inline_useless_var_reassignments (def : fun_def) : fun_def =
  (* TODO *)
  def

(** Filter the unused assignments (removes the unused variables, filters
    the function calls) *)
let filter_unused_assignments (def : fun_def) : fun_def =
  (* TODO *)
  def

(** Add unit arguments for functions with no arguments, and change their return type. *)
let to_monadic (def : fun_def) : fun_def =
  (* Update the body *)
  let obj =
    object
      inherit [_] map_expression as super

      method! visit_call env call =
        (* If no arguments, introduce unit *)
        if call.args = [] then
          let args = [ Value (SymbolicToPure.unit_rvalue, None) ] in
          { call with args } (* Otherwise: nothing to do *)
        else super#visit_call env call
    end
  in
  let body = obj#visit_expression () def.body in
  let def = { def with body } in

  (* Update the signature: first the input types *)
  let def =
    if def.inputs = [] then (
      assert (def.signature.inputs = []);
      let signature =
        { def.signature with inputs = [ SymbolicToPure.unit_ty ] }
      in
      let var_cnt = get_expression_min_var_counter def.body in
      let id, _ = VarId.fresh var_cnt in
      let var = { id; basename = None; ty = SymbolicToPure.unit_ty } in
      let inputs = [ var ] in
      { def with signature; inputs })
    else def
  in
  (* Then the output type *)
  let output_ty =
    match (def.back_id, def.signature.outputs) with
    | None, [ out_ty ] ->
        (* Forward function: there is always exactly one output *)
        SymbolicToPure.mk_result_ty out_ty
    | Some _, outputs ->
        (* Backward function: we have to group them *)
        SymbolicToPure.mk_result_ty (SymbolicToPure.mk_tuple_ty outputs)
    | _ -> failwith "Unreachable"
  in
  let outputs = [ output_ty ] in
  let signature = { def.signature with outputs } in
  { def with signature }

(** Convert the unit variables to `()` if they are used as right-values or
    `_` if they are used as left values. *)
let unit_vars_to_unit (def : fun_def) : fun_def =
  (* TODO *)
  def

(** Apply all the micro-passes to a function.

    [ctx]: used only for printing.
 *)
let apply_passes_to_def (ctx : trans_ctx) (def : fun_def) : fun_def =
  (* Debug *)
  log#ldebug
    (lazy
      ("PureMicroPasses.apply_passes_to_def: "
      ^ Print.name_to_string def.basename
      ^ " ("
      ^ Print.option_to_string T.RegionGroupId.to_string def.back_id
      ^ ")"));

  (* First, find names for the variables which are unnamed *)
  let def = compute_pretty_names def in
  log#ldebug (lazy ("compute_pretty_name:\n" ^ fun_def_to_string ctx def));

  (* TODO: we might want to leverage more the assignment meta-data, for
   * aggregates for instance. *)

  (* TODO: reorder the branches of the matches/switches *)

  (* The meta-information is now useless: remove it *)
  let def = remove_meta def in
  log#ldebug (lazy ("remove_meta:\n" ^ fun_def_to_string ctx def));

  (* Add unit arguments for functions with no arguments, and change their return type.
   * **Rk.**: from now onwards, the types in the AST are correct (until now,
   * functions had return type `t` where they should have return type `result t`).
   * Also, from now onwards, the outputs list has length 1. x*)
  let def = to_monadic def in
  log#ldebug (lazy ("to_monadic:\n" ^ fun_def_to_string ctx def));

  (* Convert the unit variables to `()` if they are used as right-values or
   * `_` if they are used as left values. *)
  let def = unit_vars_to_unit def in
  log#ldebug (lazy ("unit_vars_to_unit:\n" ^ fun_def_to_string ctx def));

  (* Inline the useless variable reassignments *)
  let def = inline_useless_var_reassignments def in
  log#ldebug
    (lazy ("inline_useless_var_assignments:\n" ^ fun_def_to_string ctx def));

  (* Filter the unused assignments (removes the unused variables, filters
   * the function calls) *)
  let def = filter_unused_assignments def in
  log#ldebug (lazy ("filter_unused_assignments:\n" ^ fun_def_to_string ctx def));

  (* TODO: deconstruct the monadic bindings into matches *)

  (* We are done *)
  def

let apply_passes_to_pure_fun_translation (ctx : trans_ctx)
    (trans : pure_fun_translation) : pure_fun_translation =
  let forward, backwards = trans in
  let forward = apply_passes_to_def ctx forward in
  let backwards = List.map (apply_passes_to_def ctx) backwards in
  (forward, backwards)
