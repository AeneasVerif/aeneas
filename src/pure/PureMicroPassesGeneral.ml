open Pure
open PureUtils
open TranslateCore
open PureMicroPassesBase

(** Remove the meta-information *)
let remove_meta (ctx : ctx) (def : fun_decl) : fun_decl =
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id PureUtils.remove_meta def

(** Introduce calls to [massert] (monadic assertion).

    The pattern below is very frequent especially as it is introduced by the
    [assert!] macro. We perform the following simplification:
    {[
      if b then e else fail ~~>massert b;
      e
    ]} *)
let intro_massert_visitor (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  let mk_massert scrut =
    let massert =
      Qualif { id = FunOrOp (Fun (Pure Assert)); generics = empty_generic_args }
    in
    let massert =
      { e = massert; ty = mk_arrow mk_bool_ty (mk_result_ty mk_unit_ty) }
    in
    [%add_loc] mk_app span massert scrut
  in
  object
    inherit [_] map_expr as super

    method! visit_Switch env scrut switch =
      match switch with
      | If (e_true, e_false) ->
          if is_fail_panic e_false.e then begin
            (* Introduce a call to [massert] *)
            let massert = mk_massert scrut in
            (* Introduce the let-binding *)
            let monadic = true in
            let pat = mk_ignored_pat mk_unit_ty in
            super#visit_Let env monadic pat massert e_true
          end
          else if is_fail_panic e_true.e then
            (* Introduce a call to [massert] (we need to negate the scrutinee) *)
            let scrut = mk_bool_not scrut in
            let massert = mk_massert scrut in
            (* Introduce the let-binding *)
            let monadic = true in
            let pat = mk_ignored_pat mk_unit_ty in
            super#visit_Let env monadic pat massert e_false
          else super#visit_Switch env scrut switch
      | _ -> super#visit_Switch env scrut switch
  end

let intro_massert = lift_expr_map_visitor intro_massert_visitor

(** Simplify the let-bindings which bind the fields of structures.

    For instance, given the following structure definition:
    {[
      struct Struct {
        x : u32,
        y : u32,
      }
    ]}

    We perform the following transformation:
    {[
      let StructCons x y = s in
      ...

       ~~>

      let x = s.x in
      let y = s.y in
      ...
    ]}

    Of course, this is not always possible depending on the backend. Also,
    recursive structures, and more specifically structures mutually recursive
    with inductives, are usually not supported. We define such recursive
    structures as inductives, in which case it is not always possible to use a
    notation for the field projections.

    The subsequent passes, in particular the ones which inline the useless
    assignments, simplify this further. *)
let simplify_decompose_struct_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expr as super

    method! visit_Let env (monadic : bool) (lv : tpat) (scrutinee : texpr)
        (next : texpr) =
      match (lv.pat, lv.ty) with
      | PAdt adt_pat, TAdt (TAdtId adt_id, generics) ->
          (* Detect if this is an enumeration or not *)
          let tdef =
            TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
          in
          let is_enum = TypesUtils.type_decl_is_enum tdef in
          (* We deconstruct the ADT with a single let-binding in two situations:
               - if the ADT is an enumeration (which must have exactly one branch)
               - if we forbid using field projectors
            *)
          let use_let_with_cons =
            is_enum
            || !Config.dont_use_field_projectors
            (* Also, there is a special case when the ADT is to be extracted as
                 a tuple, because it is a structure with unnamed fields. Some backends
                 like Lean have projectors for tuples (like so: `x.3`), but others
                 like Coq don't, in which case we have to deconstruct the whole ADT
                 at once (`let (a, b, c) = x in`) *)
            || TypesUtils.type_decl_from_type_id_is_tuple_struct
                 ctx.trans_ctx.type_ctx.type_infos (T.TAdtId adt_id)
               && not !Config.use_tuple_projectors
          in
          if use_let_with_cons then
            super#visit_Let env monadic lv scrutinee next
          else
            (* This is not an enumeration: introduce let-bindings for every
                 field.
                 We use the [dest] variable in order not to have to recompute
                 the type of the result of the projection... *)
            let gen_field_proj (field_id : FieldId.id) (dest : tpat) : texpr =
              let proj_kind = { adt_id = TAdtId adt_id; field_id } in
              let qualif = { id = Proj proj_kind; generics } in
              let proj_e = Qualif qualif in
              let proj_ty = mk_arrow scrutinee.ty dest.ty in
              let proj = { e = proj_e; ty = proj_ty } in
              [%add_loc] mk_app span proj scrutinee
            in
            let id_var_pairs =
              FieldId.mapi (fun fid v -> (fid, v)) adt_pat.fields
            in
            let monadic = false in
            let e =
              List.fold_right
                (fun (fid, pat) e ->
                  let field_proj = gen_field_proj fid pat in
                  mk_opened_let monadic pat field_proj e)
                id_var_pairs next
            in
            (super#visit_texpr env e).e
      | _ -> super#visit_Let env monadic lv scrutinee next
  end

let simplify_decompose_struct =
  lift_expr_map_visitor simplify_decompose_struct_visitor

(** Introduce the special structure create/update expressions.

    Upon generating the pure code, we introduce structure values by using the
    structure constructors:
    {[
      Cons x0 ... xn
    ]}

    This micro-pass turns those into expressions which use structure syntax:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 y ~~> { x with f2 = y }
    ]}

    Note however that we do not apply this transformation if the structure is to
    be extracted as a tuple. *)
let intro_struct_updates_visitor (ctx : ctx) (def : fun_decl) =
  let update_app visit_texpr (e : texpr) =
    [%ldebug "- e:\n" ^ texpr_to_string ctx e];
    let app, args = destruct_apps e in
    [%ldebug
      "- app: " ^ texpr_to_string ctx app ^ "\n- app.ty: "
      ^ ty_to_string ctx app.ty ^ "\n- args:\n"
      ^ String.concat "\n" (List.map (texpr_to_string ctx) args)];
    let ignore () =
      let app = visit_texpr app in
      let args = List.map visit_texpr args in
      [%ldebug
        "Ignoring and recomposing the application:\n" ^ "- app': "
        ^ texpr_to_string ctx app ^ "\n- app'.ty: " ^ ty_to_string ctx app.ty
        ^ "\n- args':\n"
        ^ String.concat "\n\n" (List.map (texpr_to_string ctx) args)];
      [%add_loc] mk_apps def.item_meta.span app args
    in
    match app.e with
    | Qualif
        {
          id = AdtCons { adt_id = TAdtId adt_id; variant_id = None };
          generics = _;
        } ->
        (* Lookup the def *)
        let decl =
          TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
        in
        (* Check if the def will be extracted as a tuple *)
        if
          TypesUtils.type_decl_from_decl_id_is_tuple_struct
            ctx.trans_ctx.type_ctx.type_infos adt_id
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
                  ctx.trans_ctx.type_ctx.type_decls_groups
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
                FieldId.mapi (fun fid fe -> (fid, visit_texpr fe)) args
              in
              let ne = { struct_id; init; updates } in
              let nty = e.ty in
              { e = StructUpdate ne; ty = nty }
            else ignore ()
          else ignore ()
    | _ -> ignore ()
  in

  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env (e : texpr) =
      match e.e with
      | App _ -> update_app (self#visit_texpr env) e
      | _ -> super#visit_texpr env e
  end

let intro_struct_updates = lift_expr_map_visitor intro_struct_updates_visitor

(** This performs the following simplifications:
    {[
      fun x1 ... xn => g x1 ... xn
      ...
        ~~>
      g
      ...
    ]} *)
let simplify_lambdas_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env e =
      match e.e with
      | Lambda _ ->
          (* Arrow case *)
          let pats, e = raw_destruct_lambdas e in
          let g, args = destruct_apps e in
          let default () =
            let e = self#visit_texpr env e in
            mk_opened_lambdas span pats e
          in
          if List.length pats = List.length args then
            (* Check if the arguments are exactly the lambdas *)
            let check_pat_arg ((pat, arg) : tpat * texpr) =
              match (pat.pat, arg.e) with
              | POpen (v, _), FVar vid -> v.id = vid
              | _ -> false
            in
            if List.for_all check_pat_arg (List.combine pats args) then
              (* Check if the application is a tuple constructor
                 or will be extracted as a projector: if
                 it is, keep the lambdas, otherwise simplify *)
              let simplify =
                match g.e with
                | Qualif { id = AdtCons { adt_id; _ }; _ } ->
                    not
                      (PureUtils.type_decl_from_type_id_is_tuple_struct
                         ctx.trans_ctx.type_ctx.type_infos adt_id)
                | Qualif { id = Proj _; _ } -> false
                | _ -> true
              in
              if simplify then self#visit_texpr env g else default ()
            else default ()
          else default ()
      | _ -> super#visit_texpr env e
  end

let simplify_lambdas = lift_expr_map_visitor simplify_lambdas_visitor

(** Simplify the let-bindings by performing the following rewritings:

    Move inner let-bindings outside. This is especially useful to simplify the
    backward expressions, when we merge the forward/backward functions. Note
    that the rule is also applied with monadic let-bindings.
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

    Simplify identity functions:
    {[
      let f := fun x => x
      ...
      f x
        ~~>
      let f := fun x => x
      ...
      x
    ]} *)
let simplify_let_bindings_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic lv rv next =
      [%ldebug "Visiting let:\n" ^ let_to_string ctx monadic lv rv next];
      match rv.e with
      | Let (rmonadic, rlv, rrv, rnext) ->
          [%ldebug "Case: inner let"];
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
                          adt_id = TBuiltin TResult;
                          variant_id = Some variant_id;
                        };
                    generics = _;
                  };
              ty = _;
            },
            x ) ->
          [%ldebug "Case: result"];
          (* return/fail case *)
          if variant_id = result_ok_id then
            (* Return case - note that the simplification we just perform
                 might have unlocked the tuple simplification below *)
            self#visit_Let env false lv x next
          else if variant_id = result_fail_id then
            (* Fail case *)
            self#visit_expr env rv.e
          else [%craise] def.item_meta.span "Unexpected"
      | App _ ->
          [%ldebug "Case: app"];
          (* This might be the tuple case *)
          if not monadic then
            match (opt_dest_struct_pat lv, opt_dest_tuple_texpr rv) with
            | Some pats, Some vals ->
                (* Tuple case *)
                let pat_vals = List.combine pats vals in
                let e =
                  List.fold_right
                    (fun (pat, v) next -> mk_opened_let false pat v next)
                    pat_vals next
                in
                super#visit_expr env e.e
            | _ -> super#visit_Let env monadic lv rv next
          else super#visit_Let env monadic lv rv next
      | Lambda (pat, body) ->
          [%ldebug "Case: lambda"];
          (* Simplify:
             {[
               let f := fun x => x
               ...
               f x
                 ~~>
               let f := fun x => x
               ...
               x
             ]}
          *)
          begin
            match (pat.pat, body.e) with
            | POpen (fv, _), FVar fid when fv.id = fid ->
                [%ldebug "Simplifying the lambda"];
                let next =
                  let env = FVarId.Set.add fid env in
                  self#visit_texpr env next
                in
                (mk_opened_let monadic lv rv next).e
            | _ ->
                [%ldebug "Not simplifying the lambda"];
                super#visit_Let env monadic lv rv next
          end
      | _ -> super#visit_Let env monadic lv rv next

    method! visit_App env f arg =
      [%ldebug
        "Visiting app: " ^ texpr_to_string ctx ([%add_loc] mk_app span f arg)];
      (* Check if this is the identity case *)
      match f.e with
      | FVar fid when FVarId.Set.mem fid env -> arg.e
      | _ -> super#visit_App env f arg
  end

let simplify_let_bindings =
  lift_expr_map_visitor_with_state simplify_let_bindings_visitor
    FVarId.Set.empty

(** Remove the duplicated function calls.

    We naturally write code which contains several times the same expression.
    For instance:
    {[
      a[i + j] = b[i + j] + 1;
        ^^^^^      ^^^^^
    ]}

    This is an issue in the generated model, because we then have to reason
    several times about the same function call. For instance, below, we have to
    prove *twice* that [i + j] is in bounds, and the proof context grows bigger
    than necessary.
    {[
      let i1 <- i + j (* *)
      let x1 <- array_index b i1
      let x2 <- x1 + 1
      let i2 <- i + j (* duplicates the expression above *)
      let a1 = array_update a i2 x2
    ]}

    This micro pass removes those duplicate function calls.

    TODO: this micro-pass will not be sound anymore once we allow stateful
    (backward) functions. *)
let simplify_duplicate_calls_visitor (_ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic pat bound next =
      let bound = self#visit_texpr env bound in
      (* Register the function call if the pattern doesn't contain ignored
         variables *)
      let env =
        let factor =
          monadic
          ||
          match destruct_apps bound with
          | { e = FVar _; _ }, _ :: _ ->
              (* May be a backward function call *)
              true
          | _ -> false
        in
        if factor then
          match tpat_to_texpr def.item_meta.span pat with
          | None -> env
          | Some pat_expr -> TExprMap.add bound (monadic, pat_expr) env
        else env
      in
      let next = self#visit_texpr env next in
      Let (monadic, pat, bound, next)

    method! visit_texpr env e =
      let e =
        match TExprMap.find_opt e env with
        | None -> e
        | Some (monadic, e) ->
            if monadic then mk_result_ok_texpr def.item_meta.span e else e
      in
      super#visit_texpr env e
  end

let simplify_duplicate_calls =
  lift_expr_map_visitor_with_state simplify_duplicate_calls_visitor
    TExprMap.empty

(** A helper predicate *)
let lift_unop (unop : unop) : bool =
  match unop with
  | Not None -> false
  | Not (Some _) | Neg _ | Cast _ | ArrayToSlice -> true

(** A helper predicate *)
let inline_unop unop = not (lift_unop unop)

(** A helper predicate *)
let lift_binop (binop : binop) : bool =
  match binop with
  | Eq _ | Lt _ | Le _ | Ne _ | Ge _ | Gt _ -> false
  | BitXor _
  | BitAnd _
  | BitOr _
  | Div _
  | Rem _
  | Add _
  | Sub _
  | Mul _
  | AddChecked _
  | SubChecked _
  | MulChecked _
  | Shl _
  | Shr _
  | Cmp _ -> true

(** A helper predicate *)
let inline_binop binop = not (lift_binop binop)

(** A helper predicate *)
let lift_fun (ctx : ctx) (fun_id : fun_id) : bool =
  (* Lookup if the function is builtin: we only lift builtin functions
     which were explictly marked to be lifted. *)
  match fun_id with
  | FromLlbc (FunId (FRegular fid), _) -> begin
      match FunDeclId.Map.find_opt fid ctx.fun_decls with
      | None -> false
      | Some def -> (
          match def.builtin_info with
          | None -> false
          | Some info -> info.lift)
    end
  | FromLlbc (FunId (FBuiltin (ArrayToSliceShared | ArrayToSliceMut)), _) ->
      true
  | _ -> false

(** A helper predicate *)
let inline_fun (_ : fun_id) : bool = false

type inline_env = { subst : texpr FVarId.Map.t; loop_back_funs : FVarId.Set.t }

let empty_inline_env : inline_env =
  { subst = FVarId.Map.empty; loop_back_funs = FVarId.Set.empty }

(** Inline the useless variable (re-)assignments:

    A lot of intermediate variable assignments are introduced through the
    compilation to MIR and by the translation itself (and the variable used on
    the left is often unnamed).

    Note that many of them are just variable "reassignments":
    [let x = y in ...]. Some others come from ??

    TODO: how do we call that when we introduce intermediate variable
    assignments for the arguments of a function call?

    [inline_named]: if [true], inline all the assignments of the form
    [let VAR = VAR in ...], otherwise inline only the ones where the variable on
    the left is anonymous.

    [inline_pure]: if [true], inline all the pure assignments where the variable
    on the left is anonymous, but the assignments where the r-expression is a
    function call (i.e.: ADT constructions, etc.), except certain cases of
    function calls.

    [inline_identity]: if [true], inline the identity functions (i.e., lambda
    functions of the shape [fun x -> x]).

    [inline_loop_back_calls]: inline calls to loop backward functions. This is
    useful to trigger simplifications, for instance in [loop_to_recursive].

    TODO: we have a smallish issue which is that rvalues should be merged with
    expressions... For now, this forces us to substitute whenever we can, but
    leave the let-bindings where they are, and eliminated them in a subsequent
    pass (if they are useless). *)
let inline_useless_var_assignments_visitor ~(inline_named : bool)
    ~(inline_const : bool) ~(inline_pure : bool) ~(inline_identity : bool)
    ?(inline_loop_back_calls : bool = false) (ctx : ctx) (def : fun_decl) =
  object (self)
    inherit [_] map_expr as super

    (** Visit the let-bindings to filter the useless ones (and update the
        substitution map while doing so *)
    method! visit_Let (env : inline_env) monadic lv re e =
      (* In order to filter, we need to check first that:
         - the let-binding is not monadic
         - the left-value is a variable

         We also inline if the binding decomposes a structure that is to be
         extracted as a tuple, and the right value is a variable.
      *)
      match (monadic, lv.pat) with
      | false, POpen (lv_var, _) ->
          (* We can filter if: 1. *)
          let filter_pure =
            (* 1.1. the left variable is unnamed or [inline_named] is true *)
            let filter_left =
              match (inline_named, lv_var.basename) with
              | true, _ | _, None -> true
              | _ -> false
            in
            (* And either:
                 1.2.1 the right-expression is a variable, a global or a const generic var *)
            let var_or_global = is_fvar re || is_cvar re || is_global re in
            (* Or:
                 1.2.2 the right-expression is a constant-value and we inline constant values,
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
                 1.2.3 the right-expression is an ADT value, a projection or a
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
                  | FunOrOp (Unop unop) -> inline_unop unop
                  | FunOrOp (Binop binop) -> inline_binop binop
                  | FunOrOp (Fun fun_id) -> inline_fun fun_id
                  | _ -> false)
              | StructUpdate _ -> true (* ADT constructor *)
              | _ -> false
            in

            (* Or:
               1.3 the right-expression is a call to a loop backward function,
               and [inline_loop_back_calls] is [true] *)
            let back_call =
              inline_loop_back_calls
              &&
              let f, _ = destruct_apps re in
              match f.e with
              | FVar fid -> FVarId.Set.mem fid env.loop_back_funs
              | _ -> false
            in

            filter_left && (var_or_global || const_re || pure_re || back_call)
          in

          (* Or if: 2. the let-binding bounds the identity function *)
          let filter_id =
            inline_identity
            &&
            match re.e with
            | Lambda ({ pat = POpen (v0, _); _ }, { e = FVar v1; _ }) ->
                v0.id = v1
            | _ -> false
          in

          let filter = filter_pure || filter_id in

          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpr env re in
          (* Update the substitution environment *)
          let env =
            if filter then
              { env with subst = FVarId.Map.add lv_var.id re env.subst }
            else env
          in
          (* Update the next expression *)
          let e = self#visit_texpr env e in
          (* Reconstruct the [let], only if the binding is not filtered *)
          if filter then e.e else Let (monadic, lv, re, e)
      | ( false,
          PAdt
            {
              variant_id = None;
              fields = [ { pat = POpen (lv_var, _); ty = _ } ];
            } ) ->
          (* Second case: we deconstruct a structure with one field that we will
               extract as tuple. *)
          let adt_id, _ = PureUtils.ty_as_adt def.item_meta.span re.ty in
          (* Update the rhs (we may perform substitutions inside, and it is
           * better to do them *before* we inline it *)
          let re = self#visit_texpr env re in
          if
            PureUtils.is_fvar re
            && type_decl_from_type_id_is_tuple_struct
                 ctx.trans_ctx.type_ctx.type_infos adt_id
          then
            (* Update the substitution environment *)
            let env =
              { env with subst = FVarId.Map.add lv_var.id re env.subst }
            in
            (* Update the next expression *)
            let e = self#visit_texpr env e in
            (* We filter the [let], and thus do not reconstruct it *)
            e.e
          else (* Nothing to do *)
            super#visit_Let env monadic lv re e
      | _ -> super#visit_Let env monadic lv re e

    (** Substitute the variables *)
    method! visit_FVar (env : inline_env) (vid : FVarId.id) =
      match FVarId.Map.find_opt vid env.subst with
      | None -> (* No substitution *) super#visit_FVar env vid
      | Some ne ->
          (* Substitute - note that we need to reexplore, because
           * there may be stacked substitutions, if we have:
           * var0 --> var1
           * var1 --> var2.
           *)
          self#visit_expr env ne.e

    method! visit_loop_body (env : inline_env) (body : loop_body) =
      (* Register the loop inputs.

         TODO: for now we register all the inputs, but we should only register
         the backward functions. *)
      let { inputs; loop_body } = body in
      let fvars = tpats_get_fvars inputs in
      let env =
        { env with loop_back_funs = FVarId.Set.union env.loop_back_funs fvars }
      in
      { inputs; loop_body = self#visit_texpr env loop_body }
  end

let inline_useless_var_assignments ~inline_named ~inline_const ~inline_pure
    ~inline_identity ?(inline_loop_back_calls = false) =
  lift_expr_map_visitor_with_state
    (inline_useless_var_assignments_visitor ~inline_named ~inline_const
       ~inline_pure ~inline_identity ~inline_loop_back_calls)
    empty_inline_env

(** Simplify let-bindings which bind tuples and which contain ignored patterns.

    Ex.:
    {[
      let (_, x) = if b then (true, 1) else (false, 0) in …

          ~>

      let x = if b then 1 else 0 in …
    ]} *)
let simplify_let_tuple span (ctx : ctx) (monadic : bool) (pat : tpat)
    (bound : texpr) : tpat * texpr * bool =
  let span = span in
  (* We attempt to filter only if:
     - the pattern is a tuple containing ignored patterns
     - the bound expression is "non trivial" (for instance, not just a
       function call) *)
  let pats = opt_destruct_tuple_tpat span pat in
  let has_ignored_pats =
    match pats with
    | None -> false
    | Some pats -> List.exists is_ignored_pat pats
  in
  let bound_non_trivial =
    match bound.e with
    | Lambda _ | Let _ | Switch _ -> true
    | _ -> false
  in

  if has_ignored_pats && bound_non_trivial then (
    (* Update *)
    let pats = Option.get pats in
    let keep = List.map (fun p -> not (is_ignored_pat p)) pats in
    [%ldebug "keep: " ^ Print.list_to_string Print.bool_to_string keep];
    let tys = List.map (fun (p : tpat) -> p.ty) pats in
    let num_nonfiltered_pats = List.length pats in
    let pats = List.filter (fun p -> not (is_ignored_pat p)) pats in
    let pats = mk_simpl_tuple_pat pats in
    let new_ty = if monadic then mk_result_ty pats.ty else pats.ty in

    (* Update an expression to filter its outputs *)
    let rec update (e : texpr) : texpr =
      [%ldebug "e:\n" ^ texpr_to_string ctx e];
      match e.e with
      | FVar _ | App _ | Loop _ | Const _ ->
          [%ldebug "expression is FVar, App, Loop, Const"];
          let tuple_size = get_tuple_size e in
          [%sanity_check] span
            (tuple_size = None || tuple_size = Some num_nonfiltered_pats);
          (* If this is a panic/break/continue, we do nothing *)
          if is_result_fail e || is_loop_result_fail_break_continue e then (
            [%ldebug "expression is a fail, break or a continue"];
            let f, args = destruct_qualif_apps e in
            [%add_loc] mk_qualif_apps span f args new_ty)
          else if is_result_ok e then (
            (* If this is an [ok] we update the inner expression *)
            [%ldebug "expression is an ok"];
            let f, args = destruct_qualif_apps e in
            match args with
            | [ x ] ->
                let x = update x in
                [%add_loc] mk_qualif_apps span f [ x ] new_ty
            | _ -> [%internal_error] span
            (* If this is a tuple we filter the arguments *))
          else if tuple_size = Some num_nonfiltered_pats then (
            [%ldebug "expression is a tuple"];
            let args = [%add_loc] destruct_tuple_texpr span e in
            [%ldebug
              "args:\n"
              ^ Print.list_to_string ~sep:"\n" (texpr_to_string ctx) args];
            let args =
              List.filter_map
                (fun (keep, arg) -> if keep then Some arg else None)
                (List.combine keep args)
            in
            mk_simpl_tuple_texpr span args)
          else (
            [%ldebug "expression is of an unknown kind"];
            (* We need to introduce an intermediate let-binding *)
            let pats, out =
              List.split
                (List.map
                   (fun (keep, ty) ->
                     if keep then
                       let fv = mk_fresh_fvar ctx ty in
                       (mk_tpat_from_fvar None fv, Some (mk_texpr_from_fvar fv))
                     else (mk_ignored_pat ty, None))
                   (List.combine keep tys))
            in
            let pats = mk_simpl_tuple_pat pats in
            let out = List.filter_map (fun x -> x) out in
            let out = mk_simpl_tuple_texpr span out in

            let monadic = is_result_ty e.ty in
            let out = if monadic then mk_result_ok_texpr span out else out in
            mk_opened_let monadic pats e out)
      | BVar _ | CVar _ | Qualif _ | StructUpdate _ -> [%internal_error] span
      | Lambda (pat, inner) -> mk_opened_lambda span pat (update inner)
      | Let (monadic, pat, bound, next) ->
          mk_opened_let monadic pat bound (update next)
      | Switch (scrut, body) ->
          let switch =
            match body with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                let branches =
                  List.map
                    (fun (br : match_branch) ->
                      { br with branch = update br.branch })
                    branches
                in
                Match branches
          in
          let ty = get_switch_body_ty switch in
          { e = Switch (scrut, switch); ty }
      | Meta (m, inner) -> mk_emeta m (update inner)
      | EError _ -> { e with ty = new_ty }
    in

    let bound = update bound in
    (pats, bound, true))
  else (pat, bound, false)

(** Filter the useless assignments (removes the useless variables, filters the
    function calls) *)
let filter_useless (ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in
  (* We first need a transformation on *left-values*, which filters the useless
     variables and tells us whether the value contains any variable which has
     not been replaced by [_] (in which case we need to keep the assignment,
     etc.).

     This is implemented as a map-reduce.

     Returns: ( filtered_left_value, *all_dummies* )

     [all_dummies]:
     If the returned boolean is true, it means that all the variables appearing
     in the filtered left-value are *dummies* (meaning that if this left-value
     appears at the left of a let-binding, this binding might potentially be
     removed).
  *)
  let lv_visitor =
    object
      inherit [_] mapreduce_tpat
      method zero _ = true
      method plus b0 b1 _ = b0 () && b1 ()

      method! visit_POpen env v mp =
        if FVarId.Set.mem v.id env then (POpen (v, mp), fun _ -> false)
        else (PIgnored, fun _ -> true)

      method! visit_PBound _ _ _ = [%internal_error] span
    end
  in
  let filter_tpat (used_vars : FVarId.Set.t) (lv : tpat) : tpat * bool =
    let lv, all_dummies = lv_visitor#visit_tpat used_vars lv in
    (lv, all_dummies ())
  in

  (* We then implement the transformation on *expressions* through a mapreduce.
     Note that the transformation is bottom-up.
     The map filters the useless assignments, the reduce computes the set of
     used variables. *)
  let expr_visitor =
    object (self)
      inherit [_] mapreduce_expr as super
      method zero _ = FVarId.Set.empty
      method plus s0 s1 _ = FVarId.Set.union (s0 ()) (s1 ())

      (** Whenever we visit a variable, we need to register the used variable *)
      method! visit_FVar _ vid = (FVar vid, fun _ -> FVarId.Set.singleton vid)

      method! visit_expr env e =
        match e with
        | BVar _ -> [%internal_error] span
        | FVar _ | CVar _ | Const _ | App _ | Qualif _
        | Meta (_, _)
        | StructUpdate _ | Lambda _
        | EError (_, _) -> super#visit_expr env e
        | Switch (scrut, switch) -> (
            match switch with
            | If (_, _) -> super#visit_expr env e
            | Match branches ->
                (* Simplify the branches *)
                let simplify_branch (br : match_branch) =
                  (* Compute the set of values used inside the branch *)
                  let branch, used = self#visit_texpr env br.branch in
                  (* Simplify the pattern *)
                  let pat, _ = filter_tpat (used ()) br.pat in
                  { pat; branch }
                in
                super#visit_expr env
                  (Switch (scrut, Match (List.map simplify_branch branches))))
        | Let (monadic, lv, re, e) ->
            (* Compute the set of values used in the next expression *)
            let e, used = self#visit_texpr env e in
            let used = used () in
            (* Filter the left values *)
            let lv, all_dummies = filter_tpat used lv in
            (* Small utility - called if we can't filter the let-binding *)
            let dont_filter () =
              let re, used_re = self#visit_texpr env re in
              let used = FVarId.Set.union used (used_re ()) in
              (* Simplify the left pattern if it only contains ignored variables *)
              let lv =
                if all_dummies then
                  let ty = lv.ty in
                  let pat = PIgnored in
                  { pat; ty }
                else lv
              in
              (* If there are ignored patterns, attempt to simplify
                 the binding and the right expression. *)
              let lv, re, updated = simplify_let_tuple span ctx monadic lv re in

              (* We may need to revisited the bound expression if we modified it:
                 some values may now be unused. *)
              let re = if updated then fst (self#visit_texpr env re) else re in

              (* Put everything together *)
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
            let {
              loop_id = _;
              span = _;
              output_tys = _;
              num_output_values = _;
              inputs;
              num_input_conts = _;
              loop_body;
              to_rec = _;
            } =
              loop
            in
            let loop_body, used =
              let { inputs; loop_body } = loop_body in
              let loop_body, used = self#visit_texpr () loop_body in
              (({ inputs; loop_body } : loop_body), used)
            in
            let used, inputs =
              List.fold_left_map
                (fun used input ->
                  let input, used' = self#visit_texpr () input in
                  (self#plus used used', input))
                used inputs
            in
            (Loop { loop with inputs; loop_body }, used)
    end
    (* We filter only inside of transparent (i.e., non-opaque) definitions *)
  in
  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body ->
      (* Visit the body *)
      let body_exp, used_vars = expr_visitor#visit_texpr () body.body in
      (* Visit the parameters - TODO: update: we can filter only if the definition
         is not recursive (otherwise it might mess up with the decrease clauses:
         the decrease clauses uses all the inputs given to the function, if some
         inputs are replaced by '_' we can't give it to the function used in the
         decreases clause).
         For now we deactivate the filtering. *)
      let used_vars = used_vars () in
      let inputs =
        if false then
          List.map (fun lv -> fst (filter_tpat used_vars lv)) body.inputs
        else body.inputs
      in
      (* Return *)
      { body = body_exp; inputs })
    def

(** Simplify let bindings which bind expressions containing a branching.

    This micro-pass does transformations of the following kind:
    {[
      let (b', x) := if b then (true, 1) else (false, 0) in
      ...

        ~~>

      let x := if b then 1 else 0 in
      let b' := b in // inlined afterwards by [inline_useless_var_assignments]
      ...
    ]}

    Expressions like the above one are often introduced when merging contexts
    after a branching. *)
let simplify_let_branching (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  (* Helper to compute the output *)
  let simplify_aux (monadic : bool) (pats : tpat list) (bound : texpr)
      (next : texpr) : tpat * texpr * texpr =
    let num_outs = List.length pats in
    (* We will accumulate the outputs we find in this array *)
    let outs = Array.init num_outs (fun _ -> []) in
    let push_to_outs i el =
      Array.set outs i (TExprSet.of_list el :: Array.get outs i)
    in

    (* Compute the set of variables which are bound inside the bound expression
       (we will ignored those, as they were not introduced before) *)
    let bound_fvars = texpr_get_bound_fvars bound in

    (* Small helper.

       When exploring expressions, we keep track of the variables we branched
       upon together with the values they were expanded to, whenever we dive into a branch.

       For instance:
       {[
         if b then
           // here we remember: b -> true
           ...
         else
           // here we remember: b -> false
           ...
       ]}

       This small helper allows, given an expression [e], to retrieve the
       list of variables that it may be equal to, in the current branch.
       For instance, in the branch [then] of the example above, [true] might
       be equal to [b]. *)
    let get_equal_values (branchings : fvar_id list TExprMap.t) (e : texpr) :
        texpr list =
      (* For now we do something simple: we simply check if there is
         exactly [e] which appears as a key in the map. We could recursively
         explore the sub-expressions of [e] instead. *)
      match TExprMap.find_opt e branchings with
      | None -> []
      | Some el -> List.map (fun id -> ({ e = FVar id; ty = e.ty } : texpr)) el
    in

    (* When we can't compute the exact list of values an expression evaluates
           to, we store an empty set of possible values for all the outputs, meaning
           we will not simplify anything. *)
    let push_empty_possibilities () =
      for i = 0 to num_outs - 1 do
        push_to_outs i []
      done
    in

    (* Is this expression a free variable which was bound before (we ignore
       the variables bound inside the bound expression of the let, as we
       can't refer to them from outside the let-binding) *)
    let is_bound_before_fvar (e : texpr) : bool =
      match e.e with
      | FVar id -> not (FVarId.Set.mem id bound_fvars)
      | _ -> false
    in

    (* Explore the bound expression. *)
    let rec explore (branchings : fvar_id list TExprMap.t) (e : texpr) : unit =
      match e.e with
      | FVar _ | CVar _ | Const _ | StructUpdate _ | Qualif _ | Lambda _ ->
          [%sanity_check] span (num_outs = 1);
          push_to_outs 0 (e :: get_equal_values branchings e)
      | BVar _ -> [%internal_error] span
      | App _ ->
          (* *)
          if is_result_fail e || is_loop_result_fail_break_continue e then ()
          else if is_result_ok e then
            let _, args = destruct_apps e in
            match args with
            | [ x ] -> explore branchings x
            | _ -> [%internal_error] span
          else if get_tuple_size e = Some num_outs then
            let args = [%add_loc] destruct_tuple_texpr span e in
            List.iteri
              (fun i arg ->
                let vl = get_equal_values branchings arg in
                push_to_outs i (arg :: vl))
              args
          else push_empty_possibilities ()
      | Let (_, _, _, next) -> explore branchings next
      | Switch (scrut, switch) -> (
          if
            (* Remember the branching, in case we branch over a variable that
               we shouldn't ignore *)
            is_bound_before_fvar scrut
          then
            let scrut_id = as_fvar span scrut in
            match switch with
            | If (e0, e1) ->
                let branchings0 =
                  TExprMap.add_to_list mk_true scrut_id branchings
                in
                explore branchings0 e0;
                let branchings1 =
                  TExprMap.add_to_list mk_false scrut_id branchings
                in
                explore branchings1 e1
            | Match branches ->
                List.iter
                  (fun ({ pat; branch } : match_branch) ->
                    let branchings =
                      match tpat_to_texpr span pat with
                      | None -> branchings
                      | Some e -> TExprMap.add_to_list e scrut_id branchings
                    in
                    explore branchings branch)
                  branches
          else
            match switch with
            | If (e0, e1) ->
                explore branchings e0;
                explore branchings e1
            | Match branches ->
                List.iter
                  (fun ({ pat = _; branch } : match_branch) ->
                    explore branchings branch)
                  branches)
      | Loop _ -> push_empty_possibilities ()
      | Meta (_, e) -> explore branchings e
      | EError _ -> ()
    in
    explore TExprMap.empty bound;

    (* Check if some of the outputs can be mapped to the same value.
       We simply check if the potential outputs have a non empty intersection
       for all the branches. *)
    let possible_outputs =
      Array.map
        (fun (ls : TExprSet.t list) ->
          match ls with
          | [] -> TExprSet.empty
          | s :: ls -> List.fold_left (fun s s' -> TExprSet.inter s s') s ls)
        outs
    in
    [%ldebug
      "possible_outputs:\n"
      ^ String.concat ",\n\n"
          ((List.map (fun s ->
                "["
                ^ String.concat ", "
                    (List.map (texpr_to_string ctx) (TExprSet.to_list s))
                ^ "]"))
             (Array.to_list possible_outputs))];

    (* Pick outputs whenever possible *)
    let keep, outputs =
      List.split
        (List.map
           (fun s ->
             (* For now, we simply pick the first output which works *)
             match TExprSet.to_list s with
             | [] -> (true, None)
             | x :: _ -> (false, Some x))
           (Array.to_list possible_outputs))
    in
    let apply_update = List.exists Option.is_some outputs in
    [%ldebug
      "chosen outputs:\n"
      ^ String.concat ",\n\n"
          (List.map (Print.option_to_string (texpr_to_string ctx)) outputs)];

    let new_ty =
      mk_simpl_tuple_ty
        (List.map
           (fun (e : texpr) -> e.ty)
           (List.filter_map (fun x -> x) outputs))
    in
    let new_ty = if monadic then mk_result_ty new_ty else new_ty in

    (* Update the bound expression *)
    let rec update (e : texpr) : texpr =
      [%ldebug "About to update expression:\n" ^ texpr_to_string ctx e];
      match e.e with
      | FVar _ | CVar _ | Const _ | StructUpdate _ | Qualif _ | Lambda _ -> (
          [%sanity_check] span (num_outs = 1);
          match List.hd outputs with
          | None -> e
          | Some e -> e)
      | BVar _ -> [%internal_error] span
      | App _ ->
          [%ldebug "is app"];
          (* *)
          let tuple_size = get_tuple_size e in
          [%sanity_check] span (tuple_size = None || tuple_size = Some num_outs);
          if is_result_fail e || is_loop_result_fail_break_continue e then (
            [%ldebug "is fail, break or continue"];
            let f, args = destruct_qualif_apps e in
            [%add_loc] mk_qualif_apps span f args new_ty)
          else if is_result_ok e then (
            [%ldebug "is ok"];
            let _, args = destruct_apps e in
            let e =
              match args with
              | [ x ] -> mk_result_ok_texpr span (update x)
              | _ -> [%internal_error] span
            in
            [%ldebug
              "result::ok expression after update:\n" ^ texpr_to_string ctx e];
            e)
          else if tuple_size = Some num_outs then (
            [%ldebug "is tuple"];
            let args = [%add_loc] destruct_tuple_texpr span e in
            [%ldebug
              "args:\n"
              ^ String.concat ",\n" (List.map (texpr_to_string ctx) args)];

            let args =
              List.filter_map
                (fun (arg, out) ->
                  match out with
                  | None -> Some arg
                  | Some _ -> None)
                (List.combine args outputs)
            in
            let e = mk_simpl_tuple_texpr span args in
            [%ldebug "Tuple after update:\n" ^ texpr_to_string ctx e];
            e)
          else (
            [%ldebug "unknown kind of expression"];
            (* TODO: we may have issues if we can't properly update the type *)
            [%internal_error] span)
      | Let (monadic, bound, pat, next) ->
          mk_opened_let monadic bound pat (update next)
      | Switch (scrut, switch) ->
          let switch =
            match switch with
            | If (e0, e1) -> If (update e0, update e1)
            | Match branches ->
                Match
                  (List.map
                     (fun (br : match_branch) ->
                       { br with branch = update br.branch })
                     branches)
          in
          { e = Switch (scrut, switch); ty = new_ty }
      | Loop _ ->
          (* TODO: we may have issues if we can't properly update the type *)
          [%internal_error] span
      | Meta (m, inner) -> mk_emeta m (update inner)
      | EError _ -> { e = e.e; ty = new_ty }
    in
    let bound = if apply_update then update bound else bound in

    (* Update the pattern *)
    let pat =
      let pats =
        List.filter_map
          (fun (keep, pat) -> if keep then Some pat else None)
          (List.combine keep pats)
      in
      mk_simpl_tuple_pat pats
    in

    (* Introduce let-bindings for the outputs we removed *)
    let next =
      mk_opened_lets false
        (List.filter_map
           (fun (pat, out) ->
             match out with
             | None -> None
             | Some out -> Some (pat, out))
           (List.combine pats outputs))
        next
    in

    (* Create the let-binding *)
    (pat, bound, next)
  in

  (* Helper to compute the output *)
  let simplify (monadic : bool) (pat : tpat) (bound : texpr) (next : texpr) :
      tpat * texpr * texpr =
    match opt_destruct_tuple_tpat span pat with
    | None -> (pat, bound, next)
    | Some pats -> simplify_aux monadic pats bound next
  in

  let visitor =
    object
      inherit [_] map_expr as super

      method! visit_Let env monadic pat bound next =
        (* Only attempt to simplify if there is a branching in the bound expression *)
        match bound.e with
        | Switch _ ->
            let pat, bound, next = simplify monadic pat bound next in
            super#visit_Let env monadic pat bound next
        | _ -> super#visit_Let env monadic pat bound next
    end
  in

  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body -> { body with body = visitor#visit_texpr () body.body })
    def

(** Simplify the lets immediately followed by an ok.

    Ex.:
    {[
      x <-- f y;
      Ok x

        ~~>

      f y
    ]}

    If [ignore_loops] is true, we do not apply this transformation binds a loop
    (this is useful to simplify some other micro-passes). *)
let simplify_let_then_ok_visitor ~(ignore_loops : bool) _ctx (def : fun_decl) =
  (* Match a pattern and an expression: evaluates to [true] if the expression
     is actually exactly the pattern *)
  let rec match_pat_and_expr (pat : tpat) (e : texpr) : bool =
    match (pat.pat, e.e) with
    | PConstant plit, Const lit -> plit = lit
    | POpen (pv, _), FVar vid -> pv.id = vid
    | PIgnored, _ ->
        (* It is ok only if we ignore the unit value *)
        pat.ty = mk_unit_ty && e = mk_unit_texpr
    | PAdt padt, _ -> (
        let qualif, args = destruct_apps e in
        match qualif.e with
        | Qualif { id = AdtCons cons_id; generics = _ } ->
            if
              pat.ty = e.ty
              && padt.variant_id = cons_id.variant_id
              && List.length padt.fields = List.length args
            then
              List.for_all
                (fun (p, e) -> match_pat_and_expr p e)
                (List.combine padt.fields args)
            else false
        | _ -> false)
    | _ -> false
  in

  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic lv rv next_e =
      (* We do a bottom up traversal (simplifying in the children nodes
         can allow simplifying in the parent nodes) *)
      let rv = self#visit_texpr env rv in
      let next_e = self#visit_texpr env next_e in
      let not_simpl_e = Let (monadic, lv, rv, next_e) in
      match next_e.e with
      | Switch _ | Loop _ | Let _ ->
          (* Small shortcut to avoid doing the check on every let-binding *)
          not_simpl_e
      | _ -> (
          (* Ignore loops if the user instructs to do so *)
          match rv.e with
          | Loop _ when ignore_loops -> not_simpl_e
          | _ -> (
              if
                (* Do the check *)
                monadic
              then
                (* The first let-binding is monadic *)
                match opt_destruct_ret next_e with
                | Some e ->
                    if match_pat_and_expr lv e then rv.e else not_simpl_e
                | None -> not_simpl_e
              else
                (* The first let-binding is not monadic *)
                match opt_destruct_ret next_e with
                | Some e ->
                    if match_pat_and_expr lv e then
                      (* We need to wrap the right-value in a ret *)
                      (mk_result_ok_texpr def.item_meta.span rv).e
                    else not_simpl_e
                | None ->
                    if match_pat_and_expr lv next_e then rv.e else not_simpl_e))
  end

let simplify_let_then_ok ~(ignore_loops : bool) =
  lift_expr_map_visitor (simplify_let_then_ok_visitor ~ignore_loops)

(** Simplify the aggregated ADTs. Ex.:
    {[
      type struct = { f0 : nat; f1 : nat; f2 : nat }

      Mkstruct x.f0 x.f1 x.f2 ~~> x
    ]}

    If [x] is not a tuple:
    {[
      let ⟨ x0, ..., xn ⟩ := x ~>
      let x0 := x.f0 in
      ...
      let xn := x.fn in
      ...
    ]} *)
let simplify_aggregates_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object
    inherit [_] map_expr as super

    (* Look for a type constructor applied to arguments *)
    method! visit_texpr env e =
      (* First simplify the sub-expressions *)
      let e = super#visit_texpr env e in
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
                TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls
              in
              let fields =
                match adt_decl.kind with
                | Enum _ | Alias _ | Opaque | TDeclError _ ->
                    [%craise] def.item_meta.span "Unreachable"
                | Union _ ->
                    [%craise] def.item_meta.span "Unions are not supported"
                | Struct fields -> fields
              in
              let num_fields = List.length fields in
              (* In order to simplify, there must be as many arguments as
               * there are fields *)
              [%sanity_check] def.item_meta.span (num_fields > 0);
              if num_fields = List.length args then
                (* We now need to check that all the arguments are of the form:
                 * [x.field] for some variable [x], and where the projection
                 * is for the proper ADT *)
                let to_var_proj (i : int) (arg : texpr) :
                    (generic_args * fvar_id) option =
                  match arg.e with
                  | App (proj, x) -> (
                      match (proj.e, x.e) with
                      | ( Qualif
                            {
                              id =
                                Proj { adt_id = TAdtId proj_adt_id; field_id };
                              generics = proj_generics;
                            },
                          FVar v ) ->
                          (* We check that this is the proper ADT, and the proper field *)
                          if proj_adt_id = adt_id && FieldId.to_int field_id = i
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
                    [%sanity_check] def.item_meta.span
                      (List.for_all
                         (fun (generics1, _) -> generics1 = generics)
                         args);
                    { e with e = FVar x })
                  else e
                else e
              else e
          | _ -> e)
      | StructUpdate { struct_id; init = None; updates } ->
          let adt_ty = e.ty in
          (* Attempt to convert all the field updates to projections
             of fields from an ADT with the same type *)
          let to_expr_proj ((fid, arg) : FieldId.id * texpr) : texpr option =
            match arg.e with
            | App (proj, x) -> (
                match proj.e with
                | Qualif
                    {
                      id = Proj { adt_id = TAdtId proj_adt_id; field_id };
                      generics = _;
                    } ->
                    (* We check that this is the proper ADT, and the proper field *)
                    if
                      TAdtId proj_adt_id = struct_id
                      && field_id = fid && x.ty = adt_ty
                    then Some x
                    else None
                | _ -> None)
            | _ -> None
          in
          let expr_projs = List.map to_expr_proj updates in
          let filt_expr_projs = List.filter_map (fun x -> x) expr_projs in
          if filt_expr_projs = [] then e
          else
            (* If all the projections are from the same expression [x], we
                 simply replace the whole expression with [x] *)
            let x = List.hd filt_expr_projs in
            if
              List.length filt_expr_projs = List.length updates
              && List.for_all (fun y -> y = x) filt_expr_projs
            then x
            else if
              (* Attempt to create an "update" expression (i.e., of
                   the shape [{ x with f := v }]).

                   This is not supported by Coq.
                *)
              Config.backend () <> Coq
            then (
              (* Compute the number of occurrences of each init value *)
              let occurs = ref TExprMap.empty in
              List.iter
                (fun x ->
                  let num =
                    match TExprMap.find_opt x !occurs with
                    | None -> 1
                    | Some n -> n + 1
                  in
                  occurs := TExprMap.add x num !occurs)
                filt_expr_projs;
              (* Find the max - note that we can initialize the max at 0,
                   because there is at least one init value *)
              let max = ref 0 in
              let x = ref x in
              List.iter
                (fun (y, n) ->
                  if n > !max then (
                    max := n;
                    x := y))
                (TExprMap.bindings !occurs);
              (* Create the update expression *)
              let updates =
                List.filter_map
                  (fun ((fid, fe), y_opt) ->
                    if y_opt = Some !x then None else Some (fid, fe))
                  (List.combine updates expr_projs)
              in
              let supd = StructUpdate { struct_id; init = Some !x; updates } in
              let e = { e with e = supd } in
              e)
            else e
      | Let
          ( false,
            {
              pat = PAdt { variant_id = None; fields };
              ty = TAdt ((TAdtId decl_id as adt_id), generics);
            },
            ({ e = FVar _; ty = x_ty } as x),
            next )
        when List.for_all is_pat_open fields
             && not
                  (TypesUtils.type_decl_from_decl_id_is_tuple_struct
                     ctx.trans_ctx.type_ctx.type_infos decl_id) ->
          let mk_proj (field_id : field_id) (field : tpat) : tpat * texpr =
            let f, _ = [%add_loc] as_pat_open span field in
            let qualif : texpr =
              {
                e = Qualif { id = Proj { adt_id; field_id }; generics };
                ty = mk_arrow x_ty f.ty;
              }
            in
            let proj = [%add_loc] mk_app span qualif x in
            (field, proj)
          in
          let lets = FieldId.mapi mk_proj fields in
          mk_opened_lets false lets next
      | _ -> e
  end

let simplify_aggregates = lift_expr_map_visitor simplify_aggregates_visitor

(** Helper: flatten nested struct updates and projections of struct updates.

    Ex.:
    [
      { { x with field0 = 0 } with field0 = 1; field1 = 2 }

        ~~>

      { x with field1 = 1; field1 = 2 }
    ]

    [
      { x with field1 = 1 }.field1 ~> 1
      { x with field1 = 1 }.field2 ~> x.field1
    ]
*)
let flatten_struct_updates (ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in
  let visitor =
    object (self)
      inherit [_] map_expr as super

      method! visit_StructUpdate env { struct_id; init; updates } =
        (* Flatten nested struct updates *)
        match init with
        | None -> super#visit_StructUpdate env { struct_id; init; updates }
        | Some init -> (
            let init = self#visit_texpr env init in
            let visit_update (fid, e) = (fid, self#visit_texpr env e) in
            let updates = List.map visit_update updates in
            match init.e with
            | StructUpdate
                { struct_id = struct_id'; init = init'; updates = updates' } ->
                [%sanity_check] span (struct_id = struct_id');
                let fids = FieldId.Set.of_list (List.map fst updates) in
                let updates' =
                  List.filter
                    (fun (fid, _) -> not (FieldId.Set.mem fid fids))
                    updates'
                in
                let updates' = List.map visit_update updates' in
                let updates = updates' @ updates in
                StructUpdate { struct_id; init = init'; updates }
            | _ -> StructUpdate { struct_id; init = Some init; updates })

      method! visit_App env f arg =
        let f = self#visit_texpr env f in
        let arg = self#visit_texpr env arg in
        match f.e with
        | Qualif { id = Proj { field_id; _ }; _ } -> (
            match arg.e with
            | StructUpdate { struct_id = _; init; updates } -> (
                (* Simplify projections.

                Check if the field we project is listed in the updates. *)
                match
                  List.find_opt (fun (fid, _) -> fid = field_id) updates
                with
                | Some (_, field) ->
                    (* We found the field: simply evaluate to the updated expression *)
                    field.e
                | None -> (
                    (* Could not find the field: there *must* be an init value *)
                    match init with
                    | None -> [%internal_error] span
                    | Some init ->
                        (* Project directly the init value *)
                        ([%add_loc] mk_app span f init).e))
            | App _ -> (
                let f, args = destruct_apps f in
                (* Check if this is a call to a constructor *)
                match f.e with
                | Qualif { id = AdtCons _; _ } -> (
                    (* Let's select the proper argument *)
                    match FieldId.nth_opt args field_id with
                    | Some e -> e.e
                    | None -> [%internal_error] span)
                | _ -> ([%add_loc] mk_app span f arg).e)
            | _ -> ([%add_loc] mk_app span f arg).e)
        | _ -> ([%add_loc] mk_app span f arg).e
    end
  in
  map_open_all_fun_decl_body_expr ctx.fresh_fvar_id (visitor#visit_texpr ()) def

(** Remark: it might be better to use egraphs *)
type simp_aggr_env = {
  (* Expansion map that we use in particular to simplify fields.

     For instance, if we see the expression [let (x, y) = p in ...]
     we store the mappings:
     {[
       p   -> (x, y)
       p.0 -> x
       p.1 -> y
     ]}
  *)
  expand_map : expr ExprMap.t;
  (* The list of values which were expanded through matches or let-bindings.

     For instance, if we see the expression [let (x, y) = p in ...] we push
     the expression [p].
  *)
  expanded : expr list;
}

(** Simplify the unchanged fields in the aggregated ADTs.

    Because of the way the symbolic execution works, we often see the following
    pattern:
    {[
      if x.field then { x with field = true } else { x with field = false }
    ]}
    This micro-pass simplifies it to:
    {[
      if x.field then x else x
    ]} *)
let simplify_aggregates_unchanged_fields_visitor (ctx : ctx) (def : fun_decl) =
  let log = Logging.simplify_aggregates_unchanged_fields_log in
  let span = def.item_meta.span in
  (* Some helpers *)
  let add_expand v e m = { m with expand_map = ExprMap.add v e m.expand_map } in
  let add_expands l m =
    { m with expand_map = ExprMap.add_list l m.expand_map }
  in
  let get_expand v m = ExprMap.find_opt v m.expand_map in
  let add_expanded e m = { m with expanded = e :: m.expanded } in
  let add_pat_eqs (bound_adt : texpr) (pat : tpat) (env : simp_aggr_env) :
      simp_aggr_env =
    (* Register the pattern - note that we may not be able to convert the
       pattern to an expression if, for instance, it contains [_] *)
    let env =
      match tpat_to_texpr span pat with
      | Some pat_expr -> add_expand bound_adt.e pat_expr.e env
      | None -> env
    in
    (* Register the fact that the scrutinee got expanded *)
    let env = add_expanded bound_adt.e env in
    (* Check if we are decomposing an ADT to introduce variables for its fields *)
    match pat.pat with
    | PAdt adt ->
        (* Check if the fields are all variables, and compute the tuple:
           (variable introduced for the field, projection) *)
        let fields = FieldId.mapi (fun id x -> (id, x)) adt.fields in
        let vars_to_projs =
          Collections.List.filter_map
            (fun ((fid, f) : _ * tpat) ->
              match f.pat with
              | POpen (var, _) ->
                  let proj = mk_adt_proj span bound_adt fid f.ty in
                  let var = { e = FVar var.id; ty = f.ty } in
                  Some (var.e, proj.e)
              | PBound _ -> [%internal_error] span
              | _ -> None)
            fields
        in
        (* We register the various mappings *)
        let env =
          add_expands (List.map (fun (x, y) -> (y, x)) vars_to_projs) env
        in
        env
    | _ -> env
  in

  (* Recursively expand a value and its subvalues *)
  let expand_expr simp_env (v : expr) : expr =
    let visitor =
      object
        inherit [_] map_expr as super

        method! visit_expr env e =
          match get_expand e simp_env with
          | None -> super#visit_expr env e
          | Some e -> super#visit_expr env e
      end
    in
    visitor#visit_expr () v
  in

  (* The visitor *)
  object (self)
    inherit [_] map_expr as super

    method! visit_Switch env scrut switch =
      [%ltrace "Visiting switch: " ^ switch_to_string ctx scrut switch];
      (* Update the scrutinee *)
      let scrut = self#visit_texpr env scrut in
      let switch =
        match switch with
        | If (b0, b1) ->
            (* Register the expansions:
                 {[
                   scrut -> true    (for the then branch)
                   scrut -> false   (for the else branch)
                 ]}
              *)
            let update v st =
              self#visit_texpr (add_expand scrut.e (mk_bool_value v).e env) st
            in
            let b0 = update true b0 in
            let b1 = update false b1 in
            If (b0, b1)
        | Match branches ->
            let update_branch (b : match_branch) =
              (* Register the information introduced by the patterns *)
              let env = add_pat_eqs scrut b.pat env in
              { b with branch = self#visit_texpr env b.branch }
            in
            let branches = List.map update_branch branches in
            Match branches
      in
      Switch (scrut, switch)

    (* We need to detect patterns of the shape: [let (x, y) = t in ...] *)
    method! visit_Let env monadic pat bound next =
      (* Register the pattern if it is not a monadic let binding *)
      let env = if monadic then env else add_pat_eqs bound pat env in
      (* Continue *)
      super#visit_Let env monadic pat bound next

    (* Update the ADT values *)
    method! visit_texpr env e0 =
      let e =
        match e0.e with
        | StructUpdate updt ->
            [%ltrace
              "Visiting struct update: " ^ struct_update_to_string ctx updt];
            (* Update the fields *)
            let updt = super#visit_struct_update env updt in
            (* Simplify *)
            begin
              match updt.init with
              | None -> super#visit_StructUpdate env updt
              | Some init ->
                  let update_field ((fid, e) : field_id * texpr) :
                      (field_id * texpr) option =
                    (* Recursively expand the value of the field, to check if it is
                         equal to the updated value: if it is the case, we can omit
                         the update. *)
                    let adt = init in
                    let field_value = mk_adt_proj span adt fid e.ty in
                    let field_value = expand_expr env field_value.e in
                    (* If this value is equal to the value we update the field
                         with, we can simply ignore the update *)
                    if field_value = expand_expr env e.e then (
                      [%ltrace "Simplifying field: " ^ texpr_to_string ctx e];
                      None)
                    else (
                      [%ltrace
                        "Not simplifying field: " ^ texpr_to_string ctx e];
                      Some (fid, e))
                  in
                  let updates = List.filter_map update_field updt.updates in
                  if updates = [] then (
                    [%ltrace
                      "StructUpdate: " ^ texpr_to_string ctx e0 ^ " ~~> "
                      ^ texpr_to_string ctx init];
                    init.e)
                  else
                    let updt1 = { updt with updates } in
                    [%ltrace
                      "StructUpdate: "
                      ^ struct_update_to_string ctx updt
                      ^ " ~~> "
                      ^ struct_update_to_string ctx updt1];
                    super#visit_StructUpdate env updt1
            end
        | App _ ->
            [%ltrace "Visiting app: " ^ texpr_to_string ctx e0];
            (* It may be an ADT expr (e.g., [Cons x y] or [(x, y)]):
                 check if it is the case, and if it is, compute the expansion
                 of all the values expanded so far, and see if exactly one of
                 those is equal to the current expression *)
            let e1 = super#visit_texpr env e0 in
            let e1_exp = expand_expr env e1.e in
            let f, _ = destruct_apps e1 in
            if is_adt_cons f then
              let expanded =
                List.filter_map
                  (fun e ->
                    let e' = expand_expr env e in
                    if e1_exp = e' then Some e else None)
                  env.expanded
              in
              begin
                match expanded with
                | [ e2 ] ->
                    [%ltrace
                      "Simplified: " ^ texpr_to_string ctx e1 ^ " ~~> "
                      ^ texpr_to_string ctx { e1 with e = e2 }];
                    e2
                | _ -> e1.e
              end
            else e1.e
        | _ -> super#visit_expr env e0.e
      in
      { e0 with e }
  end

let simplify_aggregates_unchanged_fields =
  lift_expr_map_visitor_with_state simplify_aggregates_unchanged_fields_visitor
    { expand_map = ExprMap.empty; expanded = [] }

(** Convert the unit variables to [()] if they are used as right-values or [_]
    if they are used as left values in patterns. *)
let unit_vars_to_unit (ctx : ctx) (def : fun_decl) : fun_decl =
  let span = def.item_meta.span in

  (* The map visitor *)
  let obj =
    object
      inherit [_] map_expr as super

      (** Replace in patterns *)
      method! visit_POpen _ v mp =
        if v.ty = mk_unit_ty then PIgnored else POpen (v, mp)

      method! visit_PBound _ _ _ = [%internal_error] span

      (** Replace in "regular" expressions - note that we could limit ourselves
          to variables, but this is more powerful *)
      method! visit_texpr env e =
        if e.ty = mk_unit_ty then mk_unit_texpr else super#visit_texpr env e
    end
  in
  (* Update the body *)
  map_open_all_fun_decl_body ctx.fresh_fvar_id
    (fun body ->
      let body_exp = obj#visit_texpr () body.body in
      (* Update the input parameters *)
      let inputs = List.map (obj#visit_tpat ()) body.inputs in
      (* Return *)
      { body = body_exp; inputs })
    def

(** Eliminate the box functions like [Box::new] (which is translated to the
    identity) and [Box::free] (which is translated to [()]).

    Note that the box types have already been eliminated during the translation
    from symbolic to pure. The reason why we don't eliminate the box functions
    at the same time is that we would need to eliminate them in two different
    places: when translating function calls, and when translating end
    abstractions. Here, we can do something simpler, in one micro-pass. *)
let eliminate_box_functions_visitor (_ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* The map visitor *)
  object
    inherit [_] map_expr as super

    method! visit_texpr env e =
      match opt_destruct_function_call e with
      | Some (fun_id, _generics, args) -> (
          (* Below, when dealing with the arguments: we consider the very
             general case, where functions could be boxed (meaning we
             could have: [box_new f x]) *)
          match fun_id with
          | Fun (FromLlbc (FunId (FBuiltin aid), _lp_id)) -> (
              match aid with
              | BoxNew ->
                  let arg, args = Collections.List.pop args in
                  [%add_loc] mk_apps span arg args
              | Index _
              | ArrayToSliceShared
              | ArrayToSliceMut
              | ArrayRepeat
              | PtrFromParts _ -> super#visit_texpr env e)
          | _ -> super#visit_texpr env e)
      | _ -> super#visit_texpr env e
  end

let eliminate_box_functions =
  lift_expr_map_visitor eliminate_box_functions_visitor

(** Simplify some trait calls.

    For instance, we do:
    {
      alloc.boxed.CloneBox.clone CloneInst x

          ~>

      CloneInst.clone x
    }

    TODO: we do this because otherwise we have recursion issues when for instance
    deriving [Clone] for recursive types which use box. This is a hack: we need
    a general solution (the same issue happens if you use other datatypes like [Vec]
    - we introduce a workaround for a few types like [Box] or [&T] because those uses
    are really common and we consider them as builtin).

    TODO: move this to the prepasses
*)
let simplify_trait_calls_visitor (ctx : ctx) (def : fun_decl) =
  (* Create a map from pattern to method *)
  let pats =
    [
      ("alloc::boxed::{core::clone::Clone<Box<@T>>}", "clone");
      ("core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}", "eq");
      ("alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}", "eq");
    ]
  in
  let pats =
    List.map
      (fun (pat, x) -> (NameMatcher.parse_pattern (pat ^ "::" ^ x), x))
      pats
  in
  let names_map = NameMatcher.NameMatcherMap.of_list pats in
  let match_ctx = Charon.NameMatcher.ctx_from_crate ctx.crate in
  let get_method (d : fun_decl) : string option =
    let config = ExtractName.default_match_config in
    NameMatcher.NameMatcherMap.find_opt match_ctx config d.item_meta.name
      names_map
  in

  let span = def.item_meta.span in

  (* The map visitor *)
  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env e =
      let ret_ty = e.ty in
      match opt_destruct_function_call e with
      | Some (fun_id, generics, args) -> (
          match fun_id with
          | Fun (FromLlbc (FunId (FRegular fid), _)) -> (
              match FunDeclId.Map.find_opt fid ctx.fun_decls with
              | Some d
                when List.length generics.trait_refs > 0 && List.length args > 0
                -> (
                  match get_method d with
                  | Some method_name -> (
                      (* Retrieve the first clause - TODO: is it always the first clause? *)
                      let trait_ref = List.hd generics.trait_refs in
                      match trait_ref.trait_id with
                      | TraitImpl (impl_id, impl_generics) ->
                          (* Lookup the impl to retrieve the method id *)
                          let impl =
                            [%unwrap_with_span] span
                              (TraitImplId.Map.find_opt impl_id ctx.trait_impls)
                              "Internal error"
                          in
                          let method_decl =
                            snd
                              ([%unwrap_with_span] span
                                 (List.find_opt
                                    (fun (name, _) -> name = method_name)
                                    impl.methods)
                                 "Internal error")
                          in

                          (* Create a call to the method *)
                          let fun_id = method_decl.binder_value.fun_id in
                          let qualif =
                            FunOrOp
                              (Fun (FromLlbc (FunId (FRegular fun_id), None)))
                          in
                          (* TODO: should we handle the binder? *)
                          let qualif : qualif =
                            { id = qualif; generics = impl_generics }
                          in
                          let arg_tys =
                            List.map (fun (a : texpr) -> a.ty) args
                          in
                          let qualif : texpr =
                            { e = Qualif qualif; ty = mk_arrows arg_tys ret_ty }
                          in
                          let e = [%add_loc] mk_apps span qualif args in
                          (* Should we introduce a [toResult] because the method is actually pure? *)
                          let monadic =
                            let fun_decl =
                              [%unwrap_with_span] span
                                (FunDeclId.Map.find_opt fun_id ctx.fun_decls)
                                "Could not lookup a fun declaration, probably \
                                 because of a previous error"
                            in
                            fun_decl.signature.fwd_info.effect_info.can_fail
                          in
                          let e =
                            if not monadic then mk_to_result_texpr span e else e
                          in
                          (* Re-explore *)
                          self#visit_texpr env e
                      | _ ->
                          (* TODO: simplify calls to non-impls *)
                          super#visit_texpr env e)
                  | None -> super#visit_texpr env e)
              | _ -> super#visit_texpr env e)
          | _ -> super#visit_texpr env e)
      | _ -> super#visit_texpr env e
  end

let simplify_trait_calls = lift_expr_map_visitor simplify_trait_calls_visitor

(** Simplify the lambdas by applying beta-reduction *)
let apply_beta_reduction_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  object (self)
    inherit [_] map_expr as super

    method! visit_FVar env vid =
      match FVarId.Map.find_opt vid env with
      | None -> FVar vid
      | Some e -> e.e

    method! visit_texpr env e =
      [%ldebug "e:\n" ^ texpr_to_string ctx e];
      let f, args = destruct_apps e in
      let args = List.map (self#visit_texpr env) args in
      let pats, body = raw_destruct_lambdas f in
      [%ldebug
        "After decomposing:\n- pats: "
        ^ Print.list_to_string (tpat_to_string ctx) pats
        ^ "\n- body: " ^ texpr_to_string ctx body ^ "\n- args: "
        ^ Print.list_to_string (texpr_to_string ctx) args];
      if args <> [] && pats <> [] then (
        [%ldebug "Can simplify:\n" ^ texpr_to_string ctx e];
        (* Apply the beta-reduction

           First split the arguments/patterns between those that
           will disappear and those we have to preserve. *)
        let min = Int.min (List.length args) (List.length pats) in
        let pats, kept_pats = Collections.List.split_at pats min in
        let args, kept_args = Collections.List.split_at args min in
        (* Substitute *)
        let vars =
          List.map (fun v -> (fst ([%add_loc] as_pat_open span v)).id) pats
        in
        let body =
          let env = FVarId.Map.add_list (List.combine vars args) env in
          self#visit_texpr env body
        in
        (* Reconstruct the term *)
        [%add_loc] mk_apps span
          (mk_opened_lambdas span kept_pats body)
          kept_args)
      else
        (* We may be exploring an expression of the shape:
           [(fun y -> (fun x -> e) y))]
           in which case we need to make sure we simplify the body:
           [(fun x -> e) y ~> e[x/y]]

           We also have to be careful about not infinitely looping.
        *)
        let body =
          if pats <> [] then self#visit_texpr env body
          else super#visit_texpr env body
        in
        [%add_loc] mk_apps span (mk_opened_lambdas span pats body) args
  end

let apply_beta_reduction =
  lift_expr_map_visitor_with_state apply_beta_reduction_visitor FVarId.Map.empty

(** This pass simplifies uses of array/slice index operations.

    We perform the following transformations:
    [
      let (_, back) = Array.index_mut_usize a i in
      let a' = back x in
      ...

       ~~>

      let a' = Array.update a i x in
      ...
    ]

    [
      let _, back = Array.index_mut_usize a i in
      ok (back x)

         ~~>

       Array.update a i x
    ] *)
let simplify_array_slice_update_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* The difficulty is that the let-binding which uses the backward function
     may not appear immediately after the let-binding which introduces it.

     The micro-pass is written in a general way: for instance we do not leverage
     the fact that a backward function should be used only once.
  *)

  (* Small helper: given an expression:
     [let (_, back) = index_mut a i in e2]
     attempt to simplify the let-binding.
   *)
  let try_simplify (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr)
      (back_var : fvar) (is_array : bool) (index_generics : generic_args)
      (a : texpr) (i : texpr) : texpr =
    (* Helper: outputs the input argument if this is a call to the backward function *)
    let is_call_to_back (e : texpr) : texpr option =
      let f, args = destruct_apps e in
      match (f.e, args) with
      | FVar id, [ v ] when id = back_var.id -> Some v
      | _ -> None
    in
    (* Helper to introduce a call to the proper update function *)
    let mk_call_to_update (v : texpr) =
      let array_or_slice = if is_array then Array else Slice in
      let qualif =
        Qualif
          {
            id = FunOrOp (Fun (Pure (UpdateAtIndex array_or_slice)));
            generics = index_generics;
          }
      in
      let qualif = { e = qualif; ty = mk_arrows [ a.ty; i.ty; v.ty ] e2.ty } in
      [%add_loc] mk_apps span qualif [ a; i; v ]
    in

    (* We repeteadly destruct the let-bindings in the next expression until
       the moment we find the call to the backward function. We remove this
       call and insert instead a call to [update]. As the call to the backward
       function may use variables introduced *after* the call to [index_mut]
       we do not necessarily insert it at the position of the backward call
       and may have to introduce it before: we try to introduce it as close
       as possible to the call to [index_mut].

       For instance:
       [
         let (_, back) = index_mut a i in
         let v1 = v + 1 in
         let i1 = i + 1 in
         let a1 = back v1 in
         ...

           ~>

         let v1 = v + 1 in
         let a1 = update a i v1 in (* HERE *)
         let i1 = i + 1 in
         ...
       ]

       In order to do this, we keep track of the fresh variables introduced since
       the call to [index_mut].
    *)
    let rec update (fresh_vars : FVarId.Set.t) (next : texpr) :
        (tpat * texpr * FVarId.Set.t) option * bool * texpr =
      match next.e with
      | Let (monadic', pat', bound, next') -> (
          (* Check if we are calling the backward function *)
          match is_call_to_back bound with
          | None -> (
              (* Continue *)
              let tpat_fvars = tpat_get_fvars pat' in
              let fresh_vars' = FVarId.Set.union fresh_vars tpat_fvars in
              let back_call, updated, next' = update fresh_vars' next' in
              (* Check if we already updated *)
              if updated then
                (back_call, updated, mk_opened_let monadic' pat' bound next')
              else
                (* Check if we found the backward call *)
                match back_call with
                | None ->
                    (* Nothing to do *)
                    (back_call, updated, mk_opened_let monadic' pat' bound next')
                | Some (back_pat, v, v_vars) ->
                    (* Check if the input value given to the backward call requires
                       variables that were introduced in this let-binding:
                       if yes, we insert it here, otherwise we insert it higher up *)
                    if
                      not
                        (FVarId.Set.is_empty
                           (FVarId.Set.inter v_vars tpat_fvars))
                    then
                      (* Insert here *)
                      let next' =
                        mk_opened_let true back_pat (mk_call_to_update v) next'
                      in
                      (back_call, true, mk_opened_let monadic' pat' bound next')
                    else
                      (* Do not insert here *)
                      ( back_call,
                        updated,
                        mk_opened_let monadic' pat' bound next' ))
          | Some v ->
              (* Ignore this let-binding and return information about the backward
               call, so that we can insert it before *)
              (Some (pat', v, texpr_get_fvars v), false, next'))
      | App (f, arg) -> (
          (* Check if this is the [ok (back v)] case *)
          match f.e with
          | Qualif
              {
                id =
                  AdtCons
                    { adt_id = TBuiltin TResult; variant_id = Some variant_id };
                _;
              }
            when variant_id = result_ok_id -> (
              (* Check if we are calling the backward function *)
              match is_call_to_back arg with
              | Some v ->
                  (* Introduce the backward call here (there is no point in moving it up higher).
                     Note that it's ok to output [None] for the information about the backward
                     call: the option will be matched on only if the boolean [updated] is false. *)
                  (None, true, mk_call_to_update v)
              | None -> (None, false, next))
          | _ -> (None, false, next))
      | _ ->
          (* Stop *)
          (None, false, next)
    in
    (* Update *)
    let back_call, updated, next = update FVarId.Set.empty e2 in
    (* Check if we managed to update: if no, we need to insert the call to [update] here *)
    if updated then next
    else
      match back_call with
      | None ->
          (* Could not find the call to the backward function: reconstruct the expression *)
          mk_opened_let monadic pat e1 e2
      | Some (back_pat, back_v, _) ->
          mk_opened_let true back_pat (mk_call_to_update back_v) next
  in

  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic pat e1 e2 =
      (* Update the first expression *)
      let e1 = self#visit_texpr env e1 in
      (* Update the second expression *)
      let e2 = self#visit_texpr env e2 in
      (* Check if the current let-binding is a call to an index function *)
      let e1_app, e1_args = destruct_apps e1 in
      match (pat.pat, e1_app.e, e1_args) with
      | ( (* let (_, back) = ... *)
          PAdt
            {
              variant_id = None;
              fields =
                [ { pat = PIgnored; _ }; { pat = POpen (back_var, _); _ } ];
            },
          (* ... = Array.index_mut_usize a i *)
          Qualif
            {
              id =
                FunOrOp
                  (Fun
                     (FromLlbc
                        ( FunId
                            (FBuiltin
                               (Index
                                  {
                                    is_array;
                                    mutability = RMut;
                                    is_range = false;
                                  })),
                          None )));
              generics = index_generics;
            },
          [ a; i ] ) ->
          [%ldebug
            "identified a pattern to simplify:\n"
            ^ texpr_to_string ctx { e = Let (monadic, pat, e1, e2); ty = e2.ty }];

          (* Attempt to simplify the let-binding.

             We first check that there is only a single use of the backward
             function. TODO: generalize
          *)
          let count = ref 0 in
          let count_visitor =
            object
              inherit [_] iter_expr

              method! visit_fvar_id _ fid =
                if fid = back_var.id then count := !count + 1 else ()
            end
          in
          count_visitor#visit_texpr () e2;
          if !count = 1 then
            (try_simplify monadic pat e1 e2 back_var is_array index_generics a i)
              .e
          else (mk_opened_let monadic pat e1 e2).e
      | _ -> (mk_opened_let monadic pat e1 e2).e
  end

let simplify_array_slice_update =
  lift_expr_map_visitor simplify_array_slice_update_visitor

(** Decompose let-bindings by introducing intermediate let-bindings.

    This is a utility function: see {!decompose_monadic_let_bindings} and
    {!decompose_nested_let_patterns}.

    [decompose_monadic]: always decompose a monadic let-binding
    [decompose_nested_patterns]: decompose the nested patterns *)
let decompose_let_bindings_visitor (decompose_monadic : bool)
    (decompose_nested_patterns : bool) (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* Set up the var id generator *)
  let mk_fresh (ty : ty) : tpat * texpr =
    let vid = ctx.fresh_fvar_id () in
    let tmp : fvar = { id = vid; basename = None; ty } in
    let ltmp = mk_tpat_from_fvar None tmp in
    let rtmp = mk_texpr_from_fvar tmp in
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
  let decompose_pat (lv : tpat) : (tpat * texpr) list * tpat =
    let patterns = ref [] in

    (* We decompose patterns *inside* other patterns.
       The boolean [inside] allows us to remember if we dived into a
       pattern already *)
    let visit_pats =
      object
        inherit [_] map_tpat as super

        method! visit_tpat (inside : bool) (pat : tpat) : tpat =
          match pat.pat with
          | PConstant _ | POpen _ | PIgnored -> pat
          | PBound _ -> [%internal_error] span
          | PAdt _ ->
              if not inside then super#visit_tpat true pat
              else
                let ltmp, rtmp = mk_fresh pat.ty in
                let pat = super#visit_tpat false pat in
                patterns := (pat, rtmp) :: !patterns;
                ltmp
      end
    in

    let inside = false in
    let lv = visit_pats#visit_tpat inside lv in
    (!patterns, lv)
  in

  (* It is a very simple map *)
  object (self)
    inherit [_] map_expr as super

    method! visit_Let env monadic lv re next_e =
      (* Decompose the monadic let-bindings *)
      let monadic, lv, re, next_e =
        if (not monadic) || not decompose_monadic then (monadic, lv, re, next_e)
        else
          (* If monadic, we need to check if the left-value is a variable:
           * - if yes, don't decompose
           * - if not, make the decomposition in two steps
           *)
          match lv.pat with
          | POpen _ | PIgnored ->
              (* Variable: nothing to do *)
              (monadic, lv, re, next_e)
          | PBound _ -> [%internal_error] span
          | _ ->
              (* Not a variable: decompose if required *)
              (* Introduce a temporary variable to receive the value of the
               * monadic binding *)
              let ltmp, rtmp = mk_fresh lv.ty in
              (* Visit the next expression *)
              let next_e = self#visit_texpr env next_e in
              (* Create the let-bindings *)
              (monadic, ltmp, re, mk_opened_let false lv rtmp next_e)
      in
      (* Decompose the nested let-patterns *)
      let lv, next_e =
        if not decompose_nested_patterns then (lv, next_e)
        else
          let pats, first_pat = decompose_pat lv in
          let e =
            List.fold_left
              (fun next_e (lpat, rv) -> mk_opened_let false lpat rv next_e)
              next_e pats
          in
          (first_pat, e)
      in
      (* Continue *)
      super#visit_Let env monadic lv re next_e
  end

let decompose_let_bindings (decompose_monadic : bool)
    (decompose_nested_patterns : bool) =
  lift_expr_map_visitor
    (decompose_let_bindings_visitor decompose_monadic decompose_nested_patterns)

(** Decompose monadic let-bindings.

    See the explanations in {!val:Config.decompose_monadic_let_bindings} *)
let decompose_monadic_let_bindings (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings true false ctx def

(** Decompose the nested let patterns.

    See the explanations in {!val:Config.decompose_nested_let_patterns} *)
let decompose_nested_let_patterns (ctx : ctx) (def : fun_decl) : fun_decl =
  decompose_let_bindings false true ctx def

(** Unfold the monadic let-bindings to explicit matches. *)
let unfold_monadic_let_bindings_visitors (ctx : ctx) (def : fun_decl) =
  (* It is a very simple map *)
  object (_self)
    inherit [_] map_expr as super

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
        let re_ty = Option.get (opt_destruct_result def.item_meta.span re.ty) in
        [%sanity_check] def.item_meta.span (lv.ty = re_ty);
        let err_vid = ctx.fresh_fvar_id () in
        let err_var : fvar =
          {
            id = err_vid;
            basename = Some ConstStrings.error_basename;
            ty = mk_error_ty;
          }
        in
        let err_pat = mk_tpat_from_fvar None err_var in
        let fail_pat = mk_result_fail_pat err_pat.pat lv.ty in
        let err_v = mk_texpr_from_fvar err_var in
        let fail_value = mk_result_fail_texpr def.item_meta.span err_v e.ty in
        let fail_branch = { pat = fail_pat; branch = fail_value } in
        let success_pat = mk_result_ok_pat lv in
        let success_branch = { pat = success_pat; branch = e } in
        let switch_body = Match [ fail_branch; success_branch ] in
        let e = Switch (re, switch_body) in
        (* Continue *)
        super#visit_expr env e
  end

let unfold_monadic_let_bindings =
  lift_expr_map_visitor unfold_monadic_let_bindings_visitors

(** Perform the following transformation:

    {[
      let y <-- ok e

            ~~>

      let y <-- toResult e
    ]}

    We only do this on a specific set of pure functions calls - those functions
    are identified in the "builtin" information about external function calls.
*)
let lift_pure_function_calls_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  let try_lift_expr (super_visit_e : texpr -> texpr) (visit_e : texpr -> texpr)
      (app : texpr) : bool * texpr =
    (* Check if the function should be lifted.

       Also, there is a hack: sometimes we don't want to lift because of
       universe issues (the problem is that if we have [bind x f], then [x]
       and the output of [f] must have a type which lives in the same universe).
       For now, this mostly happens when using dyn traits (because of, e.g.,
       [Debug] instances) as the Lean model introduces a universe bump, so we do
       not lift the expression if the type of the let binding contains a dyn trait.

       TODO: generalize
     *)
    let f, args = destruct_apps app in
    let f = super_visit_e f in
    let args = List.map visit_e args in
    (* *)
    let lift =
      match f.e with
      | Qualif { id = FunOrOp (Unop unop); _ } -> lift_unop unop
      | Qualif { id = FunOrOp (Binop binop); _ } -> lift_binop binop
      | Qualif { id = FunOrOp (Fun fun_id); _ } -> lift_fun ctx fun_id
      | _ -> false
    in
    let no_dyn =
      let visitor =
        object
          inherit [_] iter_expr
          method! visit_TDynTrait _ _ = raise Utils.Found
        end
      in
      try
        visitor#visit_ty () app.ty;
        true
      with Utils.Found -> false
    in
    let lift = lift && no_dyn in
    let app = [%add_loc] mk_apps span f args in
    if lift then (true, mk_to_result_texpr span app) else (false, app)
  in

  (* The map visitor *)
  object (self)
    inherit [_] map_expr as super

    method! visit_texpr env e0 =
      (* Check if this is an expression of the shape: [ok (f ...)] where
         `f` has been identified as a function which should be lifted. *)
      match destruct_apps e0 with
      | ( ({ e = Qualif { id = FunOrOp (Fun (Pure ToResult)); _ }; _ } as
           to_result_expr),
          [ app ] ) ->
          (* Attempt to lift the expression *)
          let lifted, app =
            try_lift_expr (super#visit_texpr env) (self#visit_texpr env) app
          in

          if lifted then app else [%add_loc] mk_app span to_result_expr app
      | { e = Let (monadic, pat, bound, next); ty }, [] ->
          let next = self#visit_texpr env next in
          (* Attempt to lift only if the let-expression is not already monadic. *)
          let lifted, bound =
            if monadic then (true, self#visit_texpr env bound)
            else
              try_lift_expr (super#visit_texpr env) (self#visit_texpr env) bound
          in
          { e = Let (lifted, pat, bound, next); ty }
      | f, args ->
          let f = super#visit_texpr env f in
          let args = List.map (self#visit_texpr env) args in
          [%add_loc] mk_apps span f args
  end

let lift_pure_function_calls =
  lift_expr_map_visitor_with_state lift_pure_function_calls_visitor
    FVarId.Map.empty

let mk_fresh_fuel_var (ctx : ctx) : fvar =
  let id = ctx.fresh_fvar_id () in
  { id; basename = Some ConstStrings.fuel_basename; ty = mk_fuel_ty }

(** Add the fuel parameter, if necessary *)
let add_fuel_one (ctx : ctx) (loops : fun_decl LoopId.Map.t) (def : fun_decl) :
    fun_decl =
  [%ldebug fun_decl_to_string ctx def];
  let span = def.item_meta.span in
  (* Open the binders - this is more convenient *)
  let body =
    Option.map (fun b -> snd (open_all_fun_body ctx span b)) def.body
  in

  (* Introduce variables for the fuel and the state *)
  let effekt = def.signature.fwd_info.effect_info in
  let fuel0 =
    if effekt.can_diverge && !Config.use_fuel then Some (mk_fresh_fuel_var ctx)
    else None
  in
  let fuel =
    if effekt.can_diverge && !Config.use_fuel then Some (mk_fresh_fuel_var ctx)
    else None
  in
  let fuel_expr = Option.map mk_texpr_from_fvar fuel in
  let fuel_ty = Option.map (fun (v : fvar) -> v.ty) fuel in

  (* Update the signature *)
  let sg = def.signature in
  let sg =
    { sg with inputs = Option.to_list fuel_ty @ sg.inputs; output = sg.output }
  in
  let def = { def with signature = sg } in

  (* Small helper: update a call by adding the fuel and state parameters, return
     the updated expession together with the new state *)
  let update_call (f : texpr) (args : texpr list) (fuel : texpr option) : texpr
      =
    (* We need to update the type of the function *)
    let inputs, output = destruct_arrows f.ty in
    let fuel_ty = Option.map (fun (v : texpr) -> v.ty) fuel in
    let inputs = Option.to_list fuel_ty @ inputs in
    let f = { f with ty = mk_arrows inputs output } in

    (* Put everything together *)
    let e = [%add_loc] mk_apps span f (Option.to_list fuel @ args) in

    (* Return *)
    e
  in

  (* Update the body *)
  let rec update (fuel : texpr option) (e : texpr) : texpr =
    [%ldebug "e:\n" ^ texpr_to_string ctx e];
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ -> e
    | App _ | Qualif _ ->
        (* We treat function calls, [Result::ok], [Result::fail] here *)
        let f, args = destruct_apps e in
        (* The arguments *must* be pure (which means they can not be stateful
         nor divergent) *)
        let args = List.map (update None) args in
        [%ldebug
          "- f: " ^ texpr_to_string ctx f ^ "\n- args:\n"
          ^ Print.list_to_string (texpr_to_string ctx) args];
        (* *)
        begin
          match f.e with
          | Qualif
              {
                id = FunOrOp (Fun (FromLlbc (FunId (FRegular fid'), lp_id)));
                _;
              } ->
              (* Lookup the decl *)
              let def' : fun_decl =
                match lp_id with
                | None -> FunDeclId.Map.find fid' ctx.fun_decls
                | Some lp_id ->
                    [%sanity_check] span (fid' = def.def_id);
                    LoopId.Map.find lp_id loops
              in
              [%ldebug
                "def'.signature.inputs:\n"
                ^ Print.list_to_string (ty_to_string ctx) def'.signature.inputs];
              (* This should be a full application *)
              [%sanity_check] span
                (List.length args = List.length def'.signature.inputs);

              (* Add the fuel and the state parameters. *)
              let effect' = def'.signature.fwd_info.effect_info in
              [%sanity_check] span
                ((not effect'.can_diverge) || (not !Config.use_fuel)
               || Option.is_some fuel);
              let fuel = if effect'.can_diverge then fuel else None in
              let call = update_call f args fuel in
              call
          | _ -> [%add_loc] mk_apps span f args
        end
    | Lambda _ -> e
    | Let (monadic, lv, re, next) ->
        (* Is it a function/loop call? *)
        let f, args = destruct_apps re in
        begin
          match f.e with
          | Qualif
              {
                id = FunOrOp (Fun (FromLlbc (FunId (FRegular fid'), lp_id)));
                _;
              } ->
              (* Lookup the decl *)
              let def' : fun_decl =
                match lp_id with
                | None -> FunDeclId.Map.find fid' ctx.fun_decls
                | Some lp_id ->
                    [%sanity_check] span (fid' = def.def_id);
                    LoopId.Map.find lp_id loops
              in
              (* This should be a full application *)
              [%sanity_check] span
                (List.length args = List.length def'.signature.inputs);

              (* Add the fuel and the state parameters. *)
              let call =
                let effect' = def'.signature.fwd_info.effect_info in
                let fuel' = if effect'.can_diverge then fuel else None in

                [%sanity_check] span
                  ((not effect'.can_diverge) || (not !Config.use_fuel)
                 || Option.is_some fuel');

                update_call f args fuel'
              in

              (* Update the let binding *)
              let next = update fuel next in
              mk_opened_let monadic lv call next
          | _ ->
              let re = update fuel re in
              let next = update fuel next in
              mk_opened_let monadic lv re next
        end
    | Switch (scrut, If (e1, e2)) ->
        (* The scrutinee must be pure *)
        let scrut = update None scrut in
        (* *)
        let e1 = update fuel e1 in
        let e2 = update fuel e2 in
        { e = Switch (scrut, If (e1, e2)); ty = e1.ty }
    | Switch (scrut, Match branches) ->
        (* The scrutinee must be pure *)
        let scrut = update None scrut in
        (* *)
        let branches =
          List.map
            (fun (b : match_branch) -> { b with branch = update fuel b.branch })
            branches
        in
        (* *)
        {
          e = Switch (scrut, Match branches);
          ty = (List.hd branches).branch.ty;
        }
    | Loop _ ->
        (* Loops should have been eliminated by then *)
        [%internal_error] span
    | StructUpdate _ -> e
    | Meta (m, e') -> mk_emeta m e'
    | EError _ -> e
  in
  let body =
    Option.map
      (fun (body : fun_body) ->
        let { body; inputs } = body in
        (* Update the body *)
        let body = update fuel_expr body in
        (* Wrap it in a match over the fuel if necessary *)
        let body, fuel_input =
          if effekt.is_rec && !Config.use_fuel then
            ( wrap_in_match_fuel span (Option.get fuel0).id (Option.get fuel).id
                ~close:false body,
              fuel0 )
          else (body, fuel)
        in
        (* Update the inputs *)
        let inputs =
          let fuel_pat = Option.map (mk_tpat_from_fvar None) fuel_input in
          Option.to_list fuel_pat @ inputs
        in
        (* *)
        { body; inputs })
      body
  in

  (* Close the binders *)
  let body = Option.map (close_all_fun_body span) body in
  { def with body }

let add_fuel (ctx : ctx) (trans : pure_fun_translation) : pure_fun_translation =
  let loops_map =
    LoopId.Map.of_list
      (List.map (fun (f : fun_decl) -> (Option.get f.loop_id, f)) trans.loops)
  in

  (* Add the fuel and the state *)
  let f = add_fuel_one ctx loops_map trans.f in
  let loops = List.map (add_fuel_one ctx loops_map) trans.loops in

  (* Decompose the monadic let-bindings if necessary (Coq needs this) *)
  let f, loops =
    if !Config.decompose_monadic_let_bindings then
      let f = decompose_monadic_let_bindings ctx f in
      let loops = List.map (decompose_monadic_let_bindings ctx) loops in
      (f, loops)
    else (f, loops)
  in

  (* *)
  { f; loops }

(** Perform the following transformation:

    {[
      let y <-- f x   (* Must be an application, is not necessarily monadic *)
      let (a, b) := y (* Tuple decomposition *)
      ...
    ]}

    becomes:

    {[
      let (a, b) <-- f x
      ...
    ]} *)
let merge_let_app_then_decompose_tuple_visitor (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in
  object (self)
    inherit [_] map_expr

    method! visit_Let env monadic0 pat0 bound0 next0 =
      let bound0 = self#visit_texpr env bound0 in
      (* Check if we need to merge two let-bindings *)
      if is_pat_open pat0 then
        let var0, _ = [%add_loc] as_pat_open span pat0 in
        match next0.e with
        | Let (false, pat1, { e = FVar var_id; _ }, next1) when var_id = var0.id
          -> begin
            (* Check if we are decomposing a tuple *)
            if is_pat_tuple pat1 then
              (* Introduce fresh variables for all the ignored variables
                   to make sure we can turn the pattern into an expression *)
              let pat1 =
                tpat_replace_ignored_vars_with_free_vars ctx.fresh_fvar_id pat1
              in
              let pat1_expr = Option.get (tpat_to_texpr span pat1) in
              (* Register the mapping from the variable we remove to the expression *)
              let env = FVarId.Map.add var0.id pat1_expr env in
              (* Continue *)
              let next1 = self#visit_texpr env next1 in
              Let (monadic0, pat1, bound0, next1)
            else
              let next0 = self#visit_texpr env next0 in
              Let (monadic0, pat0, bound0, next0)
          end
        | _ ->
            let next0 = self#visit_texpr env next0 in
            Let (monadic0, pat0, bound0, next0)
      else
        let next0 = self#visit_texpr env next0 in
        Let (monadic0, pat0, bound0, next0)

    (* Replace the variables *)
    method! visit_FVar env var_id =
      match FVarId.Map.find_opt var_id env with
      | None -> FVar var_id
      | Some e -> e.e
  end

let merge_let_app_then_decompose_tuple =
  lift_expr_map_visitor_with_state merge_let_app_then_decompose_tuple_visitor
    FVarId.Map.empty

(** Introduce match expressions where a let-binding decomposes an enumeration
    with > 1 variants (see [decompose_let_match]).

    Such patterns can be introduced when calling backward functions. *)
let let_to_match (ctx : ctx) (def : fun_decl) =
  let span = def.item_meta.span in

  (* A pattern appearing in a let-binding needs to be updated if it deconstructs
     an enumeration with > 1 variants *)
  let pat_needs_update pat = tpat_decomposes_enum span ctx.type_decls pat in
  (* Quick check: does the expression contains a let-binding which needs to be updated? *)
  let needs_update (e : texpr) : bool =
    let expr_visitor =
      object
        inherit [_] iter_expr as super

        method! visit_Let env monadic pat bound next =
          if pat_needs_update pat then raise Utils.Found;
          super#visit_Let env monadic pat bound next
      end
    in
    try
      expr_visitor#visit_texpr () e;
      false
    with Utils.Found -> true
  in

  (* When introducing the match, we need to find default values in the "otherwise"
     branch. We do so by computing a map from type to expression found so far.
     We also store the size of the expression in order to use the smallest expressions
     as possible. *)
  let add_expr (env : (int * texpr) TyMap.t) (size : int) (e : texpr) :
      (int * texpr) TyMap.t =
    TyMap.update e.ty
      (fun x ->
        match x with
        | None -> Some (size, e)
        | Some (size', e') ->
            if size <= size' then Some (size, e) else Some (size', e'))
      env
  in

  (* Patterns can be converted to expressions (if they don't contain ignored patterns '_').
     We can use those as default expressions as well: this helper explores a pattern
     and registers all the expressions we find inside it. *)
  let rec add_pat_aux (env : (int * texpr) TyMap.t) (p : tpat) :
      (int * texpr) TyMap.t * int * texpr option =
    match p.pat with
    | PConstant lit -> (env, 1, Some { e = Const lit; ty = p.ty })
    | PBound _ -> [%internal_error] span
    | PIgnored -> (env, 1, None)
    | POpen (fv, _) -> (env, 1, Some { e = FVar fv.id; ty = fv.ty })
    | PAdt { variant_id; fields } ->
        let (env, size), fields =
          List.fold_left_map
            (fun (env, size) e ->
              let env, size', e = add_pat env e in
              ((env, size + size' + 1), e))
            (env, 0) fields
        in
        let e =
          if List.for_all Option.is_some fields then
            let fields = List.map Option.get fields in

            (* Retrieve the type id and the type args from the pat type (simpler this way *)
            let adt_id, generics = ty_as_adt span p.ty in

            (* Create the constructor *)
            let qualif_id = AdtCons { adt_id; variant_id } in
            let qualif = { id = qualif_id; generics } in
            let cons_e = Qualif qualif in
            let field_tys = List.map (fun (v : texpr) -> v.ty) fields in
            let cons_ty = mk_arrows field_tys p.ty in
            let cons = { e = cons_e; ty = cons_ty } in

            (* Apply the constructor *)
            Some ([%add_loc] mk_apps span cons fields)
          else None
        in

        (env, size, e)
  and add_pat (env : (int * texpr) TyMap.t) (p : tpat) :
      (int * texpr) TyMap.t * int * texpr option =
    let env, size, e = add_pat_aux env p in
    let env =
      match e with
      | None -> env
      | Some e -> add_expr env size e
    in
    (env, size, e)
  in

  (* See [add_pat] above *)
  let add_pat env p =
    let env, size, _ = add_pat env p in
    (env, size)
  in

  (* Update a let-binding by introducing a match, if necessary *)
  let update_let (env : (int * texpr) TyMap.t) (pat : tpat) (bound : texpr) :
      tpat * texpr =
    let refresh_var (var : fvar) =
      mk_fresh_fvar ctx ~basename:var.basename var.ty
    in
    let get_default_expr (var : fvar) =
      match TyMap.find_opt var.ty env with
      | Some (_, e) -> e
      | None -> [%internal_error] span
    in
    decompose_let_match span refresh_var get_default_expr ctx.type_decls pat
      bound
  in

  (* Recursively update an expression to decompose all the let-bindings *)
  let rec update_aux (env : (int * texpr) TyMap.t) (e : texpr) :
      (int * texpr) TyMap.t * int * texpr =
    match e.e with
    | FVar _ | BVar _ | CVar _ | Const _ | EError _ | Qualif _ -> (env, 1, e)
    | App (f, x) ->
        let env, nf, f = update env f in
        let env, nx, x = update env x in
        (env, nf + nx + 1, [%add_loc] mk_app span f x)
    | Lambda (pat, body) ->
        let _, pat, body = open_binder ctx span pat body in
        let env', size = add_pat env pat in
        let _, size', body = update env' body in
        (env, size + size' + 1, mk_closed_lambda span pat body)
    | Let (monadic, pat, bound, next) ->
        let _, pat, next = open_binder ctx span pat next in
        let pat, bound = update_let env pat bound in
        let env, s0, bound = update env bound in
        let env', s1 = add_pat env pat in
        let _, s2, next = update env' next in
        (env, s0 + s1 + s2 + 1, mk_closed_let span monadic pat bound next)
    | Switch (scrut, switch) ->
        let env, s0, scrut = update env scrut in
        let env, s1, switch =
          match switch with
          | If (e0, e1) ->
              let env, s1, e0 = update env e0 in
              let env, s2, e1 = update env e1 in
              (env, s1 + s2, If (e0, e1))
          | Match branches ->
              let sizes, branches =
                List.split
                  (List.map
                     (fun ({ pat; branch } : match_branch) ->
                       let _, pat, branch = open_binder ctx span pat branch in
                       let env, size = add_pat env pat in
                       let _, size', branch = update env branch in
                       let pat, branch = close_binder span pat branch in
                       (size + size', ({ pat; branch } : match_branch)))
                     branches)
              in
              let size = List.fold_left (fun n n' -> n + n') 0 sizes in
              (env, size, Match branches)
        in
        (env, s0 + s1 + 1, { e with e = Switch (scrut, switch) })
    | Loop loop ->
        let (env, size), inputs =
          List.fold_left_map
            (fun (env, size) e ->
              let env, size', e = update env e in
              ((env, size + size' + 1), e))
            (env, 0) loop.inputs
        in
        let size', loop_body =
          let ({ inputs; loop_body } : loop_body) = loop.loop_body in
          let _, inputs, loop_body = open_binders ctx span inputs loop_body in
          let env', size =
            List.fold_left
              (fun (env, size) input ->
                let env, size' = add_pat env input in
                (env, size + size'))
              (env, 0) inputs
          in
          let _, size', loop_body = update env' loop_body in
          let inputs, loop_body = close_binders span inputs loop_body in
          let loop_body : loop_body = { inputs; loop_body } in
          (size + size', loop_body)
        in
        let loop = { loop with inputs; loop_body } in
        (env, size + size' + 1, { e with e = Loop loop })
    | StructUpdate { struct_id; init; updates } ->
        let env, size, init =
          match init with
          | None -> (env, 0, None)
          | Some init ->
              let env, size, init = update env init in
              (env, size, Some init)
        in
        let (env, size), updates =
          List.fold_left_map
            (fun (env, size) (fid, e) ->
              let env, size', e = update env e in
              ((env, size + size' + 1), (fid, e)))
            (env, size) updates
        in
        (env, size, { e with e = StructUpdate { struct_id; init; updates } })
    | Meta (m, e') ->
        let env, size, e' = update env e' in
        (env, size + 1, { e with e = Meta (m, e') })
  and update env e =
    let env, size, e = update_aux env e in
    let env = add_expr env size e in
    (env, size, e)
  in

  let body =
    Option.map
      (fun (body : fun_body) ->
        (* Quick check: explore while updating only if necessary *)
        if needs_update body.body then
          let _, body = open_fun_body ctx span body in
          let env =
            List.fold_left
              (fun env input ->
                let env, _ = add_pat env input in
                env)
              TyMap.empty body.inputs
          in
          let _, _, e = update env body.body in
          let body = { body with body = e } in
          close_fun_body span body
        else body)
      def.body
  in
  { def with body }

(** The syntax to match over [isize] and [usize] values doesn't work in Lean,
    because the bitwidth is unknown. In order to make it work, we update these
    matches so that they match over the inner mathematical value.

    For instance:
    {[
      match x with
      | 0#usize => ...
      | 1#usize => ...
      | _ => ...
    ]}

    becomes:
    {[
      match x.val with
      | 0 => ...
      | 1 => ...
          | _ => ...
    ]} *)
let update_match_over_isize_usize_visitor (_ctx : ctx) (f : fun_decl) =
  let span = f.item_meta.span in
  object
    inherit [_] map_expr as super

    method! visit_Switch env scrut switch =
      match switch with
      | If _ -> super#visit_Switch env scrut switch
      | Match branches -> (
          let int_ty : (integer_type * ty) option =
            match scrut.ty with
            | TLiteral (TInt Isize) -> Some (Signed Isize, TLiteral TPureInt)
            | TLiteral (TUInt Usize) -> Some (Unsigned Usize, TLiteral TPureNat)
            | _ -> None
          in
          match int_ty with
          | None -> super#visit_Switch env scrut switch
          | Some (int_ty, pure_ty) ->
              (* Update the scrutinee *)
              let proj =
                {
                  e =
                    Qualif
                      {
                        id = ScalarValProj int_ty;
                        generics = empty_generic_args;
                      };
                  ty = mk_arrow scrut.ty pure_ty;
                }
              in
              let scrut = [%add_loc] mk_app span proj scrut in
              (* Update the branches *)
              let branches =
                List.map
                  (fun ({ pat; branch } : match_branch) ->
                    let pat =
                      match pat.pat with
                      | PIgnored -> { pat = PIgnored; ty = pure_ty }
                      | PConstant (VScalar (UnsignedScalar (_, v))) ->
                          { pat = PConstant (VPureNat v); ty = pure_ty }
                      | PConstant (VScalar (SignedScalar (_, v))) ->
                          { pat = PConstant (VPureInt v); ty = pure_ty }
                      | _ ->
                          (* Shouldn't happen*)
                          [%internal_error] span
                    in
                    { pat; branch })
                  branches
              in
              super#visit_Switch env scrut (Match branches))
  end

let update_match_over_isize_usize =
  lift_expr_map_visitor update_match_over_isize_usize_visitor
