(** The generic extraction *)
(* Turn the whole module into a functor: it is very annoying to carry the
   the formatter everywhere...
*)

open Pure
open PureUtils
open TranslateCore
open ExtractBase
open Config
include ExtractTypes

(** Compute the names for all the pure functions generated from a rust function
    (forward function and backward functions).
 *)
let extract_fun_decl_register_names (ctx : extraction_ctx)
    (has_decreases_clause : fun_decl -> bool) (def : pure_fun_translation) :
    extraction_ctx =
  (* Ignore the trait methods **declarations** (rem.: we do not ignore the trait
     method implementations): we do not need to refer to them directly. We will
     only use their type for the fields of the records we generate for the trait
     declarations *)
  match def.fwd.f.kind with
  | TraitMethodDecl _ -> ctx
  | _ -> (
      (* Check if the function is builtin *)
      let builtin =
        let open ExtractBuiltin in
        let funs_map = builtin_funs_map () in
        let sname = name_to_simple_name def.fwd.f.llbc_name in
        SimpleNameMap.find_opt sname funs_map
      in
      (* Use the builtin names if necessary *)
      match builtin with
      | Some (filter_info, info) ->
          (* Register the filtering information, if there is *)
          let ctx =
            match filter_info with
            | Some keep ->
                {
                  ctx with
                  funs_filter_type_args_map =
                    FunDeclId.Map.add def.fwd.f.def_id keep
                      ctx.funs_filter_type_args_map;
                }
            | _ -> ctx
          in
          let backs = List.map (fun f -> f.f) def.backs in
          let funs = if def.keep_fwd then def.fwd.f :: backs else backs in
          List.fold_left
            (fun ctx (f : fun_decl) ->
              let open ExtractBuiltin in
              let fun_id =
                (Pure.FunId (FRegular f.def_id), f.loop_id, f.back_id)
              in
              let fun_info =
                List.find_opt
                  (fun (x : builtin_fun_info) -> x.rg = f.back_id)
                  info
              in
              match fun_info with
              | Some fun_info ->
                  ctx_add (FunId (FromLlbc fun_id)) fun_info.extract_name ctx
              | None ->
                  raise
                    (Failure
                       ("Not found: "
                       ^ name_to_string ctx f.llbc_name
                       ^ ", "
                       ^ Print.option_to_string Pure.show_loop_id f.loop_id
                       ^ Print.option_to_string Pure.show_region_group_id
                           f.back_id)))
            ctx funs
      | None ->
          let fwd = def.fwd in
          let backs = def.backs in
          (* Register the decrease clauses, if necessary *)
          let register_decreases ctx def =
            if has_decreases_clause def then
              (* Add the termination measure *)
              let ctx = ctx_add_termination_measure def ctx in
              (* Add the decreases proof for Lean only *)
              match !Config.backend with
              | Coq | FStar -> ctx
              | HOL4 -> raise (Failure "Unexpected")
              | Lean -> ctx_add_decreases_proof def ctx
            else ctx
          in
          let ctx =
            List.fold_left register_decreases ctx (fwd.f :: fwd.loops)
          in
          let register_fun ctx f = ctx_add_fun_decl def f ctx in
          let register_funs ctx fl = List.fold_left register_fun ctx fl in
          (* Register the names of the forward functions *)
          let ctx =
            if def.keep_fwd then register_funs ctx (fwd.f :: fwd.loops) else ctx
          in
          (* Register the names of the backward functions *)
          List.fold_left
            (fun ctx { f = back; loops = loop_backs } ->
              let ctx = register_fun ctx back in
              register_funs ctx loop_backs)
            ctx backs)

(** Simply add the global name to the context. *)
let extract_global_decl_register_names (ctx : extraction_ctx)
    (def : A.global_decl) : extraction_ctx =
  ctx_add_global_decl_and_body def ctx

(** The following function factorizes the extraction of ADT values.

    Note that patterns can introduce new variables: we thus return an extraction
    context updated with new bindings.

    [is_single_pat]: are we extracting a single pattern (a pattern for a let-binding
    or a lambda).

    TODO: we don't need something very generic anymore (some definitions used
    to be polymorphic).
 *)
let extract_adt_g_value
    (extract_value : extraction_ctx -> bool -> 'v -> extraction_ctx)
    (fmt : F.formatter) (ctx : extraction_ctx) (is_single_pat : bool)
    (inside : bool) (variant_id : VariantId.id option) (field_values : 'v list)
    (ty : ty) : extraction_ctx =
  match ty with
  | TAdt (TTuple, generics) ->
      (* Tuple *)
      (* For now, we only support fully applied tuple constructors *)
      assert (List.length generics.types = List.length field_values);
      assert (generics.const_generics = [] && generics.trait_refs = []);
      (* This is very annoying: in Coq, we can't write [()] for the value of
         type [unit], we have to write [tt]. *)
      if !backend = Coq && field_values = [] then (
        F.pp_print_string fmt "tt";
        ctx)
      else (
        F.pp_print_string fmt "(";
        let ctx =
          Collections.List.fold_left_link
            (fun () ->
              F.pp_print_string fmt ",";
              F.pp_print_space fmt ())
            (fun ctx v -> extract_value ctx false v)
            ctx field_values
        in
        F.pp_print_string fmt ")";
        ctx)
  | TAdt (adt_id, _) ->
      (* "Regular" ADT *)

      (* If we are generating a pattern for a let-binding and we target Lean,
         the syntax is: `let ⟨ x0, ..., xn ⟩ := ...`.

         Otherwise, it is: `let Cons x0 ... xn = ...`
      *)
      if is_single_pat && !Config.backend = Lean then (
        F.pp_print_string fmt "⟨";
        F.pp_print_space fmt ();
        let ctx =
          Collections.List.fold_left_link
            (fun _ ->
              F.pp_print_string fmt ",";
              F.pp_print_space fmt ())
            (fun ctx v -> extract_value ctx true v)
            ctx field_values
        in
        F.pp_print_space fmt ();
        F.pp_print_string fmt "⟩";
        ctx)
      else
        (* We print something of the form: [Cons field0 ... fieldn].
         * We could update the code to print something of the form:
         * [{ field0=...; ...; fieldn=...; }] in case of structures.
         *)
        let cons =
          match variant_id with
          | Some vid -> (
              (* In the case of Lean, we might have to add the type name as a prefix *)
              match (!backend, adt_id) with
              | Lean, TAssumed _ ->
                  ctx_get_type adt_id ctx ^ "." ^ ctx_get_variant adt_id vid ctx
              | _ -> ctx_get_variant adt_id vid ctx)
          | None -> ctx_get_struct adt_id ctx
        in
        let use_parentheses = inside && field_values <> [] in
        if use_parentheses then F.pp_print_string fmt "(";
        F.pp_print_string fmt cons;
        let ctx =
          Collections.List.fold_left
            (fun ctx v ->
              F.pp_print_space fmt ();
              extract_value ctx true v)
            ctx field_values
        in
        if use_parentheses then F.pp_print_string fmt ")";
        ctx
  | _ -> raise (Failure "Inconsistent typed value")

(* Extract globals in the same way as variables *)
let extract_global (ctx : extraction_ctx) (fmt : F.formatter)
    (id : A.GlobalDeclId.id) : unit =
  F.pp_print_string fmt (ctx_get_global id ctx)

(* Filter the generics of a function if it is builtin *)
let fun_builtin_filter_types (id : FunDeclId.id) (types : 'a list)
    (ctx : extraction_ctx) : ('a list, 'a list * string) Result.result =
  match FunDeclId.Map.find_opt id ctx.funs_filter_type_args_map with
  | None -> Result.Ok types
  | Some filter ->
      if List.length filter <> List.length types then (
        let decl = FunDeclId.Map.find id ctx.trans_funs in
        let err =
          "Ill-formed builtin information for function "
          ^ name_to_string ctx decl.fwd.f.llbc_name
          ^ ": "
          ^ string_of_int (List.length filter)
          ^ " filtering arguments provided for "
          ^ string_of_int (List.length types)
          ^ " type arguments"
        in
        log#serror err;
        Result.Error (types, err))
      else
        let types = List.combine filter types in
        let types =
          List.filter_map (fun (b, ty) -> if b then Some ty else None) types
        in
        Result.Ok types

(** [inside]: see {!extract_ty}.

    As a pattern can introduce new variables, we return an extraction context
    updated with new bindings.
 *)
let rec extract_typed_pattern (ctx : extraction_ctx) (fmt : F.formatter)
    (is_let : bool) (inside : bool) (v : typed_pattern) : extraction_ctx =
  match v.value with
  | PatConstant cv ->
      ctx.fmt.extract_literal fmt inside cv;
      ctx
  | PatVar (v, _) ->
      let vname =
        ctx.fmt.var_basename ctx.names_maps.names_map.names_set v.basename v.ty
      in
      let ctx, vname = ctx_add_var vname v.id ctx in
      F.pp_print_string fmt vname;
      ctx
  | PatDummy ->
      F.pp_print_string fmt "_";
      ctx
  | PatAdt av ->
      let extract_value ctx inside v =
        extract_typed_pattern ctx fmt is_let inside v
      in
      extract_adt_g_value extract_value fmt ctx is_let inside av.variant_id
        av.field_values v.ty

(** [inside]: controls the introduction of parentheses. See [extract_ty]

    TODO: replace the formatting boolean [inside] with something more general?
    Also, it seems we don't really use it...
    Cases to consider:
    - right-expression in a let: [let x = re in _] (never parentheses?)
    - next expression in a let:  [let x = _ in next_e] (never parentheses?)
    - application argument: [f (exp)]
    - match/if scrutinee: [if exp then _ else _]/[match exp | _ -> _]
 *)
let rec extract_texpression (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (e : texpression) : unit =
  match e.e with
  | Var var_id ->
      let var_name = ctx_get_var var_id ctx in
      F.pp_print_string fmt var_name
  | CVar var_id ->
      let var_name = ctx_get_const_generic_var var_id ctx in
      F.pp_print_string fmt var_name
  | Const cv -> ctx.fmt.extract_literal fmt inside cv
  | App _ ->
      let app, args = destruct_apps e in
      extract_App ctx fmt inside app args
  | Abs _ ->
      let xl, e = destruct_abs_list e in
      extract_Abs ctx fmt inside xl e
  | Qualif _ ->
      (* We use the app case *)
      extract_App ctx fmt inside e []
  | Let (_, _, _, _) -> extract_lets ctx fmt inside e
  | Switch (scrut, body) -> extract_Switch ctx fmt inside scrut body
  | Meta (_, e) -> extract_texpression ctx fmt inside e
  | StructUpdate supd -> extract_StructUpdate ctx fmt inside e.ty supd
  | Loop _ ->
      (* The loop nodes should have been eliminated in {!PureMicroPasses} *)
      raise (Failure "Unreachable")

(* Extract an application *or* a top-level qualif (function extraction has
 * to handle top-level qualifiers, so it seemed more natural to merge the
 * two cases) *)
and extract_App (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (app : texpression) (args : texpression list) : unit =
  (* We don't do the same thing if the app is a top-level identifier (function,
   * ADT constructor...) or a "regular" expression *)
  match app.e with
  | Qualif qualif -> (
      (* Top-level qualifier *)
      match qualif.id with
      | FunOrOp fun_id ->
          extract_function_call ctx fmt inside fun_id qualif.generics args
      | Global global_id -> extract_global ctx fmt global_id
      | AdtCons adt_cons_id ->
          extract_adt_cons ctx fmt inside adt_cons_id qualif.generics args
      | Proj proj ->
          extract_field_projector ctx fmt inside app proj qualif.generics args
      | TraitConst (trait_ref, generics, const_name) ->
          let use_brackets = generics <> empty_generic_args in
          if use_brackets then F.pp_print_string fmt "(";
          extract_trait_ref ctx fmt TypeDeclId.Set.empty false trait_ref;
          extract_generic_args ctx fmt TypeDeclId.Set.empty generics;
          let name =
            ctx_get_trait_const trait_ref.trait_decl_ref.trait_decl_id
              const_name ctx
          in
          let add_brackets (s : string) =
            if !backend = Coq then "(" ^ s ^ ")" else s
          in
          if use_brackets then F.pp_print_string fmt ")";
          F.pp_print_string fmt ("." ^ add_brackets name))
  | _ ->
      (* "Regular" expression *)
      (* Open parentheses *)
      if inside then F.pp_print_string fmt "(";
      (* Open a box for the application *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the app expression *)
      let app_inside = (inside && args = []) || args <> [] in
      extract_texpression ctx fmt app_inside app;
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpression ctx fmt true ve)
        args;
      (* Close the box for the application *)
      F.pp_close_box fmt ();
      (* Close parentheses *)
      if inside then F.pp_print_string fmt ")"

(** Subcase of the app case: function call *)
and extract_function_call (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (fid : fun_or_op_id) (generics : generic_args)
    (args : texpression list) : unit =
  match (fid, args) with
  | Unop unop, [ arg ] ->
      (* A unop can have *at most* one argument (the result can't be a function!).
       * Note that the way we generate the translation, we shouldn't get the
       * case where we have no argument (all functions are fully instantiated,
       * and no AST transformation introduces partial calls). *)
      ctx.fmt.extract_unop (extract_texpression ctx fmt) fmt inside unop arg
  | Binop (binop, int_ty), [ arg0; arg1 ] ->
      (* Number of arguments: similar to unop *)
      ctx.fmt.extract_binop
        (extract_texpression ctx fmt)
        fmt inside binop int_ty arg0 arg1
  | Fun fun_id, _ ->
      if inside then F.pp_print_string fmt "(";
      (* Open a box for the function call *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the function name.

         For the function name: the id is not the same depending on whether
         we call a trait method and a "regular" function (remark: trait
         method *implementations* are considered as regular functions here;
         only calls to method of traits which are parameterized in a where
         clause have a special treatment.

         Remark: the reason why trait method declarations have a special
         treatment is that, as traits are extracted to records, we may
         allow collisions between trait item names and some other names,
         while we do not allow collisions between function names.

         # Impl trait refs:
         ==================
         When the trait ref refers to an impl, in
         [InterpreterStatement.eval_transparent_function_call_symbolic] we
         replace the call to the trait impl method to a call to the function
         which implements the trait method (that is, we "forget" that we
         called a trait method, and treat it as a regular function call).

         # Provided trait methods:
         =========================
         Calls to provided trait methods also have a special treatment.
         For now, we do not allow overriding provided trait methods (methods
         for which a default implementation is provided in the trait declaration).
         Whenever we translate a provided trait method, we translate it once as
         a function which takes a trait ref as input. We have to handle this
         case below.

         With an example, if in Rust we write:
         {[
           fn Foo {
             fn f(&self) -> u32; // Required
             fn ret_true(&self) -> bool { true } // Provided
           }
         ]}

         We generate:
         {[
           structure Foo (Self : Type) = {
             f : Self -> result u32
           }

           let ret_true (Self : Type) (self_clause : Foo Self) (self : Self) : result bool =
             true
         ]}
      *)
      (match fun_id with
      | FromLlbc
          (TraitMethod (trait_ref, method_name, _fun_decl_id), lp_id, rg_id) ->
          (* We have to check whether the trait method is required or provided *)
          let trait_decl_id = trait_ref.trait_decl_ref.trait_decl_id in
          let trait_decl =
            TraitDeclId.Map.find trait_decl_id ctx.trans_trait_decls
          in
          let method_id =
            PureUtils.trait_decl_get_method trait_decl method_name
          in

          if not method_id.is_provided then (
            (* Required method *)
            assert (lp_id = None);
            extract_trait_ref ctx fmt TypeDeclId.Set.empty true trait_ref;
            let fun_name =
              ctx_get_trait_method trait_ref.trait_decl_ref.trait_decl_id
                method_name rg_id ctx
            in
            let add_brackets (s : string) =
              if !backend = Coq then "(" ^ s ^ ")" else s
            in
            F.pp_print_string fmt ("." ^ add_brackets fun_name))
          else
            (* Provided method: we see it as a regular function call, and use
               the function name *)
            let fun_id =
              FromLlbc (FunId (FRegular method_id.id), lp_id, rg_id)
            in
            let fun_name = ctx_get_function fun_id ctx in
            F.pp_print_string fmt fun_name;

            (* Note that we do not need to print the generics for the trait
               declaration: they are always implicit as they can be deduced
               from the trait self clause.

               Print the trait ref (to instantate the self clause) *)
            F.pp_print_space fmt ();
            extract_trait_ref ctx fmt TypeDeclId.Set.empty true trait_ref
      | _ ->
          let fun_name = ctx_get_function fun_id ctx in
          F.pp_print_string fmt fun_name);

      (* Sanity check: HOL4 doesn't support const generics *)
      assert (generics.const_generics = [] || !backend <> HOL4);
      (* Print the generics.

         We might need to filter some of the type arguments, if the type
         is builtin (for instance, we filter the global allocator type
         argument for `Vec::new`).
      *)
      let types =
        match fun_id with
        | FromLlbc (FunId (FRegular id), _, _) ->
            fun_builtin_filter_types id generics.types ctx
        | _ -> Result.Ok generics.types
      in
      (match types with
      | Ok types ->
          extract_generic_args ctx fmt TypeDeclId.Set.empty
            { generics with types }
      | Error (types, err) ->
          extract_generic_args ctx fmt TypeDeclId.Set.empty
            { generics with types };
          if !Config.fail_hard then raise (Failure err)
          else
            F.pp_print_string fmt
              "(\"ERROR: ill-formed builtin: invalid number of filtering \
               arguments\")");
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpression ctx fmt true ve)
        args;
      (* Close the box for the function call *)
      F.pp_close_box fmt ();
      (* Return *)
      if inside then F.pp_print_string fmt ")"
  | (Unop _ | Binop _), _ ->
      raise
        (Failure
           ("Unreachable:\n" ^ "Function: " ^ show_fun_or_op_id fid
          ^ ",\nNumber of arguments: "
           ^ string_of_int (List.length args)
           ^ ",\nArguments: "
           ^ String.concat " " (List.map show_texpression args)))

(** Subcase of the app case: ADT constructor *)
and extract_adt_cons (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (adt_cons : adt_cons_id) (generics : generic_args) (args : texpression list)
    : unit =
  let e_ty = TAdt (adt_cons.adt_id, generics) in
  let is_single_pat = false in
  let _ =
    extract_adt_g_value
      (fun ctx inside e ->
        extract_texpression ctx fmt inside e;
        ctx)
      fmt ctx is_single_pat inside adt_cons.variant_id args e_ty
  in
  ()

(** Subcase of the app case: ADT field projector.  *)
and extract_field_projector (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (original_app : texpression) (proj : projection)
    (_generics : generic_args) (args : texpression list) : unit =
  (* We isolate the first argument (if there is), in order to pretty print the
   * projection ([x.field] instead of [MkAdt?.field x] *)
  match args with
  | [ arg ] ->
      (* Exactly one argument: pretty-print *)
      let field_name = ctx_get_field proj.adt_id proj.field_id ctx in
      (* Open a box *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Extract the expression *)
      extract_texpression ctx fmt true arg;
      (* We allow to break where the "." appears (except Lean, it's a syntax error) *)
      if !backend <> Lean then F.pp_print_break fmt 0 0;
      F.pp_print_string fmt ".";
      (* If in Coq, the field projection has to be parenthesized *)
      (match !backend with
      | FStar | Lean | HOL4 -> F.pp_print_string fmt field_name
      | Coq -> F.pp_print_string fmt ("(" ^ field_name ^ ")"));
      (* Close the box *)
      F.pp_close_box fmt ()
  | arg :: args ->
      (* Call extract_App again, but in such a way that the first argument is
       * isolated *)
      extract_App ctx fmt inside (mk_app original_app arg) args
  | [] ->
      (* No argument: shouldn't happen *)
      raise (Failure "Unreachable")

and extract_Abs (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (xl : typed_pattern list) (e : texpression) : unit =
  (* Open a box for the abs expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Print the lambda - note that there should always be at least one variable *)
  assert (xl <> []);
  F.pp_print_string fmt "fun";
  let ctx =
    List.fold_left
      (fun ctx x ->
        F.pp_print_space fmt ();
        extract_typed_pattern ctx fmt true true x)
      ctx xl
  in
  F.pp_print_space fmt ();
  if !backend = Lean then F.pp_print_string fmt "=>"
  else F.pp_print_string fmt "->";
  F.pp_print_space fmt ();
  (* Print the body *)
  extract_texpression ctx fmt false e;
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the abs expression *)
  F.pp_close_box fmt ()

and extract_lets (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (e : texpression) : unit =
  (* Destruct the lets.

     Note that in the case of HOL4, we stop destructing the lets if at some point
     the "kind" (monadic or non-monadic) of the lets changes.

     We do this because in HOL4 the parsing is not very powerful:
     if we mix monadic let-bindings and non monadic let-bindings, we have to
     wrap the let-bindings inside a [do ... od] whenever we need to extract
     a monadic let-binding non immediately inside a monadic let-binding.

     Ex.:
     {[
       do
         x <- ...;
         let y = f x in
         do
           z <- g y;
           ...
         od
       od
     ]}
  *)
  let lets, next_e =
    match !backend with
    | HOL4 -> destruct_lets_no_interleave e
    | FStar | Coq | Lean -> destruct_lets e
  in
  (* Open a box for the whole expression.

     In the case of Lean, we use a vbox so that line breaks are inserted
     at the end of every let-binding: let-bindings are indeed not ended
     with an "in" keyword.
  *)
  if !Config.backend = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt "(";
  (* Extract the let-bindings *)
  let extract_let (ctx : extraction_ctx) (monadic : bool) (lv : typed_pattern)
      (re : texpression) : extraction_ctx =
    (* Open a box for the let-binding *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    let ctx =
      (* There are two cases:
       * - do we use a notation like [x <-- y;]
       * - do we use notation with let-bindings
       * Note that both notations can be used for monadic let-bindings.
       * For instance, in F*, you can write:
       * {[
       *   let* x = y in // monadic
       *   ...
       * ]}
       * TODO: cleanup
       * *)
      if monadic && (!backend = Coq || !backend = HOL4) then (
        let ctx = extract_typed_pattern ctx fmt true true lv in
        F.pp_print_space fmt ();
        let arrow =
          match !backend with
          | Coq | HOL4 -> "<-"
          | FStar | Lean -> raise (Failure "impossible")
        in
        F.pp_print_string fmt arrow;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        F.pp_print_string fmt ";";
        ctx)
      else (
        (* Print the "let" *)
        if monadic then
          match !backend with
          | FStar ->
              F.pp_print_string fmt "let*";
              F.pp_print_space fmt ()
          | Coq | Lean ->
              F.pp_print_string fmt "let";
              F.pp_print_space fmt ()
          | HOL4 -> ()
        else (
          F.pp_print_string fmt "let";
          F.pp_print_space fmt ());
        let ctx = extract_typed_pattern ctx fmt true true lv in
        F.pp_print_space fmt ();
        let eq =
          match !backend with
          | FStar -> "="
          | Coq -> ":="
          | Lean -> if monadic then "←" else ":="
          | HOL4 -> if monadic then "<-" else "="
        in
        F.pp_print_string fmt eq;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        (* End the let-binding *)
        (match !backend with
        | Lean ->
            (* In Lean, (monadic) let-bindings don't require to end with anything *)
            ()
        | Coq | FStar | HOL4 ->
            F.pp_print_space fmt ();
            F.pp_print_string fmt "in");
        ctx)
    in
    (* Close the box for the let-binding *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Return *)
    ctx
  in
  (* If Lean and HOL4, we rely on monadic blocks, so we insert a do and open a new box
     immediately *)
  let wrap_in_do_od =
    match !backend with
    | Lean ->
        (* For Lean, we wrap in a block iff at least one of the let-bindings is monadic *)
        List.exists (fun (m, _, _) -> m) lets
    | HOL4 ->
        (* HOL4 is similar to HOL4, but we add a sanity check *)
        let wrap_in_do = List.exists (fun (m, _, _) -> m) lets in
        if wrap_in_do then assert (List.for_all (fun (m, _, _) -> m) lets);
        wrap_in_do
    | FStar | Coq -> false
  in
  if wrap_in_do_od then (
    F.pp_open_vbox fmt (if !backend = Lean then ctx.indent_incr else 0);
    F.pp_print_string fmt "do";
    F.pp_print_space fmt ());
  let ctx =
    List.fold_left
      (fun ctx (monadic, lv, re) -> extract_let ctx monadic lv re)
      ctx lets
  in
  (* Open a box for the next expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print the next expression *)
  extract_texpression ctx fmt false next_e;
  (* Close the box for the next expression *)
  F.pp_close_box fmt ();

  (* do-box (Lean and HOL4 only) *)
  if wrap_in_do_od then (
    if !backend = HOL4 then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "od");
    F.pp_close_box fmt ());
  (* Close parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_Switch (ctx : extraction_ctx) (fmt : F.formatter) (_inside : bool)
    (scrut : texpression) (body : switch_body) : unit =
  (* Remark: we don't use the [inside] parameter because we extract matches in
     a conservative manner: we always make sure they are parenthesized/delimited
     with keywords such as [end] *)
  (* Open a box for the whole expression.

     In the case of Lean, we rely on indentation to delimit the end of the
     branches, and need to insert line breaks: we thus use a vbox.
  *)
  if !Config.backend = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Extract the switch *)
  (match body with
  | If (e_then, e_else) ->
      (* Open a box for the [if e] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "if";
      if !backend = Lean && ctx.use_dep_ite then F.pp_print_string fmt " h:";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpression_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      (* Close the box for the [if e] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (is_then : bool) (e_branch : texpression) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the then/else+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the then/else + space + opening parenthesis *)
        F.pp_open_hovbox fmt 0;
        let then_or_else = if is_then then "then" else "else" in
        F.pp_print_string fmt then_or_else;
        let parenth = PureUtils.texpression_requires_parentheses e_branch in
        (* Open the parenthesized expression *)
        let print_space_after_parenth =
          if parenth then (
            match !backend with
            | FStar ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "begin";
                F.pp_print_space fmt
            | Coq | Lean | HOL4 ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "(";
                F.pp_print_cut fmt)
          else F.pp_print_space fmt
        in
        (* Close the box for the then/else + space + opening parenthesis *)
        F.pp_close_box fmt ();
        print_space_after_parenth ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch expression *)
        extract_texpression ctx fmt false e_branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the parenthesized expression *)
        (if parenth then
           match !backend with
           | FStar ->
               F.pp_print_space fmt ();
               F.pp_print_string fmt "end"
           | Coq | Lean | HOL4 -> F.pp_print_string fmt ")");
        (* Close the box for the then/else+branch *)
        F.pp_close_box fmt ()
      in

      extract_branch true e_then;
      extract_branch false e_else
  | Match branches -> (
      (* Open a box for the [match ... with] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the [match ... with] *)
      let match_begin =
        match !backend with
        | FStar -> "begin match"
        | Coq -> "match"
        | Lean -> if ctx.use_dep_ite then "match h:" else "match"
        | HOL4 ->
            (* We're being extra safe in the case of HOL4 *)
            "(case"
      in
      F.pp_print_string fmt match_begin;
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpression_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      F.pp_print_space fmt ();
      let match_scrut_end =
        match !backend with FStar | Coq | Lean -> "with" | HOL4 -> "of"
      in
      F.pp_print_string fmt match_scrut_end;
      (* Close the box for the [match ... with] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (br : match_branch) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the pattern+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the pattern *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the pattern *)
        F.pp_print_string fmt "|";
        F.pp_print_space fmt ();
        let ctx = extract_typed_pattern ctx fmt false false br.pat in
        F.pp_print_space fmt ();
        let arrow =
          match !backend with FStar -> "->" | Coq | Lean | HOL4 -> "=>"
        in
        F.pp_print_string fmt arrow;
        (* Close the box for the pattern *)
        F.pp_close_box fmt ();
        F.pp_print_space fmt ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch itself *)
        extract_texpression ctx fmt false br.branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the box for the pattern+branch *)
        F.pp_close_box fmt ()
      in

      List.iter extract_branch branches;

      (* End the match *)
      match !backend with
      | Lean -> (*We rely on indentation in Lean *) ()
      | FStar | Coq ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "end"
      | HOL4 -> F.pp_print_string fmt ")"));
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_StructUpdate (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (e_ty : ty) (supd : struct_update) : unit =
  (* We can't update a subset of the fields in Coq (i.e., we can do
     [{| x:= 3; y := 4 |}], but there is no syntax for [{| s with x := 3 |}]) *)
  assert (!backend <> Coq || supd.init = None);
  (* In the case of HOL4, records with no fields are not supported and are
     thus extracted to unit. We need to check that by looking up the definition *)
  let extract_as_unit =
    match (!backend, supd.struct_id) with
    | HOL4, TAdtId adt_id ->
        let d = TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls in
        d.kind = Struct []
    | _ -> false
  in
  if extract_as_unit then
    (* Remark: this is only valid for HOL4 (for instance the Coq unit value is [tt]) *)
    F.pp_print_string fmt "()"
  else
    (* There are two cases:
       - this is a regular struct
       - this is an array
    *)
    match supd.struct_id with
    | TAdtId _ ->
        F.pp_open_hvbox fmt 0;
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Inner/outer brackets: there are several syntaxes for the field updates.

           For instance, in F*:
           {[
             { x with f = ..., ... }
           ]}

           In HOL4:
           {[
             x with <| f = ..., ... |>
           ]}

           In the above examples:
           - in F*, the { } brackets are "outer" brackets
           - in HOL4, the <| |> brackets are "inner" brackets
        *)
        (* Outer brackets *)
        let olb, orb =
          match !backend with
          | Lean | FStar -> (Some "{", Some "}")
          | Coq -> (Some "{|", Some "|}")
          | HOL4 -> (None, None)
        in
        (* Inner brackets *)
        let ilb, irb =
          match !backend with
          | Lean | FStar | Coq -> (None, None)
          | HOL4 -> (Some "<|", Some "|>")
        in
        (* Helper *)
        let print_bracket (is_left : bool) b =
          match b with
          | Some b ->
              if not is_left then F.pp_print_space fmt ();
              F.pp_print_string fmt b;
              if is_left then F.pp_print_space fmt ()
          | None -> ()
        in
        print_bracket true olb;
        let need_paren = inside && !backend = HOL4 in
        if need_paren then F.pp_print_string fmt "(";
        F.pp_open_hvbox fmt ctx.indent_incr;
        if supd.init <> None then (
          let var_name = ctx_get_var (Option.get supd.init) ctx in
          F.pp_print_string fmt var_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "with";
          F.pp_print_space fmt ());
        print_bracket true ilb;
        F.pp_open_hvbox fmt 0;
        let delimiter =
          match !backend with Lean -> "," | Coq | FStar | HOL4 -> ";"
        in
        let assign =
          match !backend with Coq | Lean | HOL4 -> ":=" | FStar -> "="
        in
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt delimiter;
            F.pp_print_space fmt ())
          (fun (fid, fe) ->
            F.pp_open_hvbox fmt ctx.indent_incr;
            let f = ctx_get_field supd.struct_id fid ctx in
            F.pp_print_string fmt f;
            F.pp_print_string fmt (" " ^ assign);
            F.pp_print_space fmt ();
            F.pp_open_hvbox fmt ctx.indent_incr;
            extract_texpression ctx fmt true fe;
            F.pp_close_box fmt ();
            F.pp_close_box fmt ())
          supd.updates;
        F.pp_close_box fmt ();
        print_bracket false irb;
        F.pp_close_box fmt ();
        F.pp_close_box fmt ();
        if need_paren then F.pp_print_string fmt ")";
        print_bracket false orb;
        F.pp_close_box fmt ()
    | TAssumed TArray ->
        (* Open the boxes *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        let need_paren = inside in
        if need_paren then F.pp_print_string fmt "(";
        (* Open the box for `Array.replicate T N [` *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the array constructor *)
        let cs = ctx_get_struct (TAssumed TArray) ctx in
        F.pp_print_string fmt cs;
        (* Print the parameters *)
        let _, generics = ty_as_adt e_ty in
        let ty = Collections.List.to_cons_nil generics.types in
        F.pp_print_space fmt ();
        extract_ty ctx fmt TypeDeclId.Set.empty true ty;
        let cg = Collections.List.to_cons_nil generics.const_generics in
        F.pp_print_space fmt ();
        extract_const_generic ctx fmt true cg;
        F.pp_print_space fmt ();
        F.pp_print_string fmt "[";
        (* Close the box for `Array.mk T N [` *)
        F.pp_close_box fmt ();
        (* Print the values *)
        let delimiter =
          match !backend with Lean -> "," | Coq | FStar | HOL4 -> ";"
        in
        F.pp_print_space fmt ();
        F.pp_open_hovbox fmt 0;
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt delimiter;
            F.pp_print_space fmt ())
          (fun (_, fe) -> extract_texpression ctx fmt false fe)
          supd.updates;
        (* Close the boxes *)
        F.pp_close_box fmt ();
        if supd.updates <> [] then F.pp_print_space fmt ();
        F.pp_print_string fmt "]";
        if need_paren then F.pp_print_string fmt ")";
        F.pp_close_box fmt ()
    | _ -> raise (Failure "Unreachable")

(** A small utility to print the parameters of a function signature.

    We return two contexts:
    - the context augmented with bindings for the generics
    - the context augmented with bindings for the generics *and*
      bindings for the input values

    We also return names for the type parameters, const generics, etc.

    TODO: do we really need the first one? We should probably always use
    the second one.
    It comes from the fact that when we print the input values for the
    decrease clause, we introduce bindings in the context (because we print
    patterns, not the variables). We should figure a cleaner way.
 *)
let extract_fun_parameters (space : bool ref) (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) :
    extraction_ctx * extraction_ctx * string list =
  (* First, add the associated types and constants if the function is a method
     in a trait declaration.

     About the order: we want to make sure the names are reserved for
     those (variable names might collide with them but it is ok, we will add
     suffixes to the variables).

     TODO: micro-pass to update what happens when calling trait provided
     functions.
  *)
  let ctx, trait_decl =
    match def.kind with
    | TraitMethodProvided (decl_id, _) ->
        let trait_decl = T.TraitDeclId.Map.find decl_id ctx.trans_trait_decls in
        let ctx, _ = ctx_add_trait_self_clause ctx in
        let ctx = { ctx with is_provided_method = true } in
        (ctx, Some trait_decl)
    | _ -> (ctx, None)
  in
  (* Add the type parameters - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params def.signature.generics ctx
  in
  (* Print the generics *)
  (* Open a box for the generics *)
  F.pp_open_hovbox fmt 0;
  (let space = Some space in
   extract_generic_params ctx fmt TypeDeclId.Set.empty ~space ~trait_decl
     def.signature.generics type_params cg_params trait_clauses);
  (* Close the box for the generics *)
  F.pp_close_box fmt ();
  (* The input parameters - note that doing this adds bindings to the context *)
  let ctx_body =
    match def.body with
    | None -> ctx
    | Some body ->
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            insert_req_space fmt space;
            (* Open a box for the input parameter *)
            F.pp_open_hovbox fmt 0;
            F.pp_print_string fmt "(";
            let ctx = extract_typed_pattern ctx fmt true false lv in
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_ty ctx fmt TypeDeclId.Set.empty false lv.ty;
            F.pp_print_string fmt ")";
            (* Close the box for the input parameters *)
            F.pp_close_box fmt ();
            ctx)
          ctx body.inputs_lvs
  in
  (ctx, ctx_body, List.concat [ type_params; cg_params; trait_clauses ])

(** A small utility to print the types of the input parameters in the form:
    [u32 -> list u32 -> ...]
    (we don't print the return type of the function)

    This is used for opaque function declarations, in particular.
 *)
let extract_fun_input_parameters_types (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  let extract_param (ty : ty) : unit =
    let inside = false in
    extract_ty ctx fmt TypeDeclId.Set.empty inside ty;
    F.pp_print_space fmt ();
    extract_arrow fmt ();
    F.pp_print_space fmt ()
  in
  List.iter extract_param def.signature.inputs

let extract_fun_inputs_output_parameters_types (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  extract_fun_input_parameters_types ctx fmt def;
  extract_ty ctx fmt TypeDeclId.Set.empty false def.signature.output

let assert_backend_supports_decreases_clauses () =
  match !backend with
  | FStar | Lean -> ()
  | _ ->
      raise
        (Failure "decreases clauses only supported for the Lean & F* backends")

(** Extract a decreases clause function template body.

    For F* only.

    In order to help the user, we can generate a template for the functions
    required by the decreases clauses for. We simply generate definitions of
    the following form in a separate file:
    {[
      let f_decrease (t : Type0) (x : t) : nat = admit()
    ]}

    Where the translated functions for [f] look like this:
    {[
      let f_fwd (t : Type0) (x : t) : Tot ... (decreases (f_decrease t x)) = ...
    ]}
 *)
let extract_template_fstar_decreases_clause (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  assert (!backend = FStar);

  (* Retrieve the function name *)
  let def_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "[" ^ name_to_string ctx def.llbc_name ^ "]: decreases clause" ];
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
  F.pp_print_string fmt "unfold";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("let " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let space = ref true in
  let _, _, _ = extract_fun_parameters space ctx fmt def in
  insert_req_space fmt space;
  F.pp_print_string fmt ":";
  (* Print the signature *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "nat";
  (* Print the "=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Print the "admit ()" *)
  F.pp_print_string fmt "admit ()";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract templates for the [termination_by] and [decreasing_by] clauses of a
    recursive function definition.

    For Lean only.

    We extract two commands. The first one is a regular definition for the
    termination measure (the value derived from the function arguments that
    decreases over function calls). The second one is a macro definition that
    defines a proof script (allowed to refer to function arguments) that proves
    termination.
*)
let extract_template_lean_termination_and_decreasing (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  assert (!backend = Lean);
  (*
   * Extract a template for the termination measure
   *)
  (* Retrieve the function name *)
  let def_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
  let def_body = Option.get def.body in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "[" ^ name_to_string ctx def.llbc_name ^ "]: termination measure" ];
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
  F.pp_print_string fmt "@[simp]";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("def " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let space = ref true in
  let _, ctx_body, _ = extract_fun_parameters space ctx fmt def in
  (* Print the ":=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Tuple of the arguments *)
  let vars = List.map (fun (v : var) -> v.id) def_body.inputs in

  if List.length vars = 1 then
    F.pp_print_string fmt (ctx_get_var (List.hd vars) ctx_body)
  else (
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt ",";
        F.pp_print_space fmt ())
      (fun v -> F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ());
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;

  (*
   * Extract a template for the decreases proof
   *)
  let def_name = ctx_get_decreases_proof def.def_id def.loop_id ctx in
  (* syntax <def_name> term ... term : tactic *)
  F.pp_print_break fmt 0 0;
  extract_comment fmt
    [ "[" ^ name_to_string ctx def.llbc_name ^ "]: decreases_by tactic" ];
  F.pp_print_space fmt ();
  F.pp_open_hvbox fmt 0;
  F.pp_print_string fmt "syntax \"";
  F.pp_print_string fmt def_name;
  F.pp_print_string fmt "\" term+ : tactic";
  F.pp_print_break fmt 0 0;
  (* macro_rules | `(tactic| fact_termination_proof $x) => `(tactic| ( *)
  F.pp_print_string fmt "macro_rules";
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "| `(tactic| ";
  F.pp_print_string fmt def_name;
  List.iter
    (fun v ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt "$";
      F.pp_print_string fmt (ctx_get_var v ctx_body))
    vars;
  F.pp_print_string fmt ") =>";
  F.pp_close_box fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "`(tactic| sorry)";
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0

let extract_fun_comment (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  let { keep_fwd; num_backs } =
    PureUtils.RegularFunIdMap.find
      (Pure.FunId (FRegular def.def_id), def.loop_id, def.back_id)
      ctx.fun_name_info
  in
  let comment_pre = "[" ^ name_to_string ctx def.llbc_name ^ "]: " in
  let comment =
    let loop_comment =
      match def.loop_id with
      | None -> ""
      | Some id -> "loop " ^ LoopId.to_string id ^ ": "
    in
    let fwd_back_comment =
      match def.back_id with
      | None -> [ "forward function" ]
      | Some id ->
          (* Check if there is only one backward function, and no forward function *)
          if (not keep_fwd) && num_backs = 1 then
            [
              "merged forward/backward function";
              "(there is a single backward function, and the forward function \
               returns ())";
            ]
          else [ "backward function " ^ T.RegionGroupId.to_string id ]
    in
    match fwd_back_comment with
    | [] -> raise (Failure "Unreachable")
    | [ s ] -> [ comment_pre ^ loop_comment ^ s ]
    | s :: sl -> (comment_pre ^ loop_comment ^ s) :: sl
  in
  extract_comment fmt comment

(** Extract a function declaration.

    This function is for all function declarations and all backends **at the exception**
    of opaque (assumed/declared) functions for HOL4.

    See {!extract_fun_decl}.
 *)
let extract_fun_decl_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  assert (not def.is_global_decl_body);
  (* Retrieve the function name *)
  let def_name =
    ctx_get_local_function def.def_id def.loop_id def.back_id ctx
  in
  (* Add a break before *)
  if !backend <> HOL4 || not (decl_is_first_from_group kind) then
    F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  F.pp_print_space fmt ();
  (* Open two boxes for the definition, so that whenever possible it gets printed on
   * one line and indents are correct *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  (* For HOL4: we may need to put parentheses around the definition *)
  let parenthesize = !backend = HOL4 && decl_is_not_last_from_group kind in
  if parenthesize then F.pp_print_string fmt "(";
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  let is_opaque = Option.is_none def.body in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque_coq = !backend = Coq && is_opaque in
  let use_forall =
    is_opaque_coq && def.signature.generics <> empty_generic_params
  in
  (* Print the qualifier ("assume", etc.). *)
  let qualif = ctx.fmt.fun_decl_kind_to_qualif kind in
  (match qualif with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
  F.pp_print_string fmt def_name;
  F.pp_print_space fmt ();
  if use_forall then (
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "forall");
  (* Open a box for "(PARAMS) : EFFECT =" *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "(PARAMS) :" *)
  F.pp_open_hovbox fmt 0;
  let space = ref true in
  let ctx, ctx_body, all_params = extract_fun_parameters space ctx fmt def in
  (* Print the return type - note that we have to be careful when
   * printing the input values for the decrease clause, because
   * it introduces bindings in the context... We thus "forget"
   * the bindings we introduced above.
   * TODO: figure out a cleaner way *)
  let _ =
    if use_forall then F.pp_print_string fmt ","
    else (
      insert_req_space fmt space;
      F.pp_print_string fmt ":");
    (* Close the box for "(PARAMS) :" *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open a box for the EFFECT *)
    F.pp_open_hvbox fmt 0;
    (* Open a box for the return type *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the return type *)
    (* For opaque definitions, as we don't have named parameters under the hand,
     * we don't print parameters in the form [(x : a) (y : b) ...] above,
     * but wait until here to print the types: [a -> b -> ...]. *)
    if is_opaque then extract_fun_input_parameters_types ctx fmt def;
    (* [Tot] *)
    if has_decreases_clause then (
      assert_backend_supports_decreases_clauses ();
      if !backend = FStar then (
        F.pp_print_string fmt "Tot";
        F.pp_print_space fmt ()));
    extract_ty ctx fmt TypeDeclId.Set.empty has_decreases_clause
      def.signature.output;
    (* Close the box for the return type *)
    F.pp_close_box fmt ();
    (* Print the decrease clause - rk.: a function with a decreases clause
     * is necessarily a transparent function *)
    if has_decreases_clause && !backend = FStar then (
      assert_backend_supports_decreases_clauses ();
      F.pp_print_space fmt ();
      (* Open a box for the decreases clause *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* *)
      F.pp_print_string fmt "(decreases (";
      F.pp_print_cut fmt ();
      (* Open a box for the decreases term *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* The name of the decrease clause *)
      let decr_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
      F.pp_print_string fmt decr_name;
      (* Print the generic parameters - TODO: we do this many
         times, we should have a helper to factor it out *)
      List.iter
        (fun (name : string) ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt name)
        all_params;
      (* Print the input values: we have to be careful here to print
       * only the input values which are in common with the *forward*
       * function (the additional input values "given back" to the
       * backward functions have no influence on termination: we thus
       * share the decrease clauses between the forward and the backward
       * functions - we also ignore the additional state received by the
       * backward function, if there is one).
       *)
      let inputs_lvs =
        let all_inputs = (Option.get def.body).inputs_lvs in
        let num_fwd_inputs =
          def.signature.info.num_fwd_inputs_with_fuel_with_state
        in
        Collections.List.prefix num_fwd_inputs all_inputs
      in
      (* TODO: we should probably print the input variables, not the typed
         patterns *)
      let _ =
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            F.pp_print_space fmt ();
            let ctx = extract_typed_pattern ctx fmt true false lv in
            ctx)
          ctx inputs_lvs
      in
      F.pp_print_string fmt "))";
      (* Close the box for the decreases term *)
      F.pp_close_box fmt ();
      (* Close the box for the decreases clause *)
      F.pp_close_box fmt ());
    (* Close the box for the EFFECT *)
    F.pp_close_box fmt ()
  in
  (* Print the "=" *)
  if not is_opaque then (
    F.pp_print_space fmt ();
    let eq = match !backend with FStar | HOL4 -> "=" | Coq | Lean -> ":=" in
    F.pp_print_string fmt eq);
  (* Close the box for "(PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open a box for the body *)
    F.pp_open_hvbox fmt 0;
    (* Extract the body *)
    let _ = extract_texpression ctx_body fmt false (Option.get def.body).body in
    (* Close the box for the body *)
    F.pp_close_box fmt ());
  (* Close the inner box for the definition *)
  F.pp_close_box fmt ();
  (* Termination clause and proof for Lean *)
  if has_decreases_clause && !backend = Lean then (
    let def_body = Option.get def.body in
    let all_vars = List.map (fun (v : var) -> v.id) def_body.inputs in
    let num_fwd_inputs =
      def.signature.info.num_fwd_inputs_with_fuel_with_state
    in
    let vars = Collections.List.prefix num_fwd_inputs all_vars in

    (* termination_by *)
    let terminates_name =
      ctx_get_termination_measure def.def_id def.loop_id ctx
    in
    F.pp_print_break fmt 0 0;
    (* Open a box for the whole [termination_by CALL => DECREASES] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    (* Open a box for {termination_by CALL =>} *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt "termination_by";
    F.pp_print_space fmt ();
    F.pp_print_string fmt def_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      all_vars;
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=>";
    (* Close the box for [termination_by CALL =>] *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open the box for [DECREASES] *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt terminates_name;
    (* Print the generic params - TODO: factor out *)
    List.iter
      (fun (name : string) ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt name)
      all_params;
    (* Print the variables *)
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    (* Close the box for [DECREASES] *)
    F.pp_close_box fmt ();
    (* Close the box for the whole [termination_by CALL => DECREASES] *)
    F.pp_close_box fmt ();

    F.pp_print_break fmt 0 0;
    (* Open a box for the [decreasing by ...] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    let decreases_name = ctx_get_decreases_proof def.def_id def.loop_id ctx in
    F.pp_print_string fmt "decreasing_by";
    F.pp_print_space fmt ();
    F.pp_open_hvbox fmt ctx.indent_incr;
    F.pp_print_string fmt decreases_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    F.pp_close_box fmt ();
    (* Close the box for the [decreasing by ...] *)
    F.pp_close_box fmt ());
  (* Close the parentheses *)
  if parenthesize then F.pp_print_string fmt ")";
  (* Add the definition end delimiter *)
  if !backend = HOL4 && decl_is_not_last_from_group kind then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "/\\")
  else if !backend = Coq && decl_is_last_from_group kind then (
    (* This is actually an end of group delimiter. For aesthetic reasons
       we print it here instead of in {!end_fun_decl_group}. *)
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");
  (* Close the outer box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  if !backend <> HOL4 || decl_is_not_last_from_group kind then
    F.pp_print_break fmt 0 0

(** Extract an opaque function declaration to HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_fun_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* Retrieve the definition name *)
  let def_name =
    ctx_get_local_function def.def_id def.loop_id def.back_id ctx
  in
  assert (def.signature.generics.const_generics = []);
  (* Add the type/const gen parameters - note that we need those bindings
     only for the generation of the type (they are not top-level) *)
  let ctx, _, _, _ = ctx_add_generic_params def.signature.generics ctx in
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;
  (* Open a box for the whole definition *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  (* Generate: `val _ = new_constant ("...",` *)
  F.pp_print_string fmt ("val _ = new_constant (\"" ^ def_name ^ "\",");
  F.pp_print_space fmt ();
  (* Open a box for the type *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "“:";
  (* Generate the type *)
  extract_fun_input_parameters_types ctx fmt def;
  extract_ty ctx fmt TypeDeclId.Set.empty false def.signature.output;
  (* Close the box for the type *)
  F.pp_print_string fmt "”";
  F.pp_close_box fmt ();
  (* Close the parenthesis opened for the inputs of `new_constant` *)
  F.pp_print_string fmt ")";
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a function declaration.

    Note that all the names used for extraction should already have been
    registered.

    We take the definition of the forward translation as parameter (which is
    equal to the definition to extract, if we extract a forward function) because
    it is useful for the decrease clause.

    This function should be inserted between calls to {!start_fun_decl_group}
    and {!end_fun_decl_group}.
 *)
let extract_fun_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  assert (not def.is_global_decl_body);
  (* We treat HOL4 opaque functions in a specific manner *)
  if !backend = HOL4 && Option.is_none def.body then
    extract_fun_decl_hol4_opaque ctx fmt def
  else extract_fun_decl_gen ctx fmt kind has_decreases_clause def

(** Extract a global declaration body of the shape "QUALIF NAME : TYPE = BODY"
    with a custom body extractor.

    We introduce this helper because every (non opaque) global declaration gets
    extracted to two declarations, and we can actually factor out the generation
    of those declarations. See {!extract_global_decl} for more explanations.
 *)
let extract_global_decl_body_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (name : string) (ty : ty)
    (extract_body : (F.formatter -> unit) Option.t) : unit =
  let is_opaque = Option.is_none extract_body in

  (* HOL4: Definition wrapper *)
  if !backend = HOL4 then (
    (* Open a vertical box: we *must* break lines *)
    F.pp_open_vbox fmt 0;
    F.pp_print_string fmt ("Definition " ^ name ^ "_def:");
    F.pp_print_space fmt ();
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt (String.make ctx.indent_incr ' '));

  (* Open the definition boxes (depth=0) *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;

  (* Open "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "QUALIF NAME " *)
  (match ctx.fmt.fun_decl_kind_to_qualif kind with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
  F.pp_print_string fmt name;
  F.pp_print_space fmt ();

  (* Open ": TYPE =" box (depth=2) *)
  F.pp_open_hvbox fmt 0;
  (* Print ": " *)
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();

  (* Open "TYPE" box (depth=3) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "TYPE" *)
  extract_ty ctx fmt TypeDeclId.Set.empty false ty;
  (* Close "TYPE" box (depth=3) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    (* Print " =" *)
    F.pp_print_space fmt ();
    let eq = match !backend with FStar | HOL4 -> "=" | Coq | Lean -> ":=" in
    F.pp_print_string fmt eq);
  (* Close ": TYPE =" box (depth=2) *)
  F.pp_close_box fmt ();
  (* Close "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open "BODY" box (depth=1) *)
    F.pp_open_hvbox fmt 0;
    (* Print "BODY" *)
    (Option.get extract_body) fmt;
    (* Close "BODY" box (depth=1) *)
    F.pp_close_box fmt ());

  (* Close the inner definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* Coq: add a "." *)
  if !backend = Coq then (
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");

  (* Close the outer definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* HOL4: Definition wrapper *)
  if !backend = HOL4 then (
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_print_string fmt "End";
    F.pp_close_box fmt ())

(** Extract an opaque global declaration for HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_global_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (name : string) (ty : ty) : unit =
  (* Open the definition boxe (depth=0) *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [val ..._def = new_constant ("...",] *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt
    ("val " ^ name ^ "_def = new_constant (\"" ^ name ^ "\", ");
  F.pp_close_box fmt ();
  (* Print the type *)
  F.pp_open_hovbox fmt 0;
  extract_ty ctx fmt TypeDeclId.Set.empty false ty;
  (* Close the definition *)
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ();
  (* Close the definition box *)
  F.pp_close_box fmt ();
  (* Add a line *)
  F.pp_print_space fmt ()

(** Extract a global declaration.

    We generate the body which *computes* the global value separately from the
    value declaration itself.

    For example in Rust,
    [static X: u32 = 3;]

    will be translated to the following F*:
    [let x_body : result u32 = Return 3] (* this has type [result u32] *)
    [let x_c : u32 = eval_global x_body] (* this has type [u32] (no [result]!) *)

    This function generates the two declarations.

    Remark: because global declaration groups are always singletons (i.e.,
    there are no groups of mutually recursive global declarations), this function
    doesn't need to be called between calls to functions of the shape
    [{start,end}_gloabl_decl_group], contrary to {!extract_type_decl}
    and {!extract_fun_decl}.
 *)
let extract_global_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (global : A.global_decl) (body : fun_decl) (interface : bool) : unit =
  assert body.is_global_decl_body;
  assert (Option.is_none body.back_id);
  assert (body.signature.inputs = []);
  assert (List.length body.signature.doutputs = 1);
  assert (body.signature.generics = empty_generic_params);

  (* Add a break then the name of the corresponding LLBC declaration *)
  F.pp_print_break fmt 0 0;
  extract_comment fmt [ "[" ^ name_to_string ctx global.name ^ "]" ];
  F.pp_print_space fmt ();

  let decl_name = ctx_get_global global.def_id ctx in
  let body_name =
    ctx_get_function
      (FromLlbc (Pure.FunId (FRegular global.body), None, None))
      ctx
  in

  let decl_ty, body_ty =
    let ty = body.signature.output in
    if body.signature.info.effect_info.can_fail then (unwrap_result_ty ty, ty)
    else (ty, mk_result_ty ty)
  in
  match body.body with
  | None ->
      (* No body: only generate a [val x_c : u32] declaration *)
      let kind = if interface then Declared else Assumed in
      if !backend = HOL4 then
        extract_global_decl_hol4_opaque ctx fmt decl_name decl_ty
      else extract_global_decl_body_gen ctx fmt kind decl_name decl_ty None
  | Some body ->
      (* There is a body *)
      (* Generate: [let x_body : result u32 = Return 3] *)
      extract_global_decl_body_gen ctx fmt SingleNonRec body_name body_ty
        (Some (fun fmt -> extract_texpression ctx fmt false body.body));
      F.pp_print_break fmt 0 0;
      (* Generate: [let x_c : u32 = eval_global x_body] *)
      extract_global_decl_body_gen ctx fmt SingleNonRec decl_name decl_ty
        (Some
           (fun fmt ->
             let body =
               match !backend with
               | FStar -> "eval_global " ^ body_name
               | Lean -> "eval_global " ^ body_name ^ " (by simp)"
               | Coq -> body_name ^ "%global"
               | HOL4 -> "get_return_value " ^ body_name
             in
             F.pp_print_string fmt body));
      (* Add a break to insert lines between declarations *)
      F.pp_print_break fmt 0 0

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_register_parent_clause_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : ExtractBuiltin.builtin_trait_decl_info option) :
    extraction_ctx =
  (* Compute the clause names *)
  let clause_names =
    match builtin_info with
    | None ->
        List.map
          (fun (c : trait_clause) ->
            let name = ctx.fmt.trait_parent_clause_name trait_decl c in
            (* Add a prefix if necessary *)
            let name =
              if !Config.record_fields_short_names then name
              else ctx.fmt.trait_decl_name trait_decl ^ name
            in
            (c.clause_id, name))
          trait_decl.parent_clauses
    | Some info ->
        List.map
          (fun (c, name) -> (c.clause_id, name))
          (List.combine trait_decl.parent_clauses info.parent_clauses)
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (cid, cname) ->
      ctx_add (TraitParentClauseId (trait_decl.def_id, cid)) cname ctx)
    ctx clause_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_register_constant_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : ExtractBuiltin.builtin_trait_decl_info option) :
    extraction_ctx =
  let consts = trait_decl.consts in
  (* Compute the names *)
  let constant_names =
    match builtin_info with
    | None ->
        List.map
          (fun (item_name, _) ->
            let name = ctx.fmt.trait_const_name trait_decl item_name in
            (* Add a prefix if necessary *)
            let name =
              if !Config.record_fields_short_names then name
              else ctx.fmt.trait_decl_name trait_decl ^ name
            in
            (item_name, name))
          consts
    | Some info ->
        let const_map = StringMap.of_list info.consts in
        List.map
          (fun (item_name, _) ->
            (item_name, StringMap.find item_name const_map))
          consts
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (item_name, name) ->
      ctx_add (TraitItemId (trait_decl.def_id, item_name)) name ctx)
    ctx constant_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_type_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : ExtractBuiltin.builtin_trait_decl_info option) :
    extraction_ctx =
  let types = trait_decl.types in
  (* Compute the names *)
  let type_names =
    match builtin_info with
    | None ->
        let compute_type_name (item_name : string) : string =
          let type_name = ctx.fmt.trait_type_name trait_decl item_name in
          if !Config.record_fields_short_names then type_name
          else ctx.fmt.trait_decl_name trait_decl ^ type_name
        in
        let compute_clause_name (item_name : string) (clause : trait_clause) :
            TraitClauseId.id * string =
          let name =
            ctx.fmt.trait_type_clause_name trait_decl item_name clause
          in
          (* Add a prefix if necessary *)
          let name =
            if !Config.record_fields_short_names then name
            else ctx.fmt.trait_decl_name trait_decl ^ name
          in
          (clause.clause_id, name)
        in
        List.map
          (fun (item_name, (item_clauses, _)) ->
            (* Type name *)
            let type_name = compute_type_name item_name in
            (* Clause names *)
            let clauses =
              List.map (compute_clause_name item_name) item_clauses
            in
            (item_name, (type_name, clauses)))
          types
    | Some info ->
        let type_map = StringMap.of_list info.types in
        List.map
          (fun (item_name, (item_clauses, _)) ->
            let type_name, clauses_info = StringMap.find item_name type_map in
            let clauses =
              List.map
                (fun (clause, clause_name) -> (clause.clause_id, clause_name))
                (List.combine item_clauses clauses_info)
            in
            (item_name, (type_name, clauses)))
          types
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (item_name, (type_name, clauses)) ->
      let ctx =
        ctx_add (TraitItemId (trait_decl.def_id, item_name)) type_name ctx
      in
      List.fold_left
        (fun ctx (clause_id, clause_name) ->
          ctx_add
            (TraitItemClauseId (trait_decl.def_id, item_name, clause_id))
            clause_name ctx)
        ctx clauses)
    ctx type_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_method_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : ExtractBuiltin.builtin_trait_decl_info option) :
    extraction_ctx =
  let required_methods = trait_decl.required_methods in
  (* Compute the names *)
  let method_names =
    (* We add one field per required forward/backward function *)
    let get_funs_for_id (id : fun_decl_id) : fun_decl list =
      let trans : pure_fun_translation = FunDeclId.Map.find id ctx.trans_funs in
      List.map (fun f -> f.f) (trans.fwd :: trans.backs)
    in
    match builtin_info with
    | None ->
        (* We add one field per required forward/backward function *)
        let compute_item_names (item_name : string) (id : fun_decl_id) :
            string * (RegionGroupId.id option * string) list =
          let compute_fun_name (f : fun_decl) : RegionGroupId.id option * string
              =
            (* We do something special to reuse the [ctx_compute_fun_decl]
               function. TODO: make it cleaner. *)
            let llbc_name : Types.name =
              [ Types.PeIdent (item_name, Disambiguator.zero) ]
            in
            let f = { f with llbc_name } in
            let trans = A.FunDeclId.Map.find f.def_id ctx.trans_funs in
            let name = ctx_compute_fun_name trans f ctx in
            (* Add a prefix if necessary *)
            let name =
              if !Config.record_fields_short_names then name
              else ctx.fmt.trait_decl_name trait_decl ^ "_" ^ name
            in
            (f.back_id, name)
          in
          let funs = get_funs_for_id id in
          (item_name, List.map compute_fun_name funs)
        in
        List.map (fun (name, id) -> compute_item_names name id) required_methods
    | Some info ->
        let funs_map = StringMap.of_list info.methods in
        List.map
          (fun (item_name, fun_id) ->
            let open ExtractBuiltin in
            let info = StringMap.find item_name funs_map in
            let trans_funs = get_funs_for_id fun_id in
            let find (trans_fun : fun_decl) =
              let info =
                List.find_opt
                  (fun (info : builtin_fun_info) -> info.rg = trans_fun.back_id)
                  info
              in
              match info with
              | Some info -> (info.rg, info.extract_name)
              | None ->
                  let err =
                    "Ill-formed builtin information for trait decl \""
                    ^ name_to_string ctx trait_decl.llbc_name
                    ^ "\", method \"" ^ item_name
                    ^ "\": could not find name for region "
                    ^ Print.option_to_string Pure.show_region_group_id
                        trans_fun.back_id
                  in
                  log#serror err;
                  if !Config.fail_hard then raise (Failure err)
                  else (trans_fun.back_id, "%ERROR_BUILTIN_NAME_NOT_FOUND%")
            in
            let rg_with_name_list = List.map find trans_funs in
            (item_name, rg_with_name_list))
          required_methods
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (item_name, funs) ->
      (* We add one field per required forward/backward function *)
      List.fold_left
        (fun ctx (rg, fun_name) ->
          ctx_add
            (TraitMethodId (trait_decl.def_id, item_name, rg))
            fun_name ctx)
        ctx funs)
    ctx method_names

(** Similar to {!extract_type_decl_register_names} *)
let extract_trait_decl_register_names (ctx : extraction_ctx)
    (trait_decl : trait_decl) : extraction_ctx =
  (* Lookup the information if this is a builtin trait *)
  let open ExtractBuiltin in
  let sname = name_to_simple_name trait_decl.llbc_name in
  let builtin_info =
    SimpleNameMap.find_opt sname (builtin_trait_decls_map ())
  in
  let ctx =
    let trait_name, trait_constructor =
      match builtin_info with
      | None ->
          ( ctx.fmt.trait_decl_name trait_decl,
            ctx.fmt.trait_decl_constructor trait_decl )
      | Some info -> (info.extract_name, info.constructor)
    in
    let ctx = ctx_add (TraitDeclId trait_decl.def_id) trait_name ctx in
    ctx_add (TraitDeclConstructorId trait_decl.def_id) trait_constructor ctx
  in
  (* Parent clauses *)
  let ctx =
    extract_trait_decl_register_parent_clause_names ctx trait_decl builtin_info
  in
  (* Constants *)
  let ctx =
    extract_trait_decl_register_constant_names ctx trait_decl builtin_info
  in
  (* Types *)
  let ctx = extract_trait_decl_type_names ctx trait_decl builtin_info in
  (* Required methods *)
  let ctx = extract_trait_decl_method_names ctx trait_decl builtin_info in
  ctx

(** Similar to {!extract_type_decl_register_names} *)
let extract_trait_impl_register_names (ctx : extraction_ctx)
    (trait_impl : trait_impl) : extraction_ctx =
  let decl_id = trait_impl.impl_trait.trait_decl_id in
  let trait_decl = TraitDeclId.Map.find decl_id ctx.trans_trait_decls in
  (* Check if the trait implementation is builtin *)
  let builtin_info =
    let open ExtractBuiltin in
    let type_sname = name_to_simple_name trait_impl.llbc_name in
    let trait_sname = name_to_simple_name trait_decl.llbc_name in
    SimpleNamePairMap.find_opt (type_sname, trait_sname)
      (builtin_trait_impls_map ())
  in
  (* Register some builtin information (if necessary) *)
  let ctx, builtin_info =
    match builtin_info with
    | None -> (ctx, None)
    | Some (filter, info) ->
        let ctx =
          match filter with
          | None -> ctx
          | Some filter ->
              {
                ctx with
                trait_impls_filter_type_args_map =
                  TraitImplId.Map.add trait_impl.def_id filter
                    ctx.trait_impls_filter_type_args_map;
              }
        in
        (ctx, Some info)
  in

  (* For now we do not support overriding provided methods *)
  assert (trait_impl.provided_methods = []);
  (* Everything is taken care of by {!extract_trait_decl_register_names} *but*
     the name of the implementation itself *)
  (* Compute the name *)
  let name =
    match builtin_info with
    | None -> ctx.fmt.trait_impl_name trait_decl trait_impl
    | Some name -> name
  in
  ctx_add (TraitImplId trait_impl.def_id) name ctx

(** Small helper.

    The type `ty` is to be understood in a very general sense.
 *)
let extract_trait_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (separator : string) (ty : unit -> unit) : unit =
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt item_name;
  F.pp_print_space fmt ();
  (* ":" or "=" *)
  F.pp_print_string fmt separator;
  ty ();
  (match !Config.backend with Lean -> () | _ -> F.pp_print_string fmt ";");
  F.pp_close_box fmt ()

let extract_trait_decl_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (ty : unit -> unit) : unit =
  extract_trait_item ctx fmt item_name ":" ty

let extract_trait_impl_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (ty : unit -> unit) : unit =
  let assign = match !Config.backend with Lean | Coq -> ":=" | _ -> "=" in
  extract_trait_item ctx fmt item_name assign ty

(** Small helper - TODO: move *)
let generic_params_drop_prefix ~(drop_trait_clauses : bool)
    (g1 : generic_params) (g2 : generic_params) : generic_params =
  let open Collections.List in
  let types = drop (length g1.types) g2.types in
  let const_generics = drop (length g1.const_generics) g2.const_generics in
  let trait_clauses =
    if drop_trait_clauses then drop (length g1.trait_clauses) g2.trait_clauses
    else g2.trait_clauses
  in
  { types; const_generics; trait_clauses }

(** Small helper.

    Extract the items for a method in a trait decl.
 *)
let extract_trait_decl_method_items (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) (item_name : string) (id : fun_decl_id) : unit =
  (* Lookup the definition *)
  let trans = A.FunDeclId.Map.find id ctx.trans_funs in
  (* Extract the items *)
  let funs = if trans.keep_fwd then trans.fwd :: trans.backs else trans.backs in
  let extract_method (f : fun_and_loops) =
    let f = f.f in
    let fun_name = ctx_get_trait_method decl.def_id item_name f.back_id ctx in
    let ty () =
      (* Extract the generics *)
      (* We need to add the generics specific to the method, by removing those
         which actually apply to the trait decl *)
      let generics =
        let drop_trait_clauses = false in
        generic_params_drop_prefix ~drop_trait_clauses decl.generics
          f.signature.generics
      in
      let ctx, type_params, cg_params, trait_clauses =
        ctx_add_generic_params generics ctx
      in
      let backend_uses_forall =
        match !backend with Coq | Lean -> true | FStar | HOL4 -> false
      in
      let generics_not_empty = generics <> empty_generic_params in
      let use_forall = generics_not_empty && backend_uses_forall in
      let use_arrows = generics_not_empty && not backend_uses_forall in
      let use_forall_use_sep = false in
      extract_generic_params ctx fmt TypeDeclId.Set.empty ~use_forall
        ~use_forall_use_sep ~use_arrows generics type_params cg_params
        trait_clauses;
      if use_forall then F.pp_print_string fmt ",";
      (* Extract the inputs and output *)
      F.pp_print_space fmt ();
      extract_fun_inputs_output_parameters_types ctx fmt f
    in
    extract_trait_decl_item ctx fmt fun_name ty
  in
  List.iter extract_method funs

(** Extract a trait declaration *)
let extract_trait_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) : unit =
  (* Retrieve the trait name *)
  let decl_name = ctx_get_trait_decl decl.def_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "Trait declaration: [" ^ name_to_string ctx decl.llbc_name ^ "]" ];
  F.pp_print_break fmt 0 0;
  (* Open two outer boxes for the definition, so that whenever possible it gets printed on
     one line and indents are correct.

     There is just an exception with Lean: in this backend, line breaks are important
     for the parsing, so we always open a vertical box.
  *)
  if !Config.backend = Lean then F.pp_open_vbox fmt ctx.indent_incr
  else (
    F.pp_open_hvbox fmt 0;
    F.pp_open_hvbox fmt ctx.indent_incr);

  (* `struct Trait (....) =` *)
  (* Open the box for the name + generics *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  let qualif =
    Option.get (ctx.fmt.type_decl_kind_to_qualif SingleNonRec (Some Struct))
  in
  (* When checking if the trait declaration is empty: we ignore the provided
     methods, because for now they are extracted separately *)
  let is_empty = trait_decl_is_empty { decl with provided_methods = [] } in
  if !backend = FStar && not is_empty then (
    F.pp_print_string fmt "noeq";
    F.pp_print_space fmt ());
  F.pp_print_string fmt qualif;
  F.pp_print_space fmt ();
  F.pp_print_string fmt decl_name;
  (* Print the generics *)
  let generics = decl.generics in
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params generics ctx
  in
  extract_generic_params ctx fmt TypeDeclId.Set.empty generics type_params
    cg_params trait_clauses;

  F.pp_print_space fmt ();
  if is_empty && !backend = FStar then (
    F.pp_print_string fmt "= unit";
    (* Outer box *)
    F.pp_close_box fmt ())
  else if is_empty && !backend = Coq then (
    (* Coq is not very good at infering constructors *)
    let cons = ctx_get_trait_constructor decl.def_id ctx in
    F.pp_print_string fmt (":= " ^ cons ^ "{}.");
    (* Outer box *)
    F.pp_close_box fmt ())
  else (
    (match !backend with
    | Lean -> F.pp_print_string fmt "where"
    | FStar -> F.pp_print_string fmt "= {"
    | Coq ->
        let cons = ctx_get_trait_constructor decl.def_id ctx in
        F.pp_print_string fmt (":= " ^ cons ^ " {")
    | _ -> F.pp_print_string fmt "{");

    (* Close the box for the name + generics *)
    F.pp_close_box fmt ();

    (*
     * Extract the items
     *)

    (* The constants *)
    List.iter
      (fun (name, (ty, _)) ->
        let item_name = ctx_get_trait_const decl.def_id name ctx in
        let ty () =
          let inside = false in
          F.pp_print_space fmt ();
          extract_ty ctx fmt TypeDeclId.Set.empty inside ty
        in
        extract_trait_decl_item ctx fmt item_name ty)
      decl.consts;

    (* The types *)
    List.iter
      (fun (name, (clauses, _)) ->
        (* Extract the type *)
        let item_name = ctx_get_trait_type decl.def_id name ctx in
        let ty () =
          F.pp_print_space fmt ();
          F.pp_print_string fmt (type_keyword ())
        in
        extract_trait_decl_item ctx fmt item_name ty;
        (* Extract the clauses *)
        List.iter
          (fun clause ->
            let item_name =
              ctx_get_trait_item_clause decl.def_id name clause.clause_id ctx
            in
            let ty () =
              F.pp_print_space fmt ();
              extract_trait_clause_type ctx fmt TypeDeclId.Set.empty clause
            in
            extract_trait_decl_item ctx fmt item_name ty)
          clauses)
      decl.types;

    (* The parent clauses - note that the parent clauses may refer to the types
       and const generics: for this reason we extract them *after* *)
    List.iter
      (fun clause ->
        let item_name =
          ctx_get_trait_parent_clause decl.def_id clause.clause_id ctx
        in
        let ty () =
          F.pp_print_space fmt ();
          extract_trait_clause_type ctx fmt TypeDeclId.Set.empty clause
        in
        extract_trait_decl_item ctx fmt item_name ty)
      decl.parent_clauses;

    (* The required methods *)
    List.iter
      (fun (name, id) -> extract_trait_decl_method_items ctx fmt decl name id)
      decl.required_methods;

    (* Close the outer boxes for the definition *)
    if !Config.backend <> Lean then F.pp_close_box fmt ();
    (* Close the brackets *)
    match !Config.backend with
    | Lean -> ()
    | Coq ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt "}."
    | _ ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt "}");
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Generate the [Arguments] instructions for the trait declarationsin Coq, so
    that we don't have to provide the implicit arguments when projecting the fields. *)
let extract_trait_decl_coq_arguments (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) : unit =
  (* Generating the [Arguments] instructions is useful only if there are parameters *)
  let num_params =
    List.length decl.generics.types
    + List.length decl.generics.const_generics
    + List.length decl.generics.trait_clauses
  in
  if num_params > 0 then (
    (* The constructor *)
    let cons_name = ctx_get_trait_constructor decl.def_id ctx in
    extract_coq_arguments_instruction ctx fmt cons_name num_params;
    (* The constants *)
    List.iter
      (fun (name, _) ->
        let item_name = ctx_get_trait_const decl.def_id name ctx in
        extract_coq_arguments_instruction ctx fmt item_name num_params)
      decl.consts;
    (* The types *)
    List.iter
      (fun (name, (clauses, _)) ->
        (* The type *)
        let item_name = ctx_get_trait_type decl.def_id name ctx in
        extract_coq_arguments_instruction ctx fmt item_name num_params;
        (* The type clauses *)
        List.iter
          (fun clause ->
            let item_name =
              ctx_get_trait_item_clause decl.def_id name clause.clause_id ctx
            in
            extract_coq_arguments_instruction ctx fmt item_name num_params)
          clauses)
      decl.types;
    (* The parent clauses *)
    List.iter
      (fun clause ->
        let item_name =
          ctx_get_trait_parent_clause decl.def_id clause.clause_id ctx
        in
        extract_coq_arguments_instruction ctx fmt item_name num_params)
      decl.parent_clauses;
    (* The required methods *)
    List.iter
      (fun (item_name, id) ->
        (* Lookup the definition *)
        let trans = A.FunDeclId.Map.find id ctx.trans_funs in
        (* Extract the items *)
        let funs =
          if trans.keep_fwd then trans.fwd :: trans.backs else trans.backs
        in
        let extract_for_method (f : fun_and_loops) =
          let f = f.f in
          let item_name =
            ctx_get_trait_method decl.def_id item_name f.back_id ctx
          in
          extract_coq_arguments_instruction ctx fmt item_name num_params
        in
        List.iter extract_for_method funs)
      decl.required_methods;
    (* Add a space *)
    F.pp_print_space fmt ())

(** See {!extract_trait_decl_coq_arguments} *)
let extract_trait_decl_extra_info (ctx : extraction_ctx) (fmt : F.formatter)
    (trait_decl : trait_decl) : unit =
  match !backend with
  | Coq -> extract_trait_decl_coq_arguments ctx fmt trait_decl
  | _ -> ()

(** Small helper.

    Extract the items for a method in a trait impl.
 *)
let extract_trait_impl_method_items (ctx : extraction_ctx) (fmt : F.formatter)
    (impl : trait_impl) (item_name : string) (id : fun_decl_id)
    (impl_generics : string list * string list * string list) : unit =
  let trait_decl_id = impl.impl_trait.trait_decl_id in
  (* Lookup the definition *)
  let trans = A.FunDeclId.Map.find id ctx.trans_funs in
  (* Extract the items *)
  let funs = if trans.keep_fwd then trans.fwd :: trans.backs else trans.backs in
  let extract_method (f : fun_and_loops) =
    let f = f.f in
    let fun_name = ctx_get_trait_method trait_decl_id item_name f.back_id ctx in
    let ty () =
      (* Filter the generics if the method is a builtin *)
      let i_tys, _, _ = impl_generics in
      let impl_types, i_tys, f_tys =
        match FunDeclId.Map.find_opt f.def_id ctx.funs_filter_type_args_map with
        | None -> (impl.generics.types, i_tys, f.signature.generics.types)
        | Some filter ->
            let filter_list filter ls =
              let ls = List.combine filter ls in
              List.filter_map (fun (b, ty) -> if b then Some ty else None) ls
            in
            let impl_types = impl.generics.types in
            let impl_filter =
              Collections.List.prefix (List.length impl_types) filter
            in
            let i_tys = i_tys in
            let i_filter = Collections.List.prefix (List.length i_tys) filter in
            ( filter_list impl_filter impl_types,
              filter_list i_filter i_tys,
              filter_list filter f.signature.generics.types )
      in
      let f_generics = { f.signature.generics with types = f_tys } in
      (* Extract the generics - we need to quantify over the generics which
         are specific to the method, and call it will all the generics
         (trait impl + method generics) *)
      let f_generics =
        let drop_trait_clauses = true in
        generic_params_drop_prefix ~drop_trait_clauses
          { impl.generics with types = impl_types }
          f_generics
      in
      (* Register and print the quantified generics *)
      let ctx, f_tys, f_cgs, f_tcs = ctx_add_generic_params f_generics ctx in
      let use_forall = f_generics <> empty_generic_params in
      extract_generic_params ctx fmt TypeDeclId.Set.empty ~use_forall f_generics
        f_tys f_cgs f_tcs;
      if use_forall then F.pp_print_string fmt ",";
      (* Extract the function call *)
      F.pp_print_space fmt ();
      let fun_name = ctx_get_local_function f.def_id None f.back_id ctx in
      F.pp_print_string fmt fun_name;
      let all_generics =
        let _, i_cgs, i_tcs = impl_generics in
        List.concat [ i_tys; f_tys; i_cgs; f_cgs; i_tcs; f_tcs ]
      in

      (* Filter the generics if the function is builtin *)
      List.iter
        (fun p ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt p)
        all_generics
    in
    extract_trait_impl_item ctx fmt fun_name ty
  in
  List.iter extract_method funs

(** Extract a trait implementation *)
let extract_trait_impl (ctx : extraction_ctx) (fmt : F.formatter)
    (impl : trait_impl) : unit =
  log#ldebug (lazy ("extract_trait_impl: " ^ name_to_string ctx impl.llbc_name));
  (* Retrieve the impl name *)
  let impl_name = ctx_get_trait_impl impl.def_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "Trait implementation: [" ^ name_to_string ctx impl.llbc_name ^ "]" ];
  F.pp_print_break fmt 0 0;

  (* Open two outer boxes for the definition, so that whenever possible it gets printed on
     one line and indents are correct.

     There is just an exception with Lean: in this backend, line breaks are important
     for the parsing, so we always open a vertical box.
  *)
  if !Config.backend = Lean then (
    F.pp_open_vbox fmt 0;
    F.pp_open_vbox fmt ctx.indent_incr)
  else (
    F.pp_open_hvbox fmt 0;
    F.pp_open_hvbox fmt ctx.indent_incr);

  (* `let (....) : Trait ... =` *)
  (* Open the box for the name + generics *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (match ctx.fmt.fun_decl_kind_to_qualif SingleNonRec with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
  F.pp_print_string fmt impl_name;

  (* Print the generics *)
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params impl.generics ctx
  in
  let all_generics = (type_params, cg_params, trait_clauses) in
  extract_generic_params ctx fmt TypeDeclId.Set.empty impl.generics type_params
    cg_params trait_clauses;

  (* Print the type *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();
  extract_trait_decl_ref ctx fmt TypeDeclId.Set.empty false impl.impl_trait;

  (* When checking if the trait impl is empty: we ignore the provided
     methods, because for now they are extracted separately *)
  let is_empty = trait_impl_is_empty { impl with provided_methods = [] } in

  F.pp_print_space fmt ();
  if is_empty && !Config.backend = FStar then (
    F.pp_print_string fmt "= ()";
    (* Outer box *)
    F.pp_close_box fmt ())
  else if is_empty && !Config.backend = Coq then (
    (* Coq is not very good at infering constructors *)
    let cons = ctx_get_trait_constructor impl.impl_trait.trait_decl_id ctx in
    F.pp_print_string fmt (":= " ^ cons ^ ".");
    (* Outer box *)
    F.pp_close_box fmt ())
  else (
    if !Config.backend = Lean then F.pp_print_string fmt ":= {"
    else if !Config.backend = Coq then F.pp_print_string fmt ":= {|"
    else F.pp_print_string fmt "= {";

    (* Close the box for the name + generics *)
    F.pp_close_box fmt ();

    (*
     * Extract the items
     *)
    let trait_decl_id = impl.impl_trait.trait_decl_id in

    (* The constants *)
    List.iter
      (fun (name, (_, id)) ->
        let item_name = ctx_get_trait_const trait_decl_id name ctx in
        let ty () =
          F.pp_print_space fmt ();
          F.pp_print_string fmt (ctx_get_global id ctx)
        in

        extract_trait_impl_item ctx fmt item_name ty)
      impl.consts;

    (* The types *)
    List.iter
      (fun (name, (trait_refs, ty)) ->
        (* Extract the type *)
        let item_name = ctx_get_trait_type trait_decl_id name ctx in
        let ty () =
          F.pp_print_space fmt ();
          extract_ty ctx fmt TypeDeclId.Set.empty false ty
        in
        extract_trait_impl_item ctx fmt item_name ty;
        (* Extract the clauses *)
        TraitClauseId.iteri
          (fun clause_id trait_ref ->
            let item_name =
              ctx_get_trait_item_clause trait_decl_id name clause_id ctx
            in
            let ty () =
              F.pp_print_space fmt ();
              extract_trait_ref ctx fmt TypeDeclId.Set.empty false trait_ref
            in
            extract_trait_impl_item ctx fmt item_name ty)
          trait_refs)
      impl.types;

    (* The parent clauses *)
    TraitClauseId.iteri
      (fun clause_id trait_ref ->
        let item_name =
          ctx_get_trait_parent_clause trait_decl_id clause_id ctx
        in
        let ty () =
          F.pp_print_space fmt ();
          extract_trait_ref ctx fmt TypeDeclId.Set.empty false trait_ref
        in
        extract_trait_impl_item ctx fmt item_name ty)
      impl.parent_trait_refs;

    (* The required methods *)
    List.iter
      (fun (name, id) ->
        extract_trait_impl_method_items ctx fmt impl name id all_generics)
      impl.required_methods;

    (* Close the outer boxes for the definition, as well as the brackets *)
    F.pp_close_box fmt ();
    if !backend = Coq then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "|}.")
    else if (not (!backend = FStar)) || not is_empty then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "}"));
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a unit test, if the function is a unit function (takes no
    parameters, returns unit).

    A unit test simply checks that the function normalizes to [Return ()].

    F*:
    {[
      let _ = assert_norm (FUNCTION = Return ())
    ]}

    Coq:
    {[
      Check (FUNCTION)%return).
    ]}
 *)
let extract_unit_test_if_unit_fun (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* We only insert unit tests for forward functions *)
  assert (def.back_id = None);
  (* Check if this is a unit function *)
  let sg = def.signature in
  if
    sg.generics = empty_generic_params
    && (sg.inputs = [ mk_unit_ty ] || sg.inputs = [])
    && sg.output = mk_result_ty mk_unit_ty
  then (
    (* Add a break before *)
    F.pp_print_break fmt 0 0;
    (* Print a comment *)
    extract_comment fmt
      [ "Unit test for [" ^ name_to_string ctx def.llbc_name ^ "]" ];
    F.pp_print_space fmt ();
    (* Open a box for the test *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the test *)
    (match !backend with
    | FStar ->
        F.pp_print_string fmt "let _ =";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "assert_norm";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt "=";
        F.pp_print_space fmt ();
        let success = ctx_get_variant (TAssumed TResult) result_return_id ctx in
        F.pp_print_string fmt (success ^ " ())")
    | Coq ->
        F.pp_print_string fmt "Check";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt ")%return."
    | Lean ->
        F.pp_print_string fmt "#assert";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt "==";
        F.pp_print_space fmt ();
        let success = ctx_get_variant (TAssumed TResult) result_return_id ctx in
        F.pp_print_string fmt ("." ^ success ^ " ())")
    | HOL4 ->
        F.pp_print_string fmt "val _ = assert_return (";
        F.pp_print_string fmt "“";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_string fmt "”)");
    (* Close the box for the test *)
    F.pp_close_box fmt ();
    (* Add a break after *)
    F.pp_print_break fmt 0 0)
  else (* Do nothing *)
    ()
