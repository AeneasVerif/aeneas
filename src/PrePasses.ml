(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it *)

open Types
open Expressions
open LlbcAst
open Utils
open LlbcAstUtils
open Errors

let log = Logging.pre_passes_log

(* Copy the statement list onto each branch of this switch. *)
let append_to_switch (switch : switch) (new_stmts : statement list) : switch =
  let append_to_block (b : block) (stmts : statement list) : block =
    { b with statements = b.statements @ stmts }
  in
  match switch with
  | If (op, st0, st1) ->
      If (op, append_to_block st0 new_stmts, append_to_block st1 new_stmts)
  | SwitchInt (op, int_ty, branches, otherwise) ->
      let branches =
        List.map (fun (svl, br) -> (svl, append_to_block br new_stmts)) branches
      in
      let otherwise = append_to_block otherwise new_stmts in
      SwitchInt (op, int_ty, branches, otherwise)
  | Match (op, branches, otherwise) ->
      let branches =
        List.map (fun (svl, br) -> (svl, append_to_block br new_stmts)) branches
      in
      let otherwise =
        Option.map (fun b -> append_to_block b new_stmts) otherwise
      in
      Match (op, branches, otherwise)

(** The Rust compiler generates a unique implementation of [Default] for arrays
    for every choice of length. For instance, if we write:
    {[
      let a: [u8; 32] = default ();
      let b: [u8; 64] = default ();
      ...
    ]}
    then rustc will introduce two different implementations of [Default]: an
    implementation for [u8; 32] and a different one for [u8; 64].

    For the purpose of the translation, we prefer using a single implementation
    which is generic in the length of the array. This pass thus replaces all the
    implementations of [Default<[T; N]>] with a single implementation.

    Concretely, we spot all the instances of [Default<[T; N]>] where [N] is a
    concrete array. We update the first such implementation so that it becomes
    generic in the length of the array, and replace all the other ones with this
    implementation. We also remove the useless implementations. *)
let update_array_default (crate : crate) : crate =
  let pctx = Print.Crate.crate_to_fmt_env crate in
  let impl_pat = NameMatcher.parse_pattern "core::default::Default" in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_name =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in

  (* First detect all the instances of [Default<[T; N]>] (and all the
     implementations of [Default<[T; N]>::default] *)
  let merged_impl = ref None in
  let merged_method = ref None in
  (* Those maps allow us to do two things:
     - store the set of trait impls and methods that implement an instance
       of [Default] for arrays
     - store for each of those the precise length for which the implementation
       is specialized (useful later when updating the crate)
  *)
  let impls = ref TraitImplId.Map.empty in
  let methods = ref FunDeclId.Map.empty in

  let visit_trait_impl _id (impl : trait_impl) : trait_impl option =
    (* Check this is an impl of [Default] for arrays *)
    let trait_decl =
      silent_unwrap_opt_span __FILE__ __LINE__ (Some impl.item_meta.span)
        (TraitDeclId.Map.find_opt impl.impl_trait.id crate.trait_decls)
    in
    if match_name impl_pat trait_decl.item_meta.name then (
      log#ldebug
        (lazy
          (__FUNCTION__ ^ ": found a matching impl.\n - decl_generics: "
          ^ Print.generic_args_to_string pctx impl.impl_trait.generics));
      (* Check the generics. Note that we ignore the case where the length
         is equal to 0, because in this case rustc uses a different impl
         which doesn't require that the type of the elements also has a
         default implementation. *)
      match impl.impl_trait.generics with
      | {
       regions = [];
       types =
         [
           TAdt
             {
               id = TBuiltin TArray;
               generics =
                 {
                   regions = [];
                   types = [ TVar (Free _) ];
                   const_generics =
                     [ (CgValue (VScalar (UnsignedScalar (Usize, nv))) as n) ];
                   trait_refs = _;
                 } as array_generics;
             };
         ];
       const_generics = [];
       trait_refs = _;
      }
        when Z.to_int nv != 0 -> begin
          (* Save the implementation and the method *)
          impls := TraitImplId.Map.add impl.def_id n !impls;
          assert (List.length impl.methods = 1);
          let meth = snd (List.hd impl.methods) in
          assert (meth.binder_params = TypesUtils.empty_generic_params);
          let method_id = meth.binder_value.id in
          methods := FunDeclId.Map.add method_id n !methods;
          (* Is it the first implementation we find? *)
          match !merged_impl with
          | None ->
              (* Update the implementation in place *)
              let cg_id = ConstGenericVarId.zero in
              let cg = CgVar (Free cg_id) in
              let generics =
                {
                  impl.impl_trait.generics with
                  types =
                    [
                      TAdt
                        {
                          id = TBuiltin TArray;
                          generics =
                            { array_generics with const_generics = [ cg ] };
                        };
                    ];
                }
              in
              let impl_trait = { impl.impl_trait with generics } in
              let params =
                {
                  impl.generics with
                  const_generics =
                    [ { index = cg_id; name = "N"; ty = TUInt Usize } ];
                }
              in
              let impl = { impl with impl_trait; generics = params } in
              (* Register it *)
              merged_impl := Some impl;
              merged_method := Some method_id;
              (* Continue *)
              Some impl
          | Some _ ->
              (* Filter the implementation *)
              None
        end
      | _ -> Some impl)
    else Some impl
  in
  let crate =
    {
      crate with
      trait_impls =
        TraitImplId.Map.filter_map visit_trait_impl crate.trait_impls;
    }
  in

  (* Check if we found a default implementation for array. If yes, we need
     to filter the [default] methods and update all the definitions to make
     sure they refer to the proper implementations and methods.
  *)
  match !merged_impl with
  | None -> crate
  | Some merged_impl ->
      let merged_method = Option.get !merged_method in
      let impls = !impls in
      let methods = !methods in

      (* Filter the functions *)
      let visit_fun id (fdecl : fun_decl) =
        match FunDeclId.Map.find_opt id methods with
        | None -> Some fdecl
        | Some _ ->
            if id = merged_method then (
              (* Update the method *)
              let cg_id = ConstGenericVarId.zero in
              let cg = CgVar (Free cg_id) in
              let sg = fdecl.signature in
              assert (sg.inputs = []);
              match sg.output with
              | TAdt
                  {
                    id = TBuiltin TArray;
                    generics =
                      {
                        regions = [];
                        types = [ TVar (Free _) ];
                        const_generics = [ _ ];
                        trait_refs = _;
                      } as array_generics;
                  } ->
                  let array_generics =
                    { array_generics with const_generics = [ cg ] }
                  in
                  let generics =
                    {
                      sg.generics with
                      const_generics =
                        [ { index = cg_id; name = "N"; ty = TUInt Usize } ];
                    }
                  in
                  let sg =
                    {
                      sg with
                      generics;
                      output =
                        TAdt { id = TBuiltin TArray; generics = array_generics };
                    }
                  in
                  let fdecl = { fdecl with signature = sg } in
                  Some fdecl
              | _ -> internal_error __FILE__ __LINE__ fdecl.item_meta.span)
            else (* Filter *)
              None
      in
      let filter_ids_visitor =
        object
          inherit [_] filter_decl_id

          method! visit_trait_impl_id _ id =
            match TraitImplId.Map.find_opt id impls with
            | None -> Some id
            | Some _ -> if id = merged_impl.def_id then Some id else None

          method! visit_fun_decl_id _ id =
            match FunDeclId.Map.find_opt id methods with
            | None -> Some id
            | Some _ -> if id = merged_method then Some id else None
        end
      in
      let crate =
        {
          crate with
          fun_decls = FunDeclId.Map.filter_map visit_fun crate.fun_decls;
          declarations =
            filter_ids_visitor#visit_declaration_groups () crate.declarations;
        }
      in

      (* Update all the definitions in the crate *)
      let visitor =
        object
          inherit [_] map_crate_with_span as super

          method! visit_TraitImpl env impl_ref =
            match TraitImplId.Map.find_opt impl_ref.id impls with
            | None -> super#visit_TraitImpl env impl_ref
            | Some n ->
                super#visit_TraitImpl env
                  {
                    id = merged_impl.def_id;
                    generics = { impl_ref.generics with const_generics = [ n ] };
                  }

          method! visit_fn_ptr env fn_ptr =
            match fn_ptr.func with
            | FunId (FRegular fid) -> begin
                match FunDeclId.Map.find_opt fid methods with
                | None -> super#visit_fn_ptr env fn_ptr
                | Some n ->
                    let fn_ptr =
                      {
                        func = FunId (FRegular merged_method);
                        generics =
                          { fn_ptr.generics with const_generics = [ n ] };
                      }
                    in
                    super#visit_fn_ptr env fn_ptr
              end
            | _ -> super#visit_fn_ptr env fn_ptr
        end
      in
      visitor#visit_crate None crate

(** This pass slightly restructures the control-flow to remove the need to merge
    branches during the symbolic execution in some quite common cases where
    doing a merge is actually not necessary and leads to an ugly translation.

    TODO: this is useless

    For instance, it performs the following transformation:
    {[
      if b {
          var@0 := &mut *x;
      }
      else {
          var@0 := move y;
      }
      return;

      ~~>

      if b {
          var@0 := &mut *x;
          return;
      }
      else {
          var@0 := move y;
          return;
      }
    ]}

    This way, the translated body doesn't have an intermediate assignment, for
    the `if ... then ... else ...` expression (together with a backward
    function).

    More precisly, we move (and duplicate) a statement happening after a
    branching inside the branches if:
    - this statement ends with [return] or [panic]
    - this statement is only made of a sequence of nops, assignments (with some
      restrictions on the rvalue), fake reads, drops (usually, returns will be
      followed by such statements) *)
let remove_useless_cf_merges (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  (* Return [true] if the statement can be moved inside the branches of a switch.
   *
   * [must_end_with_exit]: we need this boolean because the inner statements
   * (inside the encountered sequences) don't need to end with [return] or [panic],
   * but all the paths inside the whole statement have to.
   *)
  let rec can_be_moved_aux (must_end_with_exit : bool) (st : statement) : bool =
    match st.content with
    | SetDiscriminant _
    | CopyNonOverlapping _
    | Assert _
    | Call _
    | Break _
    | Continue _
    | Switch _
    | Loop _
    | Error _ -> false
    | Assign (_, rv) -> (
        match rv with
        | Use _ | RvRef _ -> not must_end_with_exit
        | Aggregate (AggregatedAdt ({ id = TTuple; _ }, _, _), []) ->
            not must_end_with_exit
        | _ -> false)
    | StorageDead _ | StorageLive _ | Deinit _ | Drop _ | Nop ->
        not must_end_with_exit
    | Abort _ | Return -> true
  and can_be_moved_seq (stmts : statement list) : bool =
    match stmts with
    | [] -> true
    | [ single ] -> can_be_moved_aux true single
    | hd :: tl -> can_be_moved_aux false hd && can_be_moved_seq tl
  in

  (* The visitor *)
  let obj =
    object
      inherit [_] map_statement as super

      method! visit_block_suffix env stmts =
        match stmts with
        | ({ content = Switch switch; _ } as st) :: tl when can_be_moved_seq tl
          ->
            let content = super#visit_Switch env (append_to_switch switch tl) in
            [ { st with content } ]
        | _ -> super#visit_block_suffix env stmts
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body -> Some { body with body = obj#visit_block () body.body }
    | None -> None
  in
  let f = { f with body } in
  log#ldebug
    (lazy
      ("Before/after [remove_useless_cf_merges]:\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f0
      ^ "\n\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f
      ^ "\n"));
  f

(** This pass restructures the control-flow by inserting all the statements
    which occur after loops *inside* the loops, thus removing the need to have
    breaks (we later check that we removed all the breaks).

    This is needed because of the way we perform the symbolic execution on the
    loops for now.

    Rem.: we check that there are no nested loops (all the breaks must break to
    the first outer loop, and the statements we insert inside the loops mustn't
    contain breaks themselves).

    For instance, it performs the following transformation:
    {[
      loop {
        if b {
          ...
          continue 0;
        }
        else {
          ...
          break 0;
        }
      };
      x := x + 1;
      return;

      ~~>

      loop {
        if b {
          ...
          continue 0;
        }
        else {
          ...
          x := x + 1;
          return;
        }
      };
    ]}

    We also insert the statements occurring after branchings (matches or if then
    else) inside the branches. For instance:
    {[
      if b {
        s0;
      }
      else {
        s1;
      }
      return;

        ~~>

      if b {
        s0;
        return;
      }
      else {
        s1;
        return;
      }
    ]}

    This is necessary because loops might appear inside branchings: if we don't
    do this some paths inside the loop might not end with a
    break/continue/return.Aeneas *)
let remove_loop_breaks (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in

  (* Check that a statement doesn't contain loops, breaks or continues *)
  let statement_has_no_loop_break_continue (st : statement) : bool =
    let obj =
      object
        inherit [_] iter_statement
        method! visit_Loop _ _ = raise Found
        method! visit_Break _ _ = raise Found
        method! visit_Continue _ _ = raise Found
      end
    in
    try
      obj#visit_statement () st;
      true
    with Found -> false
  in

  (* Replace a break statement with another statement (we check that the
     break statement breaks exactly one level, and that there are no nested
     loops.
     TODO: call this on a loop directly to avoid tracking `entered_loop`
  *)
  let replace_breaks_with (st : statement) (new_stmts : statement list) :
      statement =
    let obj =
      object (self : 'self)
        inherit [_] map_statement as super

        method! visit_block_suffix entered_loop stmts =
          match stmts with
          | ({ content = Loop loop; _ } as st) :: tl ->
              cassert __FILE__ __LINE__ (not entered_loop) st.span
                "Nested loops are not supported yet";
              { st with content = super#visit_Loop true loop }
              :: self#visit_block_suffix entered_loop tl
          | ({ content = Break i; _ } as st) :: tl ->
              cassert __FILE__ __LINE__ (i = 0) st.span
                "Breaks to outer loops are not supported yet";
              new_stmts @ self#visit_block_suffix entered_loop tl
          | _ -> super#visit_block_suffix entered_loop stmts
      end
    in
    obj#visit_statement false st
  in

  let replace_visitor =
    object
      inherit [_] map_statement as super

      method! visit_block_suffix env stmts =
        match stmts with
        | ({ content = Loop _; _ } as st) :: tl ->
            cassert __FILE__ __LINE__
              (List.for_all statement_has_no_loop_break_continue tl)
              st.span "Sequences of loops are not supported yet";
            [ super#visit_statement env (replace_breaks_with st tl) ]
        | ({ content = Switch switch; _ } as st) :: tl ->
            (* Push the remaining statements inside of the switch *)
            let content = Switch (append_to_switch switch tl) in
            let st = { st with content } in
            [ super#visit_statement env st ]
        | _ -> super#visit_block_suffix env stmts
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body ->
        Some { body with body = replace_visitor#visit_block () body.body }
    | None -> None
  in

  let f = { f with body } in
  log#ldebug
    (lazy
      ("Before/after [remove_loop_breaks]:\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f0
      ^ "\n\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f
      ^ "\n"));
  f

(** Remove the use of shallow borrows and the storage live/dead instructions.

    Storage live/dead instructions are not used by the symbolic/concrete
    interpreter, so we can safely remove them.

    Shallow borrows are used in early versions of MIR for the sole use of the
    borrow checker (they have no runtime semantics). They are used to prevent
    match guards from changing a discriminant that is being matched on.

    For instance, let's consider the following Rust code:
    {[
      let mut x = (true, true);
      match x {
          (false, _) => 1,
          (true, _) if { x.0 = false; false } => 0,
          (_, true) => 2,
          (true, _) => 3,
      }
    ]}

    If this code was allowed, it would reach an `unreachable_unchecked` code
    path. Rust disallows this by adding a shallow borrow of each place whose
    discriminant is read, and a fake (removed before codegen) read of that
    borrow.

    We discard these in Aeneas. This does allow more code to pass the
    borrow-checker, but the UB is still correctly caught by the
    evaluator/translation hence the translation is still sound. *)
let remove_shallow_borrows_storage_live_dead (crate : crate) (f : fun_decl) :
    fun_decl =
  let f0 = f in
  let filter_in_body (body : block) : block =
    let filtered = ref LocalId.Set.empty in

    let filter_visitor =
      object
        inherit [_] map_statement as super

        method! visit_Assign env p rv =
          match (p.kind, rv) with
          | PlaceLocal var_id, RvRef (_, BShallow) ->
              (* Filter *)
              filtered := LocalId.Set.add var_id !filtered;
              Nop
          | _ ->
              (* Don't filter *)
              super#visit_Assign env p rv
      end
    in

    let storage_rem_visitor =
      object
        inherit [_] map_statement as super

        method! visit_StorageLive env loc =
          if LocalId.Set.mem loc !filtered then Nop
          else super#visit_StorageLive env loc

        method! visit_StorageDead env loc =
          if LocalId.Set.mem loc !filtered then Nop
          else super#visit_StorageDead env loc
      end
    in

    (* Filter the variables *)
    let body = filter_visitor#visit_block () body in
    let body = storage_rem_visitor#visit_block () body in

    (* Check that the filtered variables have completely disappeared from the body *)
    let check_visitor =
      object
        inherit [_] iter_statement as super

        (* Remember the span of the statement we enter *)
        method! visit_statement _ st = super#visit_statement st.span st

        method! visit_local_id span id =
          cassert __FILE__ __LINE__
            (not (LocalId.Set.mem id !filtered))
            span
            "Filtered variables should have completely disappeared from the \
             body"
      end
    in
    check_visitor#visit_block body.span body;

    (* Return the updated body *)
    body
  in

  let body =
    match f.body with
    | None -> None
    | Some body -> Some { body with body = filter_in_body body.body }
  in
  let f = { f with body } in
  log#ldebug
    (lazy
      ("Before/after [remove_shallow_borrows]:\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f0
      ^ "\n\n"
      ^ Print.Crate.crate_fun_decl_to_string crate f
      ^ "\n"));
  f

(** `StorageDead`, `Deinit` and `Drop` have the same semantics as far as Aeneas
    is concerned: they store bottom in the place. This maps all three to
    `Deinit` to simplify later work. Note: `Drop` actually also calls code to
    deallocate the value; we decide to ignore this for now. *)
let unify_drops (f : fun_decl) : fun_decl =
  let lookup_local (locals : locals) (var_id : local_id) : local =
    List.nth locals.locals (LocalId.to_int var_id)
  in

  let unify_visitor =
    object
      inherit [_] map_statement
      method! visit_Drop _ p _ = Deinit p

      method! visit_StorageDead locals var_id =
        let ty = (lookup_local locals var_id).var_ty in
        let p = { kind = PlaceLocal var_id; ty } in
        Deinit p
    end
  in

  let body =
    match f.body with
    | None -> None
    | Some body ->
        let new_body = unify_visitor#visit_block body.locals body.body in
        Some { body with body = new_body }
  in
  { f with body }

(* Remove the type aliases from the type declarations and declaration groups *)
let filter_type_aliases (crate : crate) : crate =
  let type_decl_is_alias (ty : type_decl) =
    match ty.kind with
    | Alias _ -> true
    | _ -> false
  in
  (* Whether the declaration group has a single entry that is a type alias.
     Type aliases should not be in recursive groups so we also ensure this doesn't
     happen. *)
  let decl_group_is_single_alias = function
    | TypeGroup (NonRecGroup id) ->
        type_decl_is_alias (TypeDeclId.Map.find id crate.type_decls)
    | TypeGroup (RecGroup ids) ->
        List.iter
          (fun id ->
            let ty = TypeDeclId.Map.find id crate.type_decls in
            if type_decl_is_alias ty then
              craise __FILE__ __LINE__ ty.item_meta.span
                "found a type alias within a recursive group; this is \
                 unexpected")
          ids;
        false
    | _ -> false
  in
  {
    crate with
    type_decls =
      TypeDeclId.Map.filter
        (fun _id ty -> not (type_decl_is_alias ty))
        crate.type_decls;
    declarations =
      List.filter
        (fun decl -> not (decl_group_is_single_alias decl))
        crate.declarations;
  }

(** Whenever we write a string literal in Rust, rustc actually introduces a
    constant of type [&str]. Generally speaking, because [str] is unsized, it
    doesn't make sense to manipulate values of type [str] directly. But in the
    context of Aeneas, it is reasonable to decompose those literals into: a
    string stored in a local variable, then a borrow of this variable.

    Remark: the new statements all have the id 0: this pass requires to refresh
    the ids later. *)
let decompose_str_borrows (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | Some body ->
        let new_locals = ref [] in
        let _, gen =
          LocalId.mk_stateful_generator_starting_at_id
            (LocalId.of_int (List.length body.locals.locals))
        in
        let fresh_local ty =
          let local = { index = gen (); var_ty = ty; name = None } in
          new_locals := local :: !new_locals;
          local.index
        in

        (* Function to decompose a constant literal *)
        let decompose_rvalue (span : Meta.span) (lv : place) (rv : rvalue) :
            statement list =
          let new_statements = ref [] in

          (* Visit the rvalue *)
          let visitor =
            object
              inherit [_] map_statement as super

              (* We have to visit all the constant operands.
                 As we might need to replace them with borrows, while borrows
                 are rvalues (i.e., not operands) we have to introduce two
                 intermediate statements: the string initialization, then
                 the borrow, that we can finally move.
              *)
              method! visit_Constant env cv =
                match (cv.value, cv.ty) with
                | ( CLiteral (VStr str),
                    TRef
                      (_, (TAdt { id = TBuiltin TStr; _ } as str_ty), ref_kind)
                  ) ->
                    (* We need to introduce intermediate assignments *)
                    (* First the string initialization *)
                    let local_id =
                      let local_id = fresh_local str_ty in
                      let new_cv : constant_expr =
                        { value = CLiteral (VStr str); ty = str_ty }
                      in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          content =
                            Assign
                              ( { kind = PlaceLocal local_id; ty = str_ty },
                                Use (Constant new_cv) );
                          comments_before = [];
                        }
                      in
                      new_statements := st :: !new_statements;
                      local_id
                    in
                    (* Then the borrow *)
                    let local_id =
                      let nlocal_id = fresh_local cv.ty in
                      let bkind =
                        match ref_kind with
                        | RMut -> BMut
                        | RShared -> BShared
                      in
                      let rv =
                        RvRef
                          ({ kind = PlaceLocal local_id; ty = str_ty }, bkind)
                      in
                      let lv = { kind = PlaceLocal nlocal_id; ty = cv.ty } in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          content = Assign (lv, rv);
                          comments_before = [];
                        }
                      in
                      new_statements := st :: !new_statements;
                      nlocal_id
                    in
                    (* Finally we can move the value *)
                    Move { kind = PlaceLocal local_id; ty = cv.ty }
                | _ -> super#visit_Constant env cv
            end
          in

          let rv = visitor#visit_rvalue () rv in

          (* Construct the sequence *)
          let assign =
            {
              span;
              statement_id = StatementId.zero;
              content = Assign (lv, rv);
              comments_before = [];
            }
          in
          (* Note that the new statements are in reverse order *)
          let statements = assign :: !new_statements in
          List.rev statements
        in

        (* Visit all the statements and decompose the literals *)
        let visitor =
          object
            inherit [_] map_statement as super
            method! visit_statement _ st = super#visit_statement st.span st

            method! visit_block _ blk =
              let statements =
                List.concat_map
                  (fun (st : statement) ->
                    let st = super#visit_statement st.span st in
                    match st.content with
                    | Assign (lv, rv) -> decompose_rvalue st.span lv rv
                    | _ -> [ st ])
                  blk.statements
              in
              { blk with statements }
          end
        in

        let body_body = visitor#visit_block body.body.span body.body in
        Some
          {
            body with
            body = body_body;
            locals =
              {
                body.locals with
                locals = body.locals.locals @ List.rev !new_locals;
              };
          }
    | None -> None
  in
  { f with body }

(** Refresh the statement ids to make sure they are unique *)
let refresh_statement_ids (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | Some body ->
        let _, gen_id = StatementId.fresh_stateful_generator () in

        (* Visit the rvalue *)
        let visitor =
          object
            inherit [_] map_statement
            method! visit_statement_id _ _ = gen_id ()
          end
        in

        Some { body with body = visitor#visit_block () body.body }
    | None -> None
  in
  { f with body }

let apply_passes (crate : crate) : crate =
  (* Passes that apply to the whole crate *)
  let crate = update_array_default crate in
  (* Passes that apply to individual function bodies *)
  let function_passes =
    [
      remove_loop_breaks crate;
      remove_shallow_borrows_storage_live_dead crate;
      decompose_str_borrows;
      unify_drops;
      refresh_statement_ids;
    ]
  in
  (* Attempt to apply a pass: if it fails we replace the body by [None] *)
  let apply_function_pass (pass : fun_decl -> fun_decl) (f : fun_decl) =
    try pass f
    with CFailure _ ->
      (* The error was already registered, we don't need to register it twice.
         However, we replace the body of the function, and save an error to
         report to the user the fact that we will ignore the function body *)
      let fmt = Print.Crate.crate_to_fmt_env crate in
      let name = Print.name_to_string fmt f.item_meta.name in
      save_error __FILE__ __LINE__ f.item_meta.span
        ("Ignoring the body of '" ^ name ^ "' because of previous error");
      { f with body = None }
  in
  let fun_decls =
    List.fold_left
      (fun fl pass -> FunDeclId.Map.map (apply_function_pass pass) fl)
      crate.fun_decls function_passes
  in
  let crate = { crate with fun_decls } in
  let crate = filter_type_aliases crate in
  log#ldebug
    (lazy ("After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"));
  crate
