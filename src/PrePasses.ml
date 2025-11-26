(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it *)

open Types
open TypesUtils
open Expressions
open LlbcAst
open Utils
open LlbcAstUtils
open Errors

let log = Logging.pre_passes_log

let statement_to_string (crate : crate) =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in
  Print.Ast.statement_to_string fmt_env "" "  "

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
      [%silent_unwrap_opt_span] (Some impl.item_meta.span)
        (TraitDeclId.Map.find_opt impl.impl_trait.id crate.trait_decls)
    in
    if match_name impl_pat trait_decl.item_meta.name then (
      [%ldebug
        "found a matching impl.\n - decl_generics: "
        ^ Print.generic_args_to_string pctx impl.impl_trait.generics];
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
          assert (meth.binder_params = empty_generic_params);
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
              | _ -> [%internal_error] fdecl.item_meta.span)
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
            match fn_ptr.kind with
            | FunId (FRegular fid) -> begin
                match FunDeclId.Map.find_opt fid methods with
                | None -> super#visit_fn_ptr env fn_ptr
                | Some n ->
                    let fn_ptr =
                      {
                        kind = FunId (FRegular merged_method);
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

(** Check that loops:
    - do not contain early returns
    - do not continue/break to outer loops

    We also attempt to update the loops so that they have the proper shape (for
    instance, if a loop has returns but no breaks, we replace the returns with
    breaks, and move the returns after the loop).

    We do the following transformations:

    # Transformation 1:
    {[
      loop {
        if e {
          return;
        } else {
          continue;
        }
      }

        ~~>

      loop {
        if e {
          break;
        } else {
          continue;
        }
      };
      return;
    ]}

    # Transformation 2:
    {[
      loop {
        if e0 {
          st0;
          return;
        } else if e1 {
          break;
        } else {
          continue;
        }
      }
      st1;
      return;

        ~~>

      loop {
        if e0 {
          st0;
          break;
        } else if e1 {
          st1;
          break;
        } else {
          continue;
        }
      }
      return;
    ]} *)
let update_loops (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  let span = f.item_meta.span in

  let visitor =
    object (self)
      inherit [_] map_statement as super

      (* [after]: the list of statements coming *after* this one in this block.

         We return:
         - the list of statements resulting from updating the current statement
         - the list of statements to put after and that are yet to be updated
           (the reason is that we might have moved some of those statements
           inside the current statement).
      *)
      method update_statement (depth : int) (st : statement)
          (after : statement list) : statement list * statement list =
        match st.kind with
        | Loop loop -> (
            try ([ { st with kind = super#visit_Loop (depth + 1) loop } ], after)
            with Found ->
              (* We found a return in the loop: attempt to replace it with a break.

                 There are two cases:
                 - either the loop does not contain any break, in which case we
                   can simply replace the return with a break, and move the return
                   after the loop (this is transformation 1 above)
                 - or there is already a break in the loop: we can apply transformation
                   2 if the statements after the loop end with a return.
              *)
              let block_has_no_breaks (b : block) : bool =
                let visitor =
                  object
                    inherit [_] iter_statement
                    method! visit_Break _ _ = raise Found
                  end
                in
                try
                  visitor#visit_block () b;
                  true
                with Found -> false
              in
              if block_has_no_breaks loop then (* Transformation 1 *)
                let block_replace (b : block) : block =
                  let visitor =
                    object
                      inherit [_] map_statement

                      method! visit_Return _ =
                        (* Replace the return with a break *)
                        Break 0
                    end
                  in
                  visitor#visit_block () b
                in
                let loop = block_replace loop in
                let loop : statement = { st with kind = Loop loop } in
                let loop = super#visit_statement depth loop in
                let return : statement =
                  {
                    span = st.span;
                    statement_id =
                      StatementId.zero (* we'll refresh this later *);
                    kind = Return;
                    comments_before = [];
                  }
                in
                ([ loop; return ], after)
              else
                (* Transformation 2 *)
                (* Check if the statements after the loop end with a return *)
                let rec decompose_after (after : statement list) :
                    statement list * statement =
                  match after with
                  | [] ->
                      [%craise] span
                        "Early returns inside of loops are not supported yet"
                  | st :: after -> (
                      match st.kind with
                      | Return -> ([], st)
                      | _ ->
                          let after, return = decompose_after after in
                          (st :: after, return))
                in
                let after, return = decompose_after after in
                let replace (st : statement) : statement list =
                  match st.kind with
                  | Return ->
                      (* Replace the return with a break *)
                      [ { st with kind = Break 0 } ]
                  | Break i ->
                      (* Move the statements [after] before the break *)
                      [%cassert] span (i = 0)
                        "Breaks to outer loops are not supported yet";
                      after @ [ st ]
                  | _ -> [ st ]
                in
                let loop = map_statement replace loop in
                let loop : statement = { st with kind = Loop loop } in
                let loop = super#visit_statement depth loop in
                ([ loop; return ], []))
        | _ -> ([ super#visit_statement depth st ], after)

      method! visit_block depth (block : block) : block =
        let rec update (stl : statement list) : statement list =
          match stl with
          | [] -> []
          | st :: stl ->
              let stl0, stl1 = self#update_statement depth st stl in
              stl0 @ update stl1
        in
        { block with statements = update block.statements }

      method! visit_Break depth i =
        [%cassert] span (i = 0) "Breaks to outer loops are not supported yet";
        super#visit_Break depth i

      method! visit_Continue depth i =
        [%cassert] span (i = 0) "Continue to outer loops are not supported yet";
        super#visit_Continue depth i

      method! visit_Return depth =
        [%cassert] span (depth <= 1)
          "Returns inside of nested loops are not supported yet";
        (* If we are inside a loop we need to get rid of the return *)
        if depth = 1 then raise Found else super#visit_Return depth
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body -> Some { body with body = visitor#visit_block 0 body.body }
    | None -> None
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    "Before/after [update_loops]:\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f0
    ^ "\n\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f];
  f

(** Inline what comes after an [if then else], a [switch] or a [match], etc.
    under certain conditions, to prevent useless joins from being performed by
    the symbolic execution.

    The main goal of this pass is to improve the quality of the generated code.
*)
let remove_useless_joins (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in

  let rec update_block (to_inline : statement list) (block : block) :
      bool * block =
    let can_inline, statements = update_statements to_inline block.statements in
    (can_inline, { block with statements })
  and update_statements (to_inline : statement list) (ls : statement list) :
      bool * statement list =
    match ls with
    | [] -> (true, to_inline)
    | st :: ls -> (
        [%ldebug
          "ls:\n"
          ^ Print.list_to_string ~sep:"\n" (statement_to_string crate) ls];
        let can_inline, ls = update_statements to_inline ls in
        match st.kind with
        | Nop | StorageLive _ | StorageDead _ | Deinit _ | Drop _ ->
            (can_inline, st :: ls)
        | Abort _ | Return | Break _ | Continue _ -> (true, [ st ])
        | Switch switch ->
            [%ldebug "Switch: can_inline: " ^ Print.bool_to_string can_inline];
            (* Attempt to inline inside the body *)
            let to_inline, ls = if can_inline then (ls, []) else ([], ls) in
            let update b = snd (update_block to_inline b) in
            let switch =
              match switch with
              | If (scrut, st0, st1) -> If (scrut, update st0, update st1)
              | SwitchInt (op, ty, branches, otherwise) ->
                  let branches =
                    List.map (fun (pats, br) -> (pats, update br)) branches
                  in
                  let otherwise = update otherwise in
                  SwitchInt (op, ty, branches, otherwise)
              | Match (scrut, branches, otherwise) ->
                  let branches =
                    List.map (fun (id, br) -> (id, update br)) branches
                  in
                  let otherwise = Option.map update otherwise in
                  Match (scrut, branches, otherwise)
            in
            let ls = { st with kind = Switch switch } :: ls in
            [%ldebug
              "after updating the switch:\n"
              ^ Print.list_to_string ~sep:"\n" (statement_to_string crate) ls];
            (false, ls)
        | Loop loop ->
            (* Update the inside of the loop *)
            (false, { st with kind = Loop (snd (update_block [] loop)) } :: ls)
        | Assign (_, rv) -> (
            (* We allow inlining some assignments (otherwise the pass is too restrictive) *)
            match rv with
            | Use _ | RvRef _ | RawPtr _ | NullaryOp _ | Aggregate _ ->
                (can_inline, st :: ls)
            | BinaryOp _
            | UnaryOp _
            | Discriminant _
            | Len _
            | Repeat _
            | ShallowInitBox _ -> (false, st :: ls))
        | SetDiscriminant _ | CopyNonOverlapping _ | Assert _ | Call _ | Error _
          -> (false, st :: ls))
  in

  let body =
    match f.body with
    | Some body -> Some { body with body = snd (update_block [] body.body) }
    | None -> None
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    "Before/after [remove_useless_joins]:\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f0
    ^ "\n\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f];
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

    let filter_shallow (st : statement) : statement list =
      match st.kind with
      | Assign (p, rv) -> (
          match (p.kind, rv) with
          | PlaceLocal var_id, RvRef (_, BShallow, _) ->
              (* Filter *)
              filtered := LocalId.Set.add var_id !filtered;
              []
          | _ -> [ st ])
      | _ -> [ st ]
    in

    let filter_storage (st : statement) : statement list =
      match st.kind with
      | StorageLive _ -> []
      | StorageDead loc when LocalId.Set.mem loc !filtered -> []
      | _ -> [ st ]
    in

    (* Filter the variables *)
    let body = map_statement filter_shallow body in
    let body = map_statement filter_storage body in

    (* Check that the filtered variables have completely disappeared from the body *)
    let check_visitor =
      object
        inherit [_] iter_statement as super

        (* Remember the span of the statement we enter *)
        method! visit_statement _ st = super#visit_statement st.span st

        method! visit_local_id span id =
          [%cassert] span
            (not (LocalId.Set.mem id !filtered))
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
  [%ldebug
    "Before/after [remove_shallow_borrows]:\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f0
    ^ "\n\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f];
  f

(** `StorageDead`, `Deinit` and `Drop` have the same semantics as far as Aeneas
    is concerned: they store bottom in the place. This maps all three to
    `Deinit` to simplify later work. Note: `Drop` actually also calls code to
    deallocate the value; we decide to ignore this for now. *)
let unify_drops (_ : crate) (f : fun_decl) : fun_decl =
  let lookup_local (locals : locals) (var_id : local_id) : local =
    List.nth locals.locals (LocalId.to_int var_id)
  in

  let unify_visitor =
    object
      inherit [_] map_statement
      method! visit_Drop _ p _ _ = Deinit p

      method! visit_StorageDead locals var_id =
        let ty = (lookup_local locals var_id).local_ty in
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
              [%craise] ty.item_meta.span
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
let decompose_str_borrows (_ : crate) (f : fun_decl) : fun_decl =
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
          let local = { index = gen (); local_ty = ty; name = None } in
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
              method! visit_Constant env (cv : constant_expr) =
                match (cv.kind, cv.ty) with
                | ( CLiteral (VStr str),
                    TRef
                      (_, (TAdt { id = TBuiltin TStr; _ } as str_ty), ref_kind)
                  ) ->
                    (* We need to introduce intermediate assignments *)
                    (* First the string initialization *)
                    let local_id =
                      let local_id = fresh_local str_ty in
                      let new_cv : constant_expr =
                        { kind = CLiteral (VStr str); ty = str_ty }
                      in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          kind =
                            Assign
                              ( { kind = PlaceLocal local_id; ty = str_ty },
                                Use (Constant new_cv) );
                          comments_before = [];
                        }
                      in
                      new_statements := st :: !new_statements;
                      local_id
                    in
                    let str_len =
                      Constant
                        {
                          kind =
                            CLiteral
                              (VScalar
                                 (UnsignedScalar
                                    (Usize, Z.of_int (String.length str))));
                          ty = TLiteral (TUInt Usize);
                        }
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
                          ( { kind = PlaceLocal local_id; ty = str_ty },
                            bkind,
                            str_len )
                      in
                      let lv = { kind = PlaceLocal nlocal_id; ty = cv.ty } in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          kind = Assign (lv, rv);
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
              kind = Assign (lv, rv);
              comments_before = [];
            }
          in
          (* Note that the new statements are in reverse order *)
          let statements = assign :: !new_statements in
          List.rev statements
        in

        (* Visit all the statements and decompose the literals *)
        let decompose_in_statement (st : statement) : statement list =
          match st.kind with
          | Assign (lv, rv) -> decompose_rvalue st.span lv rv
          | _ -> [ st ]
        in
        let body_body = map_statement decompose_in_statement body.body in
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
let refresh_statement_ids (_ : crate) (f : fun_decl) : fun_decl =
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

(** This micro-pass introduces intermediate assignments to access the global
    values in order to simplify the semantics.

    Whenever we access a constant, we introduce a shared borrow and a
    dereference. Ex.:

    {[
      let x = copy C;

        ~~>

      let tmp = &C;
      let x = copy *C;
    ]}

    Remark: we use the crate to lookup the type of the globals.

    TODO: generalize the evaluation of globals in the symbolic interpreter. *)
let decompose_global_accesses (crate : crate) (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | None -> None
    | Some body -> (
        let new_locals = ref [] in
        let _, gen =
          LocalId.mk_stateful_generator_starting_at_id
            (LocalId.of_int (List.length body.locals.locals))
        in
        let fresh_local ty =
          let local = { index = gen (); local_ty = ty; name = None } in
          new_locals := local :: !new_locals;
          local.index
        in

        (* Function to decompose the operands in a statement *)
        let decompose_in_statement (st : statement) : statement list =
          let span = st.span in
          let new_statements = ref [] in

          (* Visit the rvalue *)
          let visitor =
            object
              inherit [_] map_statement as super
              method! visit_place _ p = super#visit_place p.ty p

              method! visit_PlaceGlobal ty gref =
                (* Compute the type of the reference *)
                let ref_ty = TRef (RErased, ty, RShared) in

                (* Introduce the intermediate reference *)
                let local_id =
                  let local_id = fresh_local ref_ty in
                  let metadata =
                    Copy
                      {
                        kind = PlaceGlobal crate.unit_metadata;
                        ty = mk_unit_ty;
                      }
                  in
                  let st =
                    {
                      span;
                      statement_id = StatementId.zero;
                      kind =
                        Assign
                          ( { kind = PlaceLocal local_id; ty = ref_ty },
                            RvRef
                              ( { kind = PlaceGlobal gref; ty },
                                BShared,
                                metadata ) );
                      comments_before = [];
                    }
                  in
                  new_statements := st :: !new_statements;
                  local_id
                in

                (* Finally we can update the place *)
                PlaceProjection
                  ({ kind = PlaceLocal local_id; ty = ref_ty }, Deref)
            end
          in

          let kind =
            match st.kind with
            | Assign (lv, rv) -> Assign (lv, visitor#visit_rvalue mk_unit_ty rv)
            | CopyNonOverlapping { src; dst; count } ->
                let src = visitor#visit_operand mk_unit_ty src in
                CopyNonOverlapping { src; dst; count }
            | Assert { cond; expected; on_failure } ->
                let cond = visitor#visit_operand mk_unit_ty cond in
                Assert { cond; expected; on_failure }
            | Call { func; args; dest } ->
                let func = visitor#visit_fn_operand mk_unit_ty func in
                let args = List.map (visitor#visit_operand mk_unit_ty) args in
                Call { func; args; dest }
            | SetDiscriminant _
            | StorageLive _
            | StorageDead _
            | Deinit _
            | Drop _
            | Abort _
            | Return
            | Break _
            | Continue _
            | Nop
            | Switch _
            | Loop _
            | Error _ -> st.kind
          in
          let st = { st with kind } in

          List.rev (st :: !new_statements)
        in

        (* Visit all the statements and decompose the operands *)
        try
          let body_body = map_statement decompose_in_statement body.body in
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
        with CFailure error ->
          let mctx = Charon.NameMatcher.ctx_from_crate crate in
          let fmt_env = Print.Crate.crate_to_fmt_env crate in
          let name = Print.Types.name_to_string fmt_env f.item_meta.name in
          let name_pattern =
            try
              let c : Charon.NameMatcher.to_pat_config =
                {
                  tgt = TkPattern;
                  use_trait_decl_refs = ExtractName.match_with_trait_decl_refs;
                }
              in
              let pat =
                LlbcAstUtils.name_to_pattern (Some f.item_meta.span) mctx c
                  f.item_meta.name
              in
              Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat
            with CFailure _ ->
              "(could not compute the name pattern due to a different error)"
          in
          [%save_error_opt_span] error.span
            ("Failure when pre- processing: " ^ name
           ^ "; ignoring its body.\nName pattern: '" ^ name_pattern ^ "'");
          None)
  in
  { f with body }

let apply_passes (crate : crate) : crate =
  (* Passes that apply to the whole crate *)
  let crate = update_array_default crate in
  (* Passes that apply to individual function bodies *)
  let function_passes =
    [
      ("update_loop", update_loops);
      ("remove_useless_joins", remove_useless_joins);
      ( "remove_shallow_borrows_storage_live_dead",
        remove_shallow_borrows_storage_live_dead );
      ("decompose_str_borrows", decompose_str_borrows);
      ("unify_drops", unify_drops);
      ("decompose_global_accesses", decompose_global_accesses);
      ("refresh_statement_ids", refresh_statement_ids);
    ]
  in
  (* Attempt to apply a pass: if it fails we replace the body by [None] *)
  let apply_function_pass (pass_name : string)
      (pass : crate -> fun_decl -> fun_decl) (f : fun_decl) =
    try
      let f = pass crate f in
      [%ltrace
        "After applying [" ^ pass_name ^ "]:\n"
        ^ Print.Crate.crate_fun_decl_to_string crate f];
      f
    with CFailure _ ->
      (* The error was already registered, we don't need to register it twice.
         However, we replace the body of the function, and save an error to
         report to the user the fact that we will ignore the function body *)
      let fmt = Print.Crate.crate_to_fmt_env crate in
      let name = Print.name_to_string fmt f.item_meta.name in
      [%save_error] f.item_meta.span
        ("Ignoring the body of '" ^ name ^ "' because of previous error");
      { f with body = None }
  in
  let fun_decls : fun_decl FunDeclId.Map.t =
    let num_decls = FunDeclId.Map.cardinal crate.fun_decls in
    ProgressBar.with_reporter num_decls "Applied prepasses: " (fun report ->
        FunDeclId.Map.map
          (fun f ->
            let f : fun_decl =
              List.fold_left
                (fun f (name, pass) -> apply_function_pass name pass f)
                f function_passes
            in
            report 1;
            f)
          crate.fun_decls)
  in
  let crate = { crate with fun_decls } in
  let crate = filter_type_aliases crate in
  [%ltrace "After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"];
  crate
