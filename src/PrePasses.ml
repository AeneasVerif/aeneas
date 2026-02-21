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

let call_to_string (crate : crate) =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in
  Print.Ast.call_to_string fmt_env "  "

let fun_decl_ref_to_string (crate : crate) =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in
  Print.fun_decl_ref_to_string fmt_env

let generic_args_to_string (crate : crate) (generics : generic_args) =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in
  let generics, traits = Print.Types.generic_args_to_strings fmt_env generics in
  "<" ^ String.concat ", " (generics @ traits) ^ ">"

let generic_params_to_string (crate : crate) (generics : generic_params) =
  let fmt_env = Print.Crate.crate_to_fmt_env crate in
  let generics, traits =
    Print.Types.generic_params_to_strings fmt_env generics
  in
  "<" ^ String.concat ", " (generics @ traits) ^ ">"

(** Erase the useless body regions.

    We erase the body regions which appear in:
    - locals
    - places

    We only keep those used in function calls. *)
let erase_body_regions (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in

  let erase_visitor =
    object
      inherit [_] map_statement

      method! visit_fn_operand _ x =
        (* Do not erase the use of body regions inside function operands *)
        x

      method! visit_RBody _ _ = RErased
      method! visit_RVar _ _ = RErased
      method! visit_RStatic _ = RErased
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body ->
        let body =
          {
            body with
            locals =
              {
                body.locals with
                locals =
                  List.map Contexts.local_erase_regions body.locals.locals;
              };
          }
        in
        Some { body with body = erase_visitor#visit_block 0 body.body }
    | None -> None
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    "Before/after [erase_body_regions]:\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f0
    ^ "\n\n"
    ^ Print.Crate.crate_fun_decl_to_string crate f];
  f

(** Replace the occurrences of [core::intrinsics::unreachable] with
    [Abort UndefinedBehavior]. This helps with the analyzes and the symbolic
    evaluation (in particular, we stop the evaluation when encountering an
    [Abort] - this can help us avoid merging control-flow after a match for
    instance *)
let remove_unreachable (crate : crate) (f : fun_decl) : fun_decl =
  let impl_pat = NameMatcher.parse_pattern "core::intrinsics::unreachable" in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_name =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in

  let is_unreachable (st : statement) : bool =
    match st.kind with
    | Call call -> (
        match call.func with
        | FnOpRegular { kind; _ } -> (
            match kind with
            | FunId (FRegular fid) ->
                let fun_decl =
                  [%silent_unwrap_opt_span] (Some st.span)
                    (FunDeclId.Map.find_opt fid crate.fun_decls)
                in
                match_name impl_pat fun_decl.item_meta.name
            | _ -> false)
        | FnOpDynamic _ -> false)
    | _ -> false
  in
  let rec update (stl : statement list) : statement list =
    match stl with
    | [] -> []
    | st :: stl ->
        if is_unreachable st then [ { st with kind = Abort UndefinedBehavior } ]
        else st :: update stl
  in
  let visitor =
    object
      inherit [_] map_statement_base as super

      method! visit_block env b =
        let b = { b with statements = update b.statements } in
        super#visit_block env b
    end
  in
  match f.body with
  | None -> f
  | Some body ->
      let body = { body with body = visitor#visit_block () body.body } in
      { f with body = Some body }

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
           TArray
             ( (TVar (Free _) as elem_ty),
               ({ kind = CLiteral (VScalar (UnsignedScalar (Usize, nv))); _ } as
                n) );
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
              let cg : Types.constant_expr =
                { kind = CVar (Free cg_id); ty = TypesUtils.mk_usize_ty }
              in
              let generics =
                {
                  impl.impl_trait.generics with
                  types = [ TArray (elem_ty, cg) ];
                }
              in
              let impl_trait = { impl.impl_trait with generics } in
              let params =
                {
                  impl.generics with
                  const_generics =
                    [
                      { index = cg_id; name = "N"; ty = TypesUtils.mk_usize_ty };
                    ];
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
              let cg : Types.constant_expr =
                { kind = CVar (Free cg_id); ty = TypesUtils.mk_usize_ty }
              in
              let sg = fdecl.signature in
              assert (sg.inputs = []);
              match sg.output with
              | TArray ((TVar (Free _) as elem_ty), _) ->
                  let generics =
                    {
                      fdecl.generics with
                      const_generics =
                        [
                          {
                            index = cg_id;
                            name = "N";
                            ty = TypesUtils.mk_usize_ty;
                          };
                        ];
                    }
                  in
                  let sg = { sg with output = TArray (elem_ty, cg) } in
                  let fdecl = { fdecl with signature = sg; generics } in
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

exception FoundStatement of statement

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
          st1;
          break;
        } else {
          continue;
        }
      }
      st2;
      return;

        ~~>

      loop {
        if e0 {
          st0;
          break;
        } else if e1 {
          st1;
          st2;
          break;
        } else {
          continue;
        }
      }
      return;
    ]}

    # Transformation 3:
    {[
      loop {
        if e0 {
          st0;
          return;
        } else if e1 {
          st1;
          break;
        } else {
          continue;
        }
      }
      st2;
      panic;

        ~~>

      loop {
        if e0 {
          st0;
          break;
        } else if e1 {
          st1;
          st2;
          panic;
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
            (* Recursively update the loop.

               Note that doing this will raise an exception if we find a loop with
               an early return. *)
            try ([ { st with kind = self#visit_Loop (depth + 1) loop } ], after)
            with FoundStatement return_st ->
              (* An exception was raised: it means we found a return in the loop: attempt
                 to replace it with a break.

                 There are 2 cases:
                 - either the loop does not contain any break, in which case we
                   can simply replace the return with a break, and move the return
                   after the loop (this is transformation 1 above)
                 - or there is already a break in the loop: we can apply transformation 2
                   (resp., 3) if the statements after the loop end with a return (resp., a panic)
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
                      method! visit_Loop i loop = super#visit_Loop (i + 1) loop

                      method! visit_Return i =
                        [%sanity_check] span (i = 0);
                        (* Replace the return with a break *)
                        Break i
                    end
                  in
                  visitor#visit_block 0 b
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
                (* Transformations 2 and 3 *)
                (* Check if the statements after the loop end with a return or a panic.
                   We output the statements with which to replace breaks.
                *)
                let rec decompose_after (after : statement list) :
                    statement list =
                  match after with
                  | [] ->
                      [%craise] span
                        "Early returns inside of loops are not supported yet"
                  | st :: after -> (
                      match st.kind with
                      | Return -> [ { st with kind = Break 0 } ]
                      | Abort _ -> [ st ]
                      | _ -> st :: decompose_after after)
                in
                let after = decompose_after after in
                let replace (st : statement) : statement list =
                  match st.kind with
                  | Return ->
                      (* Replace the return with a break *)
                      [ { st with kind = Break 0 } ]
                  | Break i ->
                      (* Move the statements [after] before the break *)
                      [%cassert] span (i = 0)
                        "Breaks to outer loops are not supported yet";
                      after
                  | _ -> [ st ]
                in

                let block_visitor =
                  object (self)
                    inherit [_] map_statement_base as super

                    method! visit_Loop depth loop =
                      super#visit_Loop (depth + 1) loop

                    method! visit_block depth b =
                      (* Only replace if the depth is 0 (it means we haven't dived
                         into an inner loop) *)
                      if depth = 0 then
                        let update st =
                          replace (self#visit_statement depth st)
                        in
                        {
                          b with
                          statements =
                            List.flatten (List.map update b.statements);
                        }
                      else b
                  end
                in

                let loop = block_visitor#visit_block 0 loop in
                let loop : statement = { st with kind = Loop loop } in
                let loop = super#visit_statement depth loop in
                ([ loop; return_st ], []))
        | _ -> ([ self#visit_statement depth st ], after)

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

      method! visit_statement depth st =
        match st.kind with
        | Return ->
            [%cassert] span (depth <= 1)
              "Returns inside of nested loops are not supported yet";
            (* If we are inside a loop we need to get rid of the return.

               Note that raising an exception containing the full return
               statement allows us to use its span when moving it after the loop. *)
            if depth = 1 then raise (FoundStatement st) else st
        | _ -> super#visit_statement depth st

      method! visit_Return _ =
        (* The Return case should have been caught by the [visit_statement] method *)
        [%internal_error] span
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
        | Nop | StorageLive _ | StorageDead _ | PlaceMention _ | Drop _ ->
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

(** We simplify statements of the shape:
    {[
      x := from_str<'_>(const ("Error"));
      panic(core::panicking::panic_fmt)

        ~>

      panic(core::panicking::panic_fmt)
    ]}

    TODO: remove *)
let simplify_panics (crate : crate) (f : fun_decl) : fun_decl =
  let pats =
    [
      "core::fmt::{core::fmt::Arguments<'a>}::from_str";
      "core::fmt::{core::fmt::Arguments<'a>}::from_str_nonconst";
    ]
  in
  let pats = List.map (fun p -> (NameMatcher.parse_pattern p, ())) pats in
  (* TODO: we shouldn't need to use a names map *)
  let names_map = NameMatcher.NameMatcherMap.of_list pats in
  let match_ctx = Charon.NameMatcher.ctx_from_crate crate in
  let is_from_str (d : fun_decl) =
    let config = ExtractName.default_match_config in
    NameMatcher.NameMatcherMap.mem match_ctx config d.item_meta.name names_map
  in

  let visitor =
    object (self)
      inherit [_] map_statement

      method! visit_block env (block : block) =
        let rec update (stl : statement list) : statement list =
          match stl with
          | [] -> []
          | [ st0; st1 ] -> (
              match (st0.kind, st1.kind) with
              | ( Call
                    { func = FnOpRegular { kind = FunId (FRegular fid); _ }; _ },
                  Abort (Panic _) ) -> (
                  match FunDeclId.Map.find_opt fid crate.fun_decls with
                  | Some decl when is_from_str decl -> [ st1 ]
                  | _ ->
                      [
                        self#visit_statement env st0;
                        self#visit_statement env st1;
                      ])
              | _ ->
                  [ self#visit_statement env st0; self#visit_statement env st1 ]
              )
          | st0 :: stl -> self#visit_statement env st0 :: update stl
        in
        { block with statements = update block.statements }
    end
  in

  let body =
    match f.body with
    | None -> None
    | Some body -> Some { body with body = visitor#visit_block () body.body }
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
            | Assert ({ cond; expected; check_kind }, on_failure) ->
                let cond = visitor#visit_operand mk_unit_ty cond in
                Assert ({ cond; expected; check_kind }, on_failure)
            | Call { func; args; dest } ->
                let func = visitor#visit_fn_operand mk_unit_ty func in
                let args = List.map (visitor#visit_operand mk_unit_ty) args in
                Call { func; args; dest }
            | SetDiscriminant _
            | StorageLive _
            | StorageDead _
            | PlaceMention _
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

(** We do not support static regions yet.

    In order to support some printing functions, for now we update their
    signature to replace ['static] with a region variable. This should be fine
    as a temporary measure as we can pretend these functions copy the input
    string they receive (the static references are references to strings).

    TODO: remove once https://github.com/AeneasVerif/aeneas/issues/727 is fixed
*)
let replace_static (crate : crate) : crate =
  (* We update the uses of: [core::fmt::{core::fmt::Arguments<'a>}::from_str] *)
  let pat =
    NameMatcher.parse_pattern "core::fmt::{core::fmt::Arguments<'a>}::from_str"
  in

  (* Find the function [core::fmt::{core::fmt::Arguments<'a>}::from_str]:
     - we want to update its signature to replace 'static with a lifetime variable
     - we want to update its uses
  *)
  let names_set = NameMatcher.NameMatcherMap.of_list [ (pat, ()) ] in
  let match_ctx = Charon.NameMatcher.ctx_from_crate crate in
  let in_set (d : fun_decl) : bool =
    let config = ExtractName.default_match_config in
    NameMatcher.NameMatcherMap.mem match_ctx config d.item_meta.name names_set
  in
  let decl_opt = ref None in
  let in_set (_ : FunDeclId.id) (d : fun_decl) =
    if in_set d then (
      decl_opt := Some d;
      true)
    else false
  in

  if not (FunDeclId.Map.exists in_set crate.fun_decls) then crate
  else (* The function [from_str] is used in the crate *)
    let d = Option.get !decl_opt in

    (* Update the signature *)
    let generics =
      {
        d.generics with
        regions =
          d.generics.regions
          @ [ { index = RegionId.of_int 1; name = Some "'b" } ];
      }
    in
    let signature =
      let visitor =
        object
          inherit [_] map_ty
          method! visit_RStatic _ = RVar (Free (RegionId.of_int 1))
        end
      in
      visitor#visit_fun_sig () d.signature
    in

    let d = { d with generics; signature } in
    [%ltrace
      "Updated declaration:\n" ^ Print.Crate.crate_fun_decl_to_string crate d];
    let crate =
      { crate with fun_decls = FunDeclId.Map.add d.def_id d crate.fun_decls }
    in

    (* Update the uses of this definition *)
    let update (f : fun_decl) : fun_decl =
      match f.body with
      | None -> f
      | Some body ->
          let visitor =
            object
              inherit [_] map_statement

              method! visit_Call _ call =
                match call.func with
                | FnOpRegular { kind = FunId (FRegular id) as kind; generics }
                  when id = d.def_id ->
                    let func =
                      FnOpRegular
                        {
                          kind;
                          generics =
                            {
                              generics with
                              regions = generics.regions @ [ RErased ];
                            };
                        }
                    in
                    Call { call with func }
                | _ -> Call call
            end
          in

          let body = { body with body = visitor#visit_block () body.body } in
          { f with body = Some body }
    in
    let fun_decls = FunDeclId.Map.map update crate.fun_decls in
    { crate with fun_decls }

(** Charon introduces vtables for the traits which support dyn. We do not want
    to translate the corresponding type and global declarations. Moreover, the
    presence of those declarations leads to mutually recursive groups of traits
    and types. This micro-pass filters these definitions. *)
let remove_vtables (crate : crate) : crate =
  let src_is_vtable (src : item_source) : bool =
    match src with
    | VTableInstanceItem _ | VTableTyItem _ | VTableMethodShimItem -> true
    | _ -> false
  in

  (* Filter the groups.

     We detect mixed groups which combine trait declarations and their corresponding
     vtable types, and remove the vtable types (and convert the group to a homogeneous
     group if possible). We also filter the globals (and the functions corresponding
     to their implementation) introduced for the vtables.
  *)
  let declarations =
    List.filter_map
      (fun (g : declaration_group) ->
        match g with
        | GlobalGroup g -> (
            (* Filter the vtables *)
            let keep (id : global_decl_id) : bool =
              match GlobalDeclId.Map.find_opt id crate.global_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (GlobalGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (GlobalGroup (NonRecGroup id)) else None)
        | FunGroup g -> (
            (* Filter the vtables *)
            let keep (id : fun_decl_id) : bool =
              match FunDeclId.Map.find_opt id crate.fun_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (FunGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (FunGroup (NonRecGroup id)) else None)
        | TypeGroup g -> (
            (* Filter the vtables *)
            let keep (id : type_decl_id) : bool =
              match TypeDeclId.Map.find_opt id crate.type_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (TypeGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (TypeGroup (NonRecGroup id)) else None)
        | MixedGroup g -> (
            (* If the group is a mutually recursive group, filter the vtable types
               and check if the resulting group is only made of trait declarations.

               TODO: we should check whether the resulting group is recursive or not.
            *)
            match g with
            | RecGroup ids ->
                let keep (id : type_decl_id) : bool =
                  match TypeDeclId.Map.find_opt id crate.type_decls with
                  | None -> true
                  | Some d -> not (src_is_vtable d.src)
                in
                let ids =
                  List.filter
                    (fun (id : item_id) ->
                      match id with
                      | IdType id -> keep id
                      | _ -> true)
                    ids
                in
                (* Note that the resulting group shouldn't be empty, but we can
                   still support this case *)
                if ids = [] then None
                else if
                  List.for_all
                    (fun (id : item_id) ->
                      match id with
                      | IdTraitDecl _ -> true
                      | _ -> false)
                    ids
                then
                  (* There only remains trait ids *)
                  let ids =
                    List.map
                      (fun (id : item_id) ->
                        match id with
                        | IdTraitDecl id -> id
                        | _ -> raise (Failure "Unreachable"))
                      ids
                  in
                  (* If the resulting group is a singleton, check whether
                     it is recursive *)
                  match ids with
                  | [ id ] ->
                      let is_rec =
                        match TraitDeclId.Map.find_opt id crate.trait_decls with
                        | None ->
                            (* don't know so by default we consider it to be recursive *)
                            true
                        | Some d ->
                            (* We count the number of occurrences of the id of the trait
                             decl itself - if it's > 1 then it means it is recursive
                             (there is one occurrence for the [def_id] field) *)
                            let found = ref 0 in
                            let visitor =
                              object (self)
                                inherit [_] iter_trait_decl

                                method! visit_trait_ref_contents _
                                    { kind; trait_decl_ref = _ } =
                                  (* We ignore the [trait_decl_ref] which refer
                                     to the trait declaration itself if this is
                                     an occurrence of [Self] *)
                                  self#visit_trait_ref_kind () kind

                                method! visit_trait_decl_id _ id' =
                                  if id' = id then found := !found + 1
                              end
                            in
                            visitor#visit_trait_decl () { d with vtable = None };
                            !found > 1
                      in
                      if is_rec then Some (TraitDeclGroup (RecGroup [ id ]))
                      else Some (TraitDeclGroup (NonRecGroup id))
                  | _ -> Some (TraitDeclGroup (RecGroup ids))
                else Some (MixedGroup (RecGroup ids))
            | _ -> Some (MixedGroup g))
        | _ -> Some g)
      crate.declarations
  in

  (* *)
  let type_decls =
    TypeDeclId.Map.filter
      (fun _ (d : type_decl) -> not (src_is_vtable d.src))
      crate.type_decls
  in

  let global_decls =
    GlobalDeclId.Map.filter
      (fun _ (d : global_decl) -> not (src_is_vtable d.src))
      crate.global_decls
  in

  let fun_decls =
    FunDeclId.Map.filter
      (fun _ (d : fun_decl) -> not (src_is_vtable d.src))
      crate.fun_decls
  in

  let trait_decls =
    TraitDeclId.Map.map
      (fun (d : trait_decl) ->
        (* Remove the vtable *)
        { d with vtable = None })
      crate.trait_decls
  in

  { crate with declarations; type_decls; global_decls; fun_decls; trait_decls }

let name_is_valid (n : string) : bool =
  let is_valid_char c =
    (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9')
    || c = '_'
  in
  String.for_all is_valid_char n

(** The basename introduced by Charon for impl types (see
    https://github.com/AeneasVerif/charon/issues/1013) is an invalid name: we
    detect this case here and use a valid name instead. As it only happens for
    inputs of type `impl Trait` we use `Impl` as a basename. *)
let rename_type_vars (crate : crate) : crate =
  let visitor =
    object
      inherit [_] map_crate as super

      method! visit_generic_params env generics =
        (* Explore the types and rename them *)
        let num_renames =
          List.length
            (List.filter
               (fun (p : type_param) -> not (name_is_valid p.name))
               generics.types)
        in
        let rename =
          if num_renames > 1 then (
            let index = ref 0 in
            fun () ->
              let i = !index in
              index := !index + 1;
              "Impl" ^ string_of_int i)
          else fun () -> "Impl"
        in
        let types =
          List.map
            (fun (p : type_param) ->
              let name = if name_is_valid p.name then p.name else rename () in
              { p with name })
            generics.types
        in
        super#visit_generic_params env { generics with types }
    end
  in
  visitor#visit_crate () crate

(** Simplify calls to:
    - the blanket [IntoIterator::into_iter] implementation (we replace it with
      an assignment)
    - the blanket [TryInto::try_into] implementation (we replace it with a call
      to the [try_from] method of the required [TryFrom] clause)

    TODO: remove once we have partial monomorphization *)
let simplify_trait_calls (crate : crate) : crate =
  (* Create a map from pattern to method *)
  (* Blanket definition for [into_iter] *)
  let into_iter_pat =
    NameMatcher.parse_pattern
      "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, \
       @Item, @I>}::into_iter"
  in
  (* Blanket definition for [try_into] *)
  let try_into_pat =
    NameMatcher.parse_pattern
      "core::convert::{core::convert::TryInto<@T, @U, @Error>}::try_into"
  in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_pattern =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in
  let is_blanket_into_iter = match_pattern into_iter_pat in
  let is_blanket_try_into = match_pattern try_into_pat in

  let try_replace_call (super_visit : unit -> statement_kind) (span : Meta.span)
      (call : call) : statement_kind =
    match call.func with
    | FnOpRegular { kind = FunId (FRegular fid); generics } -> (
        match FunDeclId.Map.find_opt fid crate.fun_decls with
        | Some d
          when List.length generics.trait_refs > 0 && List.length call.args > 0
          ->
            if is_blanket_into_iter d.item_meta.name then (
              (* Replace the call by an assignment *)
              [%sanity_check] span (List.length call.args = 1);
              let arg = Use (List.hd call.args) in
              Assign (call.dest, arg))
            else if is_blanket_try_into d.item_meta.name then (
              [%ldebug
                "- call: " ^ call_to_string crate call ^ "\n- generics: "
                ^ generic_args_to_string crate generics];
              (* There should be a single trait ref implementing [TryFrom] *)
              match generics.trait_refs with
              | [ trait_ref ] -> (
                  (* There are two cases depending on whether this is an impl or not *)
                  match trait_ref.kind with
                  | TraitImpl { id = impl_id; generics = impl_generics } ->
                      (* Lookup the impl to retrieve the method id *)
                      let impl =
                        [%unwrap_with_span] span
                          (TraitImplId.Map.find_opt impl_id crate.trait_impls)
                          "Internal error"
                      in
                      let method_ref =
                        snd
                          ([%unwrap_with_span] span
                             (List.find_opt
                                (fun (name, _) -> name = "try_from")
                                impl.methods)
                             "Internal error")
                      in

                      [%sanity_check] span
                        (method_ref.binder_params = empty_generic_params);

                      [%ldebug
                        "- call: " ^ call_to_string crate call
                        ^ "\n- generics: "
                        ^ generic_args_to_string crate generics
                        ^ "\n- impl.generic_params: "
                        ^ generic_params_to_string crate impl.generics
                        ^ "\n- impl_generics: "
                        ^ generic_args_to_string crate impl_generics
                        ^ "\n- method_ref.binder_params: "
                        ^ generic_params_to_string crate
                            method_ref.binder_params
                        ^ "\n- method_ref.binder_value: "
                        ^ fun_decl_ref_to_string crate method_ref.binder_value
                        ^ "\n "];

                      (* Instantiate *)
                      let subst =
                        [%add_loc] Substitute.make_subst_from_generics
                          (Some span) impl.generics impl_generics
                          (UnknownTrait "UNREACHABLE")
                      in
                      let generics =
                        Substitute.generic_args_substitute subst
                          method_ref.binder_value.generics
                      in

                      (* *)
                      let kind = FunId (FRegular method_ref.binder_value.id) in
                      let func = FnOpRegular { kind; generics } in
                      Call { call with func }
                  | _ ->
                      (* TODO: *)
                      super_visit ())
              | _ -> [%internal_error] span)
            else super_visit ()
        | _ -> super_visit ())
    | _ -> super_visit ()
  in

  (* The map visitor to simplify the calls *)
  let visitor =
    object
      inherit [_] map_crate as super

      (* Keep track of the last span *)
      method! visit_statement _ st = super#visit_statement (Some st.span) st

      method! visit_Call span call =
        try_replace_call
          (fun _ -> super#visit_Call span call)
          (Option.get span) call
    end
  in
  let crate = visitor#visit_crate None crate in

  (* Re-compute the set of used trait impls and fun declarations: by simplifying
     the calls we may have filtered some annoying ones

     Remark: the way we explore the crate is slightly approximative below.
     We should improve it.
  *)
  let used_impls = ref TraitImplId.Set.empty in
  let impls_to_explore = ref [] in
  let used_funs = ref FunDeclId.Set.empty in

  (* First explore the transparent functions *)
  let visitor =
    object
      inherit [_] iter_statement

      method! visit_trait_impl_id _ id =
        if not (TraitImplId.Set.mem id !used_impls) then (
          used_impls := TraitImplId.Set.add id !used_impls;
          impls_to_explore := id :: !impls_to_explore)

      method! visit_fun_decl_id _ id =
        used_funs := FunDeclId.Set.add id !used_funs
    end
  in
  FunDeclId.Map.iter
    (fun _ (f : fun_decl) ->
      if f.item_meta.is_local then visitor#visit_fun_decl_id () f.def_id;
      match f.body with
      | None -> ()
      | Some body -> visitor#visit_block () body.body)
    crate.fun_decls;

  GlobalDeclId.Map.iter
    (fun _ (d : global_decl) -> visitor#visit_fun_decl_id () d.init)
    crate.global_decls;

  TraitDeclId.Map.iter
    (fun _ (d : trait_decl) ->
      List.iter
        (fun (d : trait_method binder) ->
          visitor#visit_fun_decl_id () d.binder_value.item.id)
        d.methods)
    crate.trait_decls;

  (* Add the local trait impls *)
  TraitImplId.Map.iter
    (fun _ (d : trait_impl) ->
      if d.item_meta.is_local then visitor#visit_trait_impl_id () d.def_id)
    crate.trait_impls;

  (* Explore the impls *)
  while !impls_to_explore <> [] do
    let id = List.hd !impls_to_explore in
    impls_to_explore := List.tl !impls_to_explore;
    match TraitImplId.Map.find_opt id crate.trait_impls with
    | None -> ()
    | Some impl ->
        List.iter (visitor#visit_trait_ref ()) impl.implied_trait_refs;
        List.iter
          (fun ((_, x) : _ * fun_decl_ref binder) ->
            visitor#visit_fun_decl_id () x.binder_value.id)
          impl.methods
  done;

  (* Filter the declaration groups we want to extract *)
  let keep_group (gr : declaration_group) : bool =
    match gr with
    | TraitImplGroup (NonRecGroup id) ->
        if TraitImplId.Set.mem id !used_impls then true else false
    | TraitImplGroup (RecGroup ids) ->
        if List.exists (fun id -> TraitImplId.Set.mem id !used_impls) ids then
          true
        else false
    | FunGroup (NonRecGroup id) ->
        if FunDeclId.Set.mem id !used_funs then true else false
    | FunGroup (RecGroup ids) ->
        if List.exists (fun id -> FunDeclId.Set.mem id !used_funs) ids then true
        else false
    | _ -> true
  in
  let declarations = List.filter keep_group crate.declarations in

  (* *)
  { crate with declarations }

let apply_passes (crate : crate) : crate =
  (* Passes that apply to the whole crate *)
  let crate = update_array_default crate in
  (* Passes that apply to individual function bodies *)
  let function_passes =
    [
      ("erase_body_regions", erase_body_regions);
      ("remove_unreachable", remove_unreachable);
      ("update_loop", update_loops);
      ("remove_useless_joins", remove_useless_joins);
      ( "remove_shallow_borrows_storage_live_dead",
        remove_shallow_borrows_storage_live_dead );
      ("decompose_str_borrows", decompose_str_borrows);
      ("simplify_panics", simplify_panics);
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
            [%ltrace
              "Before applying the prepasses:\n"
              ^ Print.Crate.crate_fun_decl_to_string crate f];
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
  let crate = replace_static crate in
  let crate = remove_vtables crate in
  let crate = rename_type_vars crate in
  let crate = simplify_trait_calls crate in
  [%ltrace "After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"];
  crate
