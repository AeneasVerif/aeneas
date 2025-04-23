(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it
 *)

open Types
open Expressions
open LlbcAst
open Utils
open LlbcAstUtils
open Errors

let log = Logging.pre_passes_log

(** This pass slightly restructures the control-flow to remove the need to
    merge branches during the symbolic execution in some quite common cases
    where doing a merge is actually not necessary and leads to an ugly translation.

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

    This way, the translated body doesn't have an intermediate assignment,
    for the `if ... then ... else ...` expression (together with a backward
    function).

    More precisly, we move (and duplicate) a statement happening after a branching
    inside the branches if:
    - this statement ends with [return] or [panic]
    - this statement is only made of a sequence of nops, assignments (with some
      restrictions on the rvalue), fake reads, drops (usually, returns will be
      followed by such statements)
 *)
let remove_useless_cf_merges (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  (* Return [true] if the statement can be moved inside the branches of a switch.
   *
   * [must_end_with_exit]: we need this boolean because the inner statements
   * (inside the encountered sequences) don't need to end with [return] or [panic],
   * but all the paths inside the whole statement have to.
   * *)
  let rec can_be_moved_aux (must_end_with_exit : bool) (st : statement) : bool =
    match st.content with
    | SetDiscriminant _
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
        | Aggregate (AggregatedAdt (TTuple, _, _, _), []) ->
            not must_end_with_exit
        | _ -> false)
    | StorageDead _ | StorageLive _ | Deinit _ | Drop _ | Nop ->
        not must_end_with_exit
    | Abort _ | Return -> true
    | Sequence (st1, st2) ->
        can_be_moved_aux false st1 && can_be_moved_aux must_end_with_exit st2
  in
  let can_be_moved = can_be_moved_aux true in

  (* The visitor *)
  let obj =
    object
      inherit [_] map_statement as super

      method! visit_Sequence env st1 st2 =
        match st1.content with
        | Switch switch ->
            if can_be_moved st2 then
              super#visit_Switch env (chain_statements_in_switch switch st2)
            else super#visit_Sequence env st1 st2
        | _ -> super#visit_Sequence env st1 st2
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body -> Some { body with body = obj#visit_statement () body.body }
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
    which occur after loops *inside* the loops, thus removing the need to
    have breaks (we later check that we removed all the breaks).

    This is needed because of the way we perform the symbolic execution
    on the loops for now.

    Rem.: we check that there are no nested loops (all the breaks must break
    to the first outer loop, and the statements we insert inside the loops
    mustn't contain breaks themselves).

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

    We also insert the statements occurring after branchings (matches or
    if then else) inside the branches. For instance:
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
    do this some paths inside the loop might not end with a break/continue/return.Aeneas
  *)
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
  *)
  let replace_breaks_with (st : statement) (nst : statement) : statement =
    let obj =
      object
        inherit [_] map_statement as super

        method! visit_statement entered_loop st =
          match st.content with
          | Loop loop ->
              cassert __FILE__ __LINE__ (not entered_loop) st.span
                "Nested loops are not supported yet";
              { st with content = super#visit_Loop true loop }
          | Break i ->
              cassert __FILE__ __LINE__ (i = 0) st.span
                "Breaks to outer loops are not supported yet";
              {
                st with
                content = nst.content;
                comments_before = st.comments_before @ nst.comments_before;
              }
          | _ -> super#visit_statement entered_loop st
      end
    in
    obj#visit_statement false st
  in

  (* The visitor *)
  let replace_visitor =
    object
      inherit [_] map_statement as super

      method! visit_statement env st =
        match st.content with
        | Sequence (st1, st2) -> begin
            match st1.content with
            | Loop _ ->
                cassert __FILE__ __LINE__
                  (statement_has_no_loop_break_continue st2)
                  st2.span "Sequences of loops are not supported yet";
                super#visit_statement env (replace_breaks_with st st2)
            | Switch _ ->
                (* This pushes st2 inside of the switch *)
                super#visit_statement env (chain_statements st1 st2)
            | _ -> super#visit_statement env st
          end
        | _ -> super#visit_statement env st
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | Some body ->
        Some { body with body = replace_visitor#visit_statement () body.body }
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

(** Remove the use of shallow borrows from a function.

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
    evaluator/translation hence the translation is still sound.
 *)
let remove_shallow_borrows (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  let filter_in_body (body : statement) : statement =
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
    let body = filter_visitor#visit_statement () body in
    let body = storage_rem_visitor#visit_statement () body in

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
    check_visitor#visit_statement body.span body;

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
    is concerned: they store bottom in the place. This maps all three to `Drop`
    to simplify later work.
 *)
let unify_drops (f : fun_decl) : fun_decl =
  let lookup_local (locals : locals) (var_id : local_id) : local =
    List.nth locals.locals (LocalId.to_int var_id)
  in

  let unify_visitor =
    object
      inherit [_] map_statement
      method! visit_Deinit _ p = Drop p

      method! visit_StorageDead locals var_id =
        let ty = (lookup_local locals var_id).var_ty in
        let p = { kind = PlaceLocal var_id; ty } in
        Drop p
    end
  in

  let body =
    match f.body with
    | None -> None
    | Some body ->
        let new_body = unify_visitor#visit_statement body.locals body.body in
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

(** Whenever we write a string literal in Rust, rustc actually
    introduces a constant of type [&str].
    Generally speaking, because [str] is unsized, it doesn't
    make sense to manipulate values of type [str] directly.
    But in the context of Aeneas, it is reasonable to decompose
    those literals into: a string stored in a local variable,
    then a borrow of this variable.
 *)
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
        let decompose_rvalue (span : Meta.span) (lv : place) (rv : rvalue)
            (next : statement option) : raw_statement =
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
                    TRef (_, (TAdt (TBuiltin TStr, _) as str_ty), ref_kind) ) ->
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
            { span; content = Assign (lv, rv); comments_before = [] }
          in
          let statements, last =
            match next with
            | None -> (!new_statements, assign)
            | Some st -> (assign :: !new_statements, st)
          in
          (* Note that the new statements are in reverse order *)
          (List.fold_left
             (fun st nst ->
               { span; content = Sequence (nst, st); comments_before = [] })
             last statements)
            .content
        in

        (* Visit all the statements and decompose the literals *)
        let visitor =
          object
            inherit [_] map_statement as super
            method! visit_statement _ st = super#visit_statement st.span st

            method! visit_Sequence span st1 st2 =
              match st1.content with
              | Assign (lv, rv) -> decompose_rvalue st1.span lv rv (Some st2)
              | _ -> super#visit_Sequence span st1 st2

            method! visit_Assign span lv rv = decompose_rvalue span lv rv None
          end
        in

        let body_body = visitor#visit_statement body.body.span body.body in
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

let apply_passes (crate : crate) : crate =
  let function_passes =
    [
      remove_loop_breaks crate;
      remove_shallow_borrows crate;
      decompose_str_borrows;
      unify_drops;
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
