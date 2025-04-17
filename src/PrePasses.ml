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

(** Rustc inserts a lot of drops before the assignments.

    We consider those drops are part of the assignment, and splitting the
    drop and the assignment is problematic for us because it can introduce
    [⊥] under borrows. For instance, we encountered situations like the
    following one:

    {[
      drop( *x ); // Illegal! Inserts a ⊥ under a borrow
      *x = move ...;
    ]}

    Rem.: we don't use this anymore
 *)
let filter_drop_assigns (f : fun_decl) : fun_decl =
  (* The visitor *)
  let obj =
    object (self)
      inherit [_] map_statement as super

      method! visit_Sequence env st1 st2 =
        match (st1.content, st2.content) with
        | Drop p1, Assign (p2, _) ->
            if p1 = p2 then (self#visit_statement env st2).content
            else super#visit_Sequence env st1 st2
        | Drop p1, Sequence ({ content = Assign (p2, _); _ }, _) ->
            if p1 = p2 then (self#visit_statement env st2).content
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
  { f with body }

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
    | FakeRead _ | Drop _ | Nop -> not must_end_with_exit
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

    In theory, this allows the code to do more things than what Rust allows,
    and in particular it would allow to modify the variant of an enumeration
    in a guard, while matching over this enumeration.

    In practice, this is not a soundness issue.

    **Soundness**:
    ==============
    For instance, let's consider the following Rust code:
    {[
      match ls : &mut List<u32> {
        Nil => return None,
        Cons(hd, tl) if *hd > 0 => return Some(hd),
        Cons(hd, tl) => ...,
      }
    ]}

    The Rust compiler enforces the fact that the guard doesn't modify the
    variant of [ls]. It does so by compiling to (approximately) the following
    MIR code:
    {[
      let d = discriminant( *ls);
      switch d {
        0 => ... // Nil case
        1 => { // Cons case
          // Introduce hd and tl
          hd := &mut ( *ls as Cons).0;
          tl := &mut ( *ls as Cons).1;

          // Evaluate the guard
          tmp := &shallow *ls; // Create a shallow borrow of ls
          b := *hd > 0;
          fake_read(tmp); // Make sure the shallow borrow lives until the end of the guard

          // We evaluated the guard: go to the proper branch
          if b then {
            ... // First Cons branch
          }
          else {
            ... // Second Cons branch
          }
        }
      }
    ]}

    Shallow borrows are a bit like shared borrows but with the following
    difference:
    - they do forbid modifying the value directly below the loan
    - but they allow modifying a strict subvalue
    For instance, above, for as long as [tmp] lives:
    - we can't change the variant of [*ls]
    - but we can update [hd] and [tl]

    On our side, we have to pay attention to two things:
    - Removing shallow borrows don't modify the behavior of the program.
      In practice, adding shallow borrows can lead to a MIR program being
      rejected, but it doesn't change this program's behavior.

      Regarding this, there is something important. At the top-level AST,
      if the guard modifies the variant (say, to [Nil]) and evaluates to [false],
      then we go to the second [Cons] branch, which doesn't really make sense
      (though it is not a soundness issue - for soundness, see next point).

      At the level of MIR, as the match has been desugared, there is no issue
      in modifying the variant of the scrutinee.

    - We have to make sure the evaluation in sound. In particular, modifying
      the variant of [*ls] should invalidate [hd] and [tl]. This is important
      for the Rust compiler to enforce this on its side. In the case of LLBC,
      we don't need additional constraints because modifying [*ls] will
      indeed invalidate [hd] and [tl].

      More specifically, at the beginning of the [Cons] branch and just after
      we introduced [hd] and [tl] we have the following environment:
      {[
        ... // l0 comes from somewhere - we omit the corresponding loan
        ls -> MB l0 (Cons (ML l1) (ML l2))
        hd -> MB l1 s1
        tl -> MB l2 s2
      ]}

      If we evaluate: [*ls := Nil], we get:
      {[
        ... // l0 comes from somewhere - we omit the corresponding loan
        ls -> MB l0 Nil
        hd -> ⊥ // invalidated
        tl -> ⊥ // invalidated
      ]}

    **Implementation**:
    ===================
    The pass is implemented as follows:
    - we look for all the variables which appear in pattern of the following
      shape and remove them:
      {[
        let x = &shallow ...;
        ...
      ]}
    - whenever we find such a variable [x], we remove all the subsequent
      occurrences of [fake_read(x)].

    We then check that [x] completely disappeared from the function body (for
    sanity).
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

        method! visit_FakeRead env p =
          match p.kind with
          | PlaceLocal var_id when LocalId.Set.mem var_id !filtered ->
              (* filter *)
              Nop
          | _ ->
              (* Don't filter *)
              super#visit_FakeRead env p
      end
    in

    (* Filter the variables *)
    let body = filter_visitor#visit_statement () body in

    (* Check that the filtered variables completely disappeared from the body *)
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

(* Add the functions [new_fs] to the declaration group that [f] belongs to *)
let add_to_fundecl_group (crate: crate) (f: fun_decl_id) (new_fs: fun_decl_id list) : crate =
  match new_fs with
  (* No functions to add, this is a no-op *)
  | [] -> crate
  | _ ->
    let declarations = List.map (function
        | FunGroup decl -> FunGroup begin
            match decl with
            | NonRecGroup id when f = id -> RecGroup (f :: new_fs)
            | RecGroup l when List.mem f l -> RecGroup (new_fs @ l)
            | _ -> decl
        end
        | x -> x
      ) crate.declarations in
    {crate with declarations}

let default_span : Meta.span =
  let file : Meta.file_id = { name = Local "tmp"; contents = None } in
  let loc : Meta.loc = {line = 1; col = 0} in
  let raw_span : Meta.raw_span = {file; beg_loc = loc; end_loc = loc} in
  { span = raw_span; generated_from_span = None }

let default_meta (name: name) : item_meta =
  let attr_info : Meta.attr_info = { attributes = []; inline = None; rename = None; public = true } in
  let span = default_span in
  let source_text = None in
  let is_local = true in
  let lang_item = None in
  { name; span; source_text; attr_info; is_local; lang_item }

let default_signature : fun_sig =
  { is_unsafe = false; is_closure = false; closure_info = None; generics = TypesUtils.empty_generic_params; inputs = []; output = TypesUtils.mk_unit_ty}

let create_statement (s: raw_statement) : statement =
  { span = default_span; content = s; comments_before = [] }

let extract_if_then_else (crate: crate) (f: fun_decl) : crate =
  (* Format.printf "Function %s\n@." (Print.Crate.crate_fun_decl_to_string crate f); *)
  let _, gen = FunDeclId.mk_stateful_generator_starting_at_id
    (FunDeclId.of_int (List.length (FunDeclId.Map.to_list crate.fun_decls))) in
  let def_id = gen () in
  let item_meta = {f.item_meta with name = [PeIdent ("branches", Disambiguator.zero); PeIdent ("foobar", Disambiguator.zero)] } in
  let signature = f.signature in
  let kind = RegularItem in
  let is_global_initializer = None in
  let unit_ty = TypesUtils.mk_unit_ty in
  let return_local = { index = LocalId.zero; name = None; var_ty = unit_ty} in
  let return_place = { kind = PlaceLocal LocalId.zero; ty = unit_ty } in
  let input = { index = LocalId.incr LocalId.zero; name = Some "b"; var_ty = TLiteral TBool } in
  let locals = {arg_count = 1; locals = [return_local; input] } in
  let unit_rvalue = Aggregate (AggregatedAdt (TTuple, None, None, TypesUtils.empty_generic_args), []) in
  let assign_ret_stmt = create_statement (Assign (return_place, unit_rvalue)) in
  let return_stmt = create_statement Return in
  let body = create_statement (Sequence (assign_ret_stmt, return_stmt)) in
  let body = { span = default_span; locals; body} in
  let body = Some body in
  let fun_decl = {
    def_id;
    item_meta;
    signature;
    kind;
    is_global_initializer;
    body;
  } in
  let fun_decls = FunDeclId.Map.add def_id fun_decl crate.fun_decls in
  let crate = add_to_fundecl_group {crate with fun_decls} f.def_id [def_id] in

  (* Format.printf "Generated function %s\n@." (Print.Crate.crate_fun_decl_to_string crate fun_decl); *)
  crate

(* Retrieve the list of locals associated to the set of local ids [s] *)
let retrieve_locals locals s =
  (* TODO: This should be doable with a linear traversal of the locals list *)
  (* TODO: We might be breaking the invariant that the n-th local has localId n *)
  LocalId.Set.fold (fun id acc -> List.nth locals (LocalId.to_int id) :: acc) s []

let create_fun (def_id: FunDeclId.id) (dis: Disambiguator.id) moves reads writes s : fun_decl =
  (* TODO: Fix *)
  let name = [PeIdent ("branches", Disambiguator.zero); PeIdent ("foobar", dis)] in

  (* TODO: Need to build from region_ids initially present in function *)
  let _, gen = RegionId.fresh_stateful_generator () in
  let replace_region_id rvars l = match l.var_ty with
    | TRef (RErased, p, k) ->
        let region_id = gen () in
        { index = region_id; name = None } :: rvars, TRef (RVar (Free region_id), p, k)
    | _ -> failwith "incorrect tref type"
  in

  let regions, reads_ty = List.fold_left_map replace_region_id [] reads in
  let regions, writes_ty = List.fold_left_map replace_region_id regions writes in

  let input_tys = List.map (fun l -> l.var_ty) moves @ reads_ty @ writes_ty in
  let inputs = moves @ reads @ writes in

  let generics = {TypesUtils.empty_generic_params with regions} in
  let item_meta = default_meta name in
  let signature = {default_signature with inputs = input_tys; generics} in
  let kind = RegularItem in
  let is_global_initializer = None in
  let unit_ty = TypesUtils.mk_unit_ty in
  let return_local = { index = LocalId.zero; name = None; var_ty = unit_ty} in
  let return_place = { kind = PlaceLocal LocalId.zero; ty = unit_ty } in

  let locals = {arg_count = List.length inputs; locals = return_local :: inputs } in
  let unit_rvalue = Aggregate (AggregatedAdt (TTuple, None, None, TypesUtils.empty_generic_args), []) in
  let assign_ret_stmt = create_statement (Assign (return_place, unit_rvalue)) in
  let return_stmt = create_statement Return in
  let last_stmt = create_statement (Sequence (assign_ret_stmt, return_stmt)) in
  let body = create_statement (Sequence (s, last_stmt)) in
  let body = { span = default_span; locals; body} in
  let body = Some body in
  {
    def_id;
    item_meta;
    signature;
    kind;
    is_global_initializer;
    body;
  }

(* Collect three sets corresponding respectively to
   - moved-in variables
   - read variables
   - written variables

   TODO: This should actually return places, but we need to figure out how to
   both collect places (e.g., create a PlaceSet), and how to establish a hierarchy
   between places (e.g., to relate x and *x)
*)
let collect_places (s: raw_statement) : LocalId.Set.t * LocalId.Set.t * LocalId.Set.t =
  let add_place_to_set (p: place) s = match p.kind with
    | PlaceLocal id -> LocalId.Set.add id s
    | _ -> failwith "only supporting local places for now"
  in

  let collect_operand moves reads writes = function
    | Copy _ -> failwith "copy"
    | Move p -> add_place_to_set p moves, reads, writes
    | Constant _ -> moves, reads, writes
  in

  let collect_rvalue moves reads writes = function
    | Use o -> collect_operand moves reads writes o
    | _ -> failwith "TODO: support rvalues beyond operands"
  in

  let rec collect_stmt moves reads writes s = match s with
    | Assign (p, v) ->
        collect_rvalue moves reads (add_place_to_set p writes) v
    | FakeRead _ -> failwith "fakeread"
    | SetDiscriminant _ -> failwith "set_discriminant"
    | Drop _ -> failwith "drop"
    | Assert _ -> failwith "assert"
    | Call _ -> failwith "call"
    | Abort _ -> failwith "abort"
    | Return -> failwith "return"
    | Break _ -> failwith "break"
    | Continue _ -> failwith "continue"
    | Nop -> failwith "nop"
    | Sequence _ -> failwith "sequence"
    | Switch (If (cond, ifb, elseb)) ->
        let moves, reads, writes = collect_operand moves reads writes cond in
        let moves, reads, writes = collect_stmt moves reads writes ifb.content in
        collect_stmt moves reads writes elseb.content
    | Switch _ -> failwith "switch: Int or Match"
    | Loop _ -> failwith "loop"
    | Error _ -> failwith "error"

  in
  collect_stmt LocalId.Set.empty LocalId.Set.empty LocalId.Set.empty s

let place_of_local (l: local) : place = { kind = PlaceLocal l.index; ty = l.var_ty }

let make_operand (l: local) : operand = Move (place_of_local l)

let extract (crate: crate) (f: fun_decl) =
  (* Format.printf "Initial function %s\n@." (Print.Crate.crate_fun_decl_to_string crate f); *)
  match f.body with
  | None -> crate
  | Some body ->
    (* Keep track of all the new functions generated while traversing
       the body of [f] *)
    let new_funs = ref [] in
    let new_funs_ids = ref [] in
    let new_locals = ref [] in
    let _, gen = FunDeclId.mk_stateful_generator_starting_at_id
      (FunDeclId.of_int (List.length (FunDeclId.Map.to_list crate.fun_decls))) in
    let _, dis_gen = Disambiguator.fresh_stateful_generator () in
    let _, local_gen = LocalId.mk_stateful_generator_starting_at_id
      (LocalId.of_int (List.length body.locals.locals)) in

    let visitor =
      object
        inherit [_] map_statement as super

        method! visit_Switch _ s = match s with
        | If _ ->
            let def_id = gen () in
            let dis = dis_gen () in

            let moves, reads, writes = collect_places (Switch s) in
            (* TODO: Some filtering to avoid duplications between sets *)

            let moves = retrieve_locals body.locals.locals moves in
            let reads = retrieve_locals body.locals.locals reads in
            let writes  = retrieve_locals body.locals.locals writes in

            let ret_var_id = local_gen () in
            let ret_var = { index = ret_var_id; name = None; var_ty = TypesUtils.mk_unit_ty} in
            new_locals := ret_var :: !new_locals;


            (* A visitor to replace all occurences of [local] by [place].
               Mostly used to replace an access to a local by a deref of
               a borrow of the local *)
            let replace_place local place = object
              inherit [_] map_statement as super

              method! visit_place _ p = match p with
                | { kind = PlaceLocal pid; _} ->
                      if pid = local.index then
                        { kind = PlaceProjection (place, Deref); ty = local.var_ty}
                      else p
                | { kind = PlaceProjection (p', k); ty} ->
                      let p' = super#visit_place () p' in
                      { kind = PlaceProjection (p', k); ty }
            end
            in

            let take_borrow (is_mut: bool) sseq (local: local) : (raw_statement * statement) * local =
              let s, seq = sseq in
              let var_id = local_gen () in
              let var_ty = TRef (RErased, local.var_ty, if is_mut then RMut else RShared) in
              let var = { index = var_id; name = local.name; var_ty } in
              new_locals := var :: !new_locals;

              let place = { kind = PlaceLocal var_id; ty = var_ty } in
              let stmt = create_statement (Assign (place, RvRef (place_of_local local, if is_mut then BMut else BShared))) in
              let stmt = create_statement (Sequence (stmt, seq)) in
              (* Replace all occurences of place local by the corresponding deref of [place] *)
              ((replace_place local place)#visit_raw_statement () s, stmt), var
            in


            let (s, reads_inits), reads = List.fold_left_map (take_borrow false) (Switch s, create_statement Nop) reads in
            let (s, write_inits), writes = List.fold_left_map (take_borrow true) (s, create_statement Nop) writes in

            let new_f = create_fun def_id dis moves reads writes (create_statement s) in
            new_funs := new_f :: !new_funs;
            new_funs_ids := def_id :: !new_funs_ids;

            let moves_ops = List.map make_operand moves in
            let reads_ops = List.map make_operand reads in
            let writes_ops = List.map make_operand writes in
            (* let writes_ops = List.map make_operand writes in *)
            let call = {
              func = FnOpRegular {
                func = FunId (FRegular def_id);
                generics = TypesUtils.empty_generic_args
              };
              args = moves_ops @ reads_ops @ writes_ops;
              dest = { kind = PlaceLocal ret_var_id; ty = TypesUtils.mk_unit_ty}
            } in
            Sequence (reads_inits, create_statement (Sequence (write_inits, create_statement (Call call))))
        | _ -> super#visit_Switch () s
      end
    in

    let new_body = visitor#visit_statement () body.body in
    let locals = {
      arg_count = body.locals.arg_count;
      locals = body.locals.locals @ List.rev !new_locals
    } in

    let body = Some {body with body = new_body; locals} in

    let f = {f with body} in

    (* List.iter (fun f -> *)
    (*   Format.printf "Created function %s\n@." (Print.Crate.crate_fun_decl_to_string crate f); *)
    (* ) !new_funs; *)

    let fun_decls = FunDeclId.Map.add f.def_id f crate.fun_decls in
    let fun_decls = List.fold_left (fun fun_decls f -> FunDeclId.Map.add f.def_id f fun_decls) fun_decls !new_funs in
    let crate = add_to_fundecl_group {crate with fun_decls} f.def_id !new_funs_ids in

    (* Format.printf "Modified function %s\n@." (Print.Crate.crate_fun_decl_to_string crate f); *)
    crate

let apply_passes (crate : crate) : crate =
  let function_passes =
    [
      (* remove_loop_breaks crate; *)
      remove_shallow_borrows crate;
      decompose_str_borrows;
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
  let crate = List.fold_left (fun c (_, fdecl) -> extract c fdecl) crate (FunDeclId.Map.to_list (crate.fun_decls)) in
  let crate = filter_type_aliases crate in
  log#ldebug
    (lazy ("After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"));
  crate
