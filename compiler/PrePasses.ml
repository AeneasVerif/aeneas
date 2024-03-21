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
        | Drop p1, Sequence ({ content = Assign (p2, _); meta = _ }, _) ->
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
    | SetDiscriminant _ | Assert _ | Call _ | Break _ | Continue _ | Switch _
    | Loop _ ->
        false
    | Assign (_, rv) -> (
        match rv with
        | Use _ | RvRef _ -> not must_end_with_exit
        | Aggregate (AggregatedAdt (TTuple, _, _), []) -> not must_end_with_exit
        | _ -> false)
    | FakeRead _ | Drop _ | Nop -> not must_end_with_exit
    | Panic | Return -> true
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

        method! visit_Loop entered_loop loop =
          cassert (not entered_loop) st.meta "TODO: error message";
          super#visit_Loop true loop

        method! visit_Break _ i =
          cassert (i = 0) st.meta "TODO: error message";
          nst.content
      end
    in
    obj#visit_statement false st
  in

  (* The visitor *)
  let obj =
    object
      inherit [_] map_statement as super

      method! visit_Sequence env st1 st2 =
        match st1.content with
        | Loop _ ->
            cassert (statement_has_no_loop_break_continue st2) st2.meta "TODO: error message";
            (replace_breaks_with st1 st2).content
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
    let filtered = ref VarId.Set.empty in

    let filter_visitor =
      object
        inherit [_] map_statement as super

        method! visit_Assign env p rv =
          match (p.projection, rv) with
          | [], RvRef (_, BShallow) ->
              (* Filter *)
              filtered := VarId.Set.add p.var_id !filtered;
              Nop
          | _ ->
              (* Don't filter *)
              super#visit_Assign env p rv

        method! visit_FakeRead env p =
          if p.projection = [] && VarId.Set.mem p.var_id !filtered then
            (* Filter *)
            Nop
          else super#visit_FakeRead env p
      end
    in

    (* Filter the variables *)
    let body = filter_visitor#visit_statement () body in

    (* Check that the filtered variables completely disappeared from the body *)
    (* let statement = crate in *)
    let check_visitor =
      object
        inherit [_] iter_statement as super
                (* Remember the span of the statement we enter *)
        method! visit_statement _ st = super#visit_statement st.meta st
        method! visit_var_id meta id = cassert (not (VarId.Set.mem id !filtered)) meta "Filtered variables should have completely disappeared from the body"
      end
    in
    check_visitor#visit_statement body.meta body;

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

let apply_passes (crate : crate) : crate =
  let passes = [ remove_loop_breaks crate; remove_shallow_borrows crate ] in
  let fun_decls =
    List.fold_left
      (fun fl pass -> FunDeclId.Map.map pass fl)
      crate.fun_decls passes
  in
  let crate = { crate with fun_decls } in
  log#ldebug
    (lazy ("After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"));
  crate
