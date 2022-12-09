(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it
 *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module A = LlbcAst
module L = Logging
open Utils
open LlbcAstUtils

let log = L.pre_passes_log

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
let filter_drop_assigns (f : A.fun_decl) : A.fun_decl =
  (* The visitor *)
  let obj =
    object (self)
      inherit [_] A.map_statement as super

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
let remove_useless_cf_merges (crate : A.crate) (f : A.fun_decl) : A.fun_decl =
  let f0 = f in
  (* Return [true] if the statement can be moved inside the branches of a switch.
   *
   * [must_end_with_exit]: we need this boolean because the inner statements
   * (inside the encountered sequences) don't need to end with [return] or [panic],
   * but all the paths inside the whole statement have to.
   * *)
  let rec can_be_moved_aux (must_end_with_exit : bool) (st : A.statement) : bool
      =
    match st.content with
    | SetDiscriminant _ | Assert _ | Call _ | Break _ | Continue _ | Switch _
    | Loop _ ->
        false
    | Assign (_, rv) -> (
        match rv with
        | Use _ | Ref _ -> not must_end_with_exit
        | Aggregate (AggregatedTuple, []) -> not must_end_with_exit
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
      inherit [_] A.map_statement as super

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
let remove_loop_breaks (crate : A.crate) (f : A.fun_decl) : A.fun_decl =
  let f0 = f in

  (* Check that a statement doesn't contain loops, breaks or continues *)
  let statement_has_no_loop_break_continue (st : A.statement) : bool =
    let obj =
      object
        inherit [_] A.iter_statement
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
  let replace_breaks_with (st : A.statement) (nst : A.statement) : A.statement =
    let obj =
      object
        inherit [_] A.map_statement as super

        method! visit_Loop entered_loop loop =
          assert (not entered_loop);
          super#visit_Loop true loop

        method! visit_Break _ i =
          assert (i = 0);
          nst.content
      end
    in
    obj#visit_statement false st
  in

  (* The visitor *)
  let obj =
    object
      inherit [_] A.map_statement as super

      method! visit_Sequence env st1 st2 =
        match st1.content with
        | Loop _ ->
            assert (statement_has_no_loop_break_continue st2);
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

let apply_passes (crate : A.crate) : A.crate =
  let passes = [ remove_loop_breaks crate ] in
  let functions =
    List.fold_left (fun fl pass -> List.map pass fl) crate.functions passes
  in
  let crate = { crate with functions } in
  log#ldebug
    (lazy ("After pre-passes:\n" ^ Print.Crate.crate_to_string crate ^ "\n"));
  crate
