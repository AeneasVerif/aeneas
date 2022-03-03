(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it
 *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module A = CfimAst
module M = Modules
module L = Logging

let log = L.pre_passes_log

(** Rustc inserts a lot of drops before the assignments.
    We consider those drops are part of the assignment, and splitting the
    drop and the assignment is problematic for us because it can introduce
    ⊥ under borrows. For instance, we encountered situations like the
    following one:
    
    ```
    drop( *x ); // Illegal! Inserts a ⊥ under a borrow
    *x = move ...;
    ```

 *)
let filter_drop_assigns (f : A.fun_decl) : A.fun_decl =
  (* The visitor *)
  let obj =
    object (self)
      inherit [_] A.map_statement as super

      method! visit_Sequence env st1 st2 =
        match (st1, st2) with
        | Drop p1, Assign (p2, _) ->
            if p1 = p2 then self#visit_statement env st2
            else super#visit_Sequence env st1 st2
        | Drop p1, Sequence (Assign (p2, _), _) ->
            if p1 = p2 then self#visit_statement env st2
            else super#visit_Sequence env st1 st2
        | _ -> super#visit_Sequence env st1 st2
    end
  in
  (* Map  *)
  let body = obj#visit_statement () f.body in
  { f with body }

let apply_passes (m : M.cfim_module) : M.cfim_module =
  let functions = List.map filter_drop_assigns m.functions in
  { m with functions }
