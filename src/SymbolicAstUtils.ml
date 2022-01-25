open Errors
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
open SymbolicAst
open ValuesUtils
open InterpreterUtils

type ('c, 's) ended = EndedConcrete of 'c | EndedSymbolic of 's

type ended_loan = (V.mvalue, V.msymbolic_value list) ended

type ended_borrow = (V.mvalue, V.msymbolic_value) ended

type ended_loan_or_borrow =
  | EndedLoan of ended_loan
  | EndedBorrow of ended_borrow

(** Return the list of the meta-values given to the top owned ended mutable
    loans/borrows of an abstraction
    
    We expect an abstraction where all the loans/borrows have ended.
    
    TODO: remove
 *)
let get_top_owned_ended_loans_borrows (abs : V.abs) : ended_loan_or_borrow list
    =
  (* The accumulator *)
  let acc = ref [] in
  let add x = acc := x :: !acc in
  let add_loan x = add (EndedLoan x) in
  let add_borrow x = add (EndedBorrow x) in
  let add_sloan x = add_loan (EndedSymbolic x) in
  let add_cloan x = add_loan (EndedConcrete x) in
  let add_sborrow x = add_borrow (EndedSymbolic x) in
  let add_cborrow x = add_borrow (EndedConcrete x) in

  (* The visitor *)
  let obj =
    object
      inherit [_] V.iter_abs as super

      method! visit_aproj env aproj =
        match aproj with
        | AEndedProjLoans (msv, []) ->
            (* The symbolic value was left unchanged *)
            add_sloan [ msv ]
        | AEndedProjLoans (_, mvl) -> add_sloan (List.map fst mvl)
        | AEndedProjBorrows mv -> add_sborrow mv
        | AIgnoredProjBorrows | AProjLoans (_, _) | AProjBorrows (_, _) ->
            failwith "Unreachable"

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (_, _) | ASharedLoan (_, _, _) -> failwith "Unreachable"
        | AEndedMutLoan { child = _; given_back = _; given_back_meta } ->
            (* Add the meta-value and stop the exploration *)
            add_cloan given_back_meta
        | AEndedSharedLoan (_, _) ->
            (* We don't dive into shared loans: there is nothing to give back
             * inside (note that there could be a mutable borrow in the shared
             * value, pointing to a mutable loan in the child avalue, but this
             * borrow is in practice immutable *)
            ()
        | AIgnoredMutLoan (_, _) ->
            (* There can be *inner* mutable loans, but not outer ones *)
            failwith "Unreachable"
        | AEndedIgnoredMutLoan _ ->
            (* Dive in *)
            super#visit_aloan_content env lc
        | AIgnoredSharedLoan _ ->
            (* Ignore *)
            ()

      method! visit_aborrow_content env bc =
        match bc with
        | AMutBorrow (_, _, _) | ASharedBorrow _ | AIgnoredMutBorrow (_, _) ->
            failwith "Unreachable"
        | AEndedMutBorrow (mv, _) ->
            (* Add the meta-value and stop the exploration *)
            add_cborrow mv
        | AEndedIgnoredMutBorrow _ ->
            (* Dive in *)
            super#visit_aborrow_content env bc
        | AProjSharedBorrow _ ->
            (* Ignore *)
            ()
    end
  in
  (* Apply *)
  obj#visit_abs () abs;
  (* Return the accumulated values *)
  List.rev !acc
