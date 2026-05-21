open Aeneas

let check label expected actual =
  if actual <> expected then
    failwith
      (label ^ ": expected " ^ PrintSymbolicAst.loop_exit_kind_to_string expected
     ^ ", got " ^ PrintSymbolicAst.loop_exit_kind_to_string actual)

let check_string label expected actual =
  if actual <> expected then
    failwith (label ^ ": expected " ^ expected ^ ", got " ^ actual)

let check_invalid_break_depth () =
  try
    ignore (SymbolicAst.loop_exit_kind_from_break_depth (-1));
    failwith "negative break depth should be rejected"
  with Invalid_argument _ -> ()

let check_invalid_continue_depth depth =
  try
    ignore (SymbolicAst.loop_exit_kind_from_continue_depth depth);
    failwith "non-positive continue depth should remain LoopContinue"
  with Invalid_argument _ -> ()

let check_empty_exit kind =
  let exit =
    SymbolicAst.
      { exit_kind = kind; exit_svalues = []; exit_abs = []; exit_expr = None }
  in
  check "empty exit kind" kind exit.exit_kind;
  if exit.exit_svalues <> [] then failwith "unexpected exit symbolic values";
  if exit.exit_abs <> [] then failwith "unexpected exit abstractions";
  if exit.exit_expr <> None then failwith "unexpected exit expression"

let () =
  check "break depth 0" SymbolicAst.NormalBreak
    (SymbolicAst.loop_exit_kind_from_break_depth 0);
  check "break depth 1" (SymbolicAst.PropagatedBreak 0)
    (SymbolicAst.loop_exit_kind_from_break_depth 1);
  check "continue depth 1" (SymbolicAst.PropagatedContinue 0)
    (SymbolicAst.loop_exit_kind_from_continue_depth 1);
  check_invalid_break_depth ();
  check_invalid_continue_depth 0;
  check_invalid_continue_depth (-1);
  check_string "normal break printer" "NormalBreak"
    (PrintSymbolicAst.loop_exit_kind_to_string SymbolicAst.NormalBreak);
  check_string "propagated break printer" "PropagatedBreak 0"
    (PrintSymbolicAst.loop_exit_kind_to_string
       (SymbolicAst.PropagatedBreak 0));
  check_string "propagated continue printer" "PropagatedContinue 0"
    (PrintSymbolicAst.loop_exit_kind_to_string
       (SymbolicAst.PropagatedContinue 0));
  check_string "propagated return printer" "PropagatedReturn"
    (PrintSymbolicAst.loop_exit_kind_to_string SymbolicAst.PropagatedReturn);
  List.iter check_empty_exit
    [
      SymbolicAst.NormalBreak;
      SymbolicAst.PropagatedBreak 0;
      SymbolicAst.PropagatedContinue 0;
      SymbolicAst.PropagatedReturn;
    ]
