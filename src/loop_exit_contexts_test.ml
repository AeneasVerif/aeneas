open Aeneas

let check label expected actual =
  if actual <> expected then failwith ("unexpected exit classification: " ^ label)

let check_invalid label res =
  try
    ignore (InterpLoopsFixedPoint.classify_loop_exit_result res);
    failwith (label ^ " should be rejected")
  with Invalid_argument _ -> ()

let check_groups label expected actual =
  if actual <> expected then failwith ("unexpected exit grouping: " ^ label)

let () =
  check "break 0" InterpLoopsFixedPoint.CurrentLoopBreak
    (InterpLoopsFixedPoint.classify_loop_exit_result (Cps.Break 0));
  check "break 1" (InterpLoopsFixedPoint.PropagatedLoopBreak 0)
    (InterpLoopsFixedPoint.classify_loop_exit_result (Cps.Break 1));
  check "break 3" (InterpLoopsFixedPoint.PropagatedLoopBreak 2)
    (InterpLoopsFixedPoint.classify_loop_exit_result (Cps.Break 3));
  check "continue 0" InterpLoopsFixedPoint.NotLoopExit
    (InterpLoopsFixedPoint.classify_loop_exit_result (Cps.Continue 0));
  check "continue 1" (InterpLoopsFixedPoint.PropagatedLoopContinue 0)
    (InterpLoopsFixedPoint.classify_loop_exit_result (Cps.Continue 1));
  check "return" InterpLoopsFixedPoint.PropagatedLoopReturn
    (InterpLoopsFixedPoint.classify_loop_exit_result Cps.Return);
  check "panic" InterpLoopsFixedPoint.NotLoopExit
    (InterpLoopsFixedPoint.classify_loop_exit_result Cps.Panic);
  check "unit" InterpLoopsFixedPoint.UnitLoopResult
    (InterpLoopsFixedPoint.classify_loop_exit_result Cps.Unit);
  check_invalid "negative break" (Cps.Break (-1));
  check_invalid "negative continue" (Cps.Continue (-1));
  check_groups "empty" []
    (InterpLoopsFixedPoint.group_by_propagated_exit_kind []);
  check_groups "kind and depth partition"
    [
      (InterpLoopsFixedPoint.PropagatedBreakExit 0, [ 1; 3 ]);
      (InterpLoopsFixedPoint.PropagatedBreakExit 1, [ 2 ]);
      (InterpLoopsFixedPoint.PropagatedContinueExit 0, [ 4; 6 ]);
      (InterpLoopsFixedPoint.PropagatedReturnExit, [ 5 ]);
    ]
    (InterpLoopsFixedPoint.group_by_propagated_exit_kind
       [
         (InterpLoopsFixedPoint.PropagatedBreakExit 0, 1);
         (InterpLoopsFixedPoint.PropagatedBreakExit 1, 2);
         (InterpLoopsFixedPoint.PropagatedBreakExit 0, 3);
         (InterpLoopsFixedPoint.PropagatedContinueExit 0, 4);
         (InterpLoopsFixedPoint.PropagatedReturnExit, 5);
         (InterpLoopsFixedPoint.PropagatedContinueExit 0, 6);
       ])
