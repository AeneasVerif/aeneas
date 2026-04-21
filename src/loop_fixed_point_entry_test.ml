open Aeneas

let check label expected actual =
  if actual <> expected then failwith ("unexpected classification: " ^ label)

let check_invalid_continue_depth () =
  try
    ignore
      (InterpLoopsFixedPoint.classify_loop_entry_result (Cps.Continue (-1)));
    failwith "negative continue depth should be rejected"
  with Invalid_argument _ -> ()

let () =
  check "continue 0" InterpLoopsFixedPoint.CurrentLoopReentry
    (InterpLoopsFixedPoint.classify_loop_entry_result (Cps.Continue 0));
  check "continue 1" (InterpLoopsFixedPoint.PropagatedContinueToOuter 0)
    (InterpLoopsFixedPoint.classify_loop_entry_result (Cps.Continue 1));
  check "continue 3" (InterpLoopsFixedPoint.PropagatedContinueToOuter 2)
    (InterpLoopsFixedPoint.classify_loop_entry_result (Cps.Continue 3));
  List.iter
    (fun res ->
      check "non-reentry" InterpLoopsFixedPoint.NonReentryExit
        (InterpLoopsFixedPoint.classify_loop_entry_result res))
    [ Cps.Break 0; Cps.Break 1; Cps.Return; Cps.Panic ];
  check "unit" InterpLoopsFixedPoint.UnitResult
    (InterpLoopsFixedPoint.classify_loop_entry_result Cps.Unit);
  check_invalid_continue_depth ()
