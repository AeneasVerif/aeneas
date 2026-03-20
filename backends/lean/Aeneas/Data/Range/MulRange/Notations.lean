import Aeneas.Range.Notations
import Aeneas.Range.MulRange.Basic

namespace Aeneas.Notations

namespace MulRange

open Range -- activates the aeneas_range_tactic notation

  scoped syntax:max "[" withoutPosition(term ":" "<" term ":" "*=" term) "]" : term

  scoped macro_rules
  | `([ $start : < $stop : *= $step ]) =>
    `({ start := $start, start_pos := by aeneas_range_tactic
        stop := $stop,
        mul := $step, mul_pos := by aeneas_range_tactic : MulRange })

  example : MulRange := [1:<256:*=2]

end MulRange

end Aeneas.Notations
