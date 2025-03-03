import Aeneas.Range.Notations
import Aeneas.Range.SRRange.Basic

namespace Aeneas.Notations

namespace SRRange

open Range -- activates the aeneas_range_tactic notation

  scoped macro_rules
  | `([ $start : $stop ]) =>
    `({ start := $start, stop := $stop, step := 1,
        step_pos := by aeneas_range_tactic : SRRange })
  | `([ $start : $stop : $step ]) =>
    `({ start := $start, stop := $stop, step := $step,
        step_pos := by aeneas_range_tactic : SRRange })

end SRRange

end Aeneas.Notations
