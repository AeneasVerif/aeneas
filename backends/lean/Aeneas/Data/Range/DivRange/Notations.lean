import Aeneas.Range.Notations
import Aeneas.Range.DivRange.Basic

namespace Aeneas.Notations

namespace DivRange

open Range -- activates the aeneas_range_tactic notation

  scoped syntax:max "[" withoutPosition(term ":" ">" term ":" "/=" term) "]" : term

  scoped macro_rules
  | `([ $start :  > $stop : /= $step ]) =>
    `({ start := $start, stop := $stop, divisor := $step,
        divisor_pos := by aeneas_range_tactic : DivRange })

  example : DivRange := [256:>1:/= 2]

end DivRange

end Aeneas.Notations
