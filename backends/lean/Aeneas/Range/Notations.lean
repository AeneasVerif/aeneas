import Aeneas.ScalarTac.ScalarTac

namespace Aeneas.Notations.Range

scoped syntax "aeneas_range_tactic" : tactic

-- The default tactic to discharge proof obligations related to ranges
macro_rules
| `(tactic| aeneas_range_tactic) => `(tactic| first | decide | scalar_tac)

end Aeneas.Notations.Range
