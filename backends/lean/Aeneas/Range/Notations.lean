namespace Aeneas.Notations.Range

scoped syntax "aeneas_range_tactic" : tactic

-- The default tactic to discharge proof obligations related to ranges
macro_rules
| `(tactic| aeneas_range_tactic) => `(tactic| decide)

end Aeneas.Notations.Range
