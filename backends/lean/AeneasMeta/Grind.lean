import Lean

namespace Aeneas.Grind

open Lean Elab.Tactic Grind

def evalGrind (config : Config) : TacticM Unit := do
  -- Remark: the syntax is used to get the location at which to print the warning for grind
  discard <| evalGrindCore (← `(Grind)) config none none none

end Aeneas.Grind
