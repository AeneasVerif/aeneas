module
public import Lean
public section
open Lean Elab Term Meta

namespace Aeneas.Step

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Step
initialize registerTraceClass `StepElab
initialize registerTraceClass `DspecInduction

end Aeneas.Step
