module
public import Lean
public section
open Lean Elab Term Meta

namespace Aeneas.Step

-- We can't define and use trace classes in the same file
meta initialize registerTraceClass `Step
meta initialize registerTraceClass `StepElab
meta initialize registerTraceClass `DspecInduction

end Aeneas.Step
