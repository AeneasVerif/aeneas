import Lean
open Lean Elab Term Meta

namespace Aeneas.Progress

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Progress
initialize registerTraceClass `ProgressStar

end Aeneas.Progress
