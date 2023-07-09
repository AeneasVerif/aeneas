import Lean

namespace Diverge

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Diverge.elab
initialize registerTraceClass `Diverge.def
initialize registerTraceClass `Diverge.def.sigmas
initialize registerTraceClass `Diverge.def.genBody
initialize registerTraceClass `Diverge.def.valid
initialize registerTraceClass `Diverge.def.unfold

end Diverge
