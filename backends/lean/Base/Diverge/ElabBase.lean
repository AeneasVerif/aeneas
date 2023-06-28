import Lean

namespace Diverge

open Lean

initialize registerTraceClass `Diverge.divRecursion (inherited := true)

end Diverge
