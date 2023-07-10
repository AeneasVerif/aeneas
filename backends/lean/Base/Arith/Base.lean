import Lean

namespace Arith

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Arith

end Arith
