import Lean

namespace Aeneas.CryptoSolver

open Lean Meta

-- Trace classes (must be defined in a separate file from usage)
initialize registerTraceClass `CryptoSolver
initialize registerTraceClass `CryptoSolver.debug

end Aeneas.CryptoSolver
