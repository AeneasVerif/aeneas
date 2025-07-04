import Lean

namespace Aeneas

namespace Utils

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Utils

end Utils

end Aeneas
