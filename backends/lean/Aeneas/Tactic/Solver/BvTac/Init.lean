module
public import Lean
public section

namespace Aeneas.BvTac

open Lean Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `BvTac

end Aeneas.BvTac
