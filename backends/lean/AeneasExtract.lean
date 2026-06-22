import Aeneas

open Lean Aeneas Extract

@[extern "lean_enable_initializer_execution"]
private unsafe opaque enableInitializerExecutionUnsafe : BaseIO Unit
@[implemented_by enableInitializerExecutionUnsafe]
private opaque enableInitializerExecution : BaseIO Unit

def main : IO Unit := do
  println! "Starting extraction"
  enableInitializerExecution.toIO
  -- We need to do this otherwise loading the module (to get the environment) fails
  initSearchPath (← findSysroot)
  -- Load the environment from the module `Aeneas` and extract the state
  writeToFile `Aeneas "../../src/extract/ExtractBuiltinLean.ml"
  println! "Extraction done"
