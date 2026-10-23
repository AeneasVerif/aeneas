import Aeneas.Extract.Extract

/-!
# Extract the models of the Rust standard library

Generates `src/extract/ExtractBuiltinLean.ml`, which lists the Lean models of the Rust standard
library.
-/

open Lean Aeneas Extract

def main : IO Unit := do
  println! "Starting extraction"
  unsafe Lean.enableInitializersExecution
  -- We need to do this otherwise loading the module (to get the environment) fails
  initSearchPath (← findSysroot)
  -- Load the environment from the module `Aeneas` and extract the state
  writeToFile `Aeneas "../../src/extract/ExtractBuiltinLean.ml"
  println! "Extraction done"
