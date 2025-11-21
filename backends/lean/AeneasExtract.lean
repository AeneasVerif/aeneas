import Aeneas

open Lean Aeneas Extract

def main : IO Unit := do
  println! "Starting extraction"
  -- We need to do this otherwise loading the module (to get the environment) fails
  initSearchPath (← findSysroot)
  -- Load the environment from the module `Aeneas` and extract the state
  writeToFile `Aeneas "../../src/extract/ExtractBuiltinLean.ml"
  println! "Extraction done"
