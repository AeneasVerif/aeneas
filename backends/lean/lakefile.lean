import Lake
open Lake DSL

-- Important: mathlib imports std4 and quote4: we mustn't add a `require std4` line
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0-rc1"

package «aeneas» {}

@[default_target] lean_lib «Aeneas» {}

private def notCI : Bool := run_io
  return (← IO.getEnv "CI").isNone

@[default_target] lean_lib «AeneasMeta» {
  -- Precompiling modules triggers issues in CI so we deactivate this.
  precompileModules := notCI
}

/-- Generate the `.ml` file listing the definitions supported by the standard library. -/
lean_exe extract where
  root := `AeneasExtract
  supportInterpreter := false

/-- Extract verification documentation metadata as JSON. -/
lean_exe doc_extract where
  root := `AeneasDocExtract
  supportInterpreter := false
