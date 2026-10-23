import Lake
open Lake DSL

-- Important: mathlib imports std4 and quote4: we mustn't add a `require std4` line
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

package «aeneas» where
  preferReleaseBuild := true
  buildArchive := s!"lean-build-aeneas-{System.Platform.target}.tar.gz"
  -- Models of the Rust standard library mirror Rust paths (e.g. `core.clone.Clone.clone`)
  leanOptions := #[⟨`weak.linter.dupNamespace, false⟩]

@[default_target] lean_lib «Aeneas» {}

private def notCI : Bool := run_io
  return (← IO.getEnv "CI").isNone

@[default_target] lean_lib «AeneasMeta» {
  -- Precompiling modules triggers issues in CI so we deactivate this.
  precompileModules := notCI
}
