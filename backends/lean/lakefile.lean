import Lake
open Lake DSL

-- Important: mathlib imports std4 and quote4: we mustn't add a `require std4` line
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

package «aeneas» {}

@[default_target] lean_lib «Aeneas» {}

@[default_target] lean_lib «AeneasMeta» {
  precompileModules := true
}
