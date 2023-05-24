import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «base» {}

@[default_target]
lean_lib «Primitives» {}
