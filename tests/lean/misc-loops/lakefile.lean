import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «loops» {}

lean_lib «Base» {}

@[default_target]
lean_lib «Loops» {}
