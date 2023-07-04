import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Base from "../../backends/lean"

package «tests» {}

@[default_target]
lean_lib «Tests» {}

lean_lib hashmap
