import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «polonius_list» {}

lean_lib «Base» {}

@[default_target]
lean_lib «PoloniusList» {}
