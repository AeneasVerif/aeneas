import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Base from "../../backends/lean"

package «tests» {}

@[default_target]
lean_lib «Tests» {}

lean_lib betreeMain
lean_lib constants
lean_lib external
lean_lib hashmap
lean_lib hashmapMain
lean_lib loops
lean_lib noNestedBorrows
lean_lib paper
lean_lib poloniusList
