import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Base from "../../backends/lean"

package «tests» {}

@[default_target] lean_lib tutorial
@[default_target] lean_lib betreeMain
@[default_target] lean_lib constants
@[default_target] lean_lib external
@[default_target] lean_lib hashmap
@[default_target] lean_lib hashmapMain
@[default_target] lean_lib loops
@[default_target] lean_lib noNestedBorrows
@[default_target] lean_lib paper
@[default_target] lean_lib poloniusList
@[default_target] lean_lib array
