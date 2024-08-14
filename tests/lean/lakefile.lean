import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require base from "../../backends/lean"

package «tests» {}

@[default_target] lean_lib Arrays
@[default_target] lean_lib Avl
@[default_target] lean_lib Betree
@[default_target] lean_lib Constants
@[default_target] lean_lib Demo
@[default_target] lean_lib External
@[default_target] lean_lib Hashmap
@[default_target] lean_lib Loops
@[default_target] lean_lib NoNestedBorrows
@[default_target] lean_lib Paper
@[default_target] lean_lib PoloniusList
@[default_target] lean_lib Traits
@[default_target] lean_lib Tutorial
