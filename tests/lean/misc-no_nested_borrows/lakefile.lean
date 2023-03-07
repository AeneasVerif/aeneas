import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «no_nested_borrows» {
  -- add package configuration options here
}

lean_lib «Base» {
  -- add library configuration options here
}

lean_lib «NoNestedBorrows» {
  -- add library configuration options here
}

