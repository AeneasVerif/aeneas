import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «hashmap» {
  -- add package configuration options here
}

lean_lib «Base» {
  -- add library configuration options here
}

lean_lib «Hashmap» {
  -- add library configuration options here
}

