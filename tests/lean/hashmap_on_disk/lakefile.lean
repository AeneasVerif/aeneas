import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «hashmap_main» {
  -- add package configuration options here
}

lean_lib «Base» {
  -- add library configuration options here
}

lean_lib «HashmapMain» {
  -- add library configuration options here
}

