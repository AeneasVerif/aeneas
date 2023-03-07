import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «external» {
  -- add package configuration options here
}

lean_lib «Base» {
  -- add library configuration options here
}

lean_lib «External» {
  -- add library configuration options here
}

