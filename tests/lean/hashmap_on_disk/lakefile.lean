import Lake
open Lake DSL

package «hashmap» {
  -- add package configuration options here
}

lean_lib «Hashmap» {
  -- add library configuration options here
}

@[default_target]
lean_exe «hashmap» {
  root := `Main
}
