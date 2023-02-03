import Base.Primitives
import HashmapMain.Funs

#eval hashmap_test1_fwd == .ret ()

def main : IO Unit :=
  if hashmap_test1_fwd == .ret () then
    IO.println s!"Test OK"
  else
    throw (IO.userError s!"Test failed")
