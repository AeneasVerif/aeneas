import Base
open Primitives
open Result

namespace demo

def Vec (a : Type) (n : ℤ) := { l : List a // l.len = n }

-- set_option pp.explicit true
-- set_option pp.universes true
-- set_option pp.notation false

#check Vec
#print Vec

def append {a : Type} {n m : ℤ} (v : Vec a n) (w : Vec a m) : Vec a (n + m) :=
  let ⟨ vl, hv ⟩ := v
  match vl with
  | .nil =>
    sorry
  | .cons x vtl =>
    sorry

end demo
