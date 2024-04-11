import Lean
import Base.Primitives.Base
import Base.Primitives.CoreOps

open Primitives
open Result

namespace alloc

namespace boxed -- alloc.boxed

namespace Box -- alloc.boxed.Box

def deref (T : Type) (x : T) : Result T := ok x
def deref_mut (T : Type) (x : T) : Result (T × (T → Result T)) := ok (x, λ x => ok x)

/-- Trait instance -/
def coreopsDerefInst (Self : Type) :
  core.ops.deref.Deref Self := {
  Target := Self
  deref := deref Self
}

/-- Trait instance -/
def coreopsDerefMutInst (Self : Type) :
  core.ops.deref.DerefMut Self := {
  derefInst := coreopsDerefInst Self
  deref_mut := deref_mut Self
}

end Box -- alloc.boxed.Box

end boxed -- alloc.boxed

end alloc
