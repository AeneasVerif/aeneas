import Lean
import Base.Primitives.Base
import Base.Primitives.Core

open Primitives
open Result

namespace alloc

namespace boxed -- alloc.boxed

namespace Box -- alloc.boxed.Box

def deref {T : Type} (x : T) : Result T := ok x
def deref_mut {T : Type} (x : T) : Result (T × (T → T)) := ok (x, λ x => x)

/-- Trait instance -/
def coreopsDerefInst (Self : Type) :
  core.ops.deref.Deref Self := {
  Target := Self
  deref := deref
}

/-- Trait instance -/
def coreopsDerefMutInst (Self : Type) :
  core.ops.deref.DerefMut Self := {
  derefInst := coreopsDerefInst Self
  deref_mut := deref_mut
}

end Box -- alloc.boxed.Box

end boxed -- alloc.boxed

end alloc
