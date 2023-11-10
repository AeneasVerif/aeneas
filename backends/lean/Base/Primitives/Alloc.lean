import Lean
import Base.Primitives.Base
import Base.Primitives.CoreOps

open Primitives
open Result

namespace alloc

namespace boxed -- alloc.boxed

namespace Box -- alloc.boxed.Box

def deref (T : Type) (x : T) : Result T := ret x
def deref_mut (T : Type) (x : T) : Result T := ret x
def deref_mut_back (T : Type) (_ : T) (x : T) : Result T := ret x

/-- Trait instance -/
def coreOpsDerefInst (Self : Type) :
  core.ops.deref.Deref Self := {
  Target := Self
  deref := deref Self
}

/-- Trait instance -/
def coreOpsDerefMutInst (Self : Type) :
  core.ops.deref.DerefMut Self := {
  derefInst := coreOpsDerefInst Self
  deref_mut := deref_mut Self
  deref_mut_back := deref_mut_back Self
}

end Box -- alloc.boxed.Box

end boxed -- alloc.boxed

end alloc
