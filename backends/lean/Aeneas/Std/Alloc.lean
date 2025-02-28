import Lean
import Aeneas.Std.Core

namespace Aeneas

namespace Std

open Result

def alloc.boxed.Box.deref {T : Type} (x : T) : T := x
def alloc.boxed.Box.deref_mut {T : Type} (x : T) : (T × (T → T)) := (x, λ x => x)

/-- Trait instance -/
def core.ops.deref.DerefBoxInst (T : Type) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
def core.ops.deref.DerefMutBoxInst (T : Type) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

namespace Std

namespace Aeneas
