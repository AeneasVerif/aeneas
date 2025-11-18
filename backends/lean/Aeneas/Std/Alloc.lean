import Lean
import Aeneas.Std.Core

namespace Aeneas

namespace Std

open Result

@[rust_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref" -canFail (filterParams := [true, false])]
def alloc.boxed.Box.deref {T : Type} (x : T) : T := x

@[rust_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut" -canFail (filterParams := [true, false])]
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
