import Lean
import Aeneas.Std.Core

namespace Aeneas

namespace Std

open Result

attribute [rust_type "alloc::string::String"] String

/-- The type of the global allocator -/
@[rust_type "alloc::alloc::Global"]
inductive Global where | mk

@[rust_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref {T : Type} (x : T) : T := x

@[rust_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref_mut {T : Type} (x : T) : (T × (T → T)) := (x, λ x => x)

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>"]
def core.ops.deref.DerefBoxInst (T : Type) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>"]
def core.ops.deref.DerefMutBoxInst (T : Type) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

namespace Std

namespace Aeneas
