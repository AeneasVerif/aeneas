module
public import Aeneas.Std.Primitives
public meta import Aeneas.Extract.Extract
@[expose] public section

/-!
# `ManuallyDrop`

Drops are no-ops in the model, so `ManuallyDrop<T>` is a plain wrapper.
-/

namespace Aeneas.Std

open Result

@[rust_type "core::mem::manually_drop::ManuallyDrop"]
structure core.mem.manually_drop.ManuallyDrop (T : Type) where
  value : T

@[rust_fun "core::mem::manually_drop::{core::mem::manually_drop::ManuallyDrop<@T>}::new"]
def core.mem.manually_drop.ManuallyDrop.new {T : Type} (value : T) :
    Result (core.mem.manually_drop.ManuallyDrop T) :=
  ok ⟨value⟩

@[rust_fun "core::mem::manually_drop::{core::mem::manually_drop::ManuallyDrop<@T>}::into_inner"]
def core.mem.manually_drop.ManuallyDrop.into_inner {T : Type}
    (slot : core.mem.manually_drop.ManuallyDrop T) : Result T :=
  ok slot.value

@[rust_fun
  "core::mem::manually_drop::{core::ops::deref::Deref<core::mem::manually_drop::ManuallyDrop<@T>, @T>}::deref"]
def core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDeref.deref {T : Type}
    (slot : core.mem.manually_drop.ManuallyDrop T) : Result T :=
  ok slot.value

@[rust_fun
  "core::mem::manually_drop::{core::ops::deref::DerefMut<core::mem::manually_drop::ManuallyDrop<@T>, @T>}::deref_mut"]
def core.mem.manually_drop.ManuallyDrop.Insts.CoreOpsDerefDerefMut.deref_mut {T : Type}
    (slot : core.mem.manually_drop.ManuallyDrop T) :
    Result (T × (T → core.mem.manually_drop.ManuallyDrop T)) :=
  ok (slot.value, fun value => ⟨value⟩)

end Aeneas.Std
