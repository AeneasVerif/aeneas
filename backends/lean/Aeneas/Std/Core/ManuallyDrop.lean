/- `core::mem::manually_drop` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
@[expose] public section

/-! Drops are no-ops in the model, so `ManuallyDrop<T>` is a plain wrapper, stored in the cells of
`T` (it is `repr(transparent)`). -/

namespace Aeneas.Std

open Result

/-! ### START Trusted definitions -/

@[rust_type "core::mem::manually_drop::ManuallyDrop"]
structure core.mem.manually_drop.ManuallyDrop (T : Type) where
  value : T

instance core.mem.manually_drop.ManuallyDrop.instPointee {T : Type} [Pointee T] :
    Pointee (core.mem.manually_drop.ManuallyDrop T) where
  Cell := Pointee.Cell T
  size := Pointee.size T
  align := Pointee.align T
  nonZero := Pointee.nonZero T
  toCells m := Pointee.toCells m.value
  ofCells cells := (Pointee.ofCells (T := T) cells).map .mk

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

/-! ### END Trusted definitions -/

instance core.mem.manually_drop.ManuallyDrop.instLawful {T : Type} [Pointee T] [Pointee.Lawful T] :
    Pointee.Lawful (core.mem.manually_drop.ManuallyDrop T) where
  length_toCells m := Pointee.Lawful.length_toCells m.value
  ofCells_toCells m := by
    show (Pointee.ofCells (T := T) (Pointee.toCells m.value)).map _ = _
    rw [Pointee.Lawful.ofCells_toCells]
    rfl
  align_pos := (Pointee.Lawful.align_pos : 0 < Pointee.align T)
  align_dvd_size := (Pointee.Lawful.align_dvd_size : Pointee.align T ∣ Pointee.size T)

end Aeneas.Std
