/- `alloc::boxed`: `Box<T>` is `T` in the extracted Lean code, and `into_raw`/`from_raw` move the value
into and out of a allocation of the global allocator. -/
module
public import Aeneas.Std.Alloc.Alloc
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Convert
public import Aeneas.Std.Core.MaybeUninit
public section

open Aeneas SepLogic

namespace Aeneas.Std

open Result WP

@[expose, rust_fun "alloc::boxed::{core::ops::deref::Deref<Box<@T>, @T>}::deref" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref {T : Type _} (x : T) : T := x

@[expose, rust_fun "alloc::boxed::{core::ops::deref::DerefMut<Box<@T>, @T>}::deref_mut" -canFail (keepParams := [true, false])]
def alloc.boxed.Box.deref_mut {T : Type _} (x : T) : (T × (T → T)) := (x, λ x => x)

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::Deref<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefBoxInst (T : Type _) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- Trait instance -/
@[expose, rust_trait_impl "core::ops::deref::DerefMut<Box<@T>, @T>" (keepParams := [true, false])]
def core.ops.deref.DerefMutBoxInst (T : Type _) :
  core.ops.deref.DerefMut T T := {
  derefInst := DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::convert::AsMut<Box<@T>, @T>}::as_mut" -canFail (keepParams := [true,false])]
def alloc.boxed.AsMutBox.as_mut {T : Type _} (x : T) : T × (T → T) :=
  (x, fun x => x)

@[expose, reducible, rust_trait_impl "core::convert::AsMut<Box<@T>, @T>"]
def core.convert.AsMutBox (T : Type _) : core.convert.AsMut T T := {
  as_mut := fun x => ok (alloc.boxed.AsMutBox.as_mut x)
}

@[expose, rust_fun "alloc::boxed::{core::clone::Clone<Box<@T>>}::clone"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def alloc.boxed.CloneBox.clone {T : Type _} (cloneInst : core.clone.Clone T) : T → Result T :=
  cloneInst.clone

@[expose, reducible, rust_trait_impl "core::clone::Clone<Box<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [true, false])]
def core.clone.CloneBox {T : Type _} (cloneInst : core.clone.Clone T) : core.clone.Clone T := {
  clone := alloc.boxed.CloneBox.clone cloneInst
}

@[expose, rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::eq" (keepParams := [true, false])]
def alloc.boxed.PartialEqBox.eq
  {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) (x y : T) : Result Bool :=
  PartialEqInst.eq x y

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<Box<@T>, Box<@T>>" (keepParams := [true, false])]
def core.cmp.PartialEqBox {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) :
  core.cmp.PartialEq T T := {
  eq := alloc.boxed.PartialEqBox.eq PartialEqInst
}

/-- Allocates a pointer using `Global.allocate`, as creating a Box in Rust would do --/
@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw [Pointee T] (b : T) : Result (MutRawPtr T) := do
  let p ← Global.mk.allocate [b]
  ok p.ptr

/-- Frees the `Box` using `Global.deallocate`, as dropping a Box in Rust would do --/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw [Pointee T] (p : MutRawPtr T) : Result T := do
  let value ← RawPtr.read p
  Global.mk.deallocate ⟨p⟩ 1
  pure value

@[step]
theorem alloc.boxed.Box.into_raw.spec [Pointee T] [Pointee.Lawful T] (value : T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw value ⦃ q => ⌜q.Aligned⌝ ∗ q ↦ value ∗ q.freeable⦄ := by
  unfold alloc.boxed.Box.into_raw
  apply WP.ispec_bind (Global.allocate.spec Global.mk [value])
  · iframe
  · intro q
    apply (WP.ispec_ok _).2
    simp only [RawPtr.pointsTo_eq_range, List.length_singleton]
    iframe

/-- `q.freeable` is required: without it, `q` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour
([`Box::from_raw`](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.from_raw)). -/
@[step]
theorem alloc.boxed.Box.from_raw.spec [Pointee T] [Pointee.Lawful T] {value : T} (q : MutRawPtr T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ∗ q.freeable ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝⦄ := by
  unfold alloc.boxed.Box.from_raw
  apply WP.ispec_bind (RawPtr.read.spec q value hAlign) (entails_refl _)
  intro result
  apply WP.ispec_bind (Global.deallocate.spec Global.mk ⟨q⟩ [value] 1 rfl)
  · rw [← RawPtr.pointsTo_eq_range]
    iframe
  · intro _
    apply (WP.ispec_ok _).2
    iframe

/-- `Box::from_raw` leaves the slot of the box freed. -/
theorem alloc.boxed.Box.from_raw.spec_freed [Pointee T] [Pointee.Lawful T] {value : T}
    (q : MutRawPtr T) (hAlign : q.Aligned) :
    ⦃ q ↦ value ∗ q.freeable ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝ ∗ q.freed⦄ := by
  unfold alloc.boxed.Box.from_raw
  apply WP.ispec_bind (RawPtr.read.spec q value hAlign) (entails_refl _)
  intro result
  apply WP.ispec_bind (Global.deallocate.spec_freed Global.mk ⟨q⟩ [value] 1 rfl)
  · rw [← RawPtr.pointsTo_eq_range]
    iframe
  · intro _
    apply (WP.ispec_ok _).2
    iframe

/-- Freeing a box twice fails. -/
theorem alloc.boxed.Box.from_raw.fails_freed [Pointee T] (q : MutRawPtr T)
    (hSize : Pointee.size T ≠ 0) :
    ifails q.freed (alloc.boxed.Box.from_raw q) := by
  unfold alloc.boxed.Box.from_raw
  exact ifails_bind_left (RawPtr.read.fails_freed q hSize)

/-- Freeing a pointer which does not come from a box (`from_mut`, `as_mut_ptr`, ...) fails. -/
theorem alloc.boxed.Box.from_raw.fails_view [Pointee T] [Pointee.Lawful T] {value : T}
    (q : MutRawPtr T) :
    ifails (q ↦ value ∗ q.freeable 1 .view) (alloc.boxed.Box.from_raw q) := by
  unfold alloc.boxed.Box.from_raw
  by_cases hAlign : q.Aligned
  swap
  · exact ifails_bind_left (RawPtr.read.fails_misaligned q hAlign)
  refine ifails_bind (ispec_frame (RawPtr.read.spec q value hAlign) (q.freeable 1 .view)) fun _ => ?_
  exact ifails_bind_left (ifails_mono (by iframe) (Global.deallocate.fails_view Global.mk ⟨q⟩ 1))

/-- Freeing a pointer one past the cell of a box (an interior pointer) fails. -/
theorem alloc.boxed.Box.from_raw.fails_end [Pointee T] (q : MutRawPtr T)
    (hSize : Pointee.size T ≠ 0) :
    ifails q.freeable (alloc.boxed.Box.from_raw (q.shift 1)) := by
  unfold alloc.boxed.Box.from_raw
  exact ifails_bind_left (RawPtr.read.fails_end q 1 .global hSize)

/-- `Box::new_uninit`: a box is its content. -/
@[rust_fun "alloc::boxed::{Box<@T>}::new_uninit"]
def alloc.boxed.Box.new_uninit (T : Type u) : Result (MaybeUninit T) :=
  ok .uninit

@[rust_fun "alloc::boxed::{Box<core::mem::maybe_uninit::MaybeUninit<@T>>}::assume_init"
  (keepParams := [true, false])]
def alloc.boxed.BoxMaybeUninit.assume_init {T : Type u} (b : MaybeUninit T) : Result T :=
  core.mem.maybe_uninit.MaybeUninit.assume_init b

@[step]
theorem alloc.boxed.Box.new_uninit.spec {T : Type u} :
    alloc.boxed.Box.new_uninit T ⦃ m => m = .uninit ⦄ := by
  simp [alloc.boxed.Box.new_uninit]

@[step]
theorem alloc.boxed.BoxMaybeUninit.assume_init.spec {T : Type u} (value : T) :
    alloc.boxed.BoxMaybeUninit.assume_init (.init value) ⦃ v => v = value ⦄ := by
  simp [alloc.boxed.BoxMaybeUninit.assume_init, core.mem.maybe_uninit.MaybeUninit.assume_init]

end Aeneas.Std
