/- `alloc::boxed`: `Box<T>` is `T` in the extracted Lean code, and `into_raw`/`from_raw` move the value
into and out of a allocation of the global allocator. -/
module
public import Aeneas.Std.Alloc.Alloc
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Convert
public section

open Aeneas SepLogic

namespace Aeneas.Std

open Result

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
def alloc.boxed.Box.into_raw (b : T) : Result (MutRawPtr T) :=
  alloc.alloc.Global.mk.allocate [b]

/-- Frees the `Box` using `Global.deallocate`, as dropping a Box in Rust would do --/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw (p : MutRawPtr T) : Result T := do
  let value ← RawPtr.read p
  alloc.alloc.Global.mk.deallocate p 1
  pure value

@[step]
theorem alloc.boxed.Box.into_raw.spec (value : T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw value ⦃ q => q ↦ value ∗ q.freeable⦄ := by
  simpa only [alloc.boxed.Box.into_raw, ← RawPtr.pointsTo_eq_range, List.length_singleton] using
    alloc.alloc.Global.allocate.spec alloc.alloc.Global.mk [value]

/-- `q.freeable` is required: without it, `q` could be an interior pointer or point to a local
behind a reference, and freeing it is undefined behaviour
([`Box::from_raw`](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.from_raw)). -/
@[step]
theorem alloc.boxed.Box.from_raw.spec {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ∗ q.freeable ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝⦄ := by
  unfold alloc.boxed.Box.from_raw
  apply WP.ispec_bind (RawPtr.read.spec q value) (entails_refl _)
  intro result
  apply WP.ispec_bind (alloc.alloc.Global.deallocate.spec alloc.alloc.Global.mk q [value] 1 rfl)
  · rw [← RawPtr.pointsTo_eq_range]
    iframe
  · intro _
    apply (WP.ispec_ok _).2
    iframe

end Aeneas.Std
