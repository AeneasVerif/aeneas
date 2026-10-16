module
public import Aeneas.Std.Core.Ptr
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Cmp
@[expose] public section

/-! # `core::ptr::NonNull`

A `NonNull<T>` is a mutable raw pointer which is not null. The model of raw pointers has no null
pointer except `RawPtr.null` (the allocation `0` is never allocated). `NonNull::dangling()` points
into the allocation `0` too, so it can not be dereferenced.

`NonNull T` is a structure rather than an abbreviation of `MutRawPtr T`, so that it can appear in
recursive types (`struct Node { next: NonNull<Node> }`): the kernel does not unfold abbreviations
when checking the positivity of inductive types. -/

open Aeneas SepLogic

namespace Aeneas.Std

open Result WP

/-! ### START Trusted definitions -/

@[rust_type "core::ptr::non_null::NonNull"]
structure NonNull (T : Type _) where
  ptr : RawPtr T .Mut
  deriving Inhabited, DecidableEq

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::new" -canFail -lift]
def NonNull.new {T : Type _} (p : MutRawPtr T) : Option (NonNull T) :=
  if p.loc = (RawPtr.null : MutRawPtr T).loc then none else some ⟨p⟩

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::new_unchecked"]
def NonNull.new_unchecked {T : Type _} (p : MutRawPtr T) : Result (NonNull T) :=
  if p.loc = (RawPtr.null : MutRawPtr T).loc then fail .undef else ok ⟨p⟩

/-- A pointer which is not null but can not be dereferenced. -/
@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::dangling" -canFail -lift]
def NonNull.dangling (T : Type _) : NonNull T := ⟨⟨⟨0, 1⟩⟩⟩

@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_ptr" -canFail -lift]
def NonNull.as_ptr {T : Type _} (p : NonNull T) : MutRawPtr T := p.ptr

/-- `&*p` (see `RawPtr.as_ref_unchecked`). -/
@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_ref"
  (statefulLifetimes := [0])]
def NonNull.as_ref {T : Type} [Pointee T] (p : NonNull T) : Result (T × Result Unit) :=
  RawPtr.as_ref_unchecked p.ptr

/-- `&mut *p` (see `RawPtr.as_mut_unchecked`). The pointer is borrowed mutably: it is given back
unchanged. -/
@[rust_fun "core::ptr::non_null::{core::ptr::non_null::NonNull<@T>}::as_mut"
  (statefulLifetimes := [0])]
def NonNull.as_mut {T : Type} [Pointee T] (p : NonNull T) :
    Result (T × (T → Result Unit) × NonNull T) :=
  Aeneas.Std.bind (RawPtr.as_mut_unchecked p.ptr) fun (value, back) => ok (value, back, p)

/-- `NonNull::from(&mut x)`: a view of the borrow, like `core::ptr::from_mut`. -/
@[rust_fun
  "core::ptr::non_null::{core::convert::From<core::ptr::non_null::NonNull<@T>, &'0 mut @T>}::from"
  (statefulLifetimes := [0])]
def NonNull.from_mut {T : Type} [Pointee T] (r : T) : Result (NonNull T × Result T) :=
  Aeneas.Std.bind (core.ptr.from_mut r) fun (p, back) => ok (⟨p⟩, back)

@[rust_fun
  "core::ptr::non_null::{core::clone::Clone<core::ptr::non_null::NonNull<@T>>}::clone"]
def NonNull.Insts.CoreCloneClone.clone {T : Type _} (p : NonNull T) : Result (NonNull T) :=
  ok p

@[reducible, rust_trait_impl "core::clone::Clone<core::ptr::non_null::NonNull<@T>>"]
def NonNull.Insts.CoreCloneClone (T : Type _) : core.clone.Clone (NonNull T) := {
  clone := NonNull.Insts.CoreCloneClone.clone
}

@[reducible, rust_trait_impl "core::marker::Copy<core::ptr::non_null::NonNull<@T>>"]
def NonNull.Insts.CoreMarkerCopy (T : Type _) : core.marker.Copy (NonNull T) := {
  cloneInst := NonNull.Insts.CoreCloneClone T
}

/-- See `RawPtr.eq`. -/
@[rust_fun
  "core::ptr::non_null::{core::cmp::PartialEq<core::ptr::non_null::NonNull<@T>, core::ptr::non_null::NonNull<@T>>}::eq"]
def NonNull.Insts.CoreCmpPartialEq.eq {T : Type} [Pointee T] (p q : NonNull T) : Result Bool :=
  RawPtr.eq p.ptr q.ptr

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::ptr::non_null::NonNull<@T>, core::ptr::non_null::NonNull<@T>>"]
def NonNull.Insts.CoreCmpPartialEq (T : Type) [Pointee T] :
    core.cmp.PartialEq (NonNull T) (NonNull T) := {
  eq := NonNull.Insts.CoreCmpPartialEq.eq
}

instance NonNull.instPointee {T : Type _} : Pointee (NonNull T) := Pointee.typed (NonNull T) true

instance NonNull.instLawful {T : Type _} : Pointee.Lawful (NonNull T) := Pointee.typed.lawful _ _

/-! ### END Trusted definitions -/

@[simp] theorem NonNull.as_ptr_eq {T : Type _} (p : NonNull T) : NonNull.as_ptr p = p.ptr := rfl

theorem NonNull.dangling_ne_null {T : Type _} :
    (NonNull.dangling T).ptr.loc ≠ (RawPtr.null : MutRawPtr T).loc := by
  simp [NonNull.dangling, RawPtr.null]

section

variable {T : Type} [Pointee T] [Pointee.Lawful T]

@[step]
theorem NonNull.as_ref.spec (p : NonNull T) (value : T)
    (hAlign : p.ptr.Aligned) :
    ⦃ p.ptr ↦ value ⦄ NonNull.as_ref p
      ⦃ (result, back) => ⌜result = value ∧ back = p.ptr.endBorrow value⌝ ∗ p.ptr ↦† 1⦄ :=
  RawPtr.as_ref_unchecked.spec p.ptr value hAlign

@[step]
theorem NonNull.as_mut.spec (p : NonNull T) (value : T)
    (hAlign : p.ptr.Aligned) :
    ⦃ p.ptr ↦ value ⦄ NonNull.as_mut p
      ⦃ (result, back, p') => ⌜result = value ∧ back = p.ptr.endBorrow ∧ p' = p⌝ ∗ p.ptr ↦† 1⦄ := by
  unfold NonNull.as_mut
  apply WP.ispec_bind (RawPtr.as_mut_unchecked.spec p.ptr value hAlign)
  · iframe
  · rintro ⟨v, back⟩
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair] at *
    iframe

@[step]
theorem NonNull.from_mut.spec (value : T) :
    ⦃ emp ⦄ NonNull.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q.ptr⌝ ∗ ⌜q.ptr.Aligned⌝ ∗ q.ptr ↦ value ∗
        q.ptr.freeable 1 .view⦄ := by
  unfold NonNull.from_mut
  apply WP.ispec_bind (core.ptr.from_mut.spec value)
  · iframe
  · rintro ⟨q, back⟩
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair] at *
    iframe

end

end Aeneas.Std
