/- `core::mem::maybe_uninit` -/
module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Ptr
@[expose] public section

/-! A `MaybeUninit<T>` is either uninitialized or holds a value of `T`. In the heap, it is stored in a
cell of `T`, uninitialized if the value is (`Pointee` instance): a pointer to a `MaybeUninit<T>`
can be cast to a pointer to `T` (and back), and reading uninitialized memory at type `T` fails.

Limitation: generic code instantiated with `MaybeUninit<U>` uses the default `Pointee` instance
(cells of type `MaybeUninit U`), so its accesses to the cells of `MaybeUninit<U>` values always
fail (see `Pointee`). `MaybeUninit<MaybeUninit<U>>` is stored in cells of `MaybeUninit U`. -/

open Aeneas SepLogic

namespace Aeneas.Std

open Result WP

@[rust_type "core::mem::maybe_uninit::MaybeUninit" (body := .opaque)]
inductive MaybeUninit (T : Type u) where
  | uninit
  | init (value : T)

def MaybeUninit.toOption {T : Type u} : MaybeUninit T → Option T
  | .uninit => none
  | .init value => some value

def MaybeUninit.ofOption {T : Type u} : Option T → MaybeUninit T
  | none => .uninit
  | some value => .init value

/-- The cells of a `MaybeUninit<T>` are the cells of `T` (not of a nested `MaybeUninit`: those
are the cells of `MaybeUninit<T>`), uninitialized if the value is. -/
instance MaybeUninit.instPointee {T : Type} : Pointee (MaybeUninit T) where
  Cell := T
  toCell := MaybeUninit.toOption
  ofCell content := some (MaybeUninit.ofOption content)
  ofCell_toCell value := by cases value <;> rfl

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::uninit"]
def core.mem.maybe_uninit.MaybeUninit.uninit (T : Type u) : Result (MaybeUninit T) :=
  ok .uninit

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::new"]
def core.mem.maybe_uninit.MaybeUninit.new {T : Type u} (value : T) : Result (MaybeUninit T) :=
  ok (.init value)

/-- Initializes the value; the returned mutable borrow gives access to it. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::write"]
def core.mem.maybe_uninit.MaybeUninit.write {T : Type u} (_ : MaybeUninit T) (value : T) :
    Result (T × (T → MaybeUninit T)) :=
  ok (value, .init)

/-- Fails if the value is uninitialized. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::assume_init"]
def core.mem.maybe_uninit.MaybeUninit.assume_init {T : Type u} : MaybeUninit T → Result T
  | .uninit => fail .undef
  | .init value => ok value

/-- End of the shared borrow of `as_ptr`: the cell must still hold the value (writing through a
const pointer cast to mut is UB), and the view is freed. -/
def core.mem.maybe_uninit.MaybeUninit.end_as_ptr {T : Type} (m : MaybeUninit T)
    (p : ConstRawPtr T) : Result Unit := do
  let value ← (p.cast (MaybeUninit T)).read
  p.endView 1
  Result.require (value = m)

/-- End of the mutable borrow of `as_mut_ptr`: the content of the cell, initialized or not, is the
new value, and the view is freed. -/
def core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr {T : Type} (p : MutRawPtr T) :
    Result (MaybeUninit T) := do
  let value ← (p.cast (MaybeUninit T)).read
  p.endView 1
  .ok value

/-- The pointer is a view of the value: a fresh cell, uninitialized if the value is. The back
computation runs when the borrow ends. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_ptr"
  (statefulLifetimes := [0])]
def core.mem.maybe_uninit.MaybeUninit.as_ptr {T : Type} (m : MaybeUninit T) :
    Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.allocView [m]) fun p =>
    .ok ((p.cast T).cast_const, core.mem.maybe_uninit.MaybeUninit.end_as_ptr m (p.cast T).cast_const)

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_mut_ptr"
  (statefulLifetimes := [0])]
def core.mem.maybe_uninit.MaybeUninit.as_mut_ptr {T : Type} (m : MaybeUninit T) :
    Result (MutRawPtr T × Result (MaybeUninit T)) :=
  Aeneas.Std.bind (RawPtr.allocView [m]) fun p =>
    .ok (p.cast T, core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr (p.cast T))

@[rust_fun "core::mem::maybe_uninit::{core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>}::clone"]
def core.mem.maybe_uninit.CloneMaybeUninit.clone {T : Type u} (_ : core.marker.Copy T)
    (m : MaybeUninit T) : Result (MaybeUninit T) :=
  ok m

@[reducible, rust_trait_impl "core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.clone.CloneMaybeUninit {T : Type u} (copyInst : core.marker.Copy T) :
    core.clone.Clone (MaybeUninit T) := {
  clone := core.mem.maybe_uninit.CloneMaybeUninit.clone copyInst
}

@[reducible, rust_trait_impl "core::marker::Copy<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.marker.CopyMaybeUninit {T : Type u} (copyInst : core.marker.Copy T) :
    core.marker.Copy (MaybeUninit T) := {
  cloneInst := core.clone.CloneMaybeUninit copyInst
}

namespace MaybeUninit

@[simp] theorem toOption_uninit {T : Type u} : (uninit : MaybeUninit T).toOption = none := rfl
@[simp] theorem toOption_init {T : Type u} (v : T) : (init v).toOption = some v := rfl
@[simp] theorem ofOption_none {T : Type u} : ofOption (none : Option T) = uninit := rfl
@[simp] theorem ofOption_some {T : Type u} (v : T) : ofOption (some v) = init v := rfl
@[simp] theorem ofOption_toOption {T : Type u} (m : MaybeUninit T) : ofOption m.toOption = m := by
  cases m <;> rfl
@[simp] theorem toOption_ofOption {T : Type u} (c : Option T) : (ofOption c).toOption = c := by
  cases c <;> rfl

@[simp] theorem toCell_eq {T : Type} (m : MaybeUninit T) : Pointee.toCell m = m.toOption := rfl

@[simp] theorem ofCell_eq {T : Type} (content : Option T) :
    (Pointee.ofCell content : Option (MaybeUninit T)) = some (ofOption content) := rfl

end MaybeUninit

section

variable {T : Type} {M : Mutability}

/-- A pointer to `MaybeUninit<T>` owns cells of `T`. -/
theorem MaybeUninit.pointsTo_eq (q : RawPtr (MaybeUninit T) M) (m : MaybeUninit T) :
    (q ↦ m) = ((q.cast T) ↦? m.toOption) := rfl

theorem MaybeUninit.pointsToRange_eq (q : RawPtr (MaybeUninit T) M) (ms : List (MaybeUninit T)) :
    (q ↦* ms) = ((q.cast T) ↦*? ms.map MaybeUninit.toOption) := rfl

@[simp] theorem MaybeUninit.pointsToCell_cast (q : RawPtr T M) (content : Option T) :
    ((q.cast (MaybeUninit T)) ↦? content) = (q ↦? content) := rfl

@[simp] theorem MaybeUninit.pointsToCells_cast (q : RawPtr T M) (contents : List (Option T)) :
    ((q.cast (MaybeUninit T)) ↦*? contents) = (q ↦*? contents) := rfl

/-- A buffer of `MaybeUninit<T>` whose first cells are initialized with `vs`. -/
theorem MaybeUninit.pointsToRange_init (q : RawPtr (MaybeUninit T) M) (vs : List T)
    (ms : List (MaybeUninit T)) :
    (q ↦* (vs.map .init ++ ms)) =
      iprop((q.cast T) ↦* vs ∗ ((q.cast T).shift vs.length) ↦*? ms.map MaybeUninit.toOption) := by
  rw [MaybeUninit.pointsToRange_eq, List.map_append, List.map_map,
    show MaybeUninit.toOption ∘ MaybeUninit.init = (some : T → Option T) from rfl,
    RawPtr.pointsToCells_append, List.length_map]
  rfl

/-- `add` on a pointer to `MaybeUninit<T>` cast to a pointer to `T`. -/
theorem MaybeUninit.add_cast.spec (q : RawPtr (MaybeUninit T) M) (ms : List (MaybeUninit T))
    (count : Usize) (h : count.val ≤ ms.length) :
    ⦃ q ↦* ms ⦄ (q.cast T).add count
      ⦃ r => ⌜r = (q.cast T).shift count.val⌝ ∗ q ↦* ms ⦄ :=
  RawPtr.add.spec_cells (q.cast T) (ms.map MaybeUninit.toOption) count (by simpa)

/-- Writing through a pointer to `MaybeUninit<T>` cast to a pointer to `T` initializes it. -/
@[step]
theorem MaybeUninit.write_cast.spec (q : MutRawPtr (MaybeUninit T)) (m : MaybeUninit T) (v : T) :
    ⦃ q ↦ m ⦄ MutRawPtr.write (q.cast T) v ⦃ q ↦ MaybeUninit.init v ⦄ :=
  MutRawPtr.write.spec_cell (q.cast T) m.toOption v

theorem MaybeUninit.write_cast.spec_range (q : MutRawPtr (MaybeUninit T))
    (ms : List (MaybeUninit T)) (i : Nat) (v : T) (hIndex : i < ms.length) :
    ⦃ q ↦* ms ⦄ MutRawPtr.write ((q.cast T).shift i) v ⦃ q ↦* ms.set i (.init v) ⦄ := by
  rw [MaybeUninit.pointsToRange_eq, MaybeUninit.pointsToRange_eq, List.map_set]
  exact MutRawPtr.write.spec_cells (q.cast T) _ i v (by simpa using hIndex)

/-- Reading through a pointer to `MaybeUninit<T>` cast to a pointer to `T`. -/
@[step]
theorem MaybeUninit.read_cast.spec (q : RawPtr (MaybeUninit T) M) (v : T) :
    ⦃ q ↦ MaybeUninit.init v ⦄ RawPtr.read (q.cast T)
      ⦃ r => ⌜r = v⌝ ∗ q ↦ MaybeUninit.init v ⦄ :=
  RawPtr.read.spec (q.cast T) v

/-- Reading uninitialized memory through a pointer to `MaybeUninit<T>` cast to a pointer to `T`
fails. -/
theorem MaybeUninit.read_cast.fails (q : RawPtr (MaybeUninit T) M) :
    ifails (q ↦ MaybeUninit.uninit) (RawPtr.read (q.cast T)) :=
  RawPtr.read.fails_uninit (q.cast T) rfl

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.uninit.spec :
    core.mem.maybe_uninit.MaybeUninit.uninit T ⦃ m => m = .uninit ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.uninit]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.new.spec (value : T) :
    core.mem.maybe_uninit.MaybeUninit.new value ⦃ m => m = .init value ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.new]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.write.spec (m : MaybeUninit T) (value : T) :
    core.mem.maybe_uninit.MaybeUninit.write m value
      ⦃ v back => v = value ∧ back = .init ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.write]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.assume_init.spec (value : T) :
    core.mem.maybe_uninit.MaybeUninit.assume_init (.init value) ⦃ v => v = value ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.assume_init]

/-- `assume_init` on an uninitialized value fails. -/
theorem core.mem.maybe_uninit.MaybeUninit.assume_init.fails_uninit {P : IPre} :
    ifails P (core.mem.maybe_uninit.MaybeUninit.assume_init (.uninit : MaybeUninit T)) :=
  ifails_fail _

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_mut_ptr.spec (m : MaybeUninit T) :
    ⦃ emp ⦄ core.mem.maybe_uninit.MaybeUninit.as_mut_ptr m
      ⦃ (p, back) => ⌜back = core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr p⌝ ∗
        p ↦? m.toOption ∗ p.freeable 1 .view ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.as_mut_ptr
  apply WP.ispec_bind (RawPtr.allocView.spec [m])
  · iframe
  · intro p
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair, ← RawPtr.pointsTo_eq_range, MaybeUninit.pointsTo_eq,
      List.length_singleton, RawPtr.freeable_cast]
    iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr.spec (p : MutRawPtr T)
    (content : Option T) :
    ⦃ p ↦? content ∗ p.freeable 1 .view ⦄ core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr p
      ⦃ m => ⌜m = MaybeUninit.ofOption content⌝ ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr
  apply WP.ispec_bind (RawPtr.read.spec_cell (p.cast (MaybeUninit T)) content
    (MaybeUninit.ofOption content) rfl)
  · iframe
  · intro result
    rw [SepLogic.sep_assoc_eq, WP.ispec_ipure]
    rintro rfl
    apply WP.ispec_bind (RawPtr.endView.spec_cells p [content] 1 rfl)
    · rw [← RawPtr.pointsToCell_eq_cells]
      iframe
    · intro _
      apply (WP.ispec_ok _).2
      iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_ptr.spec (m : MaybeUninit T) :
    ⦃ emp ⦄ core.mem.maybe_uninit.MaybeUninit.as_ptr m
      ⦃ (p, back) => ⌜back = core.mem.maybe_uninit.MaybeUninit.end_as_ptr m p⌝ ∗
        p ↦? m.toOption ∗ p.freeable 1 .view ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.as_ptr
  apply WP.ispec_bind (RawPtr.allocView.spec [m])
  · iframe
  · intro p
    apply (ispec_ok _).2
    simp only [uncurry_apply_pair, ← RawPtr.pointsTo_eq_range, MaybeUninit.pointsTo_eq,
      List.length_singleton, RawPtr.freeable_cast, RawPtr.freeable_cast_const,
      RawPtr.pointsToCell_cast_const]
    iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.end_as_ptr.spec (m : MaybeUninit T)
    (p : ConstRawPtr T) :
    ⦃ p ↦? m.toOption ∗ p.freeable 1 .view ⦄ core.mem.maybe_uninit.MaybeUninit.end_as_ptr m p
      ⦃ emp ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.end_as_ptr
  apply WP.ispec_bind (RawPtr.read.spec (p.cast (MaybeUninit T)) m)
  · iframe
  · intro v
    rw [SepLogic.sep_assoc_eq, WP.ispec_ipure]
    intro hv
    apply WP.ispec_bind (RawPtr.endView.spec_cells p [m.toOption] 1 rfl)
    · rw [← RawPtr.pointsToCell_eq_cells]
      iframe
    · intro _
      apply WP.ispec_mono (Result.require.spec hv) <;> iframe

end

end Aeneas.Std
