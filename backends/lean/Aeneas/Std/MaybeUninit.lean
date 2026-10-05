module
public import Aeneas.Std.Buffer
public import Aeneas.Std.Core.Core
public meta import Aeneas.Extract.Extract
@[expose] public section

/-!
# Raw pointers to possibly uninitialized memory

The operations which convert values of type `MaybeUninit T` (or slices of
those) to raw pointers: the memory of an uninitialized value is made of
uninitialized cells, which can be written but not read.
-/

namespace Aeneas.Std

open Aeneas.SepLogic WP Result

variable {T : Type}

private theorem owns_empty_eq' : owns Heap.empty = emp :=
  bientails_eq ⟨fun _ _ => trivial, fun h _ => Heap.Sub.of_empty h⟩

namespace RawPtr

private theorem loc_add_size' [ByteRepr T] {M} (q : RawPtr T M) :
    q.loc.add (ByteRepr.size T) = (q.add 1).loc := by
  rw [loc_add, Nat.one_mul]

theorem pointsToUninit_eq_owns_of_aligned [ByteRepr T] {M} {q : RawPtr T M}
    (m : MaybeUninit T) (hAlign : q.Aligned) :
    (q ↦? m) = owns (Heap.cells q.loc m.cells) :=
  bientails_eq ⟨fun h hPointsTo => ((pointsToUninit_holds q m h).mp hPointsTo).2,
    fun h hOwns => (pointsToUninit_holds q m h).mpr ⟨hAlign, hOwns⟩⟩

theorem pointsToUninitRange_eq_owns [ByteRepr T] {M} (q : RawPtr T M)
    (ms : List (MaybeUninit T)) (hAlign : q.Aligned) :
    (q ↦?* ms) = owns (Heap.cells q.loc (ms.flatMap MaybeUninit.cells)) := by
  induction ms generalizing q with
  | nil =>
    rw [List.flatMap_nil, Heap.cells_nil, owns_empty_eq']
    rfl
  | cons m rest ih =>
    rw [pointsToUninitRange_cons, pointsToUninit_eq_owns_of_aligned m hAlign,
      ih _ ((aligned_add q 1).mpr hAlign), List.flatMap_cons, Heap.cells_append,
      bientails_eq (owns_union _ _ (Heap.compatible_cells_append _ _ _)),
      MaybeUninit.length_cells, loc_add_size']

/-- A range owns the concatenated cells of its values. -/
theorem pointsToUninitRange_owns [ByteRepr T] {M} (q : RawPtr T M)
    (ms : List (MaybeUninit T)) :
    q ↦?* ms ⊢ owns (Heap.cells q.loc (ms.flatMap MaybeUninit.cells)) := by
  induction ms generalizing q with
  | nil =>
    rw [List.flatMap_nil, Heap.cells_nil, owns_empty_eq']
    exact entails_refl _
  | cons m rest ih =>
    rw [pointsToUninitRange_cons, List.flatMap_cons, Heap.cells_append,
      bientails_eq (owns_union _ _ (Heap.compatible_cells_append _ _ _)),
      MaybeUninit.length_cells, loc_add_size']
    exact sep_mono (fun h hPointsTo => ((pointsToUninit_holds q m h).mp hPointsTo).2) (ih _)

theorem aligned_of_pointsToUninitRange [ByteRepr T] {M} {q : RawPtr T M}
    {ms : List (MaybeUninit T)} {h : Heap} (hPointsTo : (q ↦?* ms) h) (hMs : ms ≠ []) :
    q.Aligned := by
  cases ms with
  | nil => exact absurd rfl hMs
  | cons m rest =>
    obtain ⟨_, _, _, _, hFirst, -⟩ := hPointsTo
    exact ((pointsToUninit_holds q m _).mp hFirst).1

theorem pointsToUninitRange_of_owns [ByteRepr T] {M} (q : RawPtr T M)
    (ms : List (MaybeUninit T)) (hAlign : ms ≠ [] → q.Aligned) :
    owns (Heap.cells q.loc (ms.flatMap MaybeUninit.cells)) ⊢ q ↦?* ms := by
  cases ms with
  | nil => exact fun _ _ => trivial
  | cons m rest =>
    rw [pointsToUninitRange_eq_owns q _ (hAlign (List.cons_ne_nil _ _))]
    exact entails_refl _

/-! ## Allocating, reading back, writing and releasing ranges -/

/-- Allocate `ms` consecutively, at an address aligned to `align` (and to the
alignment of `T`), and pass a pointer to the first one to `mk`. -/
def allocUninit [ByteRepr T] {β : Type} (align : Nat) (ms : List (MaybeUninit T))
    (mk : MutRawPtr T → β) : Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    let loc := Heap.freshLoc h (Nat.lcm align (ByteRepr.align T))
    (mk ⟨loc.1, loc.2⟩, Heap.cells loc (ms.flatMap MaybeUninit.cells) ∪ h)

theorem allocUninit.spec [ByteRepr T] {β : Type} (align : Nat) (ms : List (MaybeUninit T))
    (mk : MutRawPtr T → β) (post : β → IProp)
    (hPost : ∀ q : MutRawPtr T, ⌜q.AlignedTo (Nat.lcm align (ByteRepr.align T))⌝ ∗
      q ↦?* ms ⊢ post (mk q)) :
    ⦃ emp ⦄ allocUninit align ms mk ⦃⇓ result => post result⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.cells (Heap.freshLoc (h ∪ frame) (Nat.lcm align (ByteRepr.align T)))
          (ms.flatMap MaybeUninit.cells))
        (h ∪ frame) :=
    Heap.compatible_fresh_cells _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.cells (Heap.freshLoc (h ∪ frame) (Nat.lcm align (ByteRepr.align T)))
        (ms.flatMap MaybeUninit.cells))
        h frame).mpr ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm, ?_⟩
  apply hPost
  apply (sep_pure_l _ _ _).mpr
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [pointsToUninitRange_eq_owns _ _ ⟨by simp [Nat.dvd_lcm_right], by simp⟩]
  exact Heap.Sub.union_left hFreshH

/-- Read back `n` possibly uninitialized values from `q` on. -/
def readUninitRange [ByteRepr T] {M} (q : RawPtr T M) (n : Nat) :
    Result (List (MaybeUninit T)) :=
  Result.guardedModify (fun h => (h.readCells q.loc (n * ByteRepr.size T)).isSome)
    fun h hSome =>
      (MaybeUninit.ofCellsRange ((h.readCells q.loc (n * ByteRepr.size T)).get hSome) n, h)

@[step]
theorem readUninitRange.spec [ByteRepr T] {M} (q : RawPtr T M) (ms : List (MaybeUninit T))
    (hSize : 0 < ByteRepr.size T) :
    ⦃ q ↦?* ms ⦄ q.readUninitRange ms.length ⦃⇓ r => ⌜r = ms⌝ ∗ q ↦?* ms⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hSub : Heap.Sub (Heap.cells q.loc (ms.flatMap MaybeUninit.cells)) (h ∪ frame) :=
    Heap.Sub.trans (pointsToUninitRange_owns q ms h hPointsTo) (Heap.Sub.union_left hCompatible)
  have hRead := Heap.readCells_of_sub hSub
  rw [MaybeUninit.length_flatMap_cells] at hRead
  refine ⟨by simp [hRead], h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨by simp only [hRead, Option.get_some, MaybeUninit.ofCellsRange_flatMap_cells _ hSize],
      hPointsTo⟩

/-- Release `n` possibly uninitialized values from `q` on. -/
def freeUninitRange [ByteRepr T] {M} (q : RawPtr T M) (n : Nat) : Result Unit :=
  Result.guardedModify (fun h => (h.readCells q.loc (n * ByteRepr.size T)).isSome)
    fun h _ => ((), h.freeBytes q.loc (n * ByteRepr.size T))

@[step]
theorem freeUninitRange.spec [ByteRepr T] {M} (q : RawPtr T M) (ms : List (MaybeUninit T)) :
    ⦃ q ↦?* ms ⦄ q.freeUninitRange ms.length ⦃⇓ emp⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := pointsToUninitRange_owns q ms h hPointsTo
  have hSub : Heap.Sub (Heap.cells q.loc (ms.flatMap MaybeUninit.cells))
      ((Heap.cells q.loc (ms.flatMap MaybeUninit.cells) ∪ rest) ∪ frame) :=
    Heap.Sub.trans (Heap.Sub.union_left hCompatibleRest) (Heap.Sub.union_left hCompatible)
  have hRead := Heap.readCells_of_sub hSub
  rw [MaybeUninit.length_flatMap_cells] at hRead
  obtain ⟨hRestFrame, hCellsRestFrame⟩ :=
    (PartialCommMonoid.compatible_assoc _ rest frame).mp ⟨hCompatibleRest, hCompatible⟩
  refine ⟨by simp [hRead], rest, hRestFrame, ?_, trivial⟩
  change Heap.freeBytes _ q.loc _ = _
  rw [PartialCommMonoid.union_assoc hCompatibleRest hCompatible,
    ← MaybeUninit.length_flatMap_cells, Heap.freeBytes_cells_union hCellsRestFrame]

/-- Overwrite the possibly uninitialized values from `q` on with `ms`. -/
def writeUninitRange [ByteRepr T] {M} (q : RawPtr T M) (ms : List (MaybeUninit T)) :
    Result Unit :=
  Result.guardedModify (fun h => (h.readCells q.loc (ms.length * ByteRepr.size T)).isSome)
    fun h _ => ((), h.writeCells q.loc (ms.flatMap MaybeUninit.cells))

@[step]
theorem writeUninitRange.spec [ByteRepr T] {M} (q : RawPtr T M)
    (old ms : List (MaybeUninit T)) (hLength : old.length = ms.length) :
    ⦃ q ↦?* old ⦄ q.writeUninitRange ms ⦃⇓ q ↦?* ms⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hAlign : ms ≠ [] → q.Aligned := fun hMs =>
    aligned_of_pointsToUninitRange hPointsTo (by
      intro hOld; subst hOld; exact hMs (List.eq_nil_of_length_eq_zero hLength.symm))
  obtain ⟨rest, hCompatibleRest, rfl⟩ := pointsToUninitRange_owns q old h hPointsTo
  have hSub : Heap.Sub (Heap.cells q.loc (old.flatMap MaybeUninit.cells))
      ((Heap.cells q.loc (old.flatMap MaybeUninit.cells) ∪ rest) ∪ frame) :=
    Heap.Sub.trans (Heap.Sub.union_left hCompatibleRest) (Heap.Sub.union_left hCompatible)
  have hRead := Heap.readCells_of_sub hSub
  rw [MaybeUninit.length_flatMap_cells, hLength] at hRead
  have hCellsLength : (ms.flatMap MaybeUninit.cells).length =
      (old.flatMap MaybeUninit.cells).length := by
    rw [MaybeUninit.length_flatMap_cells, MaybeUninit.length_flatMap_cells, hLength]
  obtain ⟨hRestFrame, hOldRestFrame⟩ :=
    (PartialCommMonoid.compatible_assoc _ rest frame).mp ⟨hCompatibleRest, hCompatible⟩
  obtain ⟨hNewRest, hNewFrame⟩ :=
    (PartialCommMonoid.compatible_assoc (Heap.cells q.loc (ms.flatMap MaybeUninit.cells))
      rest frame).mpr
      ⟨hRestFrame, Heap.compatible_cells_of_length_eq hCellsLength hOldRestFrame⟩
  refine ⟨by simp [hRead], Heap.cells q.loc (ms.flatMap MaybeUninit.cells) ∪ rest,
    hNewFrame, ?_, pointsToUninitRange_of_owns q ms hAlign _ (Heap.Sub.union_left hNewRest)⟩
  change Heap.writeCells _ q.loc _ = _
  rw [PartialCommMonoid.union_assoc hCompatibleRest hCompatible,
    Heap.writeCells_cells_union _ hCellsLength,
    PartialCommMonoid.union_assoc hNewRest hNewFrame]

end RawPtr

/-! ## Converting values of type `MaybeUninit T` to raw pointers -/

namespace MaybeUninit

/-- `MaybeUninit::as_mut_ptr`: the value is copied into fresh memory, which is
uninitialized if the value is. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_mut_ptr"]
def as_mut_ptr [ByteRepr T] (m : MaybeUninit T) : Result (MutRawPtr T) :=
  RawPtr.allocUninit (ByteRepr.align T) [m] id

@[step]
theorem as_mut_ptr.spec [ByteRepr T] (m : MaybeUninit T) :
    ⦃ emp ⦄ as_mut_ptr m ⦃⇓ p => p ↦? m⦄ :=
  RawPtr.allocUninit.spec _ _ _ _ fun _ h hq =>
    (sep_emp_r _).mp h ((sep_pure_l _ _ h).mp hq).2

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_ptr"]
def as_ptr [ByteRepr T] (m : MaybeUninit T) : Result (ConstRawPtr T) :=
  RawPtr.allocUninit (ByteRepr.align T) [m] fun q => q.retype

@[step]
theorem as_ptr.spec [ByteRepr T] (m : MaybeUninit T) :
    ⦃ emp ⦄ as_ptr m ⦃⇓ p => p ↦? m⦄ :=
  RawPtr.allocUninit.spec _ _ _ _ fun _ h hq =>
    (sep_emp_r _).mp h ((sep_pure_l _ _ h).mp hq).2

/-- End a raw pointer obtained with `MaybeUninit.as_mut_ptr`: read the value
back and free the memory. -/
def end_as_mut_ptr [ByteRepr T] (_m : MaybeUninit T) (p : MutRawPtr T) :
    Result (MaybeUninit T) := do
  let ms ← p.readUninitRange 1
  p.freeUninitRange 1
  ok ms.head!

@[step]
theorem end_as_mut_ptr.spec [ByteRepr T] (m m' : MaybeUninit T) (p : MutRawPtr T)
    (hSize : 0 < ByteRepr.size T) :
    ⦃ p ↦? m' ⦄ end_as_mut_ptr m p ⦃⇓ r => ⌜r = m'⌝⦄ := by
  unfold end_as_mut_ptr
  have hRange : (p ↦? m') = (p ↦?* [m']) := by
    rw [RawPtr.pointsToUninitRange_cons, RawPtr.pointsToUninitRange_nil,
      bientails_eq (sep_emp_r _)]
  rw [hRange]
  apply WP.ispec_bind (RawPtr.readUninitRange.spec p [m'] hSize) (sep_emp_r _).mpr
  intro r
  rw [sep_emp_r_eq]
  apply WP.ispec_ipure.mpr
  intro hr
  subst hr
  apply WP.ispec_bind (RawPtr.freeUninitRange.spec p [m']) (sep_emp_r _).mpr
  intro _
  rw [sep_emp_r_eq]
  exact (ispec_ok _).2 ((entails_emp_ipure_iff _).mpr rfl)

theorem end_as_mut_ptr.spec_init [ByteRepr T] (m : MaybeUninit T) (p : MutRawPtr T) (v : T)
    (hSize : 0 < ByteRepr.size T) :
    ⦃ p ↦ v ⦄ end_as_mut_ptr m p ⦃⇓ r => ⌜r = .init v⌝⦄ := by
  have := end_as_mut_ptr.spec m (.init v) p hSize
  rwa [RawPtr.pointsToUninit_init] at this

@[simp] theorem assume_init_init (v : T) :
    core.mem.maybe_uninit.MaybeUninit.assume_init (.init v) = ok v := rfl

@[simp] theorem assume_init_uninit :
    core.mem.maybe_uninit.MaybeUninit.assume_init (.uninit : MaybeUninit T) = fail .undef := rfl

/-- End a raw pointer obtained with `MaybeUninit.as_ptr`: free the memory. -/
def end_as_ptr [ByteRepr T] (_m : MaybeUninit T) (p : ConstRawPtr T) : Result Unit :=
  p.freeUninitRange 1

@[step]
theorem end_as_ptr.spec [ByteRepr T] (m m' : MaybeUninit T) (p : ConstRawPtr T) :
    ⦃ p ↦? m' ⦄ end_as_ptr m p ⦃⇓ emp⦄ := by
  unfold end_as_ptr
  have hRange : (p ↦? m') = (p ↦?* [m']) := by
    rw [RawPtr.pointsToUninitRange_cons, RawPtr.pointsToUninitRange_nil,
      bientails_eq (sep_emp_r _)]
  rw [hRange]
  exact RawPtr.freeUninitRange.spec p [m']

end MaybeUninit

/-! ## Converting slices of values of type `MaybeUninit T` to raw pointers -/

namespace Slice

/-- `as_mut_ptr` on a slice of values of type `MaybeUninit T`. -/
def as_mut_ptr_uninit [ByteRepr T] (s : Slice (MaybeUninit T)) :
    Result (MutRawPtr (MaybeUninit T)) :=
  RawPtr.allocUninit (ByteRepr.align T) s.val fun q => q.retype

@[step]
theorem as_mut_ptr_uninit.spec [ByteRepr T] (s : Slice (MaybeUninit T)) :
    ⦃ emp ⦄ as_mut_ptr_uninit s ⦃⇓ p => (p.retype : MutRawPtr T) ↦?* s.val⦄ :=
  RawPtr.allocUninit.spec _ _ _ _ fun _ h hq => ((sep_pure_l _ _ h).mp hq).2

def as_ptr_uninit [ByteRepr T] (s : Slice (MaybeUninit T)) :
    Result (ConstRawPtr (MaybeUninit T)) :=
  RawPtr.allocUninit (ByteRepr.align T) s.val fun q => q.retype

@[step]
theorem as_ptr_uninit.spec [ByteRepr T] (s : Slice (MaybeUninit T)) :
    ⦃ emp ⦄ as_ptr_uninit s ⦃⇓ p => (p.retype : MutRawPtr T) ↦?* s.val⦄ :=
  RawPtr.allocUninit.spec _ _ _ _ fun _ h hq => ((sep_pure_l _ _ h).mp hq).2

/-- Read back the slice converted to a raw pointer with
`Slice.as_mut_ptr_uninit`, but keep the memory (see `Slice.sync_as_mut_ptr`). -/
def sync_as_mut_ptr_uninit [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : MutRawPtr (MaybeUninit T)) : Result (Slice (MaybeUninit T)) := do
  let ms ← (p.retype : MutRawPtr T).readUninitRange s.length
  ok (s.setSlice! 0 ms)

@[step]
theorem sync_as_mut_ptr_uninit.spec [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : MutRawPtr (MaybeUninit T)) (ms : List (MaybeUninit T))
    (hLength : ms.length = s.length) (hSize : 0 < ByteRepr.size T) :
    ⦃ (p.retype : MutRawPtr T) ↦?* ms ⦄ sync_as_mut_ptr_uninit s p
      ⦃⇓ r => ⌜r.val = ms⌝ ∗ (p.retype : MutRawPtr T) ↦?* ms⦄ := by
  unfold sync_as_mut_ptr_uninit
  have := RawPtr.readUninitRange.spec (p.retype : MutRawPtr T) ms hSize
  rw [hLength] at this
  apply WP.ispec_bind this (sep_emp_r _).mpr
  intro r
  rw [sep_emp_r_eq]
  apply WP.ispec_ipure.mpr
  intro hr
  subst r
  apply (ispec_ok _).2
  have hSet : s.val.setSlice! 0 ms = ms := by
    apply List.ext_getElem <;> simp_all [List.setSlice!]
  simp only [Slice.setSlice!_val, hSet]
  exact pure_sep_intro _ trivial

/-- End a raw pointer obtained with `Slice.as_mut_ptr_uninit`: read the slice
back and free the memory. -/
def end_as_mut_ptr_uninit [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : MutRawPtr (MaybeUninit T)) : Result (Slice (MaybeUninit T)) := do
  let s' ← sync_as_mut_ptr_uninit s p
  (p.retype : MutRawPtr T).freeUninitRange s.length
  ok s'

@[step]
theorem end_as_mut_ptr_uninit.spec [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : MutRawPtr (MaybeUninit T)) (ms : List (MaybeUninit T))
    (hLength : ms.length = s.length) (hSize : 0 < ByteRepr.size T) :
    ⦃ (p.retype : MutRawPtr T) ↦?* ms ⦄ end_as_mut_ptr_uninit s p
      ⦃⇓ r => ⌜r.val = ms⌝⦄ := by
  unfold end_as_mut_ptr_uninit
  apply WP.ispec_bind (sync_as_mut_ptr_uninit.spec s p ms hLength hSize) (sep_emp_r _).mpr
  intro r
  rw [sep_emp_r_eq]
  apply WP.ispec_ipure.mpr
  intro hr
  have := RawPtr.freeUninitRange.spec (p.retype : MutRawPtr T) ms
  rw [hLength] at this
  apply WP.ispec_bind this (sep_emp_r _).mpr
  intro _
  rw [sep_emp_r_eq]
  exact (ispec_ok _).2 ((entails_emp_ipure_iff _).mpr hr)

/-- End a raw pointer obtained with `Slice.as_ptr_uninit`: free the memory. -/
def end_as_ptr_uninit [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : ConstRawPtr (MaybeUninit T)) : Result Unit :=
  (p.retype : ConstRawPtr T).freeUninitRange s.length

@[step]
theorem end_as_ptr_uninit.spec [ByteRepr T] (s : Slice (MaybeUninit T))
    (p : ConstRawPtr (MaybeUninit T)) :
    ⦃ (p.retype : MutRawPtr T) ↦?* s.val ⦄ end_as_ptr_uninit s p ⦃⇓ emp⦄ := by
  unfold end_as_ptr_uninit
  have := RawPtr.freeUninitRange.spec (p.retype : ConstRawPtr T) s.val
  have h2 := RawPtr.pointsToUninitRange_retype_eq (M' := .Mut) (p.retype : ConstRawPtr T) s.val
  simp only [RawPtr.retype_retype] at h2
  rw [h2]
  exact this

/-- Free the memory of a raw pointer obtained by converting a slice of values
of type `MaybeUninit T` (see `Slice.free_as_ptr`). -/
def free_as_ptr_uninit [ByteRepr T] {M} (s : Slice (MaybeUninit T))
    (p : RawPtr (MaybeUninit T) M) : Result Unit :=
  (p.retype : MutRawPtr T).freeUninitRange s.length

@[step]
theorem free_as_ptr_uninit.spec [ByteRepr T] {M} (s : Slice (MaybeUninit T))
    (p : RawPtr (MaybeUninit T) M) :
    ⦃ (p.retype : MutRawPtr T) ↦?* s.val ⦄ free_as_ptr_uninit s p ⦃⇓ emp⦄ :=
  RawPtr.freeUninitRange.spec (p.retype : MutRawPtr T) s.val

/-- Convert a slice of values of type `MaybeUninit T` to a raw pointer, reusing
the memory of a previous raw pointer to the same place (see
`Slice.as_ptr_reuse`). -/
def as_raw_ptr_reuse_uninit [ByteRepr T] {M M'} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) : Result (RawPtr (MaybeUninit T) M') := do
  (p.retype : MutRawPtr T).writeUninitRange s.val
  ok p.retype

theorem as_raw_ptr_reuse_uninit.spec [ByteRepr T] {M M'} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) (old : List (MaybeUninit T)) (hLength : old.length = s.length) :
    ⦃ (p.retype : MutRawPtr T) ↦?* old ⦄
      (as_raw_ptr_reuse_uninit p s : Result (RawPtr (MaybeUninit T) M'))
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ (p.retype : MutRawPtr T) ↦?* s.val⦄ := by
  unfold as_raw_ptr_reuse_uninit
  apply WP.ispec_bind (RawPtr.writeUninitRange.spec (p.retype : MutRawPtr T) old s.val hLength)
    (sep_emp_r _).mpr
  intro _
  rw [sep_emp_r_eq]
  exact (ispec_ok _).2 (pure_sep_intro _ rfl)

def as_ptr_reuse_uninit [ByteRepr T] {M} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) : Result (ConstRawPtr (MaybeUninit T)) :=
  as_raw_ptr_reuse_uninit p s

@[step]
theorem as_ptr_reuse_uninit.spec [ByteRepr T] {M} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) (old : List (MaybeUninit T)) (hLength : old.length = s.length) :
    ⦃ (p.retype : MutRawPtr T) ↦?* old ⦄ as_ptr_reuse_uninit p s
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ (p.retype : MutRawPtr T) ↦?* s.val⦄ :=
  as_raw_ptr_reuse_uninit.spec p s old hLength

def as_mut_ptr_reuse_uninit [ByteRepr T] {M} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) : Result (MutRawPtr (MaybeUninit T)) :=
  as_raw_ptr_reuse_uninit p s

@[step]
theorem as_mut_ptr_reuse_uninit.spec [ByteRepr T] {M} (p : RawPtr (MaybeUninit T) M)
    (s : Slice (MaybeUninit T)) (old : List (MaybeUninit T)) (hLength : old.length = s.length) :
    ⦃ (p.retype : MutRawPtr T) ↦?* old ⦄ as_mut_ptr_reuse_uninit p s
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ (p.retype : MutRawPtr T) ↦?* s.val⦄ :=
  as_raw_ptr_reuse_uninit.spec p s old hLength

end Slice

/-! ## Traits -/

@[rust_fun
  "core::mem::maybe_uninit::{core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>}::clone"]
def core.mem.maybe_uninit.MaybeUninit.Insts.CoreCloneClone.clone {T : Type}
    (_markerCopyInst : core.marker.Copy T) (x : MaybeUninit T) : Result (MaybeUninit T) :=
  ok x

@[reducible, rust_trait_impl "core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.mem.maybe_uninit.MaybeUninit.Insts.CoreCloneClone {T : Type}
    (markerCopyInst : core.marker.Copy T) : core.clone.Clone (MaybeUninit T) where
  clone := core.mem.maybe_uninit.MaybeUninit.Insts.CoreCloneClone.clone markerCopyInst

@[reducible, rust_trait_impl "core::marker::Copy<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.mem.maybe_uninit.MaybeUninit.Insts.CoreMarkerCopy {T : Type}
    (markerCopyInst : core.marker.Copy T) : core.marker.Copy (MaybeUninit T) where
  cloneInst := core.mem.maybe_uninit.MaybeUninit.Insts.CoreCloneClone markerCopyInst

end Aeneas.Std
