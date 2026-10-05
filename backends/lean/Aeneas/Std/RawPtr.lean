module
public import Aeneas.Std.Delab
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.Scalar.ByteRepr
public import Aeneas.Std.SliceDef
public import Aeneas.Data.BitVec
public import Aeneas.Std.WP
public import Aeneas.Std.Primitives
public import Aeneas.SepLogic
public import Aeneas.Tactic.SepLogic.IFrame
public import Aeneas.Tactic.SepLogic.IIntro
public import Aeneas.Tactic.Step.Init
@[expose] public section

/-!
# Raw pointers

`RawPtr T M` is a Rust raw pointer: a base allocation identifier and a byte
offset into that allocation. The mutability index distinguishes `*mut T` from
`*const T`; permissions are carried by separation-logic assertions rather than
by the pointer value.

The element type must have a byte representation (`ByteRepr T`):

* `q ↦ value` says that `q` is aligned for `T` and owns the bytes from `q` on
  that encode `value`;
* `q ↦* values` owns the consecutive elements starting at `q`.

Since ownership is of bytes, the type a pointer views its bytes at is a
matter of specification only: `RawPtr.cast_scalar` is the identity on
addresses.  Its `step` specification only records the address; the optional
ones reinterpret the bytes it owns, provided the address is aligned for the new
type.  Reads and writes are only defined at aligned addresses.

Reads accept both mutable and const pointers. Allocation, writes and
deallocation require a mutable pointer.
-/

open Aeneas
open Aeneas.SepLogic

namespace Aeneas.Std

open WP

inductive Mutability where
| Mut | Const

/-- A raw pointer into a heap allocation. -/
structure RawPtr (T : Type) (M : Mutability) where
  base : AllocId
  offset : Nat
  deriving Inhabited, DecidableEq

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

namespace RawPtr

/-- The byte address of a raw pointer. -/
def loc (q : RawPtr T M) : Loc := (q.base, q.offset)

/-- The heap reference addressed by a raw pointer. -/
def ref (q : RawPtr T M) : Ref T := q.loc

/-- Pointer arithmetic within the same allocation, in elements. -/
def add [ByteRepr T] (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i * ByteRepr.size T⟩

/-- Whether two pointers are interior to the same allocation. -/
def sameBase (q₁ : RawPtr T M₁) (q₂ : RawPtr U M₂) : Prop :=
  q₁.base = q₂.base

/-- How many bytes `q₂` is past `q₁`. -/
def distance (q₁ : RawPtr T M₁) (q₂ : RawPtr U M₂) : Nat :=
  q₂.offset - q₁.offset

/-- Forget write capability while preserving the address. -/
def toConst (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.base, q.offset⟩

def toMut (q : ConstRawPtr T) : MutRawPtr T :=
  ⟨q.base, q.offset⟩

/-- The same address, viewed at another element type and mutability. -/
def retype (q : RawPtr T M) : RawPtr U M' :=
  ⟨q.base, q.offset⟩

/-- Whether the address of `q` is a multiple of the alignment of `T`: the
alignment of `T` divides both the alignment of the allocation, which is that of
the type it was allocated at, and the offset into it. -/
def Aligned [ByteRepr T] (q : RawPtr T M) : Prop :=
  ByteRepr.align T ∣ q.base.align ∧ ByteRepr.align T ∣ q.offset

@[simp] theorem base_add [ByteRepr T] (q : RawPtr T M) (i : Nat) :
    (q.add i).base = q.base := rfl

@[simp] theorem offset_add [ByteRepr T] (q : RawPtr T M) (i : Nat) :
    (q.add i).offset = q.offset + i * ByteRepr.size T := rfl

@[simp] theorem add_zero [ByteRepr T] (q : RawPtr T M) : q.add 0 = q := by
  simp [add]

@[simp] theorem base_toConst (q : MutRawPtr T) : q.toConst.base = q.base := rfl

@[simp] theorem offset_toConst (q : MutRawPtr T) : q.toConst.offset = q.offset := rfl

@[simp] theorem ref_toConst (q : MutRawPtr T) : q.toConst.ref = q.ref := rfl

@[simp] theorem loc_toConst (q : MutRawPtr T) : q.toConst.loc = q.loc := rfl

@[simp] theorem base_toMut (q : ConstRawPtr T) : q.toMut.base = q.base := rfl

@[simp] theorem offset_toMut (q : ConstRawPtr T) : q.toMut.offset = q.offset := rfl

@[simp] theorem ref_toMut (q : ConstRawPtr T) : q.toMut.ref = q.ref := rfl

@[simp] theorem loc_toMut (q : ConstRawPtr T) : q.toMut.loc = q.loc := rfl

@[simp] theorem toMut_toConst (q : MutRawPtr T) : q.toConst.toMut = q := rfl

@[simp] theorem toConst_toMut (q : ConstRawPtr T) : q.toMut.toConst = q := rfl

@[simp] theorem aligned_toMut [ByteRepr T] (q : ConstRawPtr T) :
    q.toMut.Aligned ↔ q.Aligned := Iff.rfl

@[simp] theorem base_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').base = q.base := rfl

@[simp] theorem offset_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').offset = q.offset := rfl

@[simp] theorem loc_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').loc = q.loc := rfl

@[simp] theorem retype_retype (q : RawPtr T M) :
    ((q.retype : RawPtr U M').retype : RawPtr V M'') = q.retype := rfl

@[simp] theorem retype_self (q : RawPtr T M) : (q.retype : RawPtr T M) = q := rfl

theorem loc_add [ByteRepr T] (q : RawPtr T M) (i : Nat) :
    (q.add i).loc = q.loc.add (i * ByteRepr.size T) := rfl

theorem ref_add [ByteRepr T] (q : RawPtr T M) (i : Nat) :
    (q.add i).ref = q.ref.add (i * ByteRepr.size T) := rfl

theorem add_add [ByteRepr T] (q : RawPtr T M) (i j : Nat) :
    (q.add i).add j = q.add (i + j) := by
  simp [add, Nat.add_mul, Nat.add_assoc]

@[simp] theorem aligned_add [ByteRepr T] (q : RawPtr T M) (i : Nat) :
    (q.add i).Aligned ↔ q.Aligned :=
  and_congr Iff.rfl
    (Nat.dvd_add_left (Nat.dvd_trans ByteRepr.align_dvd_size (Nat.dvd_mul_left _ i)))

@[simp] theorem aligned_toConst [ByteRepr T] (q : MutRawPtr T) :
    q.toConst.Aligned ↔ q.Aligned := Iff.rfl

@[simp] theorem aligned_retype_self [ByteRepr T] (q : RawPtr T M) :
    (q.retype : RawPtr T M').Aligned ↔ q.Aligned := Iff.rfl

theorem aligned_retype_of_dvd [ByteRepr T] [ByteRepr T'] {q : RawPtr T M}
    (hAlign : ByteRepr.align T' ∣ ByteRepr.align T) (hAligned : q.Aligned) :
    (q.retype : RawPtr T' M').Aligned :=
  ⟨Nat.dvd_trans hAlign hAligned.1, Nat.dvd_trans hAlign hAligned.2⟩

/-- `q` is aligned and owns the bytes encoding `value` from the address it
holds on. -/
def pointsTo [ByteRepr T] (q : RawPtr T M) (value : T) : IProp :=
  iprop(⌜q.Aligned⌝ ∗ Ref.pointsTo q.ref value)

end RawPtr

instance instPointsToRawPtr {T : Type} {M : Mutability} [ByteRepr T] :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

namespace RawPtr

/-- `q` owns the `values.length` consecutive elements from `q` on. -/
def pointsToRange [ByteRepr T] (q : RawPtr T M) : List T → IProp
  | [] => emp
  | value :: rest => iprop(q ↦ value ∗ pointsToRange (q.add 1) rest)

end RawPtr

@[inherit_doc RawPtr.pointsToRange]
notation:50 q:50 " ↦* " values:50 => RawPtr.pointsToRange q values

theorem RawPtr.pointsTo_eq_ref [ByteRepr T] (q : RawPtr T M) (value : T) :
    (q ↦ value) = iprop(⌜q.Aligned⌝ ∗ Ref.pointsTo q.ref value) := rfl

theorem RawPtr.pointsTo_eq_owns [ByteRepr T] (q : RawPtr T M) (value : T) :
    (q ↦ value) = iprop(⌜q.Aligned⌝ ∗ owns (Heap.bytes q.loc (ByteRepr.encode value))) :=
  rfl

theorem RawPtr.pointsTo_holds [ByteRepr T] (q : RawPtr T M) (value : T) (h : Heap) :
    (q ↦ value) h ↔ q.Aligned ∧ Heap.Sub (Heap.bytes q.loc (ByteRepr.encode value)) h :=
  sep_pure_l _ _ h

theorem RawPtr.aligned_of_pointsTo [ByteRepr T] {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Aligned :=
  ((RawPtr.pointsTo_holds q value h).mp hPointsTo).1

theorem RawPtr.pointsTo_aligned [ByteRepr T] (q : RawPtr T M) (value : T) :
    q ↦ value ⊢ ⌜q.Aligned⌝ ∗ q ↦ value :=
  fun h hPointsTo => (sep_pure_l _ _ h).mpr ⟨RawPtr.aligned_of_pointsTo hPointsTo, hPointsTo⟩

theorem RawPtr.pointsTo_eq_owns_of_aligned [ByteRepr T] {q : RawPtr T M} (value : T)
    (hAlign : q.Aligned) :
    (q ↦ value) = owns (Heap.bytes q.loc (ByteRepr.encode value)) :=
  bientails_eq ⟨fun h hPointsTo => ((RawPtr.pointsTo_holds q value h).mp hPointsTo).2,
    fun h hOwns => (RawPtr.pointsTo_holds q value h).mpr ⟨hAlign, hOwns⟩⟩

theorem RawPtr.pointsTo_eq_range [ByteRepr T] (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) :=
  (sep_emp_r_eq _).symm

@[simp] theorem RawPtr.pointsTo_toConst [ByteRepr T] (q : MutRawPtr T) (value : T) :
    (q.toConst ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsTo_toMut [ByteRepr T] (q : ConstRawPtr T) (value : T) :
    (q.toMut ↦ value) = (q ↦ value) := rfl

private theorem owns_empty_eq : owns Heap.empty = emp :=
  bientails_eq ⟨fun _ _ => trivial, fun h _ => Heap.Sub.of_empty h⟩

namespace RawPtr

private theorem loc_add_size [ByteRepr T] (q : RawPtr T M) :
    q.loc.add (ByteRepr.size T) = (q.add 1).loc := by
  rw [loc_add, Nat.one_mul]

/-- An aligned range owns the concatenated encodings of its values. -/
theorem pointsToRange_eq_owns [ByteRepr T] (q : RawPtr T M) (values : List T)
    (hAlign : q.Aligned) :
    (q ↦* values) = owns (Heap.bytes q.loc (values.flatMap ByteRepr.encode)) := by
  induction values generalizing q with
  | nil =>
      rw [List.flatMap_nil, Heap.bytes_nil, owns_empty_eq]
      rfl
  | cons value rest ih =>
      change iprop(q ↦ value ∗ (q.add 1) ↦* rest) = _
      rw [pointsTo_eq_owns_of_aligned value hAlign, ih _ ((aligned_add q 1).mpr hAlign),
        List.flatMap_cons, Heap.bytes_append,
        bientails_eq (owns_union _ _ (Heap.compatible_bytes_append _ _ _)),
        ByteRepr.length_encode, loc_add_size]

/-- A range owns the concatenated encodings of its values. -/
theorem pointsToRange_owns [ByteRepr T] (q : RawPtr T M) (values : List T) :
    q ↦* values ⊢ owns (Heap.bytes q.loc (values.flatMap ByteRepr.encode)) := by
  induction values generalizing q with
  | nil =>
      rw [List.flatMap_nil, Heap.bytes_nil, owns_empty_eq]
      exact entails_refl _
  | cons value rest ih =>
      change iprop(q ↦ value ∗ (q.add 1) ↦* rest) ⊢ _
      rw [List.flatMap_cons, Heap.bytes_append,
        bientails_eq (owns_union _ _ (Heap.compatible_bytes_append _ _ _)),
        ByteRepr.length_encode, loc_add_size]
      exact sep_mono (fun h hPointsTo => ((pointsTo_holds q value h).mp hPointsTo).2) (ih _)

theorem aligned_of_pointsToRange [ByteRepr T] {q : RawPtr T M} {values : List T} {h : Heap}
    (hPointsTo : (q ↦* values) h) (hValues : values ≠ []) : q.Aligned := by
  cases values with
  | nil => exact absurd rfl hValues
  | cons value rest =>
      obtain ⟨_, _, _, _, hFirst, -⟩ := hPointsTo
      exact aligned_of_pointsTo hFirst

theorem pointsToRange_aligned [ByteRepr T] (q : RawPtr T M) (values : List T) :
    q ↦* values ⊢ ⌜values ≠ [] → q.Aligned⌝ ∗ q ↦* values :=
  fun h hPointsTo => (sep_pure_l _ _ h).mpr ⟨aligned_of_pointsToRange hPointsTo, hPointsTo⟩

theorem pointsToRange_retype_eq [ByteRepr T] (q : RawPtr T M) (values : List T) :
    ((q.retype : RawPtr T M') ↦* values) = (q ↦* values) := by
  induction values generalizing q with
  | nil => rfl
  | cons value rest ih =>
      change iprop(q ↦ value ∗ ((q.add 1).retype : RawPtr T M') ↦* rest) =
        iprop(q ↦ value ∗ (q.add 1) ↦* rest)
      rw [ih]

@[simp] theorem pointsToRange_toConst [ByteRepr T] (q : MutRawPtr T) (values : List T) :
    (q.toConst ↦* values) = (q ↦* values) :=
  pointsToRange_retype_eq q values

@[simp] theorem pointsToRange_toMut [ByteRepr T] (q : ConstRawPtr T) (values : List T) :
    (q.toMut ↦* values) = (q ↦* values) :=
  pointsToRange_retype_eq q values

theorem pointsToRange_append [ByteRepr T] (q : RawPtr T M) (xs ys : List T) :
    q ↦* (xs ++ ys) ⊣⊢ q ↦* xs ∗ (q.add xs.length) ↦* ys := by
  induction xs generalizing q with
  | nil =>
      rw [List.nil_append, List.length_nil, add_zero]
      exact ⟨(sep_emp_l _).mpr, (sep_emp_l _).mp⟩
  | cons x xs ih =>
      change iprop(q ↦ x ∗ (q.add 1) ↦* (xs ++ ys)) ⊣⊢
        iprop((q ↦ x ∗ (q.add 1) ↦* xs) ∗ (q.add (xs.length + 1)) ↦* ys)
      rw [show q.add (xs.length + 1) = (q.add 1).add xs.length by
          rw [add_add, Nat.add_comm],
        bientails_eq (ih (q.add 1)), sep_assoc_eq]
      exact ⟨entails_refl _, entails_refl _⟩

theorem pointsToRange_split [ByteRepr T] (q : RawPtr T M) (values : List T) (i : Nat) :
    q ↦* values ⊣⊢
      q ↦* values.take i ∗ (q.add (values.take i).length) ↦* values.drop i := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

theorem pointsToRange_cons [ByteRepr T] (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.add 1) ↦* rest) := rfl

theorem pointsToRange_eq_take_get_drop [ByteRepr T] {q : RawPtr T M} {values : List T}
    {i : Nat} (hIndex : i < values.length) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗
        ((q.add i) ↦ values[i] ∗ (q.add (i + 1)) ↦* values.drop (i + 1))) := by
  have hTake : (values.take i).length = i := by simp; omega
  have hSplit := bientails_eq (pointsToRange_split q values i)
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex, pointsToRange_cons, add_add]

@[simp] theorem pointsToRange_nil [ByteRepr T] (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp := rfl

/-! ## Changing the view of owned bytes

Ownership is of bytes, so owning bytes at one type is owning them at any type
whose values encode to the same bytes, at an address aligned for that type. -/

theorem pointsToRange_retype [ByteRepr T] [ByteRepr U] (q : RawPtr T M)
    (xs : List T) (ys : List U)
    (hBytes : xs.flatMap ByteRepr.encode = ys.flatMap ByteRepr.encode)
    (hAlign : ys ≠ [] → (q.retype : RawPtr U M').Aligned) :
    q ↦* xs ⊢ (q.retype : RawPtr U M') ↦* ys := by
  intro h hPointsTo
  cases ys with
  | nil => trivial
  | cons y rest =>
      rw [pointsToRange_eq_owns _ _ (hAlign (List.cons_ne_nil _ _)), ← hBytes, loc_retype]
      exact pointsToRange_owns q xs h hPointsTo

theorem pointsTo_retype [ByteRepr T] [ByteRepr U] (q : RawPtr T M) (x : T) (y : U)
    (hBytes : ByteRepr.encode x = ByteRepr.encode y)
    (hAlign : (q.retype : RawPtr U M').Aligned) :
    q ↦ x ⊢ (q.retype : RawPtr U M') ↦ y := by
  intro h hPointsTo
  rw [pointsTo_eq_owns_of_aligned y hAlign, ← hBytes, loc_retype]
  exact ((pointsTo_holds q x h).mp hPointsTo).2

theorem pointsTo_retype_of_decode [ByteRepr T] [ByteRepr U] (q : RawPtr T M)
    (x : T) (y : U) (hDecode : ByteRepr.decode (ByteRepr.encode x) = some y)
    (hAlign : (q.retype : RawPtr U M').Aligned) :
    q ↦ x ⊢ (q.retype : RawPtr U M') ↦ y :=
  pointsTo_retype q x y (ByteRepr.encode_of_decode hDecode).symm hAlign

end RawPtr

theorem RawPtr.pointsTo_exclusive [ByteRepr T] (q : RawPtr T M) (value₁ value₂ : T)
    (hSize : 0 < ByteRepr.size T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ :=
  entails_trans
    (sep_mono (fun h hPointsTo => ((RawPtr.pointsTo_holds q value₁ h).mp hPointsTo).2)
      (fun h hPointsTo => ((RawPtr.pointsTo_holds q value₂ h).mp hPointsTo).2))
    (Ref.pointsTo_exclusive q.ref value₁ value₂ hSize)

namespace RawPtr

/-- The heap containing only the bytes `q ↦ value` owns. -/
def singleton [ByteRepr T] (q : RawPtr T M) (value : T) : Heap :=
  Heap.bytes q.loc (ByteRepr.encode value)

/-- The value of type `T` the bytes of `h` at `q` decode to, if any. -/
def readValue? [ByteRepr T] (h : Heap) (q : RawPtr T M) : Option T :=
  (h.readBytes q.loc (ByteRepr.size T)).bind ByteRepr.decode

/-- Whether `h` holds a value of the pointer's element type at `q`. -/
def contains [ByteRepr T] (h : Heap) (q : RawPtr T M) : Prop :=
  (readValue? h q).isSome

theorem readValue?_of_pointsTo [ByteRepr T] {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : readValue? h q = some value := by
  have hRead := Heap.readBytes_of_sub ((pointsTo_holds q value h).mp hPointsTo).2
  rw [ByteRepr.length_encode] at hRead
  rw [readValue?, hRead, Option.bind_some, ByteRepr.decode_encode]

@[simp]
theorem not_contains_empty [ByteRepr T] (q : RawPtr T M)
    (hSize : 0 < ByteRepr.size T) : ¬ RawPtr.contains (∅ : Heap) q := by
  obtain ⟨n, hn⟩ : ∃ n, ByteRepr.size T = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hSize).symm⟩
  simp only [contains, readValue?, hn]
  rw [show (∅ : Heap) = Heap.empty from rfl, Heap.readBytes_empty_succ]
  simp

theorem contains_of_pointsTo [ByteRepr T] {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : RawPtr.contains h q := by
  simp [contains, readValue?_of_pointsTo hPointsTo]

theorem disjoint_singleton [ByteRepr T] {q r : RawPtr T M} {value₁ value₂ : T}
    (hNe : q.base ≠ r.base) :
    PartialCommMonoid.Compatible (q.singleton value₁) (r.singleton value₂) := by
  exact Heap.compatible_bytes_of_fst_ne hNe

end RawPtr

/-- Allocate `values` consecutively and pass a pointer to the first one to `mk`. -/
def RawPtr.allocArray [ByteRepr T] {β : Type} (values : List T) (mk : MutRawPtr T → β) :
    Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (mk ⟨(Heap.freshLoc h (ByteRepr.align T)).1, (Heap.freshLoc h (ByteRepr.align T)).2⟩,
      Heap.bytes (Heap.freshLoc h (ByteRepr.align T)) (values.flatMap ByteRepr.encode) ∪ h)

@[step]
theorem RawPtr.allocArray.spec [ByteRepr T] {β : Type} (values : List T)
    (mk : MutRawPtr T → β) (post : β → IProp)
    (hPost : ∀ q : MutRawPtr T, q ↦* values ⊢ post (mk q)) :
    ⦃ emp ⦄ RawPtr.allocArray values mk ⦃⇓ result => post result⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.bytes (Heap.freshLoc (h ∪ frame) (ByteRepr.align T))
          (values.flatMap ByteRepr.encode))
        (h ∪ frame) :=
    Heap.compatible_fresh _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.bytes (Heap.freshLoc (h ∪ frame) (ByteRepr.align T))
        (values.flatMap ByteRepr.encode))
        h frame).mpr ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm, ?_⟩
  apply hPost
  rw [RawPtr.pointsToRange_eq_owns _ _ ⟨by simp, by simp⟩]
  exact Heap.Sub.union_left hFreshH

/-- Materialize a list as fresh memory with the requested pointer mutability. -/
def RawPtr.materialize [ByteRepr T] (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocArray values fun q => q.retype

@[step]
theorem RawPtr.materialize.spec [ByteRepr T] (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values
      ⦃⇓ p => p ↦* values⦄ :=
  RawPtr.allocArray.spec _ _ _ fun q => by
    rw [RawPtr.pointsToRange_retype_eq]
    exact entails_refl _

/-- Allocate one mutable slot. -/
def MutRawPtr.alloc [ByteRepr T] (value : T) : Result (MutRawPtr T) :=
  RawPtr.allocArray [value] id

@[step]
theorem MutRawPtr.alloc.spec [ByteRepr T] (value : T) :
    ⦃ emp ⦄ MutRawPtr.alloc value ⦃⇓ q => q ↦ value⦄ :=
  RawPtr.allocArray.spec _ _ _ fun _ => by
    rw [RawPtr.pointsTo_eq_range]
    exact entails_refl _

namespace RawPtr

structure Readable [ByteRepr T] (q : RawPtr T M) (h : Heap) : Prop where
  contains : RawPtr.contains h q
  aligned : q.Aligned

theorem readable_of_pointsTo [ByteRepr T] {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  ⟨contains_of_pointsTo hPointsTo, aligned_of_pointsTo hPointsTo⟩

/-- Read through either a mutable or const pointer: decode the bytes at an
aligned `q`. -/
def read [ByteRepr T] (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    ((readValue? h q).get hReadable.contains, h)

@[step]
theorem read.spec [ByteRepr T] (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃⇓ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  refine ⟨readable_of_pointsTo hPointsToFrame, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨by simp only [readValue?_of_pointsTo hPointsToFrame, Option.get_some], hPointsTo⟩

/-- Reads are only defined at aligned addresses: the precondition of any
specification of a read forces the address to be aligned. -/
theorem read.aligned_of_spec [ByteRepr T] {q : RawPtr T M} {P : IProp} {Q : T → IProp}
    (hSpec : ⦃ P ⦄ q.read ⦃⇓ result => Q result⦄) : P ⊢ ⌜q.Aligned⌝ := by
  intro h hP
  rw [ispec_iff] at hSpec
  exact (hSpec emp h ((sep_emp_r P).mpr h hP)).vis_view.1.aligned

end RawPtr

/-- Write through a mutable pointer: overwrite the bytes at an aligned `q`. -/
def MutRawPtr.write [ByteRepr T] (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => RawPtr.contains h q ∧ q.Aligned) fun h _ =>
    ((), h.writeBytes q.loc (ByteRepr.encode value))

theorem MutRawPtr.write.aligned_of_spec [ByteRepr T] {q : MutRawPtr T} {value : T}
    {P : IProp} {Q : Unit → IProp} (hSpec : ⦃ P ⦄ q.write value ⦃⇓ r => Q r⦄) :
    P ⊢ ⌜q.Aligned⌝ := by
  intro h hP
  rw [ispec_iff] at hSpec
  exact (hSpec emp h ((sep_emp_r P).mpr h hP)).vis_view.1.2

@[step]
theorem MutRawPtr.write.spec [ByteRepr T] (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃⇓ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : RawPtr.contains (h ∪ frame) q :=
    RawPtr.contains_of_pointsTo
      ((q ↦ oldValue).up_closed hPointsTo (Heap.Sub.union_left hCompatible))
  obtain ⟨hAlign, rest, hCompatibleRest, rfl⟩ :=
    (RawPtr.pointsTo_holds q oldValue h).mp hPointsTo
  have hLength : (ByteRepr.encode newValue).length = (ByteRepr.encode oldValue).length := by
    rw [ByteRepr.length_encode, ByteRepr.length_encode]
  obtain ⟨hRestFrame, hOldRestFrame⟩ :=
    (PartialCommMonoid.compatible_assoc _ rest frame).mp ⟨hCompatibleRest, hCompatible⟩
  obtain ⟨hNewRest, hNewFrame⟩ :=
    (PartialCommMonoid.compatible_assoc (Heap.bytes q.loc (ByteRepr.encode newValue))
      rest frame).mpr ⟨hRestFrame, Heap.compatible_bytes_of_length_eq hLength hOldRestFrame⟩
  refine ⟨⟨hContains, hAlign⟩, Heap.bytes q.loc (ByteRepr.encode newValue) ∪ rest,
    hNewFrame, ?_, (RawPtr.pointsTo_holds q newValue _).mpr
      ⟨hAlign, Heap.Sub.union_left hNewRest⟩⟩
  change Heap.writeBytes _ q.loc _ = _
  rw [Heap.writeBytes_union, Heap.writeBytes_bytes_union _ hLength]

/-- Release the bytes addressed by a mutable pointer. -/
def MutRawPtr.free [ByteRepr T] (q : MutRawPtr T) : Result Unit :=
  Result.guardedModify (fun h => RawPtr.contains h q) fun h _ =>
    ((), h.freeBytes q.loc (ByteRepr.size T))

@[step]
theorem MutRawPtr.free.spec [ByteRepr T] (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ q.free ⦃⇓ emp⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : RawPtr.contains (h ∪ frame) q :=
    RawPtr.contains_of_pointsTo
      ((q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible))
  obtain ⟨-, rest, hCompatibleRest, rfl⟩ := (RawPtr.pointsTo_holds q value h).mp hPointsTo
  obtain ⟨hRestFrame, hOldRestFrame⟩ :=
    (PartialCommMonoid.compatible_assoc _ rest frame).mp ⟨hCompatibleRest, hCompatible⟩
  refine ⟨hContains, rest, hRestFrame, ?_, trivial⟩
  change Heap.freeBytes _ q.loc _ = _
  rw [PartialCommMonoid.union_assoc hCompatibleRest hCompatible,
    ← ByteRepr.length_encode value, Heap.freeBytes_bytes_union hOldRestFrame]

/-- Release `n` consecutive slots. -/
def MutRawPtr.freeRange [ByteRepr T] (q : MutRawPtr T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.free q
      MutRawPtr.freeRange (q.add 1) n

@[step]
theorem MutRawPtr.freeRange.spec [ByteRepr T] (q : MutRawPtr T) (values : List T) :
    ⦃ q ↦* values ⦄ q.freeRange values.length ⦃⇓ emp⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.freeRange]
      simp only [RawPtr.pointsToRange_nil]
      change ispec emp (Result.ok ()) (fun _ => emp)
      rw [ispec_ok]
      iframe
  | cons value rest ih =>
      simp only [List.length_cons, MutRawPtr.freeRange, RawPtr.pointsToRange_cons]
      apply WP.ispec_bind (MutRawPtr.free.spec q value)
      · iframe
      · intro _
        simpa using ih (q := q.add 1)

namespace RawPtr

theorem take_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set,
    if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List T) (i : Nat) (value : T) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

theorem read.spec_range [ByteRepr T] (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ (q.add i).read
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.add i) values[i])
  iframe

theorem read.spec_frame [ByteRepr T] (q : RawPtr T M) (value : T) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ q.read
      ⦃⇓ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (WP.ispec_frame (read.spec q value) H)
  apply entails_sep_postWand
  intro _
  iframe

end RawPtr

theorem MutRawPtr.write.spec_range [ByteRepr T] (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.add i) value
      ⦃⇓ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.add i) values[i] value)
  iframe

/-- Fill `n` consecutive mutable slots. -/
def MutRawPtr.fillRange [ByteRepr T] (q : MutRawPtr T) (value : T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.write q value
      MutRawPtr.fillRange (q.add 1) value n

@[step]
theorem MutRawPtr.fillRange.spec [ByteRepr T] (q : MutRawPtr T) (values : List T) (value : T) :
    ⦃ q ↦* values ⦄ q.fillRange value values.length
      ⦃⇓ q ↦* List.replicate values.length value⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.fillRange]
      simp only [RawPtr.pointsToRange_nil, List.replicate_zero]
      change ispec emp (Result.ok ()) (fun _ => emp)
      rw [ispec_ok]
      iframe
  | cons old rest ih =>
      simp only [List.length_cons, List.replicate_succ, MutRawPtr.fillRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind (MutRawPtr.write.spec q old value)
      · iframe
      · intro _
        apply WP.ispec_mono
          (WP.ispec_frame (ih (q := q.add 1)) (q ↦ value))
        exact entails_trans (by iframe)
          (entails_sep_postWand _ (by intro _; iframe))

/-- Copy `n` slots from a pointer of either mutability into mutable storage. -/
def MutRawPtr.copyRange [ByteRepr T] (dst : MutRawPtr T) (src : RawPtr T M) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      let value ← src.read
      MutRawPtr.write dst value
      MutRawPtr.copyRange (dst.add 1) (src.add 1) n

@[step]
theorem MutRawPtr.copyRange.spec [ByteRepr T] (dst : MutRawPtr T) (src : RawPtr T M)
    (dstValues srcValues : List T)
    (hLength : dstValues.length = srcValues.length) :
    ⦃ dst ↦* dstValues ∗ src ↦* srcValues ⦄
      MutRawPtr.copyRange dst src srcValues.length
      ⦃⇓ dst ↦* srcValues ∗ src ↦* srcValues⦄ := by
  induction srcValues generalizing dst src dstValues with
  | nil =>
      obtain rfl : dstValues = [] := by simpa using hLength
      simp only [List.length_nil, MutRawPtr.copyRange, RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons value rest ih =>
      obtain ⟨old, oldRest, rfl⟩ : ∃ old oldRest, dstValues = old :: oldRest := by
        cases dstValues
        · simp at hLength
        · exact ⟨_, _, rfl⟩
      have hRest : oldRest.length = rest.length := by simpa using hLength
      simp only [List.length_cons, MutRawPtr.copyRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := iprop(dst ↦ old ∗ (dst.add 1) ↦* oldRest ∗
          (src.add 1) ↦* rest))
        (RawPtr.read.spec src value)
      · change
          iprop((dst ↦ old ∗ (dst.add 1) ↦* oldRest) ∗
            (src ↦ value ∗ (src.add 1) ↦* rest)) ⊢
          iprop(src ↦ value ∗
            (dst ↦ old ∗ (dst.add 1) ↦* oldRest ∗
              (src.add 1) ↦* rest))
        iframe
      · intro readValue
        iintro hRead
        subst readValue
        apply WP.ispec_bind
          (F := iprop((dst.add 1) ↦* oldRest ∗ src ↦ value ∗
            (src.add 1) ↦* rest))
          (MutRawPtr.write.spec dst old value)
        · iframe
        · intro _
          apply WP.ispec_mono
            (WP.ispec_frame
              (ih (dst := dst.add 1) (src := src.add 1)
                (dstValues := oldRest) hRest)
              (iprop(dst ↦ value ∗ src ↦ value)))
          refine entails_trans (by iframe) (entails_sep_postWand _ ?_)
          intro _
          change
            iprop(((dst.add 1) ↦* rest ∗ (src.add 1) ↦* rest) ∗
              (dst ↦ value ∗ src ↦ value)) ⊢
            iprop((dst ↦ value ∗ (dst.add 1) ↦* rest) ∗
              (src ↦ value ∗ (src.add 1) ↦* rest))
          iframe

/-- Compare two ranges through pointers of either mutability. -/
def RawPtr.compareRange [ByteRepr T] [DecidableEq T]
    (left : RawPtr T M₁) (right : RawPtr T M₂) : Nat → Result Bool
  | 0 => pure true
  | n + 1 => do
      let x ← left.read
      let y ← right.read
      if x = y then
        (left.add 1).compareRange (right.add 1) n
      else
        pure false

@[step]
theorem RawPtr.compareRange.spec [ByteRepr T] [DecidableEq T]
    (left : RawPtr T M₁) (right : RawPtr T M₂)
    (leftValues rightValues : List T)
    (hLength : leftValues.length = rightValues.length) :
    ⦃ left ↦* leftValues ∗ right ↦* rightValues ⦄
      left.compareRange right leftValues.length
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦* leftValues ∗ right ↦* rightValues)⦄ := by
  induction leftValues generalizing left right rightValues with
  | nil =>
      obtain rfl : rightValues = [] := by simpa using hLength.symm
      simp only [List.length_nil, RawPtr.compareRange,
        RawPtr.pointsToRange_nil]
      apply (ispec_ok _).2
      iframe
  | cons x leftRest ih =>
      obtain ⟨y, rightRest, rfl⟩ : ∃ y rightRest, rightValues = y :: rightRest := by
        cases rightValues
        · simp at hLength
        · exact ⟨_, _, rfl⟩
      have hRest : leftRest.length = rightRest.length := by simpa using hLength
      simp only [List.length_cons, RawPtr.compareRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := iprop((left.add 1) ↦* leftRest ∗ right ↦ y ∗
          (right.add 1) ↦* rightRest))
        (RawPtr.read.spec left x)
      · iframe
      · intro readX
        iintro hReadX
        subst readX
        apply WP.ispec_bind
          (F := iprop(left ↦ x ∗ (left.add 1) ↦* leftRest ∗
            (right.add 1) ↦* rightRest))
          (RawPtr.read.spec right y)
        · iframe
        · intro readY
          iintro hReadY
          subst readY
          by_cases hxy : x = y
          · subst y
            simp only [List.cons.injEq, true_and]
            apply WP.ispec_mono
              (WP.ispec_frame
                (ih (left := left.add 1) (right := right.add 1)
                  (rightValues := rightRest) hRest)
                (iprop(left ↦ x ∗ right ↦ x)))
            exact entails_trans (by iframe)
              (entails_sep_postWand _ (by intro _; iframe))
          · simp only [if_neg hxy]
            apply (ispec_ok _).2
            simp only [List.cons.injEq, hxy, false_and]
            iframe

/-- Materialize a mutable value as one mutable heap slot. -/
def MutRawPtr.mut_to_raw [ByteRepr T] (value : T) : Result (MutRawPtr T) :=
  MutRawPtr.alloc value

@[step]
theorem MutRawPtr.mut_to_raw.spec [ByteRepr T] (value : T) :
    ⦃ emp ⦄ MutRawPtr.mut_to_raw value ⦃⇓ q => q ↦ value⦄ :=
  MutRawPtr.alloc.spec value

/-- Read and release `n` consecutive mutable slots. -/
def MutRawPtr.takeRange [ByteRepr T] (q : MutRawPtr T) : Nat → Result (List T)
  | 0 => pure []
  | n + 1 => do
      let value ← q.read
      MutRawPtr.free q
      let rest ← MutRawPtr.takeRange (q.add 1) n
      pure (value :: rest)

@[step]
theorem MutRawPtr.takeRange.spec [ByteRepr T] (q : MutRawPtr T) (values : List T) :
    ⦃ q ↦* values ⦄ MutRawPtr.takeRange q values.length
      ⦃⇓ result => ⌜result = values⌝⦄ := by
  induction values generalizing q with
  | nil =>
      simp only [List.length_nil, MutRawPtr.takeRange]
      simp only [RawPtr.pointsToRange_nil]
      change ispec emp (Result.ok []) (fun result => ⌜result = []⌝)
      rw [ispec_ok]
      simp
  | cons value rest ih =>
      simp only [List.length_cons, MutRawPtr.takeRange,
        RawPtr.pointsToRange_cons]
      apply WP.ispec_bind
        (F := (q.add 1) ↦* rest)
        (RawPtr.read.spec q value)
      · iframe
      · intro readValue
        iintro hRead
        subst readValue
        apply WP.ispec_bind
          (F := (q.add 1) ↦* rest)
          (MutRawPtr.free.spec q value)
        · iframe
        · intro _
          apply WP.ispec_bind (F := emp) (ih (q := q.add 1))
          · iframe
          intro result
          apply (ispec_ok _).2
          iintro hResult
          subst result
          iframe

theorem MutRawPtr.takeRange.spec_of_length [ByteRepr T] (q : MutRawPtr T)
    (values : List T) (n : Nat) (hLength : values.length = n) :
    ⦃ q ↦* values ⦄ MutRawPtr.takeRange q n
      ⦃⇓ result => ⌜result = values⌝⦄ := by
  subst n
  exact MutRawPtr.takeRange.spec q values

/-- Read and release one mutable slot. -/
def MutRawPtr.end_mut_to_raw [ByteRepr T] (q : MutRawPtr T) : Result T := do
  let value ← q.read
  MutRawPtr.free q
  pure value

@[step]
theorem MutRawPtr.end_mut_to_raw.spec [ByteRepr T] {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ⦄ MutRawPtr.end_mut_to_raw q
      ⦃⇓ result => ⌜result = value⌝⦄ := by
  unfold MutRawPtr.end_mut_to_raw
  apply WP.ispec_bind (RawPtr.read.spec q value)
  · iframe
  · intro readValue
    iintro hRead
    subst readValue
    apply WP.ispec_bind (MutRawPtr.free.spec q value)
    · iframe
    · intro _
      apply (ispec_ok _).2
      iframe

/-- Reinterpret the bytes a pointer addresses at another element type and
mutability.  The address is unchanged and the heap is untouched: `spec`, the
one `step` uses, only records the address, and the others transfer ownership
from one view of the bytes to another, which requires the address to be aligned
for the new type. -/
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) (p : RawPtr T M) :
    Result (RawPtr T' M') :=
  .ok p.retype

@[step]
theorem RawPtr.cast_scalar.spec (p : RawPtr T M) :
    ⦃ emp ⦄ RawPtr.cast_scalar T' M' p ⦃⇓ q => ⌜q = p.retype⌝⦄ :=
  (ispec_ok _).2 fun _ _ => rfl

theorem RawPtr.cast_scalar.spec_range [ByteRepr T] [ByteRepr T'] (p : RawPtr T M)
    (xs : List T) (ys : List T')
    (hBytes : xs.flatMap ByteRepr.encode = ys.flatMap ByteRepr.encode)
    (hAlign : (xs ≠ [] → p.Aligned) → ys ≠ [] → (p.retype : RawPtr T' M').Aligned) :
    ⦃ p ↦* xs ⦄ RawPtr.cast_scalar T' M' p
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ q ↦* ys⦄ := by
  apply (ispec_ok _).2
  intro h hPointsTo
  exact (sep_pure_l _ _ h).mpr ⟨rfl, RawPtr.pointsToRange_retype p xs ys hBytes
    (hAlign (RawPtr.aligned_of_pointsToRange hPointsTo)) h hPointsTo⟩

theorem RawPtr.cast_scalar.spec_of_decode [ByteRepr T] [ByteRepr T'] (p : RawPtr T M)
    (x : T) (y : T') (hDecode : ByteRepr.decode (ByteRepr.encode x) = some y)
    (hAlign : p.Aligned → (p.retype : RawPtr T' M').Aligned) :
    ⦃ p ↦ x ⦄ RawPtr.cast_scalar T' M' p
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ q ↦ y⦄ := by
  apply (ispec_ok _).2
  intro h hPointsTo
  exact (sep_pure_l _ _ h).mpr ⟨rfl, RawPtr.pointsTo_retype_of_decode p x y hDecode
    (hAlign (RawPtr.aligned_of_pointsTo hPointsTo)) h hPointsTo⟩

theorem RawPtr.cast_scalar.spec_of_dvd [ByteRepr T] [ByteRepr T'] (p : RawPtr T M) (x : T)
    (hDecode : (ByteRepr.decode (α := T') (ByteRepr.encode x)).isSome)
    (hAlign : ByteRepr.align T' ∣ ByteRepr.align T) :
    ⦃ p ↦ x ⦄ RawPtr.cast_scalar T' M' p
      ⦃⇓ q => ⌜q = p.retype⌝ ∗ q ↦ (ByteRepr.decode (ByteRepr.encode x)).get hDecode⦄ :=
  RawPtr.cast_scalar.spec_of_decode p x _ (Option.some_get hDecode).symm
    (RawPtr.aligned_retype_of_dvd hAlign)

end Aeneas.Std
