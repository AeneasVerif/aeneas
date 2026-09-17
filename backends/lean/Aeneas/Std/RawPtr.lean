import Aeneas.Std.Delab
import Aeneas.Std.Scalar.Core
import Aeneas.Std.WP
import Aeneas.Data.Coinductive.StateMachine
import Aeneas.Std.Primitives
import Aeneas.SepLogic
import Aeneas.Tactic.SepLogic.Frame
import Aeneas.Tactic.SepLogic.Intro
import Aeneas.Tactic.Step.Init

/-!
# Raw pointers

`RawPtr T M` is a Rust raw pointer: a base allocation identifier and an offset
into that allocation. The mutability index distinguishes `*mut T` from
`*const T`; permissions are carried by separation-logic assertions rather than
by the pointer value.

* `q ↦ value` owns exactly the slot `q` addresses;
* `q ↦* values` owns the consecutive slots starting at `q`.

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

/-- The heap reference addressed by a raw pointer. -/
def ref (q : RawPtr T M) : Ref T := (q.base, q.offset)

/-- Pointer arithmetic within the same allocation. -/
def add (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i⟩

/-- Whether two pointers are interior to the same allocation. -/
def sameBase (q₁ : RawPtr T M₁) (q₂ : RawPtr U M₂) : Prop :=
  q₁.base = q₂.base

/-- How far `q₂` is past `q₁`. -/
def distance (q₁ : RawPtr T M₁) (q₂ : RawPtr U M₂) : Nat :=
  q₂.offset - q₁.offset

/-- Forget write capability while preserving the address. -/
def toConst (q : MutRawPtr T) : ConstRawPtr T :=
  ⟨q.base, q.offset⟩

@[simp] theorem base_add (q : RawPtr T M) (i : Nat) :
    (q.add i).base = q.base := rfl

@[simp] theorem offset_add (q : RawPtr T M) (i : Nat) :
    (q.add i).offset = q.offset + i := rfl

@[simp] theorem add_zero (q : RawPtr T M) : q.add 0 = q := rfl

@[simp] theorem base_toConst (q : MutRawPtr T) : q.toConst.base = q.base := rfl

@[simp] theorem offset_toConst (q : MutRawPtr T) : q.toConst.offset = q.offset := rfl

@[simp] theorem ref_toConst (q : MutRawPtr T) : q.toConst.ref = q.ref := rfl

theorem ref_add (q : RawPtr T M) (i : Nat) :
    (q.add i).ref = q.ref.add i := rfl

theorem add_add (q : RawPtr T M) (i j : Nat) :
    (q.add i).add j = q.add (i + j) := by
  simp [add, Nat.add_assoc]

/-- `q` owns the `values.length` slots from `q` on. -/
def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  owns (Heap.rangeHeap q.ref values)

/-- `q` owns exactly the slot it addresses. -/
def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  Ref.pointsTo q.ref value

end RawPtr

instance instPointsToRawPtr {T : Type} {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

@[inherit_doc RawPtr.pointsToRange]
notation:50 q:50 " ↦* " values:50 => RawPtr.pointsToRange q values

theorem RawPtr.pointsTo_eq_ref (q : RawPtr T M) (value : T) :
    (q ↦ value) = Ref.pointsTo q.ref value := rfl

theorem RawPtr.pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) := by
  rw [RawPtr.pointsTo_eq_ref, RawPtr.pointsToRange, Heap.rangeHeap_singleton]
  rfl

@[simp] theorem RawPtr.pointsTo_toConst (q : MutRawPtr T) (value : T) :
    (q.toConst ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsToRange_toConst (q : MutRawPtr T) (values : List T) :
    (q.toConst ↦* values) = (q ↦* values) := rfl

namespace RawPtr

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    q ↦* (xs ++ ys) ⊣⊢ q ↦* xs ∗ (q.add xs.length) ↦* ys := by
  rw [pointsToRange, pointsToRange, pointsToRange, ref_add,
    Heap.rangeHeap_append q.ref xs ys]
  exact owns_union _ _ (Heap.compatible_rangeHeap_append q.ref xs ys)

theorem pointsToRange_split (q : RawPtr T M) (values : List T) (i : Nat) :
    q ↦* values ⊣⊢
      q ↦* values.take i ∗ (q.add (values.take i).length) ↦* values.drop i := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

theorem pointsToRange_eq_take_get_drop {q : RawPtr T M} {values : List T} {i : Nat}
    (hIndex : i < values.length) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗
        ((q.add i) ↦ values[i] ∗ (q.add (i + 1)) ↦* values.drop (i + 1))) := by
  have hTake : (values.take i).length = i := by simp; omega
  have hSplit := bientails_eq (pointsToRange_split q values i)
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex,
    show values[i] :: values.drop (i + 1)
      = [values[i]] ++ values.drop (i + 1) from rfl,
    bientails_eq
      (pointsToRange_append (q.add i) [values[i]] (values.drop (i + 1))),
    ← pointsTo_eq_range]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.add 1) ↦* rest) := by
  rw [show (value :: rest) = [value] ++ rest from rfl,
    bientails_eq (pointsToRange_append q [value] rest), ← pointsTo_eq_range]
  rfl

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  bientails_eq ⟨fun _ _ => trivial, fun h _ => Heap.Sub.of_empty h⟩

end RawPtr

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rw [RawPtr.pointsTo_eq_ref, RawPtr.pointsTo_eq_ref]
  exact Ref.pointsTo_exclusive q.ref value₁ value₂

namespace RawPtr

/-- The heap containing only the slot addressed by `q`. -/
def singleton (q : RawPtr T M) (value : T) : Heap :=
  Heap.singleton q.ref value

/-- Whether `h` contains a value of the pointer's element type at `q`. -/
def contains (h : Heap) (q : RawPtr T M) : Prop :=
  Heap.contains h q.ref

@[simp]
theorem not_contains_empty (q : RawPtr T M) :
    ¬ RawPtr.contains (∅ : Heap) q :=
  Heap.not_contains_empty q.ref

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : RawPtr.contains h q :=
  Heap.contains_of_sub hPointsTo

theorem ref_injective {q r : RawPtr T M} (hEq : q.ref = r.ref) : q = r := by
  cases q
  cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [RawPtr.ref] at hBase hOffset
  simp_all

theorem disjoint_singleton {q r : RawPtr T M} {value₁ value₂ : T} (hNe : q ≠ r) :
    PartialCommMonoid.Compatible (q.singleton value₁) (r.singleton value₂) :=
  Heap.disjoint_singleton fun hEq => hNe (ref_injective hEq)

end RawPtr

/-- Allocate `values` consecutively and pass their first reference to `mk`. -/
def RawPtr.allocArray {β : Type} (values : List T) (mk : Ref T → β) : Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (mk (Heap.freshRef T h), Heap.freshHeap h values)

theorem RawPtr.allocArray.spec {β : Type} (values : List T) (mk : Ref T → β)
    (post : β → IProp)
    (hPost : ∀ r : Ref T, owns (Heap.rangeHeap r values) ⊢ post (mk r)) :
    ⦃ emp ⦄ RawPtr.allocArray values mk ⦃⇓ result => post result⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.rangeHeap (Heap.freshRef T (h ∪ frame)) values) (h ∪ frame) :=
    Heap.compatible_freshRef _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.rangeHeap (Heap.freshRef T (h ∪ frame)) values) h frame).mpr
        ⟨hCompatible, hFresh⟩
  exact ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm,
    hPost _ _ (Heap.Sub.union_left hFreshH)⟩

/-- Materialize a list as fresh memory with the requested pointer mutability. -/
def RawPtr.materialize (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocArray values fun r => ⟨r.base, r.offset⟩

@[step]
theorem RawPtr.materialize.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values
      ⦃⇓ p => p ↦* values⦄ :=
  RawPtr.allocArray.spec _ _ _ fun _ => entails_refl _

/-- Allocate one mutable slot. -/
def MutRawPtr.alloc (value : T) : Result (MutRawPtr T) :=
  RawPtr.allocArray [value] fun r => ⟨r.base, r.offset⟩

@[step]
theorem MutRawPtr.alloc.spec (value : T) :
    ⦃ emp ⦄ MutRawPtr.alloc value ⦃⇓ q => q ↦ value⦄ :=
  RawPtr.allocArray.spec _ _ _ fun _ => entails_refl _

namespace RawPtr

structure Readable (q : RawPtr T M) (h : Heap) : Prop where
  contains : Heap.contains h q.ref

theorem readable_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  ⟨Heap.contains_of_sub hPointsTo⟩

/-- Read through either a mutable or const pointer. -/
def read (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    (Heap.read q.ref h hReadable.contains, h)

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃⇓ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    readable_of_pointsTo hPointsToFrame
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨Heap.read_of_sub hPointsToFrame hReadable.contains, hPointsTo⟩

end RawPtr

/-- Write through a mutable pointer. -/
def MutRawPtr.write (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h q.ref) fun h hContains =>
    ((), Heap.update q.ref value h hContains)

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃⇓ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hPointsTo
  have hContainsSlot := Heap.contains_singleton q.ref oldValue
  have hContains : Heap.contains (Heap.singleton q.ref oldValue ∪ rest) q.ref :=
    Heap.contains_union_left hContainsSlot
  refine ⟨Heap.contains_union_left hContains,
    Heap.update q.ref newValue _ hContains,
    Heap.disjoint_update_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.update_union_left q.ref newValue hContains
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.singleton q.ref newValue) rest := by
      have hUpdated := Heap.disjoint_update_left (value := newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.update_singleton] at hUpdated
    rw [show hContains = Heap.contains_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.update_union_left q.ref newValue hContainsSlot,
      Heap.update_singleton]
    exact Heap.Sub.union_left hCompatibleNew

/-- Release the slot addressed by a mutable pointer. -/
def MutRawPtr.free (q : MutRawPtr T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h q.ref) fun h hContains =>
    ((), Heap.free q.ref h hContains)

@[step]
theorem MutRawPtr.free.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ q.free ⦃⇓ emp⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h q.ref := Heap.contains_of_sub hPointsTo
  refine ⟨Heap.contains_union_left hContains, Heap.free q.ref h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, trivial⟩
  simpa only [show Heap.contains_union_left hContains =
      Heap.contains_union_left (h₂ := frame) hContains from rfl] using
    Heap.free_union_left q.ref hCompatible hContains

/-- Release `n` consecutive slots. -/
def MutRawPtr.freeRange (q : MutRawPtr T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.free q
      MutRawPtr.freeRange (q.add 1) n

@[step]
theorem MutRawPtr.freeRange.spec (q : MutRawPtr T) (values : List T) :
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

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ (q.add i).read
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.add i) values[i])
  iframe

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ q.read
      ⦃⇓ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_conseq (WP.ispec_frame (read.spec q value) H)
  · exact entails_refl _
  · intro _
    iframe

end RawPtr

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
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
def MutRawPtr.fillRange (q : MutRawPtr T) (value : T) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      MutRawPtr.write q value
      MutRawPtr.fillRange (q.add 1) value n

@[step]
theorem MutRawPtr.fillRange.spec (q : MutRawPtr T) (values : List T) (value : T) :
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
        apply WP.ispec_conseq
          (WP.ispec_frame (ih (q := q.add 1)) (q ↦ value))
        · iframe
        · intro _
          iframe

/-- Copy `n` slots from a pointer of either mutability into mutable storage. -/
def MutRawPtr.copyRange (dst : MutRawPtr T) (src : RawPtr T M) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      let value ← src.read
      MutRawPtr.write dst value
      MutRawPtr.copyRange (dst.add 1) (src.add 1) n

@[step]
theorem MutRawPtr.copyRange.spec (dst : MutRawPtr T) (src : RawPtr T M)
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
          apply WP.ispec_conseq
            (WP.ispec_frame
              (ih (dst := dst.add 1) (src := src.add 1)
                (dstValues := oldRest) hRest)
              (iprop(dst ↦ value ∗ src ↦ value)))
          · iframe
          · intro _
            change
              iprop(((dst.add 1) ↦* rest ∗ (src.add 1) ↦* rest) ∗
                (dst ↦ value ∗ src ↦ value)) ⊢
              iprop((dst ↦ value ∗ (dst.add 1) ↦* rest) ∗
                (src ↦ value ∗ (src.add 1) ↦* rest))
            iframe

/-- Compare two ranges through pointers of either mutability. -/
def RawPtr.compareRange [DecidableEq T]
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
theorem RawPtr.compareRange.spec [DecidableEq T]
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
            apply WP.ispec_conseq
              (WP.ispec_frame
                (ih (left := left.add 1) (right := right.add 1)
                  (rightValues := rightRest) hRest)
                (iprop(left ↦ x ∗ right ↦ x)))
            · iframe
            · intro _
              iframe
          · simp only [if_neg hxy]
            apply (ispec_ok _).2
            simp only [List.cons.injEq, hxy, false_and]
            iframe

/-- Materialize a mutable value as one mutable heap slot. -/
def MutRawPtr.mut_to_raw (value : T) : Result (MutRawPtr T) :=
  MutRawPtr.alloc value

@[step]
theorem MutRawPtr.mut_to_raw.spec (value : T) :
    ⦃ emp ⦄ MutRawPtr.mut_to_raw value ⦃⇓ q => q ↦ value⦄ :=
  MutRawPtr.alloc.spec value

/-- Read and release `n` consecutive mutable slots. -/
def MutRawPtr.takeRange (q : MutRawPtr T) : Nat → Result (List T)
  | 0 => pure []
  | n + 1 => do
      let value ← q.read
      MutRawPtr.free q
      let rest ← MutRawPtr.takeRange (q.add 1) n
      pure (value :: rest)

@[step]
theorem MutRawPtr.takeRange.spec (q : MutRawPtr T) (values : List T) :
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

theorem MutRawPtr.takeRange.spec_of_length (q : MutRawPtr T)
    (values : List T) (n : Nat) (hLength : values.length = n) :
    ⦃ q ↦* values ⦄ MutRawPtr.takeRange q n
      ⦃⇓ result => ⌜result = values⌝⦄ := by
  subst n
  exact MutRawPtr.takeRange.spec q values

/-- Read and release one mutable slot. -/
def MutRawPtr.end_mut_to_raw (q : MutRawPtr T) : Result T := do
  let value ← q.read
  MutRawPtr.free q
  pure value

@[step]
theorem MutRawPtr.end_mut_to_raw.spec {value : T} (q : MutRawPtr T) :
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

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability)
    [IsScalar T] [IsScalar T'] (_ : RawPtr T M) :
    Result (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std
