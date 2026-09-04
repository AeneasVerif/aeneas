import Aeneas.SLPoC.ST

/-!
# Interior pointers

`Ptr α` is a Rust pointer: a base address and an offset into an allocation,
carrying neither a length nor a permission.  This file is the first layer of
`MutableData/`: it lays a run of slots out (`allocArray`), addresses one, and
walks a range.  Authority lives in the assertion, not in the value:

* `q ↦ value` owns exactly the slot `q` addresses;
* `q ↦* values` owns the `values.length` slots from `q` on.

Because an allocation is a run of slots, each its own heap entry, ownership of
one allocation splits along its indices: `q ↦* xs ++ ys` splits into `q ↦* xs`
and `q.add xs.length ↦* ys`, with both halves interior to the *same*
allocation.  Two interior pointers may alias; their assertions compose exactly
when the intervals they own are disjoint.

No operation has a precondition: pointer arithmetic, allocation, reads, writes
and deallocation are total functions of their arguments.  What may go wrong is
caught by the separation logic, and by the definedness guard of the event a
heap operation triggers — a read through a dangling or unowned pointer is
*stuck*, not erroneous.

This file is also where the heap of `Aeneas.Std.Heap` stops being visible: a
`Ref` never appears outside `MutableData/`.

[`Buffer.lean`](Buffer.lean) builds bounded views on this, and
[`Array.lean`](Array.lean) the arrays whose length is part of their type.
-/

namespace Aeneas.SepLogic

open Aeneas.Std (AllocId Heap Ref Result)

variable {α : Type}

/-- A Rust pointer: a base address and an offset into it.  It carries neither a
length nor a permission — both live in the points-to assertion. -/
structure Ptr (α : Type) where
  base : AllocId
  offset : Nat
  /- Pointers are inhabited, which is what makes the `unwrap`s of a translated
     Rust program expressible as `Option.get!`. -/
  deriving Inhabited, DecidableEq

namespace Ptr

/-- The slot this pointer addresses. -/
def ref (q : Ptr α) : Ref α := (q.base, q.offset)

/-- Pointer arithmetic: same allocation, later offset. -/
def add (q : Ptr α) (i : Nat) : Ptr α := ⟨q.base, q.offset + i⟩

/-- Whether two pointers are interior to the same allocation. -/
def sameBase (q₁ q₂ : Ptr α) : Prop := q₁.base = q₂.base

/-- How far `q₂` is past `q₁`. -/
def distance (q₁ q₂ : Ptr α) : Nat := q₂.offset - q₁.offset

@[simp] theorem base_add (q : Ptr α) (i : Nat) : (q.add i).base = q.base := rfl
@[simp] theorem offset_add (q : Ptr α) (i : Nat) :
    (q.add i).offset = q.offset + i := rfl
@[simp] theorem add_zero (q : Ptr α) : q.add 0 = q := rfl

theorem ref_add (q : Ptr α) (i : Nat) : (q.add i).ref = q.ref.add i := rfl

theorem add_add (q : Ptr α) (i j : Nat) : (q.add i).add j = q.add (i + j) := by
  simp [add, Nat.add_assoc]

/-! ## Points-to -/

/-- `q` owns the `values.length` slots from `q` on, holding `values`. -/
def pointsToRange (q : Ptr α) (values : List α) : IProp :=
  owns (Heap.rangeHeap q.ref values)

/-- `q` owns exactly the slot it addresses.  This is the reference assertion
directly rather than the one-slot range, so that the common case costs the
elaborator no unfolding. -/
def pointsTo (q : Ptr α) (value : α) : IProp := Ref.pointsTo q.ref value

end Ptr

instance instPointsToPtr {α : Type} : PointsTo (Ptr α) α := ⟨Ptr.pointsTo⟩

@[inherit_doc Ptr.pointsToRange]
notation:50 q:50 " ↦* " values:50 => Ptr.pointsToRange q values

/-- Owning the slot a pointer addresses is owning the reference underneath it.
This is the only place the two layers are identified. -/
theorem Ptr.pointsTo_eq_ref (q : Ptr α) (value : α) :
    (q ↦ value) = Ref.pointsTo q.ref value := rfl

/-- A slot is the range of one value. -/
theorem Ptr.pointsTo_eq_range (q : Ptr α) (value : α) :
    (q ↦ value) = (q ↦* [value]) := by
  rw [Ptr.pointsTo_eq_ref, Ptr.pointsToRange, Heap.rangeHeap_singleton]
  rfl

/-! ## Splitting and joining ranges

The whole point of an allocation being a run of slots: two disjoint ranges of
one allocation are owned separately and joined back. -/

namespace Ptr

/-- `splitRange` and `joinRange` at once. -/
theorem pointsToRange_append (q : Ptr α) (xs ys : List α) :
    q ↦* (xs ++ ys) ⊣⊢ q ↦* xs ∗ (q.add xs.length) ↦* ys := by
  rw [pointsToRange, pointsToRange, pointsToRange, ref_add,
    Heap.rangeHeap_append q.ref xs ys]
  exact owns_union _ _ (Heap.compatible_rangeHeap_append q.ref xs ys)

/-- Split a range anywhere. -/
theorem pointsToRange_split (q : Ptr α) (values : List α) (i : Nat) :
    q ↦* values ⊣⊢
      q ↦* values.take i ∗ (q.add (values.take i).length) ↦* values.drop i := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

/-- Carve the slot at `i` out of a range, keeping what is before and after it.
Stated as an equation so that it rewrites in either direction: this is both the
split that hands one slot to a read or a write, and the join that gives the
range back. -/
theorem pointsToRange_eq_take_get_drop {q : Ptr α} {values : List α} {i : Nat}
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

theorem pointsToRange_cons (q : Ptr α) (value : α) (rest : List α) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.add 1) ↦* rest) := by
  rw [show (value :: rest) = [value] ++ rest from rfl,
    bientails_eq (pointsToRange_append q [value] rest), ← pointsTo_eq_range]
  rfl

@[simp] theorem pointsToRange_nil (q : Ptr α) :
    (q ↦* ([] : List α)) = emp :=
  bientails_eq ⟨fun _ _ => trivial, fun h _ => Heap.Sub.of_empty h⟩

end Ptr

/-- Points-to is exclusive: a slot cannot be owned twice. -/
theorem pointsTo_exclusive (q : Ptr α) (value₁ value₂ : α) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rw [Ptr.pointsTo_eq_ref, Ptr.pointsTo_eq_ref]
  exact Ref.pointsTo_exclusive q.ref value₁ value₂

/-! ## What a points-to assertion says about the heap

These are the only lemmas that let a test look at the heap underneath an
assertion; the `Ref` they are stated over stays hidden. -/

namespace Ptr

/-- The heap of the single slot `q` addresses, holding `value`. -/
def singleton (q : Ptr α) (value : α) : Heap :=
  Heap.singleton q.ref value

/-- `h` has a slot at `q`, and it holds a value of type `α`.  This is the
definedness guard of every operation on `q`. -/
def contains (h : Heap) (q : Ptr α) : Prop :=
  Heap.contains h q.ref

@[simp]
theorem not_contains_empty (q : Ptr α) : ¬ Ptr.contains (∅ : Heap) q :=
  Heap.not_contains_empty q.ref

/-- Owning a slot is having one: this is what an affine points-to assertion
gives, the rest of the heap being unconstrained. -/
theorem contains_of_pointsTo {q : Ptr α} {value : α} {h : Heap}
    (hPointsTo : (q ↦ value) h) : Ptr.contains h q :=
  Heap.contains_of_sub hPointsTo

theorem ref_injective {q r : Ptr α} (hEq : q.ref = r.ref) : q = r := by
  cases q; cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [Ptr.ref] at hBase hOffset
  simp_all

/-- Two slots at different pointers are disjoint. -/
theorem disjoint_singleton {q r : Ptr α} {value₁ value₂ : α} (hNe : q ≠ r) :
    PartialCommMonoid.Compatible (q.singleton value₁) (r.singleton value₂) :=
  Heap.disjoint_singleton fun hEq => hNe (ref_injective hEq)

end Ptr

/-! ## Allocation

Allocation lays a run of slots out at a fresh address and hands it back in
whatever wrapper the caller asks for: a pointer to its first slot, or a buffer
spanning all of them. -/

/-- Allocate the run `values`, and wrap the address it starts at. -/
def allocArray {β : Type} (values : List α) (mk : Ref α → β) : Result β :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (mk (Heap.freshRef α h), Heap.freshHeap h values)

theorem allocArray.spec {β : Type} (values : List α) (mk : Ref α → β)
    (post : β → IProp)
    (hPost : ∀ r : Ref α, owns (Heap.rangeHeap r values) ⊢ post (mk r)) :
    ⦃ emp ⦄ allocArray values mk ⦃⇓ result => post result⦄ := by
  apply triple_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.rangeHeap (Heap.freshRef α (h ∪ frame)) values) (h ∪ frame) :=
    Heap.compatible_freshRef _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.rangeHeap (Heap.freshRef α (h ∪ frame)) values) h frame).mpr
        ⟨hCompatible, hFresh⟩
  exact ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm,
    hPost _ _ (Heap.Sub.union_left hFreshH)⟩

/-! ## The one-slot allocation -/

/-- Allocate one slot holding `value`. -/
def alloc (value : α) : Result (Ptr α) :=
  allocArray [value] fun r => ⟨r.base, r.offset⟩

@[step]
theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ q => q ↦ value⦄ :=
  allocArray.spec _ _ _ fun _ => entails_refl _

/-! ## Reading

The definedness guard of a read is that the heap has the slot the pointer
addresses.  It is a guard, not a precondition — `read` itself takes no proof,
and owning the slot is what discharges it. -/

/-- The definedness guard of a read: the heap has the slot `q` addresses, and
it holds a value of type `α`. -/
structure Ptr.Readable (q : Ptr α) (h : Heap) : Prop where
  contains : Heap.contains h q.ref

/-- Owning the slot discharges the guard. -/
theorem Ptr.readable_of_pointsTo {q : Ptr α} {value : α} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  ⟨Heap.contains_of_sub hPointsTo⟩

def read (q : Ptr α) : Result α :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    (Heap.read q.ref h hReadable.contains, h)

@[step]
theorem read.spec (q : Ptr α) (value : α) :
    ⦃ q ↦ value ⦄ read q
      ⦃⇓ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    Ptr.readable_of_pointsTo hPointsToFrame
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr
    ⟨Heap.read_of_sub hPointsToFrame hReadable.contains, hPointsTo⟩

/-! ## Writing and releasing

Both are total in the value they are given, so their guard is only that the
slot exists. -/

def update (q : Ptr α) (value : α) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h q.ref) fun h hContains =>
    ((), Heap.update q.ref value h hContains)

@[step]
theorem update.spec (q : Ptr α) (oldValue newValue : α) :
    ⦃ q ↦ oldValue ⦄ update q newValue ⦃⇓ q ↦ newValue⦄ := by
  apply triple_guardedModify
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

def free (q : Ptr α) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h q.ref) fun h hContains =>
    ((), Heap.free q.ref h hContains)

@[step]
theorem free.spec (q : Ptr α) (value : α) :
    ⦃ q ↦ value ⦄ free q ⦃⇓ emp⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h q.ref := Heap.contains_of_sub hPointsTo
  refine ⟨Heap.contains_union_left hContains, Heap.free q.ref h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, trivial⟩
  simpa only [show Heap.contains_union_left hContains =
      Heap.contains_union_left (h₂ := frame) hContains from rfl] using
    Heap.free_union_left q.ref hCompatible hContains

/-! ## Releasing a range

Ownership is slot-granular, so releasing a range is releasing its slots: what a
heap still holds is exactly what has not been freed, and `Heap.size` counts
it. -/

/-- Release the `n` slots from `q` on. -/
def freeRange (q : Ptr α) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      free q
      freeRange (q.add 1) n

@[step]
theorem freeRange.spec (q : Ptr α) (values : List α) :
    ⦃ q ↦* values ⦄ freeRange q values.length ⦃⇓ emp⦄ := by
  induction values generalizing q with
  | nil => exact triple_pure fun _ _ => trivial
  | cons value rest ih =>
      have hSplit :
          (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.add 1) ↦* rest) := by
        rw [show (value :: rest) = [value] ++ rest from rfl,
          bientails_eq (Ptr.pointsToRange_append q [value] rest),
          ← Ptr.pointsTo_eq_range]
        rfl
      show triple _ (do free q; freeRange (q.add 1) rest.length) _
      rw [hSplit]
      apply triple_bind (triple_frame (free.spec q value) ((q.add 1) ↦* rest))
      intro _
      exact triple_conseq (ih (q := q.add 1)) (sep_elim_left _ _)
        fun _ => entails_refl _

/-! ## Reading and writing through a range

The specifications above own one slot; these own the whole range and give it
back, which is the contract a client of an array wants.  They are *not*
registered with `step` — `read.spec` and `update.spec` are the ones to try
first, and registering both would make `step` ambiguous.  A proof that owns a
range reaches them by rewriting with `pointsToRange_eq_take_get_drop`, exactly
as they do. -/

namespace Ptr

/-- Writing one slot changes neither what is before it… -/
theorem take_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set, if_neg (show ¬ i = n by omega)]

/-- …nor what is after it. -/
theorem drop_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

end Ptr

theorem read.spec_range (q : Ptr α) (values : List α) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ read (q.add i)
      ⦃⇓ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [Ptr.pointsToRange_eq_take_get_drop hIndex]
  step*

theorem update.spec_range (q : Ptr α) (values : List α) (i : Nat) (value : α)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ update (q.add i) value
      ⦃⇓ q ↦* values.set i value⦄ := by
  rw [Ptr.pointsToRange_eq_take_get_drop hIndex,
    Ptr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    Ptr.take_set, Ptr.drop_set, List.getElem_set_self]
  step*

/-- Reading one slot of a range, with a frame: this is the shape the bulk
operations below walk a range in. -/
theorem read.spec_frame (q : Ptr α) (value : α) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ read q
      ⦃⇓ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ :=
  triple_conseq (triple_frame (read.spec q value) H) (entails_refl _)
    fun _ => (sep_assoc _ _ _).mp

/-! ## Bulk operations

Filling, copying and comparing a range: each walks it one slot at a time, and
each specification is proved by induction on the values the range holds, the
frame rule carrying the slots already visited. -/

/-- Overwrite the `n` slots from `q` on with `value`. -/
def fillRange (q : Ptr α) (value : α) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      update q value
      fillRange (q.add 1) value n

@[step]
theorem fillRange.spec (q : Ptr α) (values : List α) (value : α) :
    ⦃ q ↦* values ⦄ fillRange q value values.length
      ⦃⇓ q ↦* List.replicate values.length value⦄ := by
  induction values generalizing q with
  | nil => exact triple_pure (entails_refl _)
  | cons old rest ih =>
      rw [List.length_cons, List.replicate_succ, Ptr.pointsToRange_cons,
        Ptr.pointsToRange_cons]
      show triple _ (do update q value; fillRange (q.add 1) value rest.length) _
      apply triple_bind (triple_frame (update.spec q old value) _)
      intro _
      exact triple_frame_left (ih (q := q.add 1)) _

/-- Copy the `n` slots from `src` on into the `n` slots from `dst` on. -/
def copyRange (dst src : Ptr α) : Nat → Result Unit
  | 0 => pure ()
  | n + 1 => do
      let value ← read src
      update dst value
      copyRange (dst.add 1) (src.add 1) n

@[step]
theorem copyRange.spec (dst src : Ptr α) (dstValues srcValues : List α)
    (hLength : dstValues.length = srcValues.length) :
    ⦃ dst ↦* dstValues ∗ src ↦* srcValues ⦄
      copyRange dst src srcValues.length
      ⦃⇓ dst ↦* srcValues ∗ src ↦* srcValues⦄ := by
  induction srcValues generalizing dst src dstValues with
  | nil =>
      refine triple_pure (entails_trans (entails_emp_r _) ?_)
      rw [Ptr.pointsToRange_nil, Ptr.pointsToRange_nil]
      exact (sep_emp_l emp).mpr
  | cons value rest ih =>
      obtain ⟨old, oldRest, rfl⟩ : ∃ old oldRest, dstValues = old :: oldRest := by
        cases dstValues with
        | nil => simp at hLength
        | cons old oldRest => exact ⟨old, oldRest, rfl⟩
      have hRest : oldRest.length = rest.length := by simpa using hLength
      rw [List.length_cons, Ptr.pointsToRange_cons, Ptr.pointsToRange_cons,
        Ptr.pointsToRange_cons]
      refine triple_conseq (P' := iprop(src ↦ value ∗
          (dst ↦ old ∗ ((dst.add 1) ↦* oldRest ∗ (src.add 1) ↦* rest))))
        ?_ (by iframe) (fun _ => entails_refl _)
      apply triple_bind (read.spec_frame src value _)
      intro result
      apply triple_ipure
      intro hResult
      rw [hResult]
      refine triple_conseq (P' := iprop(dst ↦ old ∗
          (src ↦ value ∗ ((dst.add 1) ↦* oldRest ∗ (src.add 1) ↦* rest))))
        ?_ (by iframe) (fun _ => entails_refl _)
      apply triple_bind (triple_frame (update.spec dst old value) _)
      intro _
      have hTail := triple_frame (ih (dst.add 1) (src.add 1) oldRest hRest)
        iprop(dst ↦ value ∗ src ↦ value)
      exact triple_conseq hTail (by iframe) (fun _ => by iframe)

/-- Whether the `n` slots from `left` on hold the same values as the `n` slots
from `right` on. -/
def compareRange [DecidableEq α] (left right : Ptr α) : Nat → Result Bool
  | 0 => pure true
  | n + 1 => do
      let x ← read left
      let y ← read right
      if x = y then compareRange (left.add 1) (right.add 1) n else pure false

@[step]
theorem compareRange.spec [DecidableEq α] (left right : Ptr α)
    (leftValues rightValues : List α)
    (hLength : leftValues.length = rightValues.length) :
    ⦃ left ↦* leftValues ∗ right ↦* rightValues ⦄
      compareRange left right leftValues.length
      ⦃⇓ result => ⌜result = decide (leftValues = rightValues)⌝ ∗
        (left ↦* leftValues ∗ right ↦* rightValues)⦄ := by
  induction leftValues generalizing left right rightValues with
  | nil =>
      obtain rfl : rightValues = [] := by
        cases rightValues with
        | nil => rfl
        | cons _ _ => simp at hLength
      exact triple_pure fun h hPre => (sep_pure_l _ _ h).mpr ⟨by simp, hPre⟩
  | cons x lrest ih =>
      obtain ⟨y, rrest, rfl⟩ : ∃ y rrest, rightValues = y :: rrest := by
        cases rightValues with
        | nil => simp at hLength
        | cons y rrest => exact ⟨y, rrest, rfl⟩
      have hRest : lrest.length = rrest.length := by simpa using hLength
      rw [List.length_cons, Ptr.pointsToRange_cons, Ptr.pointsToRange_cons]
      refine triple_conseq (P' := iprop(left ↦ x ∗
          (right ↦ y ∗ ((left.add 1) ↦* lrest ∗ (right.add 1) ↦* rrest))))
        ?_ (by iframe) (fun _ => entails_refl _)
      apply triple_bind (read.spec_frame left x _)
      intro resultLeft
      apply triple_ipure
      intro hLeft
      rw [hLeft]
      refine triple_conseq (P' := iprop(right ↦ y ∗
          (left ↦ x ∗ ((left.add 1) ↦* lrest ∗ (right.add 1) ↦* rrest))))
        ?_ (by iframe) (fun _ => entails_refl _)
      apply triple_bind (read.spec_frame right y _)
      intro resultRight
      apply triple_ipure
      intro hRight
      rw [hRight]
      by_cases hEq : x = y
      · rw [if_pos hEq]
        have hTail := triple_frame (ih (left.add 1) (right.add 1) rrest hRest)
          iprop(left ↦ x ∗ right ↦ y)
        refine triple_conseq hTail (by iframe) fun result h hPost => ?_
        obtain ⟨hResult, hOwn⟩ :=
          (sep_pure_l _ _ h).mp ((sep_assoc _ _ _).mp h hPost)
        refine (sep_pure_l _ _ h).mpr ⟨?_, ?_⟩
        · rw [hResult, hEq]; simp
        · exact (by iframe : iprop(((left.add 1) ↦* lrest ∗
            (right.add 1) ↦* rrest) ∗ (left ↦ x ∗ right ↦ y)) ⊢
              iprop((left ↦ x ∗ (left.add 1) ↦* lrest) ∗
                (right ↦ y ∗ (right.add 1) ↦* rrest))) h hOwn
      · rw [if_neg hEq]
        refine triple_pure fun h hPre => (sep_pure_l _ _ h).mpr ⟨by simp [hEq], ?_⟩
        exact (by iframe : iprop(right ↦ y ∗ (left ↦ x ∗
          ((left.add 1) ↦* lrest ∗ (right.add 1) ↦* rrest))) ⊢
            iprop((left ↦ x ∗ (left.add 1) ↦* lrest) ∗
              (right ↦ y ∗ (right.add 1) ↦* rrest))) h hPre

/-! ## Turning a mutable borrow into a raw pointer and back -/

def mut_to_raw {α : Type} (value : α) : Result (Ptr α) :=
  alloc value

@[step]
theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ q => q ↦ value⦄ :=
  alloc.spec value

/-- Read and release `n` consecutive slots. -/
def takeRange (q : Ptr α) : Nat → Result (List α)
  | 0 => pure []
  | n + 1 => do
      let value ← read q
      free q
      let rest ← takeRange (q.add 1) n
      pure (value :: rest)

@[step]
theorem takeRange.spec (q : Ptr α) (values : List α) :
    ⦃ q ↦* values ⦄ takeRange q values.length
      ⦃⇓ result => ⌜result = values⌝⦄ := by
  induction values generalizing q with
  | nil =>
      exact triple_pure fun _ _ => rfl
  | cons value rest ih =>
      rw [Ptr.pointsToRange_cons]
      simp only [List.length_cons, takeRange]
      apply triple_bind (read.spec_frame q value ((q.add 1) ↦* rest))
      intro result
      apply triple_ipure
      intro hResult
      apply triple_bind
        (triple_conseq (triple_frame (free.spec q value) ((q.add 1) ↦* rest))
          (entails_refl _) fun _ => (sep_emp_l _).mp)
      intro _
      apply triple_bind (ih (q := q.add 1))
      intro tail
      exact triple_pure fun _ hTail => by
        change result :: tail = value :: rest
        exact congrArg₂ List.cons hResult hTail

theorem takeRange.spec_of_length (q : Ptr α) (values : List α) (n : Nat)
    (hLength : values.length = n) :
    ⦃ q ↦* values ⦄ takeRange q n
      ⦃⇓ result => ⌜result = values⌝⦄ := by
  subst n
  exact takeRange.spec q values

def end_mut_to_raw {α : Type} (q : Ptr α) : Result α := do
  let value ← read q
  free q
  pure value

@[step]
theorem end_mut_to_raw.spec {α : Type} {value : α} (q : Ptr α) :
    ⦃ q ↦ value ⦄ end_mut_to_raw q ⦃⇓ result => ⌜result = value⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_bind (read.spec q value)
  intro result
  apply triple_ipure
  intro hResult
  apply triple_seq (free.spec q value)
  exact triple_pure fun _ _ => hResult

end Aeneas.SepLogic
