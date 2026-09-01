import Aeneas.SLPoC.MutableData.Array

/-!
# Interior pointers

`Ptr α` is a Rust pointer in the style of Pulse's `ArrayPtr`: a base address
and an offset into the allocation of [`Array.lean`](Array.lean), carrying
neither a length nor a permission.  Authority lives in the assertion, not in
the value:

* `q ↦ value` owns exactly the slot `q` addresses;
* `q ↦* values` owns the `values.length` slots from `q` on.

Because ownership of one allocation splits along its indices, `q ↦* xs ++ ys`
splits into `q ↦* xs` and `q.add xs.length ↦* ys`, with both halves naming the
*same* cell.  Two interior pointers may alias; their assertions compose exactly
when the intervals they own are disjoint.

No operation has a precondition: pointer arithmetic, allocation, reads, writes
and deallocation are total functions of their arguments.  What may go wrong is
caught by the separation logic, and by the definedness guard of the event a
heap operation triggers — a read through a dangling, unowned or uninitialized
pointer is *stuck*, not erroneous.
-/

namespace Aeneas.SLPoC

variable {α : Type}

/-- A Rust pointer: a base address and an offset into it.  It carries neither a
length nor a permission — both live in the points-to assertion. -/
structure Ptr (α : Type) where
  base : AllocId
  offset : Nat
  /- Pointers are inhabited, which is what makes the `unwrap`s of a translated
     Rust program expressible as `Option.get!`. -/
  deriving Inhabited

namespace Ptr

/-- The reference the allocation this pointer is interior to is reached
through. -/
def baseRef (q : Ptr α) : ArrayBase α := q.base

/-- Pointer arithmetic: same allocation, later offset. -/
def add (q : Ptr α) (i : Nat) : Ptr α := ⟨q.base, q.offset + i⟩

/-- Whether two pointers are interior to the same allocation. -/
def sameBase (q₁ q₂ : Ptr α) : Prop := q₁.base = q₂.base

/-- How far `q₂` is past `q₁`. -/
def distance (q₁ q₂ : Ptr α) : Nat := q₂.offset - q₁.offset

@[simp] theorem base_add (q : Ptr α) (i : Nat) : (q.add i).base = q.base := rfl
@[simp] theorem offset_add (q : Ptr α) (i : Nat) :
    (q.add i).offset = q.offset + i := rfl
@[simp] theorem baseRef_add (q : Ptr α) (i : Nat) :
    (q.add i).baseRef = q.baseRef := rfl

/-! ## Fragments -/

/-- The fragment of the allocation that owning `values` from `q` amounts to. -/
def frag (q : Ptr α) (values : List α) : ArrayCarrier α :=
  Frags.ofList q.offset (values.map InitState.initialized)

theorem get_frag {q : Ptr α} {values : List α} {i k : Nat}
    (hIndex : i = q.offset + k) (hk : k < values.length) :
    (q.frag values).get i = .owned (.initialized values[k]) := by
  subst hIndex
  rw [frag, Frags.get_ofList_of_mem (by simp; omega)]
  congr 1
  simp

theorem get_frag_of_not_mem {q : Ptr α} {values : List α} {i : Nat}
    (hIndex : ¬ (q.offset ≤ i ∧ i - q.offset < values.length)) :
    (q.frag values).get i = .unowned :=
  Frags.get_ofList_of_not_mem (by simpa using hIndex)

theorem isOwned_frag {q : Ptr α} {values : List α} {i k : Nat}
    (hIndex : i = q.offset + k) (hk : k < values.length) :
    ((q.frag values).get i).IsOwned := by
  rw [get_frag hIndex hk]; trivial

@[simp] theorem frag_nil (q : Ptr α) : q.frag [] = Frags.one := by
  simp [frag]

/-! ## Points-to -/

/-- `q` owns the `values.length` slots from `q` on, holding `values`. -/
def pointsToRange (q : Ptr α) (values : List α) : IProp :=
  Ref.pointsTo q.baseRef (q.frag values)

/-- `q` owns exactly the slot it addresses. -/
def pointsTo (q : Ptr α) (value : α) : IProp := q.pointsToRange [value]

/-- The fragment of an allocation that owns `n` slots from `q` on, none of them
written yet. -/
def fragUninit (q : Ptr α) (n : Nat) : ArrayCarrier α :=
  Frags.ofList q.offset (List.replicate n InitState.uninitialized)

/-- `q` owns `n` slots from `q` on, and no value has been written to them. -/
def pointsToUninit (q : Ptr α) (n : Nat) : IProp :=
  Ref.pointsTo q.baseRef (q.fragUninit n)

end Ptr

instance instPointsToPtr {α : Type} : PointsTo (Ptr α) α := ⟨Ptr.pointsTo⟩

@[inherit_doc Ptr.pointsToRange]
notation:50 q:50 " ↦* " values:50 => Ptr.pointsToRange q values

/-! ## Splitting and joining ranges

The whole point of indexing references by a PCM: two disjoint ranges of one
allocation are owned separately and joined back. -/

namespace Ptr

theorem composable_frag_append (q : Ptr α) (xs ys : List α) :
    (arrayPCM α).Composable (q.frag xs) ((q.add xs.length).frag ys) := by
  show Frags.Composable _ _
  have := Frags.composable_ofList_append (α := InitState α) q.offset
    (xs.map InitState.initialized) (ys.map InitState.initialized)
  simpa [frag, add] using this

theorem op_frag_append (q : Ptr α) (xs ys : List α) :
    (arrayPCM α).op (q.frag xs) ((q.add xs.length).frag ys) =
      q.frag (xs ++ ys) := by
  show Frags.op _ _ = _
  have := Frags.op_ofList_append (α := InitState α) q.offset
    (xs.map InitState.initialized) (ys.map InitState.initialized)
  simpa [frag, add] using this

/-- `splitRange` and `joinRange` at once. -/
theorem pointsToRange_append (q : Ptr α) (xs ys : List α) :
    q ↦* (xs ++ ys) ⊣⊢ q ↦* xs ∗ (q.add xs.length) ↦* ys := by
  rw [pointsToRange, pointsToRange, pointsToRange, ← op_frag_append q xs ys]
  exact Ref.pointsTo_op _ _ _ (composable_frag_append q xs ys)

/-- Split a range anywhere. -/
theorem pointsToRange_split (q : Ptr α) (values : List α) (i : Nat) :
    q ↦* values ⊣⊢
      q ↦* values.take i ∗ (q.add (values.take i).length) ↦* values.drop i := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

/-- One range cannot be owned twice. -/
theorem not_composable_frag (q : Ptr α) (values₁ values₂ : List α)
    (hNonempty₁ : 0 < values₁.length) (hNonempty₂ : 0 < values₂.length) :
    ¬ (arrayPCM α).Composable (q.frag values₁) (q.frag values₂) := by
  intro hComposable
  have hSlot := hComposable q.offset
  rw [get_frag (k := 0) (Nat.add_zero _).symm hNonempty₁,
    get_frag (k := 0) (Nat.add_zero _).symm hNonempty₂] at hSlot
  exact hSlot

end Ptr

/-- Points-to is exclusive: a slot cannot be owned twice. -/
theorem pointsTo_exclusive (q : Ptr α) (value₁ value₂ : α) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ :=
  Ref.pointsTo_exclusive q.baseRef _ _
    (Ptr.not_composable_frag q [value₁] [value₂] (by simp) (by simp))

/-! ## What a points-to assertion says about the cell -/

namespace Ptr

theorem get_of_pointsToRange {q : Ptr α} {values : List α} {h : Heap}
    {i k : Nat} (hPointsTo : (q ↦* values) h) (hIndex : i = q.offset + k)
    (hk : k < values.length) :
    (h.get q.baseRef).get i = .owned (.initialized values[k]) := by
  have hCompatible :
      (PCM.frags (InitState α)).Compatible (q.frag values) (h.get q.baseRef) :=
    Ref.compatible_of_pointsTo hPointsTo
  rw [Frags.compatible_get hCompatible (isOwned_frag hIndex hk),
    get_frag hIndex hk]

theorem isOwned_of_pointsToRange {q : Ptr α} {values : List α} {h : Heap}
    {i k : Nat} (hPointsTo : (q ↦* values) h) (hIndex : i = q.offset + k)
    (hk : k < values.length) : ((h.get q.baseRef).get i).IsOwned := by
  rw [get_of_pointsToRange hPointsTo hIndex hk]; trivial

end Ptr

/-! ## Allocation -/

/-- Allocate one slot holding `value`. -/
def alloc (value : α) : St (Ptr α) :=
  allocArray (Frags.ofList 0 [InitState.initialized value]) fun r => ⟨r, 0⟩

@[step]
theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ q => q ↦ value⦄ :=
  allocArray.spec _ _ _ fun _ => entails_refl _

/-! ## Reading -/

/-- The definedness guard of a read: the allocation exists and the slot the
pointer addresses is owned and initialized.  It is a guard, not a
precondition — `read` itself takes no proof. -/
structure Ptr.Readable (q : Ptr α) (h : Heap) : Prop where
  contains : contains h q.baseRef
  init : ((h.select q.baseRef contains).get q.offset).IsInit

/-- The value the pointer addresses.  The guard makes the match compute; no
default value is invented. -/
def Ptr.readValue (q : Ptr α) (h : Heap) (hReadable : q.Readable h) : α :=
  Exclusive.getInit _ hReadable.init

theorem Ptr.readValue_eq {q : Ptr α} {h : Heap} {value : α}
    (hReadable : q.Readable h)
    (hSlot : (h.get q.baseRef).get q.offset = .owned (.initialized value)) :
    q.readValue h hReadable = value :=
  Exclusive.getInit_eq _ hReadable.init value
    (by rw [← Heap.get_eq_select _ _ hReadable.contains]; exact hSlot)

/-- Owning the slot discharges the guard. -/
theorem Ptr.readable_of_pointsToRange {q : Ptr α} {values : List α} {h : Heap}
    (hPointsTo : (q ↦* values) h) (hNonempty : 0 < values.length) :
    q.Readable h := by
  refine ⟨contains_of_sub hPointsTo, ?_⟩
  rw [← Heap.get_eq_select _ _ (contains_of_sub hPointsTo),
    get_of_pointsToRange hPointsTo (Nat.add_zero _).symm hNonempty]
  trivial

def read (q : Ptr α) : St α :=
  guardedModify (fun h => q.Readable h) fun h hReadable =>
    (q.readValue h hReadable, h)

@[step]
theorem read.spec (q : Ptr α) (value : α) :
    ⦃ q ↦ value ⦄ read q
      ⦃⇓ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    Ptr.readable_of_pointsToRange hPointsToFrame (by simp)
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  refine (sep_pure_l _ _ h).mpr ⟨?_, hPointsTo⟩
  exact Ptr.readValue_eq hReadable
    (Ptr.get_of_pointsToRange hPointsToFrame (Nat.add_zero _).symm (by simp))

/-! ## Writing -/

/-- Writing one slot replaces whatever it held. -/
theorem Ptr.set_slot {q : Ptr α} {old : InitState α} {newValue : α} :
    Frags.set q.offset (.owned (.initialized newValue))
        (Frags.ofList q.offset [old]) = q.frag [newValue] := by
  apply Frags.ext
  intro i
  rw [Frags.get_set]
  by_cases hi : i = q.offset
  · rw [if_pos hi, get_frag (k := 0) (by omega) (by simp)]
    rfl
  · rw [if_neg hi, Frags.get_ofList_of_not_mem (by simp; omega),
      get_frag_of_not_mem (by simp; omega)]

def update (q : Ptr α) (value : α) : St Unit :=
  guardedModify (fun h => contains h q.baseRef) fun h hContains =>
    ((), h.upd q.baseRef
      (Frags.set q.offset (.owned (.initialized value))) hContains)

/-- The slot a pointer addresses may be written whatever it held: initialized,
or allocated and not yet written. -/
theorem update.spec_slot (q : Ptr α) (old : InitState α) (newValue : α) :
    ⦃ Ref.pointsTo q.baseRef (Frags.ofList q.offset [old]) ⦄
      update q newValue ⦃⇓ q ↦ newValue⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : contains h q.baseRef := contains_of_sub hPointsTo
  have hFramePreserving :=
    Frags.framePreserving_set (α := InitState α) q.offset
      (InitState.initialized newValue)
  have hOwnsFrag : ((Frags.ofList q.offset [old]).get q.offset).IsOwned :=
    Frags.isOwned_ofList (by simp)
  have hOwns : ((h.get q.baseRef).get q.offset).IsOwned := by
    rw [Frags.compatible_get
      (show (PCM.frags (InitState α)).Compatible (Frags.ofList q.offset [old])
        (h.get q.baseRef) from Ref.compatible_of_pointsTo hPointsTo) hOwnsFrag]
    exact hOwnsFrag
  refine ⟨contains_union_left hContains,
    h.upd q.baseRef (Frags.set q.offset (.owned (.initialized newValue)))
      hContains,
    Heap.disjoint_upd_left hFramePreserving hCompatible hContains hOwns,
    Heap.upd_union_left hFramePreserving hCompatible hContains hOwns, ?_⟩
  have hSub := sub_upd hFramePreserving hPointsTo hOwnsFrag hContains
  rwa [Ptr.set_slot] at hSub

@[step]
theorem update.spec (q : Ptr α) (oldValue newValue : α) :
    ⦃ q ↦ oldValue ⦄ update q newValue ⦃⇓ q ↦ newValue⦄ :=
  update.spec_slot q (.initialized oldValue) newValue

/-- Not registered with `step`: `update.spec` is the one to try first, and a
program that writes to a slot allocated uninitialized names this one. -/
theorem update.spec_uninit (q : Ptr α) (newValue : α) :
    ⦃ q.pointsToUninit 1 ⦄ update q newValue ⦃⇓ q ↦ newValue⦄ :=
  update.spec_slot q .uninitialized newValue

/-! ## Deallocation

Deallocation releases the fragment its argument owns; nothing removes an
address, exactly as in Pulse.  `Heap.size`, which counts the cells that still
own something, is therefore what tells a leak from a clean run. -/

def free (q : Ptr α) : St Unit :=
  guardedModify (fun h => contains h q.baseRef) fun h hContains =>
    ((), h.upd q.baseRef (Frags.release q.offset 1) hContains)

@[step]
theorem free.spec (q : Ptr α) (value : α) :
    ⦃ q ↦ value ⦄ free q ⦃⇓ emp⦄ := by
  apply triple_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : contains h q.baseRef := contains_of_sub hPointsTo
  have hFramePreserving :=
    Frags.framePreserving_release (α := InitState α) q.offset 1
  have hOwns : ∀ j, q.offset ≤ j → j < q.offset + 1 →
      ((h.get q.baseRef).get j).IsOwned := by
    intro j hLow hHigh
    exact Ptr.isOwned_of_pointsToRange hPointsTo (k := 0) (by omega) (by simp)
  exact ⟨contains_union_left hContains,
    h.upd q.baseRef (Frags.release q.offset 1) hContains,
    Heap.disjoint_upd_left hFramePreserving hCompatible hContains hOwns,
    Heap.upd_union_left hFramePreserving hCompatible hContains hOwns, trivial⟩

/-! ## Turning a mutable borrow into a raw pointer and back -/

def mut_to_raw {α : Type} (value : α) : St (Ptr α) :=
  alloc value

@[step]
theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ q => q ↦ value⦄ :=
  alloc.spec value

def end_mut_to_raw {α : Type} (q : Ptr α) : St α := do
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

end Aeneas.SLPoC
