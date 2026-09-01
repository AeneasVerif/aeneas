import Aeneas.SLPoC.ST

/-!
# Allocations

A translated Rust program manipulates *pointers* and *buffers*, not the PCM
references of `Aeneas.SLPoC.Heap`.  Following Pulse, both are built on a single
kind of allocation, defined here: **one** PCM reference whose carrier is a
finitely supported map from indices to exclusively owned, possibly
uninitialized slots.

Making an allocation one cell rather than one cell per element is what lets its
ownership split along its indices: two owners of disjoint index ranges hold
*composable fragments of the same cell*, and rejoin them without the heap ever
being told.

Every operation of this directory is one `guardedModify` of
`Aeneas.SLPoC.ST`, whose guard is a *definedness* condition and never a
precondition on the caller: none of them asks for a proof.

[`Ptr.lean`](Ptr.lean) builds interior pointers on this, and
[`Buffer.lean`](Buffer.lean) bounded views.
-/

namespace Aeneas.SLPoC

variable {α : Type}

/-! ## The PCM an allocation is made with -/

/-- The carrier of the PCM of an allocation. -/
abbrev ArrayCarrier (α : Type) := Frags (InitState α)

/-- The PCM of an allocation: exclusive ownership, index by index. -/
def arrayPCM (α : Type) : PCM (ArrayCarrier α) := PCM.frags (InitState α)

/-- The reference an allocation is reached through. -/
abbrev ArrayBase (α : Type) := Ref (ArrayCarrier α) (arrayPCM α)

@[simp] theorem arrayPCM_op (x y : ArrayCarrier α) :
    (arrayPCM α).op x y = Frags.op x y := rfl

@[simp] theorem arrayPCM_composable (x y : ArrayCarrier α) :
    (arrayPCM α).Composable x y ↔ Frags.Composable x y := Iff.rfl

@[simp] theorem arrayPCM_one : (arrayPCM α).one = Frags.one := rfl

/-! ## Allocation

Allocation makes one cell of the array PCM and hands its address back in
whatever wrapper the caller asks for: a pointer to the first slot, or a buffer
spanning all of them. -/

/-- Allocate one array cell holding `x`, and wrap its address. -/
def allocArray {β : Type} (x : ArrayCarrier α) (mk : ArrayBase α → β) : St β :=
  guardedModify (fun _ => True) fun h _ =>
    (mk (freshRef (ArrayCarrier α) (arrayPCM α) h),
      freshHeap (p := arrayPCM α) h x)

theorem allocArray.spec {β : Type} (x : ArrayCarrier α) (mk : ArrayBase α → β)
    (post : β → IProp)
    (hPost : ∀ r : ArrayBase α, Ref.pointsTo r x ⊢ post (mk r)) :
    ⦃ emp ⦄ allocArray x mk ⦃⇓ result => post result⦄ := by
  apply triple_guardedModify
  intro h _ frame hCompatible
  have hFresh := fresh_freshRef (p := arrayPCM α) x (h ∪ frame)
  obtain ⟨hCompatibleFresh, hFreshHeap⟩ := fresh_eq_singleton_union hFresh
  obtain ⟨hCompatibleFreshH, hCompatibleFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (singleton (freshRef (ArrayCarrier α) (arrayPCM α) (h ∪ frame)) x)
      h frame).mpr ⟨hCompatible, hCompatibleFresh⟩
  exact ⟨trivial, _, hCompatibleFreshFrame,
    hFreshHeap.trans
      (PartialCommMonoid.union_assoc
        hCompatibleFreshH hCompatibleFreshFrame).symm,
    hPost _ _ (Heap.Sub.union_left hCompatibleFreshH)⟩

end Aeneas.SLPoC
