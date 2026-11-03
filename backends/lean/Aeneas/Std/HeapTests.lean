module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, `dealloc` only accepts a whole block of the right
kind, once, and freed blocks can never be used again. Then, the examples of `Aeneas.Std.Heap`,
proved with the separation logic of `Aeneas.Std.HeapLemmas`. -/

namespace Aeneas.Std.HeapTests

open State SepLogic

attribute [local simp] State.cell State.empty State.newBlock State.allocBlock State.removeBlock
  State.setCell Heap.setCell RawPtr.loc RawPtr.shift

-- The start of the first allocation in the empty memory.
local notation "p₀" => (RawPtr.mk 0 0 : MutRawPtr Nat)

/-- A fresh heap allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ s₁ s₂, State.alloc [value] empty p₀ s₁ ∧ dealloc p₀ 1 s₁ () s₂ ∧
      ∀ s₃, ¬ dealloc p₀ 1 s₂ () s₃ :=
  ⟨_, _, rfl, ⟨⟨rfl, rfl, fun i hi => ⟨Nat, some value, by simp_all⟩⟩, rfl⟩,
    fun _ ⟨⟨_, h, _⟩, _⟩ => by simp at h⟩

/-- A two-cell allocation is deallocated whole. -/
example (a b : Nat) : ∃ s, dealloc p₀ 2 (empty.allocBlock [a, b] .heap).2 () s :=
  ⟨_, ⟨rfl, rfl, fun i hi => ⟨Nat, [a, b][i]?, by simp_all⟩⟩, rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ s₁ s₂, State.alloc ([] : List Nat) empty p₀ s₁ ∧ dealloc p₀ 0 s₁ () s₂ ∧
      ∀ s₃, ¬ dealloc p₀ 0 s₂ () s₃ :=
  ⟨_, _, rfl, ⟨⟨rfl, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩, rfl⟩,
    fun _ ⟨⟨_, h, _⟩, _⟩ => by simp at h⟩

/-- Creating a view after a deallocation gets a new id, and the freed block stays dead. -/
example {α : Type} (s s₁ s₂ : State) (hInv : s.Inv) (q : MutRawPtr Nat) (p : MutRawPtr α)
    (value : α) (h₁ : dealloc q 1 s () s₁) (h₂ : newView [value] s₁ p s₂) :
    p.allocId ≠ q.allocId ∧ ¬ s₂.IsLive q := by
  obtain ⟨⟨hOff, hAlloc, _⟩, rfl⟩ := h₁
  simp only [newBlock, allocBlock, removeBlock, Prod.mk.injEq] at h₂
  obtain ⟨rfl, rfl⟩ := h₂
  have hLt : q.allocId < s.next := by
    refine Nat.lt_of_not_le fun hle => ?_
    simp [(hInv _ hle).1] at hAlloc
  refine ⟨Nat.ne_of_gt hLt, fun ⟨ty, value', hCell⟩ => ?_⟩
  simp [hOff, Nat.ne_of_lt hLt] at hCell

/-- An empty view reserves its id, and its pointer stays dead after the next view. -/
example {α β : Type} (s s₁ s₂ : State) (hInv : s.Inv) (p : MutRawPtr α) (p' : MutRawPtr β)
    (value : β) (h₁ : newView ([] : List α) s p s₁) (h₂ : newView [value] s₁ p' s₂) :
    p'.allocId ≠ p.allocId ∧ ¬ s₂.IsLive p := by
  simp only [newBlock, allocBlock, Prod.mk.injEq] at h₁ h₂
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨rfl, rfl⟩ := h₂
  have hNone : s.heap.cells ⟨s.next, 0⟩ = none := (hInv s.next (Nat.le_refl _)).2 0
  refine ⟨by simp, fun ⟨ty, value', hCell⟩ => ?_⟩
  simp [hNone] at hCell

/-- A view (e.g. a copy behind a reference) cannot be deallocated through the allocator. -/
example (value : Nat) (s : State) : ¬ dealloc p₀ 1 (empty.allocBlock [value] .view).2 () s :=
  fun ⟨⟨_, h, _⟩, _⟩ => by simp at h

/-- Conversely, memory from the global allocator cannot be released as a view. -/
example (value : Nat) (s : State) : ¬ removeView p₀ 1 (empty.allocBlock [value] .heap).2 () s :=
  fun ⟨⟨_, h, _⟩, _⟩ => by simp at h

/-- `endBorrow` never applies to a freed block. -/
example (s s₁ s₂ : State) (q : MutRawPtr Nat) (value : Nat) (h₁ : dealloc q 1 s () s₁) :
    ¬ endBorrow q value s₁ () s₂ := by
  obtain ⟨⟨hOff, _, _⟩, rfl⟩ := h₁
  rintro ⟨h, _⟩
  simp [hOff] at h

/-- While a cell is borrowed, its block cannot be deallocated. -/
example (s s₁ s₂ : State) (q : MutRawPtr Nat) (x : Nat) (kind : AllocKind)
    (h₁ : borrow q s x s₁) : ¬ freeBlock q 1 kind s₁ () s₂ := by
  obtain ⟨_, rfl⟩ := h₁
  rintro ⟨⟨_, _, hLive⟩, _⟩
  obtain ⟨ty, value, hCell⟩ := hLive 0 Nat.one_pos
  simp at hCell

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) (s : State) :
    ¬ dealloc (RawPtr.shift p₀ 1) 1 (empty.allocBlock [a, b] .heap).2 () s :=
  fun ⟨⟨h, _, _⟩, _⟩ => by simp at h

/-- A size smaller than the block's is rejected. -/
example (a b : Nat) (s : State) : ¬ dealloc p₀ 1 (empty.allocBlock [a, b] .heap).2 () s :=
  fun ⟨⟨_, h, _⟩, _⟩ => by simp at h

/-- A size larger than the block's is rejected. -/
example (value : Nat) (s : State) : ¬ dealloc p₀ 2 (empty.allocBlock [value] .heap).2 () s :=
  fun ⟨⟨_, h, _⟩, _⟩ => by simp at h

/-- A shifted pointer moves within its allocation. -/
example (q : MutRawPtr Nat) : (q.shift 1).shift 2 = q.shift 3 :=
  RawPtr.shift_shift q 1 2

/-- The second cell of a fresh allocation holds the second value, and reading it can only
return that value. -/
example (s : State) (a b : Nat) :
    read (⟨s.next, 1⟩ : MutRawPtr Nat) (s.allocBlock [a, b] .heap).2 b (s.allocBlock [a, b] .heap).2 ∧
      ∀ x s', read (⟨s.next, 1⟩ : MutRawPtr Nat) (s.allocBlock [a, b] .heap).2 x s' → x = b :=
  ⟨⟨by simp, rfl⟩, fun _ _ ⟨h, _⟩ => by simpa using h.symm⟩

/-- Allocation frames the existing memory: a cell already there keeps its value. -/
example (s : State) (hInv : s.Inv) (q : MutRawPtr Nat) (value : Nat)
    (hCell : s.cell q = some (.owned Nat (some value))) (values : List Nat) :
    read q (s.allocBlock values .heap).2 value (s.allocBlock values .heap).2 := by
  have hNe : q.allocId ≠ s.next := fun hEq => by
    have := (hInv q.allocId (Nat.le_of_eq hEq.symm)).2 q.offset
    simp at hCell
    simp [hCell] at this
  simp at hCell
  exact ⟨by simp [hNe, hCell], rfl⟩

/-! ### The examples of `Aeneas.Std.Heap`

The programs below are the memory effects of the Lean models of the examples: one operation per
`Result.guardedModify`. -/

/-- The precondition of an operation on the fresh block of `[value]`: its cell, and the right to
free it (framed). -/
private theorem fresh_block {kind : AllocKind} {p : MutRawPtr α} {value : α} {h : Heap} :
    sep (alloc kind p.loc [value].length) (block p.loc [value].length fun o => .owned α [value][o]?) h →
      sep (pointsTo p value) (alloc kind p.loc 1) h := fun hp =>
  (sep_comm _ _ _).mp (sep_mono (fun _ h => h)
    (fun _ h => (block_congr fun i hi => by simp at hi; simp [hi]).mp h) hp)

/-- `Box::into_raw(Box::new(value))`, then `*Box::from_raw(p)`. -/
def boxIntoFromRaw (value : Nat) : Cmd.{0, 0} Nat :=
  Cmd.bind (State.alloc [value]) fun p =>
  Cmd.bind (State.read p) fun x =>
  Cmd.bind (State.dealloc p 1) fun _ =>
  Cmd.pure x

example (value : Nat) : Triple emp (boxIntoFromRaw value) (fun x h => x = value ∧ emp h) := by
  refine Triple.bind (newBlock_spec [value] .heap) fun p => ?_
  refine Triple.conseq (fun _ => fresh_block) (fun _ _ h => h) ?_
  refine Triple.bind (frame (read_spec p value)) fun x => ?_
  refine Triple.conseq (fun h hp => (sep_and_left _ _ _ h).mp hp) (fun _ _ h => h)
    (Triple.pure_pre fun hx => ?_)
  subst hx
  refine Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
    (freeBlock_spec p 1 .heap _ fun _ _ => ⟨Nat, _, rfl⟩)) fun _ => ?_
  exact Triple.pure x

/-- A raw pointer to the local `x = 0`, a write of `1` through it, and the end of the borrow of
`x`. -/
def rawPtrOfPlace : Cmd.{0, 0} Nat :=
  Cmd.bind (State.newView [0]) fun p =>
  Cmd.bind (State.write p 1) fun _ =>
  Cmd.bind (State.read p) fun x =>
  Cmd.bind (State.removeView p 1) fun _ =>
  Cmd.pure x

example : Triple emp rawPtrOfPlace (fun x h => x = 1 ∧ emp h) := by
  refine Triple.bind (newBlock_spec [0] .view) fun p => ?_
  refine Triple.conseq (fun _ => fresh_block) (fun _ _ h => h) ?_
  refine Triple.bind (frame (write_spec p (some 0) 1)) fun _ => ?_
  refine Triple.bind (frame (read_spec p 1)) fun x => ?_
  refine Triple.conseq (fun h hp => (sep_and_left _ _ _ h).mp hp) (fun _ _ h => h)
    (Triple.pure_pre fun hx => ?_)
  subst hx
  refine Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
    (freeBlock_spec p 1 .view _ fun _ _ => ⟨Nat, _, rfl⟩)) fun _ => ?_
  exact Triple.pure _

/-- As `rawPtrOfPlace`, then the raw pointer is converted to a borrow (`&mut *p`), through which
`2` is written. Returns the value of the borrow, and the final value of `x`. -/
def rawPtrToBorrow : Cmd.{0, 0} (Nat × Nat) :=
  Cmd.bind (State.newView [0]) fun p =>
  Cmd.bind (State.write p 1) fun _ =>
  Cmd.bind (State.borrow p) fun p1 =>
  Cmd.bind (State.endBorrow p 2) fun _ =>
  Cmd.bind (State.read p) fun x =>
  Cmd.bind (State.removeView p 1) fun _ =>
  Cmd.pure (p1, x)

example : Triple emp rawPtrToBorrow (fun r h => r = (1, 2) ∧ emp h) := by
  refine Triple.bind (newBlock_spec [0] .view) fun p => ?_
  refine Triple.conseq (fun _ => fresh_block) (fun _ _ h => h) ?_
  refine Triple.bind (frame (write_spec p (some 0) 1)) fun _ => ?_
  refine Triple.bind (frame (borrow_spec p 1)) fun p1 => ?_
  refine Triple.conseq (fun h hp => (sep_and_left _ _ _ h).mp hp) (fun _ _ h => h)
    (Triple.pure_pre fun hp1 => ?_)
  subst hp1
  refine Triple.bind (frame (endBorrow_spec p 2)) fun _ => ?_
  refine Triple.bind (frame (read_spec p 2)) fun x => ?_
  refine Triple.conseq (fun h hp => (sep_and_left _ _ _ h).mp hp) (fun _ _ h => h)
    (Triple.pure_pre fun hx => ?_)
  subst hx
  refine Triple.bind (Triple.conseq (fun h hp => (sep_comm _ _ h).mp hp) (fun _ _ h => h)
    (freeBlock_spec p 1 .view _ fun _ _ => ⟨Nat, _, rfl⟩)) fun _ => ?_
  exact Triple.pure _

end Aeneas.Std.HeapTests
