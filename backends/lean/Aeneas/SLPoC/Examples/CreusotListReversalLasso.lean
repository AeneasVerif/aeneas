import Aeneas.SLPoC.Step

/-!
# Creusot's list-reversal lasso

This is a sequential SLPoC port of Creusot's
`tests/should_succeed/list_reversal_lasso.rs`.  The Rust example stores node
addresses as indices in a `Vec<usize>`, uses `usize::MAX` as null, and reverses
links until the rewiring itself makes the cursor null.  SLPoC pointers do not
support vector-style pointer arithmetic, so addresses below are first-order
natural-number names and the finite part of memory relevant to the proof is
described by `Segment`/`Lasso`.  The executable store is held in one SLPoC heap
cell and each iteration performs an explicit read-modify-write of one named
node.  `Option Addr` is the honest replacement for the null sentinel.

Lean also requires structural termination.  Consequently `reverse` receives a
fuel bound; the lasso specification supplies the exact Creusot traversal
`stem ++ cycle ++ stem.reverse`, of length `2 * stem.length + cycle.length`.
The program still obtains every successor from memory, rather than from the
ghost trace.  The final theorem identifies the complete resulting memory with
the pure cell-wise rewiring model, proves that unrelated addresses are
unchanged, and identifies the returned pointer as the original head.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace CreusotListReversalLasso

/-! # Executable definitions -/

/-- First-order names for nodes.  They are not SLPoC pointers and support no
pointer arithmetic. -/
abbrev Addr := Nat

/-- The only mutable field of a node in the Creusot example. -/
structure Node where
  next : Option Addr
deriving DecidableEq

/-- An explicit first-order memory.  Only the finitely many addresses mentioned
by a representation predicate matter; the total map avoids inventing bounds or
pointer arithmetic absent from SLPoC. -/
structure Memory where
  node : Addr → Node

namespace Memory

/-- Read the successor stored in one named node. -/
def next (m : Memory) (p : Addr) : Option Addr :=
  (m.node p).next

/-- Cell-wise replacement of one node's successor. -/
def writeNext (m : Memory) (p : Addr) (q : Option Addr) : Memory :=
  { node := Function.update m.node p { next := q } }

@[simp] theorem next_writeNext_same (m : Memory) (p : Addr) (q : Option Addr) :
    (m.writeNext p q).next p = q := by
  simp [next, writeNext]

@[simp] theorem next_writeNext_of_ne (m : Memory) (p r : Addr) (q : Option Addr)
    (h : r ≠ p) :
    (m.writeNext p q).next r = m.next r := by
  simp [next, writeNext, h]

end Memory

/-- The loop body, made structurally recursive by an explicit fuel bound.
`current` and `reversed` are Creusot's `l` and `r`, respectively. -/
def reverseAux (memory : Ptr Memory) :
    Nat → Option Addr → Option Addr → St (Option Addr)
  | 0, _, reversed => pure reversed
  | _ + 1, none, reversed => pure reversed
  | fuel + 1, some current, reversed => do
      let m ← read memory
      let next := m.next current
      update memory (m.writeNext current reversed)
      reverseAux memory fuel next (some current)

/-- Reverse/rewire successors until null is reached or `fuel` iterations have
been performed.  The lasso theorem proves that its exact bound reaches null. -/
def reverse (memory : Ptr Memory) (head : Option Addr) (fuel : Nat) :
    St (Option Addr) :=
  reverseAux memory fuel head none

/-! # Ghost state, specifications and proofs -/

/-- The pointer at the front of a segment, with `last` used for the empty
segment. -/
def firstOr (xs : List Addr) (last : Option Addr) : Option Addr :=
  match xs with
  | [] => last
  | x :: _ => some x

theorem firstOr_append (xs ys : List Addr) (last : Option Addr) :
    firstOr (xs ++ ys) last = firstOr xs (firstOr ys last) := by
  cases xs <;> rfl

/-- Pure model of the writes performed while visiting `xs`, in visit order. -/
def rewire : Memory → Option Addr → List Addr → Memory
  | m, _, [] => m
  | m, previous, p :: ps =>
      rewire (m.writeNext p previous) (some p) ps

/-- The final `r` pointer after visiting `xs`. -/
def lastVisited : Option Addr → List Addr → Option Addr
  | previous, [] => previous
  | _, p :: ps => lastVisited (some p) ps

@[simp] theorem rewire_nil (m : Memory) (previous : Option Addr) :
    rewire m previous [] = m := rfl

@[simp] theorem rewire_cons (m : Memory) (previous : Option Addr)
    (p : Addr) (ps : List Addr) :
    rewire m previous (p :: ps) =
      rewire (m.writeNext p previous) (some p) ps := rfl

@[simp] theorem lastVisited_nil (previous : Option Addr) :
    lastVisited previous [] = previous := rfl

@[simp] theorem lastVisited_cons (previous : Option Addr)
    (p : Addr) (ps : List Addr) :
    lastVisited previous (p :: ps) = lastVisited (some p) ps := rfl

theorem rewire_append (m : Memory) (previous : Option Addr)
    (xs ys : List Addr) :
    rewire m previous (xs ++ ys) =
      rewire (rewire m previous xs) (lastVisited previous xs) ys := by
  induction xs generalizing m previous with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, rewire_cons, lastVisited_cons]
    exact ih (m.writeNext x previous) (some x)

theorem lastVisited_append (previous : Option Addr) (xs ys : List Addr) :
    lastVisited previous (xs ++ ys) =
      lastVisited (lastVisited previous xs) ys := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, lastVisited_cons]
    exact ih _

theorem firstOr_reverse (xs : List Addr) (last : Option Addr) :
    firstOr xs.reverse last = lastVisited last xs := by
  induction xs generalizing last with
  | nil => rfl
  | cons x xs ih =>
      rw [List.reverse_cons, firstOr_append]
      exact ih (some x)

theorem lastVisited_reverse_of_ne_nil (previous : Option Addr)
    {xs : List Addr} (hne : xs ≠ []) :
    lastVisited previous xs.reverse = firstOr xs none := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      rw [List.reverse_cons, lastVisited_append]
      rfl

/-- A first-order, acyclic path segment.  Besides its edge equations it records
that no address occurs twice, exactly the distinctness part of Creusot's
`list_seg`. -/
inductive Segment (m : Memory) : Option Addr → List Addr → Option Addr → Prop
  | nil (last : Option Addr) : Segment m last [] last
  | cons (p : Addr) (ps : List Addr) (last : Option Addr)
      (next_eq : m.next p = firstOr ps last)
      (fresh : p ∉ ps)
      (tail : Segment m (firstOr ps last) ps last) :
      Segment m (some p) (p :: ps) last

namespace Segment

theorem nodup {m : Memory} {current last : Option Addr} {xs : List Addr}
    (h : Segment m current xs last) : xs.Nodup := by
  induction h with
  | nil => exact .nil
  | cons p ps _ _ fresh _ ih => exact .cons fresh ih

theorem head_eq {m : Memory} {current last : Option Addr} {x : Addr}
    {xs : List Addr} (h : Segment m current (x :: xs) last) :
    current = some x := by
  cases h
  rfl

/-- Updating an address outside a segment preserves that segment. -/
theorem writeNext_of_not_mem {m : Memory} {current last : Option Addr}
    {xs : List Addr} (h : Segment m current xs last) (p : Addr)
    (q : Option Addr) (hp : p ∉ xs) :
    Segment (m.writeNext p q) current xs last := by
  induction h with
  | nil =>
      exact .nil _
  | cons x xs last next_eq fresh tail ih =>
      simp only [List.mem_cons, not_or] at hp
      have hxp : x ≠ p := by exact fun h => hp.1 h.symm
      apply Segment.cons x xs last
      · simpa [Memory.next_writeNext_of_ne _ _ _ _ hxp] using next_eq
      · exact fresh
      · exact ih hp.2

/-- Rewiring only addresses disjoint from a segment preserves it. -/
theorem rewire_of_disjoint {m : Memory} {current last : Option Addr}
    {xs writes : List Addr} (h : Segment m current xs last)
    (previous : Option Addr)
    (hdisjoint : ∀ p, p ∈ writes → p ∉ xs) :
    Segment (rewire m previous writes) current xs last := by
  induction writes generalizing m previous with
  | nil => simpa using h
  | cons p ps ih =>
      simp only [rewire_cons]
      apply ih (m := m.writeNext p previous) (previous := some p)
      · exact h.writeNext_of_not_mem p previous (hdisjoint p (by simp))
      · intro q hq
        exact hdisjoint q (by simp [hq])

theorem rewire_next_of_not_mem (m : Memory) (previous : Option Addr)
    (xs : List Addr) (p : Addr) (hp : p ∉ xs) :
    (rewire m previous xs).next p = m.next p := by
  induction xs generalizing m previous with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hp
      rw [rewire_cons, ih _ _ hp.2]
      exact Memory.next_writeNext_of_ne _ _ _ _ hp.1

/-- Append one known final cell to a segment. -/
theorem snoc {m : Memory} {current : Option Addr} {xs : List Addr}
    {p : Addr} (h : Segment m current xs (some p))
    (hp : p ∉ xs) {last : Option Addr} (hnext : m.next p = last) :
    Segment m current (xs ++ [p]) last := by
  induction xs generalizing current p with
  | nil =>
      cases h
      simpa [firstOr] using
        (Segment.cons (m := m) p [] last hnext (by simp) (.nil last))
  | cons x xs ih =>
      cases h with
      | cons _ _ _ next_eq fresh tail =>
          apply Segment.cons x (xs ++ [p]) last
          · rw [firstOr_append]
            simpa [firstOr] using next_eq
          · simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨fresh, fun hxp => hp (by simp [hxp])⟩
          · simp only [List.mem_cons, not_or] at hp
            rw [firstOr_append]
            change Segment m (firstOr xs (some p)) (xs ++ [p]) last
            exact ih tail hp.2 hnext

/-- Rewiring a duplicate-free segment creates the reversed segment. -/
theorem rewire_reverse {m : Memory} {current last : Option Addr}
    {xs : List Addr} (h : Segment m current xs last)
    (previous : Option Addr) :
    Segment (rewire m previous xs) (lastVisited previous xs)
      xs.reverse previous := by
  have hnodup := h.nodup
  clear h current last
  induction xs generalizing m previous with
  | nil =>
      exact .nil previous
  | cons p ps ih =>
      simp only [List.nodup_cons] at hnodup
      simp only [rewire_cons, lastVisited_cons, List.reverse_cons]
      have hrev :
          Segment (rewire (m.writeNext p previous) (some p) ps)
            (lastVisited (some p) ps) ps.reverse (some p) :=
        ih (m := m.writeNext p previous) (previous := some p) hnodup.2
      apply hrev.snoc
      · simpa using hnodup.1
      · rw [rewire_next_of_not_mem _ _ _ p hnodup.1]
        exact Memory.next_writeNext_same _ _ _

end Segment

/-- Dynamic loop invariant: `trace` is exactly the sequence of cells fetched
from memory after accounting for all preceding writes. -/
inductive ReversalTrace :
    Memory → Option Addr → Option Addr → List Addr → Option Addr → Prop
  | nil (m : Memory) (current previous : Option Addr) :
      ReversalTrace m current previous [] current
  | cons (m : Memory) (p : Addr) (previous : Option Addr)
      (ps : List Addr) (final : Option Addr)
      (tail : ReversalTrace (m.writeNext p previous) (m.next p)
        (some p) ps final) :
      ReversalTrace m (some p) previous (p :: ps) final

namespace ReversalTrace

/-- A static duplicate-free segment supplies one phase of the dynamic loop
trace. -/
theorem ofSegment {m : Memory} {current last previous : Option Addr}
    {xs : List Addr} (h : Segment m current xs last) :
    ReversalTrace m current previous xs last := by
  induction xs generalizing m current previous with
  | nil =>
      cases h
      exact .nil _ _ _
  | cons p ps ih =>
      cases h with
      | cons _ _ last next_eq fresh tail =>
          apply ReversalTrace.cons
          rw [next_eq]
          exact ih (m := m.writeNext p previous)
            (current := firstOr ps last) (previous := some p)
            (tail.writeNext_of_not_mem p previous fresh)

/-- Concatenate two consecutive dynamic phases. -/
theorem append {m : Memory} {current previous middle final : Option Addr}
    {xs ys : List Addr}
    (hxs : ReversalTrace m current previous xs middle)
    (hys : ReversalTrace (rewire m previous xs) middle
      (lastVisited previous xs) ys final) :
    ReversalTrace m current previous (xs ++ ys) final := by
  induction hxs with
  | nil =>
      simpa using hys
  | cons m p previous ps middle tail ih =>
      simp only [List.cons_append, rewire_cons, lastVisited_cons] at hys ⊢
      exact ReversalTrace.cons _ _ _ _ _ (ih hys)

end ReversalTrace

/-- The original cycle entry is the last cell visited in the nonempty stem. -/
def entry (stem : List Addr) : Option Addr :=
  lastVisited none stem

/-- The first cycle-only node, or the entry itself for Creusot's empty-`s2`
self-loop case. -/
def middle (stem cycle : List Addr) : Option Addr :=
  firstOr cycle (entry stem)

/-- Creusot's `lasso(first, s1, s2)`: a nonempty acyclic stem, a disjoint
acyclic cycle remainder, a link from the stem to that remainder (or to itself
when it is empty), and a link back to the stem's final node. -/
def Lasso (m : Memory) (head : Option Addr)
    (stem cycle : List Addr) : Prop :=
  stem ≠ [] ∧
  (∀ p, p ∈ stem → p ∉ cycle) ∧
  Segment m head stem (middle stem cycle) ∧
  Segment m (middle stem cycle) cycle (entry stem)

/-- Exact sequence of loop iterations in Creusot's lasso reversal. -/
def traversal (stem cycle : List Addr) : List Addr :=
  stem ++ cycle ++ stem.reverse

/-- Functional loop invariant used by the executable proof.  It says that,
after accounting for preceding writes, following memory traverses the stem,
then the cycle-only nodes, then the already-reversed stem, and reaches null. -/
def LassoInvariant (m : Memory) (head : Option Addr)
    (stem cycle : List Addr) : Prop :=
  ReversalTrace m head none (traversal stem cycle) none

namespace Lasso

theorem head_eq {m : Memory} {head : Option Addr} {p : Addr}
    {stem cycle : List Addr} (h : Lasso m head (p :: stem) cycle) :
    head = some p :=
  h.2.2.1.head_eq

/-- The explicit lasso representation entails the three-phase dynamic loop
invariant; it is not assumed separately by the client specification. -/
theorem invariant {m : Memory} {head : Option Addr}
    {stem cycle : List Addr} (h : Lasso m head stem cycle) :
    LassoInvariant m head stem cycle := by
  rcases h with ⟨hne, hdisjoint, hstem, hcycle⟩
  let m₁ := rewire m none stem
  let m₂ := rewire m₁ (entry stem) cycle

  have hcycle₁ : Segment m₁ (middle stem cycle) cycle (entry stem) := by
    apply hcycle.rewire_of_disjoint none
    intro p hp
    exact hdisjoint p hp

  have hreverse₁ :
      Segment m₁ (entry stem) stem.reverse none := by
    exact hstem.rewire_reverse none

  have hreverse₂ :
      Segment m₂ (entry stem) stem.reverse none := by
    apply hreverse₁.rewire_of_disjoint (entry stem)
    intro p hp
    simpa using fun hpstem => hdisjoint p hpstem hp

  have ht₁ :
      ReversalTrace m head none stem (middle stem cycle) :=
    ReversalTrace.ofSegment hstem
  have ht₂ :
      ReversalTrace m₁ (middle stem cycle) (entry stem)
        cycle (entry stem) :=
    ReversalTrace.ofSegment hcycle₁
  have ht₃ :
      ReversalTrace m₂ (entry stem) (lastVisited (entry stem) cycle)
        stem.reverse none :=
    ReversalTrace.ofSegment hreverse₂

  unfold LassoInvariant traversal
  rw [List.append_assoc]
  exact ht₁.append (ht₂.append ht₃)

/-- The exact rewiring model has Creusot's post-state shape: the stem is
unchanged as a path and the cycle-only part is reversed. -/
theorem rewire_result {m : Memory} {head : Option Addr}
    {stem cycle : List Addr} (h : Lasso m head stem cycle) :
    Lasso (rewire m none (traversal stem cycle))
      head stem cycle.reverse := by
  rcases h with ⟨hne, hdisjoint, hstem, hcycle⟩
  let m₁ := rewire m none stem
  let cycleLast := lastVisited (entry stem) cycle
  let m₂ := rewire m₁ (entry stem) cycle
  let m₃ := rewire m₂ cycleLast stem.reverse

  have hcycle₁ : Segment m₁ (middle stem cycle) cycle (entry stem) := by
    apply hcycle.rewire_of_disjoint none
    intro p hp
    exact hdisjoint p hp

  have hreverse₁ : Segment m₁ (entry stem) stem.reverse none :=
    hstem.rewire_reverse none

  have hreverse₂ : Segment m₂ (entry stem) stem.reverse none := by
    apply hreverse₁.rewire_of_disjoint (entry stem)
    intro p hp
    simpa using fun hpstem => hdisjoint p hpstem hp

  have hcycleReverse₂ :
      Segment m₂ cycleLast cycle.reverse (entry stem) := by
    exact hcycle₁.rewire_reverse (entry stem)

  have hcycleReverse₃ :
      Segment m₃ cycleLast cycle.reverse (entry stem) := by
    apply hcycleReverse₂.rewire_of_disjoint cycleLast
    intro p hp hpc
    apply hdisjoint p
    · simpa using hp
    · simpa using hpc

  have hstem₃raw :
      Segment m₃ (lastVisited cycleLast stem.reverse)
        stem.reverse.reverse cycleLast :=
    hreverse₂.rewire_reverse cycleLast

  have hhead : head = firstOr stem none := by
    cases stem with
    | nil => contradiction
    | cons p ps => exact hstem.head_eq
  have hcurrent : lastVisited cycleLast stem.reverse = head := by
    rw [lastVisited_reverse_of_ne_nil cycleLast hne, ← hhead]
  have hmiddle : middle stem cycle.reverse = cycleLast := by
    exact firstOr_reverse cycle (entry stem)

  have hstem₃ : Segment m₃ head stem (middle stem cycle.reverse) := by
    rw [List.reverse_reverse] at hstem₃raw
    rw [hcurrent] at hstem₃raw
    rw [hmiddle]
    exact hstem₃raw

  have hcycle₃ :
      Segment m₃ (middle stem cycle.reverse) cycle.reverse (entry stem) := by
    rw [hmiddle]
    exact hcycleReverse₃

  have hm₃ : rewire m none (traversal stem cycle) = m₃ := by
    unfold traversal m₃ m₂ m₁ cycleLast
    rw [rewire_append, rewire_append, lastVisited_append]
    rfl

  rw [hm₃]
  refine ⟨hne, ?_, hstem₃, hcycle₃⟩
  intro p hp hpc
  exact hdisjoint p hp (by simpa using hpc)

end Lasso

theorem lastVisited_traversal (previous : Option Addr)
    {stem cycle : List Addr} (hne : stem ≠ []) :
    lastVisited previous (traversal stem cycle) = firstOr stem none := by
  unfold traversal
  rw [lastVisited_append, lastVisited_append]
  exact lastVisited_reverse_of_ne_nil _ hne

/-- The program follows a certified dynamic trace and realizes exactly the pure
cell-wise rewiring model. -/
theorem reverseAux.spec (memory : Ptr Memory) (m : Memory)
    (current previous final : Option Addr) (trace : List Addr)
    (htrace : ReversalTrace m current previous trace final) :
    ⦃ memory ↦ m ⦄
      reverseAux memory trace.length current previous
    ⦃⇓ result =>
      iprop(⌜result = lastVisited previous trace⌝ ∗
        memory ↦ rewire m previous trace)⦄ := by
  induction htrace with
  | nil =>
      simp only [List.length_nil]
      unfold reverseAux
      sl_step*
  | cons m p previous ps final tail ih =>
      simp only [List.length_cons]
      unfold reverseAux
      sl_step* 2
      exact ih

/-- Exact functional correctness for Creusot's lasso reversal.  The returned
pointer is the original head and the entire final memory is the pure rewiring
obtained by visiting `stem ++ cycle ++ stem.reverse`. -/
theorem reverse.spec (memory : Ptr Memory) (m : Memory)
    (head : Option Addr) (stem cycle : List Addr)
    (hlasso : Lasso m head stem cycle) :
    ⦃ memory ↦ m ⦄
      reverse memory head (traversal stem cycle).length
    ⦃⇓ result =>
      iprop(⌜result = head ∧
          Lasso (rewire m none (traversal stem cycle))
            result stem cycle.reverse ∧
          ∀ p, p ∉ traversal stem cycle →
            (rewire m none (traversal stem cycle)).next p = m.next p⌝ ∗
        memory ↦ rewire m none (traversal stem cycle))⦄ := by
  have hhead : head = firstOr stem none := by
    cases stem with
    | nil => exact False.elim (hlasso.1 rfl)
    | cons p ps => exact hlasso.head_eq
  have hPure (result : Option Addr)
      (hresultLast : result = lastVisited none (traversal stem cycle)) :
      result = head ∧
        Lasso (rewire m none (traversal stem cycle))
          result stem cycle.reverse ∧
        ∀ p, p ∉ traversal stem cycle →
          (rewire m none (traversal stem cycle)).next p = m.next p := by
    rw [lastVisited_traversal none hlasso.1] at hresultLast
    have hresult : result = head := hresultLast.trans hhead.symm
    refine ⟨hresult, ?_, ?_⟩
    · rw [hresult]
      exact hlasso.rewire_result
    · intro p hp
      exact Segment.rewire_next_of_not_mem _ _ _ _ hp
  unfold reverse
  sl_step with reverseAux.spec memory m head none none
    (traversal stem cycle) hlasso.invariant

end CreusotListReversalLasso

end Aeneas.SLPoC
