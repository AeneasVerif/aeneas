import Base
import Tutorial.Tutorial
open Primitives Result

set_option maxHeartbeats 1000000

namespace tutorial

/- # Basic tactics -/

/- Exercise 1: Version 1: -/
example α (n : Nat) (x y : α) (l0 l1 l2 : List α)
  (h0 : l1 = x :: l0)
  (h1 : l2 = y :: l1)
  (h2 : l0.length = n) :
  l2.length = n + 2 := by
  -- Using the keyword `only` to decompose what happens step by step
  simp only [h1]
  simp only [h0]
  simp only [List.length_cons]
  simp -- This simplifies the `... + 1 + 1 = ... + 2`
  simp [h2]

/- Exercise 1: Version 2: the proof can be reduced to a one-liner. -/
example α (n : Nat) (x y : α) (l0 l1 l2 : List α)
  (h0 : l1 = x :: l0)
  (h1 : l2 = y :: l1)
  (h2 : l0.length = n) :
  l2.length = n + 2 := by
  simp [*]

example (a b c d : Prop) (h0 : a → b → c) (h1 : c → d → e)
  (ha : a) (hb : b) (hd : d) : e := by
  have hc := h0 ha hb
  have he := h1 hc hd
  apply he

/- # Some proofs of programs -/

open CList

@[simp] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

/-- Theorem about `list_nth_mut1`: verbose version -/
theorem list_nth_mut1_spec {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  ∃ x back, list_nth_mut1 T l i = ok (x, back) ∧
  x = l.toList.index i.toNat ∧
  ∀ x', ∃ l', back x' = ok l' ∧ l'.toList = l.toList.update i.toNat x' := by
  rw [list_nth_mut1, list_nth_mut1_loop]
  split
  . rename_i hd tl
    split
    . -- This call to `simp` simplifies the `∃ x back, ...`
      simp
      split_conjs
      . -- Reasoning about `List.index`:
        have hi : i.toNat = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hIndex := List.index_zero_cons hd tl.toList
        simp only [hIndex]
      . intro x
        -- Reasoning about `List.update`:
        have hi : i.toNat = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hUpdate := List.update_zero_cons hd tl.toList x
        simp only [hUpdate]
    . simp at *
      progress as ⟨ i1, hi1 ⟩
      progress as ⟨ tl1, back, htl1 ⟩
      simp
      split_conjs
      . have hIndex := List.index_nzero_cons hd tl.toList i.toNat (by scalar_tac)
        simp only [hIndex]
        simp only [htl1]
        have hiEq : i1.toNat = i.toNat - 1 := by scalar_tac
        simp only [hiEq]
      . -- Backward function
        intro x'
        progress as ⟨ tl2, htl2 ⟩
        simp
        have hUpdate := List.update_nzero_cons hd tl.toList i.toNat x' (by scalar_tac)
        simp only [hUpdate]
        simp only [htl2]
        have hiEq : i1.toNat = i.toNat - 1 := by scalar_tac
        simp only [hiEq]
  . simp_all
    scalar_tac

/-- Theorem about `list_nth_mut1`: simple version.

    Remark: a simple way of simplifying the context is simply to
    call `simp_all`. Below, we're trying to be a bit more precise with
    the calls to the simplifier, for instance by using `simp [*]`
    or `simp at *` when it is enough.
 -/
theorem list_nth_mut1_spec' {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  ∃ x back, list_nth_mut1 T l i = ok (x, back) ∧
  x = l.toList.index i.toNat ∧
  ∀ x', ∃ l', back x' = ok l' ∧ l'.toList = l.toList.update i.toNat x' := by
  rw [list_nth_mut1, list_nth_mut1_loop]
  split
  . split
    . simp
      split_conjs
      . simp_all
      . intro x
        simp_all
    . simp at *
      progress as ⟨ i1 ⟩
      progress as ⟨ tl1, back ⟩
      simp
      split_conjs
      . simp [*]
      . -- Backward function
        intro x'
        progress as ⟨ tl2 ⟩
        simp [*]
  . simp_all
    scalar_tac

/-- Theorem about `list_tail`: verbose version -/
@[pspec]
theorem list_tail_spec {T : Type} (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.toList = l.toList ++ tl'.toList := by
  rw [list_tail, list_tail_loop]
  split
  . rename_i hd tl
    simp
    progress as ⟨ back, hBack ⟩
    -- This call to `simp` simplifies the `∃ ...`
    simp
    -- Proving the post-condition about the backward function
    intro tl1
    progress as ⟨ tl2, htl2 ⟩
    -- Simplify the `toList` and the equality
    simp
    -- Finish
    simp only [htl2]
  . -- Quite a few things automatically happen here
    simp

/-- Theorem about `list_tail: simple version -/
@[pspec]
theorem list_tail_spec' {T : Type} (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.toList = l.toList ++ tl'.toList := by
  rw [list_tail, list_tail_loop]
  split
  . simp
    progress as ⟨ back ⟩
    simp
    -- Proving the post-condition about the backward function
    intro tl'
    progress
    simp [*]
  . simp

/-- Theorem about `append_in_place` -/
@[pspec]
theorem append_in_place_spec {T : Type} (l0 l1 : CList T) :
  ∃ l2, append_in_place T l0 l1 = ok l2 ∧
  l2.toList = l0.toList ++ l1.toList := by
  rw [append_in_place]
  progress as ⟨ tl, back ⟩
  progress as ⟨ l2 ⟩
  -- Nothing much to do here
  simp [*]

@[pspec]
theorem reverse_loop_spec {T : Type} (l : CList T) (out : CList T) :
  ∃ l', reverse_loop T l out = ok l' ∧
  l'.toList = l.toList.reverse ++ out.toList := by
  rw [reverse_loop]
  split
  . progress as ⟨ l1, hl1 ⟩
    simp at *
    simp [hl1]
  . simp

theorem reverse_spec {T : Type} (l : CList T) :
  ∃ l', reverse T l = ok l' ∧
  l'.toList = l.toList.reverse := by
  rw [reverse]
  progress as ⟨ l', hl' ⟩
  simp at hl'
  simp [hl']

/-
  # BIG NUMBERS
 -/

attribute [-simp] Int.reducePow Nat.reducePow

-- Auxiliary definitions to interpret a vector of u32 as a mathematical integer
@[simp]
def toInt_aux (l : List U32) : ℤ :=
  match l with
  | [] => 0
  | x :: l =>
    x + 2 ^ 32 * toInt_aux l

@[reducible]
def toInt (x : alloc.vec.Vec U32) : ℤ := toInt_aux x.val

/-- The theorem about `zero_loop` -/
@[pspec]
theorem zero_loop_spec
  (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  ∃ x',
    zero_loop x i = ok x' ∧
    x'.length = x.length ∧
    (∀ j, j < i.toNat → x'.val.index j = x.val.index j) ∧
    (∀ j, i.toNat ≤ j → j < x.length → x'.val.index j = 0#u32) := by
  rw [zero_loop]
  simp
  split
  . progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ x1 ⟩
    progress as ⟨ x2, _, hSame, hZero ⟩
    simp_all
    split_conjs
    . intro j h0
      replace hSame := hSame j (by scalar_tac)
      simp_all
    . intro j h0 h1
      dcases j = i.toNat <;> simp_all
      have := hZero j (by scalar_tac)
      simp_all
  . simp; scalar_tac
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

theorem all_nil_impl_toInt_eq_zero
  (l : List U32) (h : ∀ (j : ℕ), j < l.length → l.index j = 0#u32) :
  toInt_aux l = 0 := by
  match l with
  | [] => simp
  | hd :: tl =>
    have h1 := h 0
    simp at *
    simp [*]
    apply all_nil_impl_toInt_eq_zero
    intro j h2
    have := h (j + 1) (by simp [*])
    simp at this
    simp_all

/-- The theorem about `zero` -/
theorem zero_spec (x : alloc.vec.Vec U32) :
  ∃ x',
    zero x = ok x' ∧
    x'.length = x.length ∧
    toInt x' = 0 := by
  rw [zero]
  progress as ⟨ x', hLength, hSame, hZero ⟩
  simp_all
  apply all_nil_impl_toInt_eq_zero
  simp_all

/-- You will need this lemma for the proof of `add_no_overflow_loop_spec`.

    Advice: do the proof of `add_no_overflow_loop_spec` first, then come back to prove this lemma.
 -/
@[simp]
theorem toInt_aux_drop (l : List U32) (i : Nat) (h0 : i < l.length) :
  toInt_aux (l.drop i) = l.index i + 2 ^ 32 * toInt_aux (l.drop (i + 1)) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    have := toInt_aux_drop tl (i - 1) (by scalar_tac)
    simp_all
    scalar_nf at *
    have : 1 + (i - 1) = i := by scalar_tac
    simp [*]

@[simp]
theorem toInt_aux_update (l : List U32) (i : Nat) (x : U32) (h0 : i < l.length) :
  toInt_aux (l.update i x) = toInt_aux l + 2 ^ (32 * i) * (x - l.index i) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    . scalar_eq_nf
    . have := toInt_aux_update tl (i - 1) x (by scalar_tac)
      simp_all
      scalar_nf at *
      scalar_eq_nf
      /- Note that we coerce the righ-hand side (also works with the left-hand side) so that
         it gets interpreted as an ℤ and not a ℕ. It is important: `(2 : ℕ) ^ ...` is not (at all)
         the same as `2 : ℤ`.
       -/
      have : 2 ^ (i * 32) = (2 ^ ((i - 1) * 32) * 4294967296 : Int) := by
        scalar_nf
        have : i = i - 1 + 1 := by scalar_tac
        /- This is slightly technical: we use a "conversion" to apply the rewriting only
           to the left-hand-side of the goal. Also note that we're using `rw` instead of
           `simp` otherwise the rewriting will be applied indefinitely (we can apply `i = i - 1 + 1``
           to `i - 1 + 1`, etc.).

           If you don't want to go into too many technicalities, you can also do:
           ```
           have : i * 32 = (i - 1) * 32 + 32 := by scalar_tac
           simp [*]
           ```
         -/
        conv => lhs; rw [this]
        scalar_nf
      simp [mul_assoc, *]
      scalar_eq_nf

/-- The proof about `add_no_overflow_loop` -/
@[pspec]
theorem add_no_overflow_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize)
  (hLength : x.length = y.length)
  -- No overflow occurs when we add the individual thunks
  (hNoOverflow : ∀ (j : Nat), i.toNat ≤ j → j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max)
  (hi : i.val ≤ x.length) :
  ∃ x', add_no_overflow_loop x y i = ok x' ∧
  x'.length = x.length ∧
  toInt x' = toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.drop i.toNat) := by
  rw [add_no_overflow_loop]
  simp
  split
  . progress as ⟨ yv ⟩
    progress as ⟨ xv ⟩
    progress as ⟨ sum ⟩
    . -- This precondition is not proven automatically
      have := hNoOverflow i.toNat (by scalar_tac) (by scalar_tac)
      scalar_tac
    progress as ⟨ i' ⟩
    progress as ⟨ x1 ⟩
    progress as ⟨ x2 ⟩
    . -- This precondition is not proven automatically
      intro j h0 h1
      simp_all
      -- Simplifying (x.update ...).index:
      have := List.index_update_neq x.val i.toNat j sum (by scalar_tac)
      simp [*]
      apply hNoOverflow j (by scalar_tac) (by scalar_tac)
    -- Postcondition
    /- Note that you don't have to manually call the lemmas `toInt_aux_update`
        and `toInt_aux_drop` below if you first do:
        ```
        have : i.toNat < x.length := by scalar_tac
        ```
        (simp_all will automatically apply the lemmas and prove the
        the precondition sby using the context)
      -/
    simp_all [toInt]
    scalar_eq_nf
    -- Simplifying: toInt_aux ((↑x).update (↑i).toNat sum)
    have := toInt_aux_update x.val i.toNat sum (by scalar_tac)
    simp [*]; scalar_eq_nf
    -- Simplifying: toInt_aux (List.drop (1 + (↑i).toNat) ↑y
    have := toInt_aux_drop y.val i.toNat (by scalar_tac)
    simp [*]; scalar_eq_nf
  . simp_all
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/-- The proof about `add_no_overflow` -/
theorem add_no_overflow_spec (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length)
  (hNoOverflow : ∀ (j : Nat), j < x.length → (x.val.index j).val + (y.val.index j).val ≤ U32.max) :
  ∃ x', add_no_overflow x y = ok x' ∧
  x'.length = y.length ∧
  toInt x' = toInt x + toInt y := by
  rw [add_no_overflow]
  progress as ⟨ x' ⟩ <;>
  simp_all [toInt]

/-- The proof about `add_with_carry_loop` -/
@[pspec]
theorem add_with_carry_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize)
  (hLength : x.length = y.length)
  (hi : i.val ≤ x.length)
  (hCarryLe : c0.val ≤ 1) :
  ∃ x' c1, add_with_carry_loop x y c0 i = ok (c1, x') ∧
  x'.length = x.length ∧
  c1.val ≤ 1 ∧
  toInt x' + c1.val * 2 ^ (32 * x'.length) =
    toInt x + 2 ^ (32 * i.toNat) * toInt_aux (y.val.drop i.toNat) + c0.val * 2 ^ (32 * i.toNat) := by
  rw [add_with_carry_loop]
  simp
  split
  . progress as ⟨ xi ⟩
    progress as ⟨ c0u ⟩
    . progress as ⟨ s1, c1, hConv1 ⟩
      progress as ⟨ yi ⟩
      progress as ⟨ s2, c2, hConv2 ⟩
      progress as ⟨ c1u ⟩
      progress as ⟨ c2u ⟩
      progress as ⟨ c3 ⟩
      progress as ⟨ _ ⟩
      progress as ⟨ i1 ⟩
      progress as ⟨ x1 ⟩
      progress as ⟨ c4, x2 ⟩
      -- Proving the post-condition
      simp_all [toInt]
      have hxUpdate := toInt_aux_update x.val i.toNat s2 (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_aux_drop y.val i.toNat (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      scalar_eq_nf
      split at hConv1 <;>
      split at hConv2 <;>
      simp_all <;>
      scalar_eq_nf <;> simp [U32.max] <;> scalar_eq_nf
  . simp_all
termination_by (x.length - i.val).toNat
decreasing_by scalar_decr_tac

/-- The proof about `add_with_carry` -/
@[pspec]
theorem add_with_carry_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length) :
  ∃ x' c, add_with_carry x y = ok (c, x') ∧
  x'.length = x.length ∧
  c.val ≤ 1 ∧
  toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y := by
  rw [add_with_carry]
  progress as ⟨ c, x' ⟩
  simp_all

end tutorial
