import Aeneas
import Tutorial.Tutorial
open Aeneas Std Result

set_option maxHeartbeats 1000000

namespace tutorial

#setup_aeneas_simps

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

@[simp, grind, agrind] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

/-- Theorem about `list_nth_mut1`: verbose version -/
theorem list_nth_mut1_spec {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.toNat < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.toNat]! ∧
    ∀ x', (back x').toList = l.toList.set i.toNat x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  split
  . rename_i hd tl
    split
    . -- This call to `simp` simplifies the `∃ x back, ...`
      simp
      split_conjs
      . -- Reasoning about `List.index`:
        have hi : i.toNat = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hIndex := @List.getElem!_cons_zero _ hd _ tl.toList
        simp only [hIndex]
      . intro x
        -- Reasoning about `List.update`:
        have hi : i.toNat = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hUpdate := @List.set_cons_zero _ hd tl.toList x
        simp only [hUpdate]
    . simp at *
      step as ⟨ i1, hi1 ⟩
      step as ⟨ tl1, back, htl1, hback ⟩
      simp
      split_conjs
      . have hIndex := List.getElem!_cons_nzero hd tl.toList i.toNat (by scalar_tac)
        simp only [hIndex]
        simp only [htl1]
        have hiEq : i1.toNat = i.toNat - 1 := by scalar_tac
        simp only [hiEq]
      . -- Backward function
        intro x'
        simp [hback]
        have hUpdate := List.set_cons_nzero hd tl.toList i.toNat (by scalar_tac) x'
        simp only [hUpdate]
        have hiEq : i1.toNat = i.toNat - 1 := by scalar_tac
        simp only [hiEq]
  . simp_all

/-- Theorem about `list_nth_mut1`: simpler version.

    Remark: a simple way of simplifying the context is simply to
    call `simp_all`. Below, we're trying to be a bit more precise with
    the calls to the simplifier, for instance by using `simp [*]`
    or `simp at *` when it is enough.
 -/
theorem list_nth_mut1_spec' {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.toNat < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.toNat]! ∧
    ∀ x', (back x').toList = l.toList.set i.toNat x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  split
  . split
    . simp
      split_conjs
      . simp_all
      . intro x
        simp_all
    . simp at *
      step as ⟨ i1 ⟩
      step as ⟨ tl1, back ⟩
      simp
      split_conjs
      . simp [*]
      . -- Backward function
        intro x'
        simp [*]
  . simp_all

/- Even simpler: `step*` can do most of the work -/
theorem list_nth_mut1_spec'' {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.toNat < l.toList.length) :
  list_nth_mut1 l i ⦃ x back =>
    x = l.toList[i.toNat]! ∧
    ∀ x', (back x').toList = l.toList.set i.toNat x' ⦄ := by
  unfold list_nth_mut1 list_nth_mut1_loop
  /- `step*` repeatedly applies `step`, while doing a case disjunction whenever it
      encounters a branching. Note that one can automatically generate the corresponding
      proof script by using `step*?`. -/
  step*
  simp_all

/-- Theorem about `list_tail_loop`: verbose version -/
@[step]
theorem list_tail_loop_spec {T : Type} (l : CList T) :
  list_tail_loop l ⦃ back =>
    ∀ tl', (back tl').toList = l.toList ++ tl'.toList ⦄ := by
  unfold list_tail_loop
  cases h: l
  . rename_i hd tl
    simp
    step as ⟨ back, hBack ⟩
    -- This call to `simp` simplifies the `∃ ...`
    simp
    -- Proving the post-condition about the backward function
    intro tl1
    -- Simplify the `toList` and the equality
    simp only [hBack]
  . -- Quite a few things automatically happen here
    simp

/-- Theorem about `list_tail_loop: simple version -/
@[step]
theorem list_tail_loop_spec' {T : Type} (l : CList T) :
  list_tail_loop l ⦃ back =>
    ∀ tl', (back tl').toList = l.toList ++ tl'.toList ⦄ := by
  unfold list_tail_loop
  step*

@[step]
theorem list_tail_spec {T : Type} (l : CList T) :
  list_tail l ⦃ tl back =>
    tl = CNil ∧
    ∀ tl', (back tl').toList = l.toList ++ tl'.toList ⦄ := by
  unfold list_tail
  step*

/-- Theorem about `append_in_place` -/
@[step]
theorem append_in_place_spec {T : Type} (l0 l1 : CList T) :
  append_in_place l0 l1 ⦃ l2 =>
    l2.toList = l0.toList ++ l1.toList ⦄ := by
  unfold append_in_place
  step*

-- Verbose version
theorem reverse_loop_spec {T : Type} (l : CList T) (out : CList T) :
  reverse_loop l out ⦃ l' =>
    l'.toList = l.toList.reverse ++ out.toList ⦄ := by
  unfold reverse_loop
  cases h: l
  . step as ⟨ l1, hl1 ⟩
    simp at *
    simp [hl1]
  . simp

-- Simple version
@[step]
theorem reverse_loop_spec' {T : Type} (l : CList T) (out : CList T) :
  reverse_loop l out ⦃ l' =>
    l'.toList = l.toList.reverse ++ out.toList ⦄ := by
  unfold reverse_loop
  step*
  agrind


theorem reverse_spec {T : Type} (l : CList T) :
  reverse l ⦃ l' =>
    l'.toList = l.toList.reverse ⦄ := by
  unfold reverse
  step*

/-
  # BIG NUMBERS
 -/

attribute [-simp] Int.reducePow Nat.reducePow

-- Auxiliary definitions to interpret a vector of u32 as a mathematical integer
@[simp]
def toInt (l : List U32) : Int :=
  match l with
  | [] => 0
  | x :: l =>
    x + 2 ^ 32 * toInt l

/-- The theorem about `zero_loop` -/
@[step]
theorem zero_loop_spec
  (x : alloc.vec.Vec U32) (i : Usize) (h : i.toNat ≤ x.length) :
  zero_loop x i ⦃ x' =>
    x'.length = x.length ∧
    (∀ j, j < i.toNat → x'[j]! = x[j]!) ∧
    (∀ j, i.toNat ≤ j → j < x.length → x'[j]! = 0#u32) ⦄ := by
  unfold zero_loop
  simp
  split
  . step as ⟨ _ ⟩
    step as ⟨ i1 ⟩
    step as ⟨ x1, _, hSame, hZero ⟩
    simp_all
    simp at hSame hZero -- TODO: why doesn't `simp_all` simplify these two hypotheses?
    split_conjs
    · scalar_tac
    · intro j h0
      replace hSame := hSame j (by scalar_tac)
      simp_all
    · intro j h0 h1
      dcases j = i.toNat <;> try simp [*]
      · have := hZero j (by scalar_tac)
        simp_all
  . simp; scalar_tac
termination_by x.length - i.toNat
decreasing_by scalar_decr_tac

theorem all_nil_impl_toInt_eq_zero
  (l : List U32) (h : ∀ (j : ℕ), j < l.length → l[j]! = 0#u32) :
  toInt l = 0 := by
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
  zero x ⦃ x' =>
    x'.length = x.length ∧
    toInt x' = 0 ⦄ := by
  unfold zero
  step as ⟨ x', hLength, hSame, hZero ⟩
  simp_all
  apply all_nil_impl_toInt_eq_zero
  simp_all

/-- You will need this lemma for the proof of `add_no_overflow_loop_spec`.

    Advice: do the proof of `add_no_overflow_loop_spec` first, then come back to prove this lemma.
 -/
@[simp]
theorem toInt_drop (l : List U32) (i : Nat) (h0 : i < l.length) :
  toInt (l.drop i) = l[i]! + 2 ^ 32 * toInt (l.drop (i + 1)) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    have := toInt_drop tl (i - 1) (by scalar_tac)
    simp_all
    ring_nf at *
    have : 1 + (i - 1) = i := by scalar_tac
    simp [*]

@[simp]
theorem toInt_update (l : List U32) (i : Nat) (x : U32) (h0 : i < l.length) :
  toInt (l.set i x) = toInt l + 2 ^ (32 * i) * (x - l[i]!) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    . ring_eq_nf
    . have := toInt_update tl (i - 1) x (by scalar_tac)
      simp_all
      ring_nf at *
      ring_eq_nf
      /- Note that we coerce the righ-hand side (also works with the left-hand side) so that
         it gets interpreted as an ℤ and not a ℕ. It is important: `(2 : ℕ) ^ ...` is not (at all)
         the same as `2 : ℤ`.
       -/
      have : 2 ^ (i * 32) = (2 ^ ((i - 1) * 32) * 4294967296 : Int) := by
        ring_nf
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
        ring_nf
      simp [mul_assoc, *]

/-- The proof about `add_no_overflow_loop` -/
@[step]
theorem add_no_overflow_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize)
  (hLength : x.length = y.length)
  -- No overflow occurs when we add the individual thunks
  (hNoOverflow : ∀ (j : Nat), i.toNat ≤ j → j < x.length → x[j]!.toNat + y[j]!.toNat ≤ U32.max) :
  add_no_overflow_loop x y i ⦃ x' =>
    x'.length = x.length ∧
    toInt x' = toInt x + 2 ^ (32 * i.toNat) * toInt (y.toNat.drop i.toNat) ⦄ := by
  unfold add_no_overflow_loop
  simp
  split
  . step as ⟨ yv ⟩
    step as ⟨ xv ⟩
    step as ⟨ sum ⟩
    step as ⟨ i' ⟩
    step as ⟨ x1 ⟩
    all_goals simp_all <;> grind
  . simp_all
termination_by x.length - i.toNat
decreasing_by scalar_decr_tac

/-- The proof about `add_no_overflow` -/
theorem add_no_overflow_spec (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length)
  (hNoOverflow : ∀ (j : Nat), j < x.length → x[j]!.toNat + y[j]!.toNat ≤ U32.max) :
  add_no_overflow x y ⦃ x' =>
    x'.length = y.length ∧
    toInt x' = toInt x + toInt y ⦄ := by
  unfold add_no_overflow
  step as ⟨ x' ⟩
  simp_all

/-- The proof about `add_with_carry_loop`: detailed version -/
@[step]
theorem add_with_carry_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize)
  (hLength : x.length = y.length)
  (hi : i.toNat ≤ x.length)
  (hCarryLe : c0.toNat ≤ 1) :
  add_with_carry_loop x y c0 i ⦃ c1 x' =>
    x'.length = x.length ∧
    c1.toNat ≤ 1 ∧
    toInt x' + c1.toNat * 2 ^ (32 * x'.length) =
      toInt x + 2 ^ (32 * i.toNat) * toInt (y.toNat.drop i.toNat) + c0.toNat * 2 ^ (32 * i.toNat) ⦄ := by
  unfold add_with_carry_loop
  simp
  split
  . step as ⟨ xi ⟩
    step as ⟨ c0u ⟩
    step as ⟨ s1, c1, hConv1 ⟩
    step as ⟨ yi ⟩
    step as ⟨ s2, c2, hConv2 ⟩
    step as ⟨ c1u, hc1u ⟩
    step as ⟨ c2u, hc2u ⟩
    step as ⟨ c3, hc3 ⟩
    · -- The call to `agrind` in `step` doesn't perform case splits on the `if then else` by default
      agrind
    step as ⟨ fst, index_back, _, hIndexBack ⟩
    step as ⟨ i1 ⟩
    have : c3.toNat ≤ 1 := by
      /- We need to make a case disjunction on hConv1 and hConv2.
         This can be done with `split at hConv1 <;> ...`, but
         `scalar_tac` can actually do it for us with the `+split``
        option, which allows it to make a case disjunction over
        the `if then else` appearing in the context.
       -/
      scalar_tac +split
    step as ⟨ c4, x1, _, _, hc4 ⟩
    -- Proving the post-condition
    . simp [*]
    . simp only [*]
      agrind
    . simp [hc4, hIndexBack]
      have hxUpdate := toInt_update x.toNat i.toNat s2 (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_drop y.toNat i.toNat (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      ring_eq_nf

      -- The best way is to do a case disjunction and treat each sub-case separately
      split at hConv1 <;>
      split at hConv2
      . have hConv1' : (s1.toNat : Int) = xi.toNat + c0u.toNat - U32.size := by agrind
        have hConv2' : (s2.toNat : Int) = s1.toNat + yi.toNat - U32.size := by agrind
        agrind
      . have hConv1' : (s1.toNat : Int) = xi.toNat + c0u.toNat - U32.size := by agrind
        simp [*, U32.size_eq]
        grind
      . have hConv2' : (s2.toNat : Int) = s1.toNat + yi.toNat - U32.size := by scalar_tac
        simp [*, U32.size_eq]
        grind
      . simp [*]
        ring_eq_nf
  . simp_all
    agrind
termination_by x.length - i.toNat
decreasing_by scalar_decr_tac

/-- The proof about `add_with_carry` -/
@[step]
theorem add_with_carry_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length) :
  add_with_carry x y ⦃ c x' =>
    x'.length = x.length ∧
    c.toNat ≤ 1 ∧
    toInt x' + c.toNat * 2 ^ (32 * x'.length) = toInt x + toInt y ⦄ := by
  unfold add_with_carry
  step as ⟨ c, x' ⟩
  simp_all

end tutorial
