import Aeneas
import Tutorial.Tutorial
open Aeneas.Std Result

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

@[simp] def CList.toList {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.toList

/-- Theorem about `list_nth_mut1`: verbose version -/
theorem list_nth_mut1_spec {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  ∃ x back, list_nth_mut1 l i = ok (x, back) ∧
  x = l.toList[i.val]! ∧
  ∀ x', (back x').toList = l.toList.set i.val x' := by
  unfold list_nth_mut1 list_nth_mut1_loop
  split
  . rename_i hd tl
    split
    . -- This call to `simp` simplifies the `∃ x back, ...`
      simp
      split_conjs
      . -- Reasoning about `List.index`:
        have hi : i.val = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hIndex := @List.getElem!_cons_zero _ hd _ tl.toList
        simp only [hIndex]
      . intro x
        -- Reasoning about `List.update`:
        have hi : i.val = 0 := by scalar_tac
        simp only [hi] -- Without the `only`, this actually finished the goal
        have hUpdate := @List.set_cons_zero _ hd tl.toList x
        simp only [hUpdate]
    . simp at *
      progress as ⟨ i1, hi1 ⟩
      progress as ⟨ tl1, back, htl1, hback ⟩
      simp
      split_conjs
      . have hIndex := List.getElem!_cons_nzero hd tl.toList i.val (by scalar_tac)
        simp only [hIndex]
        simp only [htl1]
        have hiEq : i1.val = i.val - 1 := by scalar_tac
        simp only [hiEq]
      . -- Backward function
        intro x'
        simp [hback]
        have hUpdate := List.set_cons_nzero hd tl.toList i.val (by scalar_tac) x'
        simp only [hUpdate]
        have hiEq : i1.val = i.val - 1 := by scalar_tac
        simp only [hiEq]
  . simp_all

/-- Theorem about `list_nth_mut1`: simple version.

    Remark: a simple way of simplifying the context is simply to
    call `simp_all`. Below, we're trying to be a bit more precise with
    the calls to the simplifier, for instance by using `simp [*]`
    or `simp at *` when it is enough.
 -/
theorem list_nth_mut1_spec' {T: Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.toList.length) :
  ∃ x back, list_nth_mut1 l i = ok (x, back) ∧
  x = l.toList[i.val]! ∧
  ∀ x', (back x').toList = l.toList.set i.val x' := by
  unfold list_nth_mut1 list_nth_mut1_loop
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
        simp [*]
  . simp_all

/-- Theorem about `list_tail_loop`: verbose version -/
@[progress]
theorem list_tail_loop_spec {T : Type} (l : CList T) :
  ∃ back, list_tail_loop l = ok back ∧
  ∀ tl', (back tl').toList = l.toList ++ tl'.toList := by
  unfold list_tail_loop
  split
  . rename_i hd tl
    simp
    progress as ⟨ back, hBack ⟩
    -- This call to `simp` simplifies the `∃ ...`
    simp
    -- Proving the post-condition about the backward function
    intro tl1
    -- Simplify the `toList` and the equality
    simp only [hBack]
  . -- Quite a few things automatically happen here
    simp

/-- Theorem about `list_tail_loop: simple version -/
@[progress]
theorem list_tail_loop_spec' {T : Type} (l : CList T) :
  ∃ back, list_tail_loop l = ok back ∧
  ∀ tl', (back tl').toList = l.toList ++ tl'.toList := by
  unfold list_tail_loop
  progress*

@[progress]
theorem list_tail_spec {T : Type} (l : CList T) :
  ∃ back, list_tail l = ok (CList.CNil, back) ∧
  ∀ tl', (back tl').toList = l.toList ++ tl'.toList := by
  unfold list_tail
  progress*

/-- Theorem about `append_in_place` -/
@[progress]
theorem append_in_place_spec {T : Type} (l0 l1 : CList T) :
  ∃ l2, append_in_place l0 l1 = ok l2 ∧
  l2.toList = l0.toList ++ l1.toList := by
  unfold append_in_place
  progress as ⟨ tl, back ⟩
  progress as ⟨ l2 ⟩

@[progress]
theorem reverse_loop_spec {T : Type} (l : CList T) (out : CList T) :
  ∃ l', reverse_loop l out = ok l' ∧
  l'.toList = l.toList.reverse ++ out.toList := by
  unfold reverse_loop
  split
  . progress as ⟨ l1, hl1 ⟩
    simp at *
    simp [hl1]
  . simp

theorem reverse_spec {T : Type} (l : CList T) :
  ∃ l', reverse l = ok l' ∧
  l'.toList = l.toList.reverse := by
  unfold reverse
  progress as ⟨ l', hl' ⟩
  simp at hl'
  simp [hl']

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
@[progress]
theorem zero_loop_spec
  (x : alloc.vec.Vec U32) (i : Usize) (h : i.val ≤ x.length) :
  ∃ x',
    zero_loop x i = ok x' ∧
    x'.length = x.length ∧
    (∀ j, j < i.val → x'[j]! = x[j]!) ∧
    (∀ j, i.val ≤ j → j < x.length → x'[j]! = 0#u32) := by
  unfold zero_loop
  simp
  split
  . progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    progress as ⟨ x1, _, hSame, hZero ⟩
    simp_all
    split_conjs
    . intro j h0
      replace hSame := hSame j (by scalar_tac)
      simp_all
    . intro j h0 h1
      dcases j = i.val <;> try simp [*]
      have := hZero j (by scalar_tac)
      simp_all
  . simp; scalar_tac
termination_by x.length - i.val
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
  ∃ x',
    zero x = ok x' ∧
    x'.length = x.length ∧
    toInt x' = 0 := by
  unfold zero
  progress as ⟨ x', hLength, hSame, hZero ⟩
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
    scalar_nf at *
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
    . scalar_eq_nf
    . have := toInt_update tl (i - 1) x (by scalar_tac)
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
@[progress]
theorem add_no_overflow_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (i : Usize)
  (hLength : x.length = y.length)
  -- No overflow occurs when we add the individual thunks
  (hNoOverflow : ∀ (j : Nat), i.val ≤ j → j < x.length → x[j]!.val + y[j]!.val ≤ U32.max) :
  ∃ x', add_no_overflow_loop x y i = ok x' ∧
  x'.length = x.length ∧
  toInt x' = toInt x + 2 ^ (32 * i.val) * toInt (y.val.drop i.val) := by
  unfold add_no_overflow_loop
  simp
  split
  . progress as ⟨ yv ⟩
    progress as ⟨ xv ⟩
    progress as ⟨ sum ⟩
    . -- This precondition is not proven automatically
      have := hNoOverflow i.val (by scalar_tac) (by scalar_tac)
      scalar_tac
    progress as ⟨ i' ⟩
    progress as ⟨ x1 ⟩
    . -- This precondition is not proven automatically
      intro j h0 h1
      simp_all
      -- Simplifying (x.update ...).index:
      have := List.getElem!_set_ne x.val i.val j sum (by scalar_tac)
      simp [*]
      apply hNoOverflow j (by scalar_tac) (by scalar_tac)
    -- Postcondition
    /- Note that you don't have to manually call the lemmas `toInt_update`
        and `toInt_drop` below if you first do:
        ```
        have : i.val < x.length := by scalar_tac
        ```
        (simp_all will automatically apply the lemmas and prove the
        the precondition sby using the context)
      -/
    simp_all
    scalar_eq_nf
  . simp_all
termination_by x.length - i.val
decreasing_by scalar_decr_tac

/-- The proof about `add_no_overflow` -/
theorem add_no_overflow_spec (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length)
  (hNoOverflow : ∀ (j : Nat), j < x.length → x[j]!.val + y[j]!.val ≤ U32.max) :
  ∃ x', add_no_overflow x y = ok x' ∧
  x'.length = y.length ∧
  toInt x' = toInt x + toInt y := by
  unfold add_no_overflow
  progress as ⟨ x' ⟩ <;>
  simp_all

/-- The proof about `add_with_carry_loop` -/
@[progress]
theorem add_with_carry_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize)
  (hLength : x.length = y.length)
  (hi : i.val ≤ x.length)
  (hCarryLe : c0.val ≤ 1) :
  ∃ x' c1, add_with_carry_loop x y c0 i = ok (c1, x') ∧
  x'.length = x.length ∧
  c1.val ≤ 1 ∧
  toInt x' + c1.val * 2 ^ (32 * x'.length) =
    toInt x + 2 ^ (32 * i.val) * toInt (y.val.drop i.val) + c0.val * 2 ^ (32 * i.val) := by
  unfold add_with_carry_loop
  simp
  split
  . progress as ⟨ xi ⟩
    progress as ⟨ c0u ⟩
    have : c0u.val = c0.val := by scalar_tac
    progress as ⟨ s1, c1, hConv1 ⟩
    progress as ⟨ yi ⟩
    progress as ⟨ s2, c2, hConv2 ⟩
    progress as ⟨ c1u, hc1u ⟩
    progress as ⟨ c2u, hc2u ⟩
    progress as ⟨ c3, hc3 ⟩
    progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    have : c3.val ≤ 1 := by
      /- We need to make a case disjunction on hConv1 and hConv2.
         This can be done with `split at hConv1 <;> ...`, but
         `scalar_tac` can actually do it for us with the `+split``
        option, which allows it to make a case disjunction over
        the `if then else` appearing in the context.
       -/
      scalar_tac +split
    progress as ⟨ c4, x1, _, _, hc4 ⟩
    -- Proving the post-condition
    split_conjs
    . simp [*]
    . simp [*]
    . simp [hc4]
      have hxUpdate := toInt_update x.val i.val s2 (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_drop y.val i.val (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      scalar_eq_nf
      -- The best way is to do a case disjunction and treat each sub-case separately
      split at hConv1 <;>
      split at hConv2
      . have hConv1' : (s1.val : Int) = xi.val + c0u.val - U32.size := by scalar_tac
        have hConv2' : (s2.val : Int) = s1.val + yi.val - U32.size := by scalar_tac
        simp [hConv2', hConv1']
        /- `U32.size_eq` is a lemma which allows to simplify `U32.size`.
           But you can also simply do `simp [U32.size]`, which simplifies
           `U32.size` to `2^U32.numBits`, then simplify `U32.numBits`. -/
        simp [*, U32.size_eq]
        scalar_eq_nf
      . have hConv1' : (s1.val : Int) = xi.val + c0u.val - U32.size := by scalar_tac
        simp [hConv2, hConv1']
        simp [*, U32.size_eq]
        scalar_eq_nf
      . have hConv2' : (s2.val : Int) = s1.val + yi.val - U32.size := by scalar_tac
        simp [hConv2', hConv1]
        simp [*, U32.size_eq]
        scalar_eq_nf
      . simp [*]
        scalar_eq_nf
  . simp_all
    scalar_tac
termination_by x.length - i.val
decreasing_by scalar_decr_tac

/-- The proof about `add_with_carry` -/
@[progress]
theorem add_with_carry_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32)
  (hLength : x.length = y.length) :
  ∃ x' c, add_with_carry x y = ok (c, x') ∧
  x'.length = x.length ∧
  c.val ≤ 1 ∧
  toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y := by
  unfold add_with_carry
  progress as ⟨ c, x' ⟩
  simp_all

end tutorial
