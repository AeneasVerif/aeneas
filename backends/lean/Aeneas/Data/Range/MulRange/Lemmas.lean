import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Tactic.Ring.RingNF
import Aeneas.Range.MulRange.Basic
import Aeneas.Range.DivRange.Lemmas

namespace Aeneas

-- Auxiliary lemma
theorem pow_ineq' (stop mul start : Nat) (hMul : 1 < mul) (hStart : 0 < start) :
  stop ≤ start * mul ^ (stop + 1):= by
  have := pow_ineq stop mul hMul
  have := @Nat.le_mul_of_pos_right start (mul ^ (stop + 1)) hStart
  rw [Nat.mul_comm] at this
  omega

namespace MulRange

theorem mulRange_step (stop mul : Nat) (hMul : 1 < mul) (i : Nat) (hi : 0 < i) (hi' : i < stop) :
  Aeneas.mulRange stop mul hMul i hi = i :: Aeneas.mulRange stop mul hMul (i * mul) (by rw [Nat.mul_pos_iff_of_pos_left] <;> omega) := by
  conv => lhs; unfold Aeneas.mulRange
  simp [hi']

theorem mulRange_nil (stop mul : Nat) (hMul : 1 < mul) (i : Nat) (hi : 0 < i) (hi' : stop ≤ i) :
  Aeneas.mulRange stop mul hMul i hi = [] := by
  conv => lhs; unfold Aeneas.mulRange
  simp [hi']

/-!
# Lemmas about `MulRange`

We provide lemmas rewriting for loops over `MulRange` in terms of `List.range'`.
-/

private theorem mem_of_mem_MulRange_aux
  (stop mul start : Nat) (hMul : 1 < mul) (i : Nat) (hi : 0 < i ∧ ∃ k, i = start * mul ^ k)
  (a : Nat) :
  a ∈ mulRange stop mul hMul i hi.left →
  start ≤ a ∧ a < stop ∧ ∃ k, a = start * mul ^ k
  := by
  unfold mulRange
  dcases h: i < stop
  . simp only [h, ↓reduceIte, List.mem_cons]
    intro hMem
    cases hMem
    . simp_all only [and_self, and_true]
      have ⟨ k, hk ⟩ := hi.right
      have := Nat.one_le_pow k mul (by omega)
      have := @Nat.le_mul_of_pos_right (mul ^ k) start (by omega)
      omega
    . rename_i hMem
      apply mem_of_mem_MulRange_aux stop mul start hMul (i * mul)
        (by
          split_conjs
          . apply Nat.mul_pos <;> omega
          . have ⟨ k, hk ⟩ := hi.right
            exists k + 1
            simp [hk, mul_assoc, ← Nat.pow_add_one])
        a hMem
  . simp_all
termination_by stop - i
decreasing_by
  have : i < i * mul := by rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  omega

private theorem mem_of_mem_MulRange (r : MulRange) (a : Nat)
  (h : a ∈ mulRange r.stop r.mul r.mul_pos r.start r.start_pos) : a ∈ r := by
  apply mem_of_mem_MulRange_aux r.stop r.mul r.start r.mul_pos r.start
    (by
      simp [r.start_pos]
      exists 0; simp)
    a h

@[simp]
private theorem i_of_MulRange_start_pos (r : MulRange) (i : Nat) (hi : ∃ k, i = r.start * r.mul ^ k):
  0 < i := by
  have ⟨ k, hk ⟩ := hi
  simp only [hk]
  apply Nat.mul_pos
  . apply r.start_pos
  . apply Nat.pow_pos
    have := r.mul_pos
    omega

private theorem mem_of_mem_MulRange_i (r : MulRange)
  (i : Nat) (h1 : ∃ k, i = r.start * r.mul ^ k) (a : Nat)
  (h : a ∈ mulRange r.stop r.mul r.mul_pos i
    (by apply i_of_MulRange_start_pos; assumption)) : a ∈ r := by
  apply mem_of_mem_MulRange_aux r.stop r.mul r.start r.mul_pos i
    (by
      split_conjs
      . apply i_of_MulRange_start_pos; assumption
      . apply h1)
    a h

private theorem forIn'_loop_eq_forIn'_MulRange [Monad m] (r : MulRange)
    (fuel : Nat) (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) (i)
    (hk : ∃ k, i = r.start * r.mul ^ k)
    (hStart : r.start ≤ i)
    (hFuel : r.stop ≤ i * r.mul ^ fuel) :
    forIn'.loop r f fuel init i hk hStart =
      forIn' (mulRange r.stop r.mul r.mul_pos i (by have := r.start_pos; omega)) init
        fun a h =>
          f a (mem_of_mem_MulRange_i r i hk a h) := by
  cases fuel
  . rw [forIn'.loop]
    simp only [pow_zero, mul_one] at hFuel
    unfold mulRange
    have : ¬ i < r.stop := by omega
    simp [*]
  . rename_i fuel
    simp only [forIn'.loop]
    unfold mulRange
    dcases hStop : i < r.stop <;> simp only [hStop, ↓reduceDIte, ↓reduceIte, List.forIn'_cons, List.forIn'_nil]
    apply bind_congr
    intro x
    cases x
    . simp
    . rename_i x
      simp only
      replace ⟨ k, hk ⟩ := hk
      have := r.mul_pos
      have h0 : ∃ k, i * r.mul = r.start * r.mul ^ k := by
        exists (k + 1)
        simp [hk, Nat.mul_assoc, Nat.pow_add]
      have h1 : r.start ≤ i * r.mul := by
        have := @Nat.le_mul_of_pos_right r.mul i (by omega)
        omega
      have h2 : r.stop ≤ i * r.mul * r.mul ^ fuel := by
        simp only [Nat.pow_add_one] at hFuel
        ring_nf at hFuel
        apply hFuel
      have hEq := forIn'_loop_eq_forIn'_MulRange r fuel x f (i * r.mul) h0 h1 h2
      simp [hEq]

-- Auxiliary lemma
private theorem pow_ineq (r: MulRange) :
  r.stop ≤ r.start * r.mul ^ (r.stop + 1) := by
  apply pow_ineq' r.stop r.mul r.start r.mul_pos r.start_pos

@[simp] theorem forIn_eq_forIn_MulRange [Monad m] (r : MulRange)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (mulRange r.stop r.mul r.mul_pos r.start r.start_pos) init f := by
  simp only [forIn, forIn', MulRange.forIn']
  rw [forIn'_loop_eq_forIn'_MulRange]
  . simp
  . apply pow_ineq

@[simp] theorem forIn'_eq_forIn_MulRange [Monad m] (r : MulRange)
    (init : β) (f : (a:Nat) → (a ∈ r) → β → m (ForInStep β)) :
    forIn' r init f =
      forIn' (mulRange r.stop r.mul r.mul_pos r.start r.start_pos) init
        (fun a h => f a (mem_of_mem_MulRange r a h)) := by
  simp only [forIn', MulRange.forIn']
  rw [forIn'_loop_eq_forIn'_MulRange]
  . simp
  . apply pow_ineq

private theorem MulRange_imp_pred (r : MulRange) (i : Nat)
  (h0: r.start ≤ i ∧ ∃ k, i = r.start * r.mul ^ k) :
  r.start ≤ i * r.mul ∧ ∃ k, i * r.mul = r.start * r.mul ^ k := by
  have := r.mul_pos
  split_conjs
  . have := @Nat.le_mul_of_pos_right r.mul i (by omega)
    omega
  . have ⟨ k, hk ⟩ := h0.right
    exists k + 1
    simp [hk, Nat.mul_assoc, ← Nat.pow_add_one]

@[simp]
def foldWhile'_step {α : Type u} (r : MulRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : r.start ≤ i ∧ ∃ k, i = r.start * r.mul ^ k)
  (h : i < r.stop) :
  foldWhile' r f i init hi =
  foldWhile' r f (i * r.mul)
    (f init i (by simp only [Membership.mem]; split_conjs <;> simp [*]))
      (by apply MulRange_imp_pred; assumption)
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

@[simp]
def foldWhile'_id {α : Type u} (r : MulRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : r.start ≤ i ∧ ∃ k, i = r.start * r.mul ^ k) (h : ¬ i < r.stop) :
  foldWhile' r f i init hi = init
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

@[simp]
def foldWhile_step {α : Type u} (stop mul : Nat) (f : α → Nat → α) (i : Nat)
  (init : α) (hMul) (hi : 0 < i) (h : i < stop) :
  foldWhile stop mul hMul f i hi init =
    foldWhile stop mul hMul f (i * mul)
      (by apply Nat.mul_pos <;> omega) (f init i)
  := by
  conv => lhs; unfold foldWhile
  simp [*]

@[simp]
def foldWhile_id {α : Type u} (stop mul : Nat) (f : α → Nat → α) (i : Nat)
  (init : α) (hMul) (hi : 0 < i) (h : ¬ i < stop) :
  foldWhile stop mul hMul f i hi init = init := by
  conv => lhs; unfold foldWhile
  simp [*]

@[simp]
theorem foldl_MulRange_foldWhile (stop mul i : Nat) (hMul) (hi)
  (f : α → Nat → α) (init : α) :
  List.foldl f init (mulRange stop mul hMul i hi) = foldWhile stop mul hMul f i hi init := by
  unfold mulRange foldWhile
  by_cases h: i < stop <;> simp only [h, ↓reduceIte, List.foldl_cons, List.foldl_nil]
  rw [foldl_MulRange_foldWhile]
termination_by stop - i
decreasing_by
  have : i < i * mul := by rw [Nat.lt_mul_iff_one_lt_right] <;> assumption
  omega

end MulRange

end Aeneas
