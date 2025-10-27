import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Sub.Defs
import Aeneas.Range.DivRange.Basic

namespace Aeneas

-- Auxiliary lemma - TODO: move?
theorem pow_ineq (start divisor : Nat) (hDiv : 1 < divisor) :
  start ≤ divisor ^ (start + 1) := by
  have h0 := Nat.log_le_self divisor start
  have h1 : start < divisor ^ (Nat.log divisor start + 1) :=
    Nat.lt_pow_succ_log_self hDiv start
  have h3 : Nat.log divisor start + 1 ≤ start + 1 := by omega
  have := @Nat.pow_le_pow_right divisor (by omega) _ _  h3
  omega

namespace DivRange

/-!
# Lemmas about `DivRange`

We provide lemmas rewriting for loops over `DivRange` in terms of `List.range'`.
-/

@[simp]
private theorem divRange_loop_zero (stop divisor fuel : Nat) :
  divRange.loop stop divisor fuel 0 = [] := by
  cases fuel <;> simp [divRange.loop]

private theorem mem_of_mem_divRange_loop_aux
  (fuel : Nat) :
  ∀ (start stop divisor a : Nat),
  1 < divisor →
  start ≤ divisor ^ fuel →
  a ∈ divRange.loop stop divisor fuel start →
  stop < a ∧ a ≤ start ∧ ∃ k, a = start / divisor ^ k
  := by
  induction fuel <;> intros start stop divisor a hDiv hStartLe hMem
  . simp only [Nat.pow_zero] at hStartLe
    unfold divRange.loop at hMem
    cases hMem
  . rename_i fuel hInd
    simp only [divRange.loop, gt_iff_lt, List.mem_ite_nil_right, List.mem_cons] at hMem
    replace ⟨ hIneq, hMem ⟩ := hMem
    cases hMem
    . simp_all only [le_refl, true_and]
      exists 0
      simp
    . rename_i hMem
      have hPowIneq : start / divisor ≤ divisor ^ fuel := by
        have h := @Nat.div_le_div_right start (divisor ^ (fuel + 1)) divisor hStartLe
        simp only [Nat.pow_add_one'] at h
        have := @Nat.mul_div_cancel_left (divisor ^ fuel) divisor (by omega)
        simp_all
      replace hInd := hInd (start / divisor) stop divisor a (by omega) hPowIneq hMem
      have : a ≤ start := by
        have := Nat.div_le_self start divisor
        omega
      simp only [true_and, hInd, this]
      have ⟨ k, hkEq ⟩ := hInd.right.right
      exists (k + 1)
      simp [hkEq, Nat.div_div_eq_div_mul, Nat.pow_add_one']

private theorem mem_of_mem_divRange (r : DivRange) (a : Nat)
    (h : a ∈ divRange r.start r.stop r.divisor) : a ∈ r := by
  have hDiv := r.divisor_pos
  have h0 := Nat.log_le_self r.divisor r.start
  have h1 : r.start < r.divisor ^ (Nat.log r.divisor r.start + 1) :=
    Nat.lt_pow_succ_log_self hDiv r.start
  have h2 : r.start + 1 ≤ r.divisor ^ (Nat.log r.divisor r.start + 1) := by omega
  have h3 : Nat.log r.divisor r.start + 1 ≤ r.start + 1 := by omega
  have := @Nat.pow_le_pow_right r.divisor (by omega) _ _  h3
  have hStartLe : r.start ≤ r.divisor ^ (r.start + 1) := by omega

  have := mem_of_mem_divRange_loop_aux (r.start + 1) r.start r.stop r.divisor a hDiv
            hStartLe (by simp_all [divRange])
  simp [Membership.mem, this]

private theorem mem_of_mem_divRange_loop (r : DivRange) (i : Nat) (fuel a : Nat)
  (hStart : i ≤ r.start)
  (hFuel : i ≤ r.divisor ^ fuel)
  (hᵢ : ∃ k, i = r.start / r.divisor ^ k)
  (hMem : a ∈ divRange.loop r.stop r.divisor fuel i) :
  r.stop < a ∧ a ≤ r.start ∧ ∃ k, a = r.start / r.divisor ^ k
  := by
  have h := mem_of_mem_divRange_loop_aux fuel i r.stop r.divisor a r.divisor_pos hFuel hMem
  split_conjs
  . omega
  . omega
  . have ⟨ k, hk ⟩ := hᵢ
    have ⟨ k', hk' ⟩ := h.right.right
    exists (k + k')
    simp [*, Nat.div_div_eq_div_mul, Nat.pow_add]

private theorem forIn'_loop_eq_forIn'_divRange [Monad m] (r : DivRange)
    (fuel : Nat) (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) (i) (hk : ∃ k, i = r.start / r.divisor ^ k)
    (hStart : i ≤ r.start) (hFuel : i ≤ r.divisor ^ fuel) :
    forIn'.loop r f fuel init i hk hStart =
      forIn' (divRange.loop r.stop r.divisor fuel i) init
        fun a h =>
          f a (mem_of_mem_divRange_loop r i fuel a hStart hFuel hk h) := by
  cases fuel
  . rw [forIn'.loop]
    simp [divRange.loop]
  . rename_i fuel
    simp only [forIn'.loop, divRange.loop, gt_iff_lt]
    dcases hStop : r.stop < i <;> simp only [hStop, ↓reduceDIte, ↓reduceIte, List.forIn'_nil, List.forIn'_cons]
    apply bind_congr
    intro x
    cases x
    . simp
    . rename_i x
      simp only
      replace ⟨ k, hk ⟩ := hk
      have hiDiv : ∃ k, i / r.divisor = r.start / r.divisor ^ k := by
        exists (k + 1)
        simp [hk, Nat.div_div_eq_div_mul, Nat.pow_add]
      have hiLe : i / r.divisor ≤ r.start := by
        have := Nat.div_le_self i r.divisor
        omega
      have hiDivLe : i / r.divisor ≤ r.divisor ^ fuel := by
        have h1 := @Nat.div_le_div_right _ _ r.divisor hFuel
        have h2 : r.divisor = r.divisor ^ 1 := by simp
        conv at h1 => rhs; rhs; rw [h2]
        rw [Nat.pow_div] at h1 <;> try omega
        . simp only [Nat.add_one_sub_one] at h1
          apply h1
        . have := r.divisor_pos
          omega
      have hEq := forIn'_loop_eq_forIn'_divRange r fuel x f (i / r.divisor) hiDiv hiLe hiDivLe
      simp [hEq]

-- Auxiliary lemma
private theorem pow_ineq (r: DivRange) :
  r.start ≤ r.divisor ^ (r.start + 1) := by
  cases r; apply Aeneas.pow_ineq; simp; assumption

@[simp] theorem forIn_eq_forIn_divRange [Monad m] (r : DivRange)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (divRange r.start r.stop r.divisor ) init f := by
  simp only [forIn, forIn', divRange, DivRange.forIn']
  rw [forIn'_loop_eq_forIn'_divRange]
  . simp
  . apply pow_ineq

@[simp] theorem forIn'_eq_forIn_divRange [Monad m] (r : DivRange)
    (init : β) (f : (a:Nat) → (a ∈ r) → β → m (ForInStep β)) :
    forIn' r init f =
      forIn' (divRange r.start r.stop r.divisor ) init
        (fun a h => f a (mem_of_mem_divRange r a h)) := by
  simp only [forIn', divRange, DivRange.forIn']
  rw [forIn'_loop_eq_forIn'_divRange]
  . simp
  . apply pow_ineq

@[simp]
def foldWhile'_step {α : Type u} (r : DivRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : i ≤ r.start ∧ ∃ k, i = r.start / r.divisor ^ k)
  (h : r.stop < i) :
  foldWhile' r f i init hi =
  foldWhile' r f (i / r.divisor)
    (f init i (by simp only [Membership.mem]; split_conjs <;> simp [*]))
      (by split_conjs
          . have := Nat.div_le_self i r.divisor; omega
          . have ⟨ k, hk ⟩ := hi.right
            exists k + 1
            simp [hk, Nat.div_div_eq_div_mul, ← Nat.pow_add_one])
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

@[simp]
def foldWhile'_id {α : Type u} (r : DivRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : i ≤ r.start ∧ ∃ k, i = r.start / r.divisor ^ k)
  (h : ¬ r.stop < i) :
  foldWhile' r f i init hi = init
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

@[simp]
def foldWhile_step {α : Type u} (stop divisor : Nat) (hDiv : 1 < divisor)
  (f : α → Nat → α) (i : Nat) (init : α) (h : stop < i) :
  foldWhile stop divisor hDiv f i init = foldWhile stop divisor hDiv f (i / divisor) (f init i) := by
  conv => lhs; unfold foldWhile
  simp [*]

@[simp]
def foldWhile_id {α : Type u} (stop divisor : Nat) (hDiv : 1 < divisor)
  (f : α → Nat → α) (i : Nat) (init : α) (h : ¬ stop < i) :
  foldWhile stop divisor hDiv f i init = init := by
  conv => lhs; unfold foldWhile
  simp [*]

private theorem divRange.loop_le_maxSteps_eq (stop div maxSteps start : Nat) (hDiv : 1 < div) (hMaxSteps : start + 1 ≤ maxSteps) :
  divRange.loop stop div maxSteps start = divRange.loop stop div (start + 1) start := by
  cases maxSteps
  . omega
  . rename_i maxSteps
    unfold divRange.loop
    dcases h: stop < start
    . simp only [gt_iff_lt, h, ↓reduceIte, List.cons.injEq, true_and]
      have : start / div < start := by apply Nat.div_lt_self <;> omega
      have h1 : start / div + 1 ≤ maxSteps := by omega
      have := divRange.loop_le_maxSteps_eq stop div maxSteps (start / div) hDiv h1
      rw [this]
      have h2 : start / div + 1 ≤ start := by omega
      have := divRange.loop_le_maxSteps_eq stop div start (start / div) hDiv h2
      rw [this]
    .simp [h]

private theorem foldl_divRange_loop_foldWhile (start stop div maxSteps : Nat) (hMaxSteps : start + 1 ≤ maxSteps)
  (hDiv : 1 < div) (f : α → Nat → α) (init : α) :
  List.foldl f init (divRange.loop stop div maxSteps start) = foldWhile stop div hDiv f start init := by
  cases maxSteps
  . omega
  . rename_i maxSteps
    unfold divRange.loop foldWhile
    dcases h: stop < start
    . simp only [gt_iff_lt, h, ↓reduceIte, List.foldl_cons]
      rw [foldl_divRange_loop_foldWhile]
      have : start / div < start := by apply Nat.div_lt_self <;> omega
      omega
    . simp [h]

@[simp]
theorem foldl_divRange_foldWhile (start stop div : Nat) (hDiv : 1 < div) (f : α → Nat → α) (init : α) :
  List.foldl f init (divRange start stop div) = foldWhile stop div hDiv f start init := by
  unfold divRange
  rw [foldl_divRange_loop_foldWhile]
  simp

end DivRange

end Aeneas
