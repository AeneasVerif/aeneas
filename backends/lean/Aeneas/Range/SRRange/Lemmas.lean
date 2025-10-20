import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Sub.Basic
import Aeneas.Range.SRRange.Basic
import Aeneas.List.List

namespace Aeneas

namespace SRRange

/-!
# Lemmas about `SRRange`

We provide lemmas rewriting for loops over `SRRange` in terms of `List.range'`.
Remark: the lemmas below are adapted from `Std.Range`.
-/

/-- Generalization of `mem_of_mem_range'` used in `forIn'_loop_eq_forIn'_range'` below. -/
private theorem mem_of_mem_range'_aux {r : SRRange} {a : Nat} (w₁ : (i - r.start) % r.step = 0)
    (w₂ : r.start ≤ i)
    (h : a ∈ List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) : a ∈ r := by
  obtain ⟨j, h', rfl⟩ := List.mem_range'.1 h
  refine ⟨by omega, ?_⟩
  rw [Nat.lt_div_iff_mul_lt r.step_pos, Nat.mul_comm] at h'
  constructor
  · omega
  · rwa [Nat.add_comm, Nat.add_sub_assoc w₂, Nat.mul_add_mod_self_left]

theorem mem_of_mem_range' {r : SRRange} (h : x ∈ List.range' r.start r.size r.step) : x ∈ r := by
  unfold size at h
  apply mem_of_mem_range'_aux (by simp) (by simp) h

private theorem size_eq (r : SRRange) (h : i < r.stop) :
    (r.stop - i + r.step - 1) / r.step =
      (r.stop - (i + r.step) + r.step - 1) / r.step + 1 := by
  have w := r.step_pos
  if i + r.step < r.stop then -- Not sure this case split is strictly necessary.
    rw [Nat.div_eq_iff w, Nat.add_one_mul]
    have : (r.stop - (i + r.step) + r.step - 1) / r.step * r.step ≤
        (r.stop - (i + r.step) + r.step - 1) := Nat.div_mul_le_self _ _
    have : r.stop - (i + r.step) + r.step - 1 - r.step <
        (r.stop - (i + r.step) + r.step - 1) / r.step * r.step :=
      Nat.lt_div_mul_self w (by omega)
    omega
  else
    have : (r.stop - i + r.step - 1) / r.step = 1 := by
      rw [Nat.div_eq_iff w, Nat.one_mul]
      omega
    have : (r.stop - (i + r.step) + r.step - 1) / r.step = 0 := by
      rw [Nat.div_eq_iff] <;> omega
    omega

private theorem forIn'_loop_eq_forIn'_range' [Monad m] (r : SRRange)
    (maxSteps : Nat) (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) (i) (w₁) (w₂)
    (hMaxSteps : r.stop - i ≤ maxSteps) :
    forIn'.loop r f maxSteps init i w₁ w₂ =
      forIn' (List.range' i ((r.stop - i + r.step - 1) / r.step) r.step) init
        fun a h => f a (mem_of_mem_range'_aux w₁ w₂ h) := by
  have w := r.step_pos
  revert init i
  induction maxSteps <;> intros init i w₁ w₂ hMaxSteps
  . rw [forIn'.loop]
    simp only [forIn']
    have hEq : (r.stop - i + r.step - 1) / r.step = 0 := by
      have : r.stop - i + r.step - 1 < r.step := by omega
      simp [this]
    simp [hEq]
  . rename_i maxSteps hInd
    rw [forIn'.loop]
    split <;> rename_i h
    · simp only [size_eq r h, List.range'_succ, List.forIn'_cons]
      congr 1
      funext step
      split
      · simp
      · rw [hInd]
        omega
    · have : (r.stop - i + r.step - 1) / r.step = 0 := by
        rw [Nat.div_eq_iff] <;> omega
      simp [this]

@[simp]
theorem forIn'_eq_forIn'_range' [Monad m] (r : SRRange)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
    forIn' r init f =
      forIn' (List.range' r.start r.size r.step) init (fun a h => f a (mem_of_mem_range' h)) := by
  conv => lhs; simp only [forIn', SRRange.forIn']
  simp only [size]
  rw [forIn'_loop_eq_forIn'_range']
  simp [SRRange.sizeBound]

@[simp]
theorem forIn_eq_forIn_range' [Monad m] (r : SRRange)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start r.size r.step) init f := by
  simp only [forIn, forIn'_eq_forIn'_range']

def foldWhile'_step {α : Type u} (r : SRRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : r.start ≤ i ∧ (i - r.start) % r.step = 0)
  (h : i < r.stop) :
  foldWhile' r f i init hi =
  foldWhile' r f (i + r.step)
    (f init i (by simp [Membership.mem]; split_conjs <;> tauto))
    (by split_conjs
        . omega
        . have := @Nat.add_mod_left r.step (i - r.start)
          have : r.step + (i - r.start) = i + r.step - r.start := by omega
          simp_all only)
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

@[simp]
def foldWhile'_id {α : Type u} (r : SRRange) (f : α → (a : Nat) → a ∈ r → α) (i : Nat) (init : α)
  (hi : r.start ≤ i ∧ (i - r.start) % r.step = 0)
  (h : ¬ i < r.stop) :
  foldWhile' r f i init hi = init
  := by
  conv => lhs; unfold foldWhile'
  simp [*]

def foldWhile_step {α : Type u} (max step : Nat) (hStep : 0 < step) (f : α → Nat → α) (i : Nat) (init : α)
  (h : i < max) : foldWhile max step hStep f i init = foldWhile max step hStep f (i + step) (f init i) := by
  conv => lhs; unfold foldWhile
  simp [*]

@[simp]
def foldWhile_id {α : Type u} (max step : Nat) (hStep : 0 < step) (f : α → Nat → α) (i : Nat) (init : α)
  (h : ¬ i < max) : foldWhile max step hStep f i init = init := by
  conv => lhs; unfold foldWhile
  simp [*]

theorem foldl_range'_eq_foldWhile (start len step : Nat) (hStep : 0 < step) (f : α → Nat → α) (init : α) :
  List.foldl f init (List.range' start len step) = foldWhile (start + len * step) step hStep f start init := by
  cases len
  . simp only [List.range'_zero, List.foldl_nil, Nat.zero_mul, Nat.add_zero]
    unfold foldWhile
    simp
  . rename_i len
    simp only [List.range', List.foldl_cons]
    have := foldl_range'_eq_foldWhile (start + step) len step hStep f (f init start)
    simp only [this]
    conv => rhs; unfold foldWhile
    have : start < start + (len + 1) * step := by simp [*]
    simp only [this, ↓reduceIte]
    ring_nf

theorem eq_foldWhile {α} (max step : Nat) (hStep : 0 < step) (f f_body : α → Nat → α) (i) (x)
  (heq : ∀ x i, f x i = if i < max then f (f_body x i) (i + step) else x) :
  f x i = foldWhile max step hStep f_body i x := by
  by_cases hi : i < max
  . unfold foldWhile
    simp [hi]
    have hind := eq_foldWhile max step hStep f f_body (i + step)
    rw [← hind]
    . replace heq := heq x i
      simp [heq, hi]
    . apply heq
  . unfold foldWhile
    simp only [↓reduceIte, heq, hi]
termination_by max - i
decreasing_by simp_wf; omega

theorem foldWhile_shift_start {α : Type u} (max step : Nat) (hStep : 0 < step) (f : α → Nat → α) (start : Nat) (init : α) :
  foldWhile max step hStep f start init = foldWhile (max - start) step hStep (fun x i => f x (i + start)) 0 init := by
  unfold foldWhile
  by_cases h0 : start < max
  . have h0' : 0 < max - start := by omega
    simp only [h0, h0', ↓reduceIte, Nat.zero_add]
    by_cases h1 : start + step < max
    . have := foldWhile_shift_start max step hStep f (start + step) (f init start)
      simp only [this]
      have := foldWhile_shift_start (max - start) step hStep (fun x i => f x (i + start)) step (f init start)
      simp only [this]
      have : max - (start + step) = max - start - step := by omega
      rw [this]; clear this
      have hi i : i + step + start = i + (start + step) := by omega
      simp only [hi]
    . simp [h1, not_false_eq_true, foldWhile_id]
      have h2 : ¬ step < max - start := by omega
      simp only [h2, not_false_eq_true, foldWhile_id]
  . simp [h0]
termination_by max - step - start
decreasing_by all_goals (simp_wf; omega)

theorem foldWhile_forall_eq_imp_eq {α : Type u} (max step : Nat) (hStep : 0 < step)
  (f0 f1 : α → Nat → α) (start : Nat) (init : α)
  (h : ∀ x i, start ≤ i → i < max → f0 x i = f1 x i) :
  foldWhile max step hStep f0 start init = foldWhile max step hStep f1 start init := by
  dcases h0 : start < max <;> unfold foldWhile <;> simp [h0]
  rw [h] <;> try omega
  rw [foldWhile_forall_eq_imp_eq]
  intro x i h0 h1
  apply h <;> omega
termination_by max - start
decreasing_by (simp_wf; omega)

end SRRange

end Aeneas
