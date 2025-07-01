import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic
import AeneasMeta.Utils

namespace Aeneas

-- TODO: move
/-- A "structural recursion" range type, that we use to implement for
    loops with structural induction.

    This is the same as `Std.Range`, but with a slighly different implementation
    of the loop inside the `forIn'` function, for which we introduce a fuel parameter.

    We do this because of issues with the kernel reducing definitions eagerly, leading
    to explosions in the presence of well-founded recursion. This this:
    https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/simp.20taking.20a.20long.20time.20on.20a.20small.20definition/near/495050322
  -/
structure MulRange where
  start : Nat := 0
  start_pos : 0 < start
  stop  : Nat
  mul  : Nat
  mul_pos : 1 < mul

instance : Membership Nat MulRange where
  mem r i := r.start ≤ i ∧ i < r.stop ∧ ∃ k, i = r.start * r.mul ^ k

namespace MulRange
universe u v

@[inline] protected def forIn' [Monad m] (range : MulRange) (init : β)
    (f : (i : Nat) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (maxSteps : Nat) (b : β) (i : Nat)
      (hs : ∃ k, i = range.start * range.mul ^ k)
      (hl : range.start ≤ i) : m β := do
    -- Introduce structural induction
    match maxSteps with
    | 0 => pure b
    | maxSteps+1 =>
      if h : i < range.stop then
        match (← f i ⟨hl, h, hs⟩ b) with
        | .done b  => pure b
        | .yield b =>
          have := range.mul_pos
          loop maxSteps b (i * range.mul)
            (by
              have ⟨ k, hk ⟩ := hs
              exists (k + 1)
              simp only [hk]
              simp only [Nat.mul_assoc, Nat.pow_add_one])
            (by
              have := @Nat.le_mul_of_pos_right range.mul i (by omega)
              omega)
      else
        pure b
  loop (range.stop + 1) init range.start (by exists 0; simp) (by omega)

instance : ForIn' m MulRange Nat inferInstance where
  forIn' := MulRange.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

end MulRange

/-!
We now introduce a convenient `mulRange` definition
-/

def mulRange (stop mul : Nat) (hMul : 1 < mul) (i : Nat) (hi : 0 < i) : List Nat :=
  if i < stop then
    i :: mulRange stop mul hMul (i * mul) (by rw [Nat.mul_pos_iff_of_pos_left] <;> omega)
  else []
termination_by stop - i
decreasing_by
  have : i < i * mul := by rw [Nat.lt_mul_iff_one_lt_right] <;> assumption
  omega

namespace MulRange

/-- A convenient utility for the proofs -/
def foldWhile' {α : Type u} (r : MulRange) (f : α → (a : Nat) → (a ∈ r) → α) (i : Nat) (init : α)
  (hi : r.start ≤ i ∧ ∃ k, i = r.start * r.mul ^ k) : α :=
  if h: i < r.stop then
    foldWhile' r f (i * r.mul)
      (f init i (by simp only [Membership.mem]; split_conjs <;> simp [*]))
      (by
        have := r.mul_pos
        split_conjs
        . have := @Nat.le_mul_of_pos_right r.mul i (by omega)
          omega
        . have ⟨ k, hk ⟩ := hi.right
          exists k + 1
          simp only [hk, Nat.mul_assoc, ← Nat.pow_add_one])
  else init
termination_by r.stop - i
decreasing_by
  have := r.mul_pos
  have := r.start_pos
  have : i < i * r.mul := by rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  omega

/-- A convenient utility for the proofs -/
def foldWhile {α : Type u} (stop mul : Nat) (hMul : 1 < mul)
  (f : α → (a : Nat) → α) (i : Nat) (hi : 0 < i) (init : α) : α :=
if i < stop then
    foldWhile stop mul hMul f (i * mul) (by simp only [hi, Nat.mul_pos_iff_of_pos_left]; omega) (f init i)
  else init
termination_by stop - i
decreasing_by
  have : i < i * mul := by rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  omega

end MulRange

end Aeneas
