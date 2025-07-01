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
structure DivRange where
  start : Nat := 0
  stop  : Nat
  divisor  : Nat
  divisor_pos : 1 < divisor

instance : Membership Nat DivRange where
  mem r i := r.stop < i ∧ i ≤ r.start ∧ ∃ k, i = r.start / r.divisor ^ k

namespace DivRange
universe u v

@[inline] protected def forIn' [Monad m] (range : DivRange) (init : β)
    (f : (i : Nat) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (maxSteps : Nat) (b : β) (i : Nat)
      (hs : ∃ k, i = range.start / range.divisor ^ k)
      (hl : i ≤ range.start) : m β := do
    -- Introduce structural induction
    match maxSteps with
    | 0 => pure b
    | maxSteps+1 =>
      if h : range.stop < i then
        match (← f i ⟨h, hl, hs⟩ b) with
        | .done b  => pure b
        | .yield b =>
          have := range.divisor_pos
          loop maxSteps b (i / range.divisor)
            (by
              have ⟨ k, hk ⟩ := hs
              exists (k + 1)
              simp only [hk]
              simp [Nat.div_div_eq_div_mul, Nat.pow_add_one])
            (by
              have := @Nat.div_le_self i range.divisor
              omega)
      else
        pure b
  loop (range.start + 1) init range.start (by exists 0; simp) (by omega)

instance : ForIn' m DivRange Nat inferInstance where
  forIn' := DivRange.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

end DivRange

/-!
We now introduce a convenient `DivRange` definition
-/

-- TODO: don't use a fuel
def divRange (start stop div : Nat) : List Nat :=
  let rec loop (fuel i : Nat) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if i > stop then
        i :: loop fuel (i / div)
      else []
  loop (start + 1) start

namespace DivRange

/-- A convenient utility for the proofs -/
def foldWhile' {α : Type u} (r : DivRange) (f : α → (a : Nat) → (a ∈ r) → α) (i : Nat) (init : α)
  (hi : i ≤ r.start ∧ ∃ k, i = r.start / r.divisor ^ k) : α :=
  if h: r.stop < i then
    foldWhile' r f (i / r.divisor)
      (f init i (by simp [Membership.mem]; split_conjs <;> simp [*]))
      (by split_conjs
          . have := Nat.div_le_self i r.divisor; omega
          . have ⟨ k, hk ⟩ := hi.right
            exists k + 1
            simp [hk, Nat.div_div_eq_div_mul, ← Nat.pow_add_one])
  else init
termination_by i
decreasing_by apply Nat.div_lt_self; omega; apply r.divisor_pos

/-- A convenient utility for the proofs -/
def foldWhile {α : Type u} (stop divisor : Nat) (hDiv : 1 < divisor)
  (f : α → (a : Nat) → α) (i : Nat) (init : α) : α :=
if stop < i then
    foldWhile stop divisor hDiv f (i / divisor) (f init i)
  else init
termination_by i
decreasing_by apply Nat.div_lt_self; omega; apply hDiv

end DivRange

end Aeneas
