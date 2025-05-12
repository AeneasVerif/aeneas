import Lean
import Mathlib.Tactic.OfNat
import Aeneas.ScalarTac.ScalarTac

@[simp, scalar_tac_simps]
theorem Fin.val_ofNat{n: Nat}[NeZero n]{x: Nat} :
  (ofNat(x): Fin n).val = x % n := by simp [OfNat.ofNat, Fin.instOfNat]

@[scalar_tac Fin.val x]
theorem Fin.val_le {n : Nat} (x : Fin n) :
  x.val < n := by omega
