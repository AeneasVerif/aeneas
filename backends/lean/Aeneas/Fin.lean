import Lean
import Mathlib.Tactic.OfNat
import Aeneas.ScalarTac.ScalarTac

attribute [scalar_tac_simps] Fin.val_ofNat

@[scalar_tac Fin.val x]
theorem Fin.val_le {n : Nat} (x : Fin n) :
  x.val < n := by omega
