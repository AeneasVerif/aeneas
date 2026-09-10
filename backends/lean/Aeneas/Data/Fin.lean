module
public import Lean
public import Mathlib.Tactic.OfNat
public import Aeneas.Tactic.Solver.ScalarTac.ScalarTac
public section

attribute [scalar_tac_simps] Fin.val_ofNat

@[scalar_tac Fin.val x]
theorem Fin.val_le {n : Nat} (x : Fin n) :
  x.val < n := by omega
