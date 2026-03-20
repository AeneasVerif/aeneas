import Lean

/-! "Fast" simp.

A version of simp with `maxDischargeDepth` set by default to 1: this is dramatically faster.
-/

declare_simp_like_tactic fsimp "fsimp " (maxDischargeDepth := 1)
declare_simp_like_tactic (all := true) fsimp_all "fsimp_all " (maxDischargeDepth := 1)

example : True := by fsimp
example (x y z : Nat) (p : Nat → Prop) (h0 : p x) (h1 : p x → p y) (h2 : p y → p z) : p z := by fsimp_all
