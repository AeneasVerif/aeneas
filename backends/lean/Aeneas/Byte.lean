import Lean
import Aeneas.SimpLists.Init
import Aeneas.SimpScalar.Init

abbrev Byte := BitVec 8
abbrev Byte.ofNat := BitVec.ofNat 8
abbrev Byte.val (b : Byte) := @BitVec.toNat 8 b
abbrev Byte.testBit (b : Byte) := Nat.testBit b.toNat

@[simp, simp_lists_simps, simp_scalar_simps]
theorem Byte.testBit_default (i : Nat) : (default : Byte).testBit i = false := by simp [Byte.testBit, default]
