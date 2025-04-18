import Lean

abbrev Byte := BitVec 8
abbrev Byte.ofNat := BitVec.ofNat 8
abbrev Byte.val (b : Byte) := @BitVec.toNat 8 b
abbrev Byte.testBit (b : Byte) := Nat.testBit b.toNat
