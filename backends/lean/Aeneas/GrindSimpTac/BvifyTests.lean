import Aeneas.GrindSimpTac.Bvify

/-!
# Tests for `gbvify`

These mirror examples from `Aeneas.Bvify.Bvify`.
-/

open Aeneas Aeneas.Arith Aeneas.Std

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  gbvify 8 at h
  apply h

example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  gbvify 8 at *
  bv_decide

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  gbvify 8 at h
  apply h

example (x : U8) (h : x.val < 32) : x.bv < 32#8 := by
  gbvify 8 at *
  apply h

example (a : U32) (h : a.val = 3329) : a.bv = 3329#32 := by
  gbvify 32 at *
  apply h

/--
info: example
  (a : U32)
  (b : U32)
  (c : U32)
  (h0 : c.bv ≤ 3329#32)
  (h1 : a.bv + b.bv ≤ 3329#32 + c.bv) :
  a.bv + b.bv ≤ 3329#32 + c.bv
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (a b c : U32) (h0 : c.val ≤ 3329) (h1 : a.val + b.val ≤ 3329 + c.val) : a.bv + b.bv ≤ 3329#32 + c.bv := by
  gbvify 32 at *
  extract_goal1
  assumption

example (n a : Nat) (h : a < 2^n) : BitVec.ofNat n a ≤ BitVec.ofNat n (2^n - 1) := by
  gbvify n at *
  tauto

/--
info: example
  (a : U32)
  (b : U32)
  (c : U32)
  (h : a.bv + b.bv < 32#32)
  (hc : c.bv = a.bv + b.bv) :
  c.bv % 32#32 = (a.bv + b.bv) % 32#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example
  (a b c : U32) (h : a.val + b.val < 32) (hc : c.val = a.val + b.val) :
  (c.val : ZMod 32) = (a.val : ZMod 32) + (b.val : ZMod 32) := by
  gbvify 32 at *
  extract_goal1
  bv_decide

example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (c1 : U32)
  (hc1 : (↑c1 : ℕ) = (↑a : ℕ) + (↑b : ℕ))
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv - 3329#32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16)
  (c4 : U32)
  (hc4 : (↑c4 : ℕ) = (↑(3329#u32 &&& c3) : ℕ))
  (_ : c4.bv = 3329#32 &&& c3.bv)
  (c5 : U32)
  (hc5 : c5.bv = c2.bv + c4.bv) :
  (c5.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329) ∧ c5.val < 3329
  := by
  gbvify 32 at *
  simp_all only
  bv_decide

example
  (a : U32)
  (b : U32)
  (_ : a.val ≤ 6658)
  (ha : a.val < b.val + 3329)
  (hb : b.val ≤ 3329)
  (c1 : U32)
  (hc1 : c1.bv = a.bv - b.bv)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = c1.bv + c3.bv) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329) ∧
  c4.val < 3329
  := by
  gbvify 32 at *
  simp_all only
  bv_decide

example
  (x : U16) (_ : x.val < 3329)
  (y : U32) (_ : y = core.convert.num.FromU32U16.from x) :
  y.val = x.val
  := by
  gbvify 32 at *
  bv_decide

example
  (x : U32) (_ : x.val < 3329)
  (y : U16) (_ : y = UScalar.cast UScalarTy.U16 x) :
  y.val = x.val
  := by
  gbvify 16 at *
  bv_decide

grind_pattern [agrind] Nat.shiftRight_le => m >>> n
  where
    not_value n

grind_pattern [agrind] Nat.shiftRight_eq_div_pow => m >>> n where
  is_strict_value n
  is_ground n

example (x : Nat) : x >>> 31 ≤ x := by agrind

example (x : U64) : x.val >>> 31 < 2^33 := by
  gbvify 64
  bv_decide

example (n : Nat) (x : U64) : x.val >>> n ≤ 2^64 - 1 := by
  gbvify 64
  bv_decide

/--
info: example
  (x : U32)
  (a : U32)
  (b : U32)
  (h : x.bv = a.bv + b.bv) :
  x.bv % 3329#32 = (a.bv + b.bv) % 3329#32
  := by sorry
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (x a b : U32) (h : x.val = a.val + b.val) : (x.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329) := by
  gbvify 32 at *
  extract_goal1
  simp [h]

example (byte : U8) : 8 ∣ (byte &&& 16#u8).val := by
  gbvify 8; bv_decide
