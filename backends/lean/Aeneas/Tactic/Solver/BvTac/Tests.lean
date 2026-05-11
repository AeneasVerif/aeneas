import Aeneas.Tactic.Solver.BvTac.BvTac
import Aeneas.Std

/-!
# bv_tac regression tests

Each example must be closed by `bv_tac N`.
-/

open Aeneas Std

example (x y : U8) : (x ||| y).val = 0 ↔ x.val = 0 ∧ y.val = 0 := by
  bv_tac 8

example (x y : U8) : (x ^^^ y).val = 0 ↔ x = y := by
  bv_tac 8

example (a b : U8) : b ^^^ ((a ^^^ b) &&& ⟨0xFF#8⟩) = a := by
  bv_tac 8

example (a b : U8) : b ^^^ ((a ^^^ b) &&& ⟨0x00#8⟩) = b := by
  bv_tac 8

example (x : U32) : (x &&& 65535#u32).val ≤ 65535 := by
  bv_tac 32

example (a : U32) (ha : a.val < 2 * 3329)
    (res : U32) (hres : res = core.num.U32.wrapping_sub a 3329#u32)
    (i : U32) (hi1 : i.val = res.val >>> 16) (hi2 : i.bv = res.bv >>> 16) :
    (decide (i = 0#u32) || decide (i = 65535#u32)) = true := by
  bv_tac 32

example (a : U32) (ha : a.val < 2 * 3329)
    (res : U32) (hres : res = core.num.U32.wrapping_sub a 3329#u32)
    (i : U32) (hi1 : i.val = res.val >>> 16) (hi2 : i.bv = res.bv >>> 16)
    (hmask : (decide (i = 0#u32) || decide (i = 65535#u32)) = true)
    (i2 : U32) (hi2_1 : i2.val = (3329#u32 &&& i).val) (hi2_2 : i2.bv = 3329#32 &&& i.bv)
    (res1 : U32) (hres1 : res1 = core.num.U32.wrapping_add res i2) :
    res1.val < 3329 := by
  bv_tac 32

example (b bMont : U32) (hb : b.val < 3329)
    (hbMont : bMont.val = b.val * 3327#u32 % 65536#u32) :
    bMont.val ≤ 65535 := by
  bv_tac 32

example (b bMont : U32) (hb : b.val < 3329)
    (hbMont : bMont.val = b.val * 3327#u32 % 65536#u32)
    (b1 : U32) (hb1' : b1.val = b.val * 3327#u32)
    (b2 : U32) (hb2 : b2.val = b1.val &&& 65535#u32) :
    bMont = b2 := by
  bv_tac 32
