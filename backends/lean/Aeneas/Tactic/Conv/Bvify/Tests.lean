import Aeneas.Tactic.Conv.Bvify.Bvify
import Aeneas.Std

/-!
# bvify regression tests

`bvify N` lifts `.val` (Nat) goals to `.bv` (BitVec) goals.
`#guard_msgs` constrains the resulting unsolved goal after `bvify`.
-/

open Aeneas Std

/--
error: unsolved goals
a b : U32
h : a.bv < 3329#32
h2 : b.bv < 3329#32
⊢ a.bv &&& 65535#32 ≤ 65535#32
-/
#guard_msgs in
example (a b : U32) (h : a.val < 3329) (h2 : b.val < 3329) :
    (a &&& 65535#u32).val ≤ 65535 := by
  bvify 32 at *

/--
error: unsolved goals
x y : U8
⊢ x.bv ^^^ y.bv = 0#8 ↔ x.bv = y.bv
-/
#guard_msgs in
example (x y : U8) : (x ^^^ y).val = 0 ↔ x = y := by
  bvify 8

/--
error: unsolved goals
a res i : U32
hi2 : i.bv = res.bv >>> 16
ha : a.bv < 6658#32
hres : res.bv = a.bv - 3329#32
⊢ i.bv = 0#32 ∨ i.bv = 65535#32
-/
#guard_msgs in
example (a : U32) (ha : a.val < 2 * 3329)
    (res : U32) (hres : res = core.num.U32.wrapping_sub a 3329#u32)
    (i : U32) (hi2 : i.bv = res.bv >>> 16) :
    i = 0#u32 ∨ i = 65535#u32 := by
  bvify 32 at *
