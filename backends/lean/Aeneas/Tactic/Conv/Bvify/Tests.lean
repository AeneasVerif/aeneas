module
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

/--
error: unsolved goals
a b : Usize
h : a.bv < b.bv
⊢ a.bv ≤ b.bv
-/
#guard_msgs in
example (a b : Usize) (h : a < b) : a ≤ b := by
  bvify System.Platform.numBits at *

/-!
# `bvify ... by`
-/

/- `bvify` gets stuck on the subtraction: `scalar_tac` can not prove `y.val ≤ x.val` -/
/--
error: unsolved goals
x y z : U8
h0 : ↑y * ↑y ≤ ↑x * ↑x
h : BitVec.ofNat 8 (↑x - ↑y) = z.bv
⊢ x.bv - y.bv = z.bv
-/
#guard_msgs in
example (x y z : U8) (h0 : y.val * y.val ≤ x.val * x.val) (h : x.val - y.val = z.val) :
    x.bv - y.bv = z.bv := by
  bvify 8 at h

/- `bvify ... by` lifts the hypothesis, and we prove the equivalence ourselves -/
example (x y z : U8) (h0 : y.val * y.val ≤ x.val * x.val) (h : x.val - y.val = z.val) :
    x.bv - y.bv = z.bv := by
  bvify 8 at h by
    have : y.val ≤ x.val := Nat.mul_self_le_mul_self_iff.mp h0
    natify; simp_scalar
  exact h

/- The goal the tactic has to prove -/
/--
error: bvify: the tactic did not prove that the lifted proposition is equivalent to the original one:
x y z : U8
h0 : ↑y * ↑y ≤ ↑x * ↑x
h : ↑x - ↑y = ↑z
⊢ ↑x - ↑y = ↑z ↔ x.bv - y.bv = z.bv
-/
#guard_msgs in
example (x y z : U8) (h0 : y.val * y.val ≤ x.val * x.val) (h : x.val - y.val = z.val) :
    x.bv - y.bv = z.bv := by
  bvify 8 at h by skip

/- Lifting the goal -/
/--
error: unsolved goals
x y z : U8
h0 : ↑y * ↑y ≤ ↑x * ↑x
⊢ x.bv - y.bv = z.bv
-/
#guard_msgs in
example (x y z : U8) (h0 : y.val * y.val ≤ x.val * x.val) :
    x.val - y.val = z.val := by
  bvify 8 by
    have : y.val ≤ x.val := Nat.mul_self_le_mul_self_iff.mp h0
    bvify 8

/- There is nothing to lift -/
/--
error: bvify: could not lift
  x.bv < y.bv
-/
#guard_msgs in
example (x y : U8) (h : x.bv < y.bv) : x.bv < y.bv := by
  bvify 8 at h by simp

/- `bvify ... by` lifts a single proposition -/
/--
error: `bvify ... by` lifts a single proposition: expected `at h`
-/
#guard_msgs in
example (x y : U8) (h : x.val < y.val) : x.bv < y.bv := by
  bvify 8 at * by simp
