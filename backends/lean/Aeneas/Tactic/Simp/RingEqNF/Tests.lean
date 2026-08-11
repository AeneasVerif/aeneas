/-
Copyright (c) 2024 Aeneas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aeneas.Tactic.Simp.RingEqNF.Tactic

/-!
# Tests for `ring_eq_nf`
-/

open Aeneas.RingEqNF

namespace Aeneas.RingEqNF.Tests

/-! ## Full cancellation (closes the goal) -/

-- Both sides normalize to the same expression → closed by ring
example (x y : Int) : 3 * x + 2 * y = 2 * y + 3 * x := by
  ring_eq_nf

example (x y : Nat) : x + y + x = 2 * x + y := by
  ring_eq_nf

/-! ## Hypothesis simplification -/

-- The main example: 3*x + 2*y = x + 3*y → x*2 = y
example (x y : Int) (h : 3 * x + 2 * y = x + 3 * y) : x * 2 = y := by
  ring_eq_nf at h
  exact h

-- Same on Nat
example (x y : Nat) (h : 3 * x + 2 * y = x + 3 * y) : x * 2 = y := by
  ring_eq_nf at h
  exact h

-- Simple: x + y = y → x = 0
example (x y : Nat) (h : x + y = y) : x = 0 := by
  ring_eq_nf at h
  exact h

-- Cancel b from both sides: 3*a + b = a + b → a*2 = 0
example (a b : Int) (h : 3 * a + b = a + b) : a * 2 = 0 := by
  ring_eq_nf at h
  exact h

/-! ## Using the result with ring_nf -/

-- The hypothesis form matches ring_nf convention (base * coeff)
-- Use ring_nf to normalize the goal to match, then exact
example (x y : Int) (h : 3 * x + 2 * y = x + 3 * y) : 2 * x = y := by
  ring_eq_nf at h
  ring_nf
  exact h

example (a b : Int) (h : 3 * a + b = a + b) : 2 * a = 0 := by
  ring_eq_nf at h
  ring_nf
  exact h

/-! ## Goal simplification -/

-- ring_eq_nf applied to a goal (not hypothesis)
-- After ring_eq_nf, the goal is simplified with common terms cancelled
example (x y : Int) (h : x * 2 = y) : 3 * x + 2 * y = x + 3 * y := by
  ring_eq_nf
  exact h

/-! ## Big-integer limb arithmetic

These tests are modelled on the `toInt_update` and `add_with_carry_loop_spec`
proofs from the Aeneas Tutorial where `ring_eq_nf` is used. In those proofs the goals
involve equalities between large polynomial expressions over integer limb
values, powers of 2, and shared sub-expressions that should be cancelled.
-/

-- Inspired by toInt_update, case i = 0:
-- After unfolding toInt for a cons and simplifying with i=0, the goal has the form
-- ↑x + 2^32 * toInt tl = (↑hd + 2^32 * toInt tl) + 1 * (↑x - ↑hd)
-- which simplifies by cancelling the 2^32 * toInt tl on both sides.
example (x hd rest : Int) :
    x + 2 ^ 32 * rest = (hd + 2 ^ 32 * rest) + 1 * (x - hd) := by
  ring_eq_nf

-- Inspired by toInt_update, inductive case:
-- ring_nf expands 2^32 to 4294967296 and distributes, so after cancelling `hd`,
-- the remaining terms still have a common factor 4294967296.
example (hd tl_upd tl_int diff pow32i : Int)
    (h : hd + 2 ^ 32 * tl_upd = hd + 2 ^ 32 * (tl_int + pow32i * diff)) :
    2 ^ 32 * tl_upd = 2 ^ 32 * (tl_int + pow32i * diff) := by
  ring_eq_nf at h
  -- The user-written goal is not in ring_nf form; normalize it to match h
  ring_nf; exact h

-- Cancelling a shared `hd` and `2^32 * tl_int` from both sides
example (hd tl_int pow32i diff : Int) :
    hd + 2 ^ 32 * (tl_int + pow32i * diff) =
    (hd + 2 ^ 32 * tl_int) + 2 ^ 32 * pow32i * diff := by
  ring_eq_nf

-- Inspired by add_with_carry_loop_spec:
-- After inlining toInt_update and toInt_drop, there are large shared terms.
-- The carry-add proof sees a goal roughly like:
-- toInt_x + 2^(32*i) * (s2 - x_i) + c1 * 2^(32*len) =
--   toInt_x + 2^(32*i) * (y_i + 2^32 * rest_y) + c0 * 2^(32*i)
-- which should cancel toInt_x and partially cancel the 2^(32*i) factor.
example (toInt_x s2_val x_i y_i rest_y c0 c1 pow_i pow_len pow32 : Int)
    (h : toInt_x + pow_i * (s2_val - x_i) + c1 * pow_len =
         toInt_x + pow_i * (y_i + pow32 * rest_y) + c0 * pow_i) :
    pow_i * (s2_val - x_i) + c1 * pow_len =
    pow_i * (y_i + pow32 * rest_y) + c0 * pow_i := by
  ring_eq_nf at h
  -- The user-written goal is not in ring_nf form; normalize it to match h.
  -- Note: ring_nf now produces subtraction in the normal form, which ring_eq_nf
  -- doesn't cancel, so we close the remaining gap with omega.
  ring_nf; omega

-- Simpler version: cancel shared addend from both sides of a carry equation
example (a b c d shared : Int)
    (h : shared + a + b = shared + c + d) :
    a + b = c + d := by
  ring_eq_nf at h
  exact h

-- Multiple shared terms
example (a b c x y z : Int)
    (h : a + x + b + y + c = x + y + a + 2 * b + z) :
    c = b + z := by
  ring_eq_nf at h
  exact h

-- With multiplication by constants and powers (like limb arithmetic)
example (limb0 limb1 limb2 v0 v1 v2 : Int) :
    limb0 + 2 ^ 32 * limb1 + 2 ^ 64 * limb2 + (v0 + 2 ^ 32 * v1 + 2 ^ 64 * v2) =
    (limb0 + v0) + 2 ^ 32 * (limb1 + v1) + 2 ^ 64 * (limb2 + v2) := by
  ring_eq_nf

-- Powers of 2 with shared base in hypothesis (full cancellation)
set_option linter.unusedVariables false in
example (a b c : Int) (pow : Int)
    (h : a + pow * b + pow * c = a + pow * (b + c)) : True := by
  ring_eq_nf at h
  trivial

-- Natural number variant with addition (no Nat subtraction)
set_option linter.unusedVariables false in
example (a b c : Nat) (h : a + b + c = b + c + a) : True := by
  ring_eq_nf at h
  trivial

end Aeneas.RingEqNF.Tests
