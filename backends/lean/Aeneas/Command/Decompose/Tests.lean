/-
Tests for the #decompose command
-/
import Aeneas.Command.Decompose
import Aeneas.Std

open Aeneas.Std
open Aeneas.Command.Decompose

-- ============================================================================
-- Test 1: Simple letRange — extract first 3 bindings
-- ============================================================================

def test1 (x y : U32) : Result U32 := do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  let x3 ← x2 + 1#u32
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  let y3 ← y2 + 1#u32
  x3 + y3

#decompose test1 test1_eq
  letRange 0 3 => test1_x
  letRange 1 3 => test1_y

#check @test1_x  -- U32 → Result U32
#check @test1_y  -- U32 → Result U32
#check @test1_eq -- ∀ (x y : U32), test1 x y = ...

-- ============================================================================
-- Test 2: Tuple return — continuation needs multiple variables
-- ============================================================================

def test2 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← 2#u32 * x
  a + b

#decompose test2 test2_eq
  letRange 0 2 => test2_aux

#check @test2_aux  -- U32 → Result (U32 × U32)
#check @test2_eq

-- ============================================================================
-- Test 3: Branch + letRange + full
-- ============================================================================

def test3 (b : Bool) (x y : U32) : Result U32 := do
  if b then
    let x1 ← x + 1#u32
    let x2 ← x1 + 1#u32
    let x3 ← x2 + 1#u32
    let y1 ← y + 1#u32
    let y2 ← y1 + 1#u32
    let y3 ← y2 + 1#u32
    x3 + y3
  else
    x + y

#decompose test3 test3_eq
  branch 0 (letRange 0 3) => test3_x
  branch 0 (letRange 1 3) => test3_y
  branch 0 full => test3_then

#check @test3_x
#check @test3_y
#check @test3_then
#check @test3_eq

-- ============================================================================
-- Test 4: Full extraction (proof by rfl)
-- ============================================================================

def test4 (x y : U32) : Result U32 := do
  let z ← x + y
  z + 1#u32

#decompose test4 test4_eq
  full => test4_body

#check @test4_body
#check @test4_eq

-- ============================================================================
-- Test 5: letRange including terminal (proof by rfl)
-- ============================================================================

def test5 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 1#u32
  b + 1#u32

#decompose test5 test5_eq
  letRange 0 3 => test5_all

#check @test5_all
#check @test5_eq

-- ============================================================================
-- Test 6: Pure let-bindings
-- ============================================================================

def test6 (x : Nat) : Nat :=
  let a := x + 1
  let b := a + 2
  let c := b + 3
  c + 4

#decompose test6 test6_eq
  letRange 0 3 => test6_aux

#check @test6_aux
#check @test6_eq

-- ============================================================================
-- Test 7: Verify the generated theorems have no sorry
-- ============================================================================

-- These should all type-check without sorry warnings
#print axioms test1_eq
#print axioms test2_eq
#print axioms test3_eq
#print axioms test4_eq
#print axioms test5_eq
#print axioms test6_eq

-- ============================================================================
-- Test 8: Noncomputable functions
-- ============================================================================

noncomputable opaque wipeSlice : Slice U8 → Result Unit

noncomputable def test8 (x : U32) (s : Slice U8) : Result U32 := do
  let a ← x + 1#u32
  let _ ← wipeSlice s
  a + 2#u32

#decompose test8 test8_eq
full => test8_body

-- Verify
#print axioms test8_eq

-- ============================================================================
-- Test 9: Side-effect only range (monadic, continuation uses no range variables)
-- ============================================================================

noncomputable opaque sideEffect1 : U32 → Result Unit
noncomputable opaque sideEffect2 : U32 → Result Unit

noncomputable def test9 (x y : U32) : Result U32 := do
  let _ ← sideEffect1 x
  let _ ← sideEffect2 y
  pure 42#u32

-- Extract the two side-effect bindings — continuation uses none of them
#decompose test9 test9_eq
  letRange 0 2 => test9_effects

#check @test9_effects  -- should return m PUnit
#check @test9_eq
#print axioms test9_eq

-- ============================================================================
-- Test 10: Single binding extraction
-- ============================================================================

def test10 (x y : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← y + 1#u32
  a + b

-- Extract only the first binding
#decompose test10 test10_eq
  letRange 0 1 => test10_first

#check @test10_first
#check @test10_eq
#print axioms test10_eq

-- ============================================================================
-- Test 11: Triple tuple return (continuation needs 3 variables)
-- ============================================================================

def test11 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  let sum ← a + b
  sum + c

#decompose test11 test11_eq
  letRange 0 3 => test11_triple

#check @test11_triple  -- should return Result (U32 × U32 × U32)
#check @test11_eq
#print axioms test11_eq

-- ============================================================================
-- Test 12: Quad tuple return (4 variables needed)
-- ============================================================================

def test12 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  let d ← x + 4#u32
  let s1 ← a + b
  let s2 ← c + d
  s1 + s2

#decompose test12 test12_eq
  letRange 0 4 => test12_quad

#check @test12_quad  -- should return Result (U32 × U32 × U32 × U32)
#check @test12_eq
#print axioms test12_eq

-- ============================================================================
-- Test 13: Mixed pure and monadic bindings
-- ============================================================================

def test13 (x : U32) : Result U32 := do
  let a := x.val     -- pure
  let b ← x + 1#u32  -- monadic
  let c := a + 1      -- pure
  let d ← b + 2#u32  -- monadic
  if c > 0 then pure d else d + 1#u32

-- Extract first 2 (one pure, one monadic)
#decompose test13 test13_eq
  letRange 0 2 => test13_mixed1
  letRange 1 2 => test13_mixed2

#check @test13_mixed1
#check @test13_mixed2
#check @test13_eq
#print axioms test13_eq

-- ============================================================================
-- Test 14: Big monadic function (20 bindings) with 4 sequential decompositions
-- Performance stress test
-- ============================================================================

def test14 (x : U32) : Result U32 := do
  let a0 ← x + 1#u32
  let a1 ← a0 + 1#u32
  let a2 ← a1 + 1#u32
  let a3 ← a2 + 1#u32
  let a4 ← a3 + 1#u32
  let a5 ← a4 + 1#u32
  let a6 ← a5 + 1#u32
  let a7 ← a6 + 1#u32
  let a8 ← a7 + 1#u32
  let a9 ← a8 + 1#u32
  let a10 ← a9 + 1#u32
  let a11 ← a10 + 1#u32
  let a12 ← a11 + 1#u32
  let a13 ← a12 + 1#u32
  let a14 ← a13 + 1#u32
  let a15 ← a14 + 1#u32
  let a16 ← a15 + 1#u32
  let a17 ← a16 + 1#u32
  let a18 ← a17 + 1#u32
  let a19 ← a18 + 1#u32
  a19 + x

-- Four sequential letRange decompositions splitting the chain into 5-binding chunks
#decompose test14 test14_eq
  letRange 0 5 => test14_chunk1
  letRange 1 5 => test14_chunk2
  letRange 1 5 => test14_chunk3
  letRange 1 5 => test14_chunk4

#check @test14_chunk1
#check @test14_chunk2
#check @test14_chunk3
#check @test14_chunk4
#check @test14_eq
#print axioms test14_eq

-- ============================================================================
-- Test 15: Big pure function (20 bindings) — performance test
-- ============================================================================

def test15 (x : Nat) : Nat :=
  let a0 := x + 1
  let a1 := a0 + 1
  let a2 := a1 + 1
  let a3 := a2 + 1
  let a4 := a3 + 1
  let a5 := a4 + 1
  let a6 := a5 + 1
  let a7 := a6 + 1
  let a8 := a7 + 1
  let a9 := a8 + 1
  let a10 := a9 + 1
  let a11 := a10 + 1
  let a12 := a11 + 1
  let a13 := a12 + 1
  let a14 := a13 + 1
  let a15 := a14 + 1
  let a16 := a15 + 1
  let a17 := a16 + 1
  let a18 := a17 + 1
  let a19 := a18 + 1
  a19 + x

-- Split into 4 chunks
#decompose test15 test15_eq
  letRange 0 5 => test15_chunk1
  letRange 1 5 => test15_chunk2
  letRange 1 5 => test15_chunk3
  letRange 1 5 => test15_chunk4

#check @test15_eq
#print axioms test15_eq

-- ============================================================================
-- Test 16: Deep pattern composition — branch+branch+letRange
-- ============================================================================

def test16 (b1 b2 : Bool) (x : U32) : Result U32 := do
  if b1 then
    if b2 then
      let a ← x + 1#u32
      let b ← a + 2#u32
      let c ← b + 3#u32
      c + 4#u32
    else
      x + 10#u32
  else
    x + 20#u32

#decompose test16 test16_eq
  branch 0 (branch 0 (letRange 0 3)) => test16_inner

#check @test16_inner
#check @test16_eq
#print axioms test16_eq

-- ============================================================================
-- Test 17: Pure with multiple variables needed by continuation (tuple)
-- ============================================================================

def test17 (x : Nat) : Nat :=
  let a := x + 1
  let b := x + 2
  a + b + x

#decompose test17 test17_eq
  letRange 0 2 => test17_pair

#check @test17_pair  -- should be Nat → Nat × Nat
#check @test17_eq
#print axioms test17_eq

-- ============================================================================
-- Test 18: letAt pattern — extract from inside a binding's value
-- ============================================================================

def test18_helper (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 2#u32
  b + 3#u32

def test18 (x y : U32) : Result U32 := do
  let z ← test18_helper x  -- binding 0
  let w ← y + z             -- binding 1
  w + 1#u32                  -- terminal

-- Navigate to binding 0's value (test18_helper x) and extract it
-- letAt syntax requires parens: letAt 0 (full)
#decompose test18 test18_eq
  letAt 0 (full) => test18_inner

#check @test18_inner
#check @test18_eq
#print axioms test18_eq

-- ============================================================================
-- Test 19: dite branch — dependent if-then-else
-- ============================================================================

def test19 (n : Nat) : Nat :=
  if _h : n > 0 then
    n + 1
  else
    0

#decompose test19 test19_eq
  branch 0 full => test19_then

#check @test19_then
#check @test19_eq
#print axioms test19_eq

-- ============================================================================
-- Test 20: appFun pattern — modify the function part of an application
-- ============================================================================

def test20_inner (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 1#u32
  b + 1#u32

-- We use appFun to reach the function part.
-- test20_fn wraps a pure function that directly calls test20_inner.
def test20_fn (f : U32 → Result U32) (x : U32) : Result U32 :=
  f x

def test20 (x : U32) : Result U32 :=
  test20_fn test20_inner x

-- argArg 0 full: replace the first argument (test20_inner) of test20_fn
#decompose test20 test20_eq
  argArg 0 full => test20_extracted

#check @test20_extracted
#check @test20_eq
#print axioms test20_eq

-- ============================================================================
-- Test 21: lam pattern — modify under lambda binders
-- ============================================================================

-- We create a function whose body is a lambda
def test21_apply (f : U32 → Result U32) (x : U32) : Result U32 := f x

def test21 (x : U32) : Result U32 :=
  test21_apply (fun y => do let z ← y + x; z + 1#u32) x

-- Navigate into the lambda argument with argArg 0 (lam 1 ...)
#decompose test21 test21_eq
  argArg 0 (lam 1 full) => test21_body

#check @test21_body
#check @test21_eq
#print axioms test21_eq

-- ============================================================================
-- Test 22: Recursive function
-- ============================================================================

-- Recursive functions compile to Nat.brecOn/WellFounded.fix, creating complex
-- internal structures. Let's test with a simpler pattern-match function that
-- uses casesOn.
-- Note: Lean compiles `match` to `casesOn` which can be navigated with argArg.
-- For the successor case: Nat.casesOn n (zero_case) (fun n => succ_case)
-- argArg 0 = zero case, argArg 1 = succ case (then lam 1 to enter the lambda)

def test22 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

-- Match compiles to `test22.match_1 motive n zero_case succ_case`:
-- argArg 0 = motive, 1 = discriminant, 2 = zero case, 3 = succ case.
-- argArg 3 navigates to the successor branch, lam 1 enters the `fun k =>` binder
#decompose test22 test22_eq
  argArg 3 (lam 1 (letRange 0 3)) => test22_compute

#check @test22_compute
#check @test22_eq
#print axioms test22_eq

-- ============================================================================
-- Test 23: Side-effect only with interleaved monadic+pure
-- ============================================================================

noncomputable opaque log : String → Result Unit

noncomputable def test23 (x : U32) : Result U32 := do
  let _ ← log "start"
  let _ ← log "middle"
  x + 1#u32

-- Extract first 2 bindings (2 monadic side-effects, no vars needed by continuation)
#decompose test23 test23_eq
  letRange 0 2 => test23_prefix

#check @test23_prefix
#check @test23_eq
#print axioms test23_eq

-- ============================================================================
-- Test 24: Multiple parameters with various types
-- ============================================================================

def test24 (n : Nat) (x : U32) (s : Slice U8) (b : Bool) : Result U32 := do
  let a ← x + 1#u32
  let len : Nat := s.val.length
  let c ← if b then x + 2#u32 else pure a
  if len > n then c + 1#u32 else pure c

#decompose test24 test24_eq
  letRange 0 3 => test24_prefix

#check @test24_prefix
#check @test24_eq
#print axioms test24_eq

-- ============================================================================
-- Test 25: Bigger stress test — 30 bindings, 6 decomposition steps
-- ============================================================================

def test25 (x : U32) : Result U32 := do
  let a0 ← x + 1#u32
  let a1 ← a0 + 1#u32
  let a2 ← a1 + 1#u32
  let a3 ← a2 + 1#u32
  let a4 ← a3 + 1#u32
  let a5 ← a4 + 1#u32
  let a6 ← a5 + 1#u32
  let a7 ← a6 + 1#u32
  let a8 ← a7 + 1#u32
  let a9 ← a8 + 1#u32
  let a10 ← a9 + 1#u32
  let a11 ← a10 + 1#u32
  let a12 ← a11 + 1#u32
  let a13 ← a12 + 1#u32
  let a14 ← a13 + 1#u32
  let a15 ← a14 + 1#u32
  let a16 ← a15 + 1#u32
  let a17 ← a16 + 1#u32
  let a18 ← a17 + 1#u32
  let a19 ← a18 + 1#u32
  let a20 ← a19 + 1#u32
  let a21 ← a20 + 1#u32
  let a22 ← a21 + 1#u32
  let a23 ← a22 + 1#u32
  let a24 ← a23 + 1#u32
  let a25 ← a24 + 1#u32
  let a26 ← a25 + 1#u32
  let a27 ← a26 + 1#u32
  let a28 ← a27 + 1#u32
  let a29 ← a28 + 1#u32
  a29 + x

-- 6 sequential decompositions, each extracting 5 bindings
#decompose test25 test25_eq
  letRange 0 5 => test25_chunk1
  letRange 1 5 => test25_chunk2
  letRange 1 5 => test25_chunk3
  letRange 1 5 => test25_chunk4
  letRange 1 5 => test25_chunk5
  letRange 1 5 => test25_chunk6

#check @test25_eq
#print axioms test25_eq

-- ============================================================================
-- Test 26: letRange starting in the middle — tests that outer bindings are captured
-- ============================================================================

def test26 (x : U32) : Result U32 := do
  let a ← x + 1#u32     -- binding 0
  let b ← a + 2#u32     -- binding 1
  let c ← b + 3#u32     -- binding 2
  let d ← c + a         -- binding 3 (references a from binding 0)
  let e ← d + b         -- binding 4 (references b from binding 1)
  e + 1#u32

-- Extract bindings 2-4 (which reference a, b from outside the range)
#decompose test26 test26_eq
  letRange 2 3 => test26_middle

#check @test26_middle  -- should take a, b as parameters
#check @test26_eq
#print axioms test26_eq

-- ============================================================================
-- Test 27: letAt navigating to binding 1's value (deeper navigation)
-- ============================================================================

def test27_aux1 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  a + 2#u32

def test27_aux2 (y : U32) : Result U32 := do
  let b ← y + 10#u32
  b + 20#u32

def test27 (x y : U32) : Result U32 := do
  let p ← test27_aux1 x    -- binding 0
  let q ← test27_aux2 y    -- binding 1 (we will navigate into this)
  p + q

-- Navigate to binding 1's value (test27_aux2 y) and extract it
#decompose test27 test27_eq
  letAt 1 (full) => test27_extracted

#check @test27_extracted
#check @test27_eq
#print axioms test27_eq

-- ============================================================================
-- Test 28: Pure function with branch — full extraction from branch body
-- ============================================================================

def test28 (b : Bool) (x : Nat) : Nat :=
  if b then
    let a := x + 1
    let b := a + 2
    let c := b + 3
    c + a
  else
    x

#decompose test28 test28_eq
  branch 0 full => test28_then

#check @test28_then
#check @test28_eq
#print axioms test28_eq

-- ============================================================================
-- Test 29: Pure neededFVars == 0 — range where no variables are used by continuation
-- ============================================================================

-- In pure mode, when no range variables are used, the definition is created
-- but the body is just the continuation (let-reduction makes them equal by rfl)
def test29 (x : Nat) : Nat :=
  let _a := x + 1
  let _b := x + 2
  x + 3

#decompose test29 test29_eq
  letRange 0 2 => test29_unused

#check @test29_unused
#check @test29_eq
#print axioms test29_eq

-- ============================================================================
-- Test 30: Universe polymorphism
-- ============================================================================

universe u
def test30 {α : Type u} (x : α) : α :=
  let a := x
  let b := a
  b

#decompose test30 test30_eq
  letRange 0 2 => test30_aux

#check @test30_aux
#check @test30_eq
#print axioms test30_eq

-- ============================================================================
-- Test 31: Branch followed by letRange on both branches
-- ============================================================================

def test31 (b : Bool) (x y : U32) : Result U32 := do
  if b then
    let a ← x + 1#u32
    let b ← a + 2#u32
    b + y
  else
    let c ← y + 10#u32
    let d ← c + 20#u32
    d + x

#decompose test31 test31_eq
  branch 0 (letRange 0 2) => test31_then_prefix
  branch 1 (letRange 0 2) => test31_else_prefix

#check @test31_then_prefix
#check @test31_else_prefix
#check @test31_eq
#print axioms test31_eq

-- ============================================================================
-- Test 32: Implicit type parameters
-- ============================================================================

def test32 {n : Nat} (x : Fin n) : Nat :=
  let a := x.val + 1
  let b := a + n
  b

#decompose test32 test32_eq
  letRange 0 2 => test32_aux

#check @test32_aux
#check @test32_eq
#print axioms test32_eq

-- ============================================================================
-- Test 33: Big monadic function (66 lines) with nested if-then-else
-- Stress test: decomposed into 10 auxiliary functions, from leaves to root.
-- Profile the #decompose command to verify it is almost instant.
-- ============================================================================

def test33 (mode : Bool) (flag : Bool) (x y z w : U32) : Result U32 := do
  if mode then
    if flag then
      -- Then-then: 10 heavy bindings
      let c0 ← x + 1#u32
      let c1 ← c0 + y
      let c2 ← c1 * 2#u32
      let c3 ← c2 + z
      let c4 ← c3 + w
      let c5 ← c4 + 10#u32
      let c6 ← c5 * 3#u32
      let c7 ← c6 + c0
      let c8 ← c7 + c1
      let c9 ← c8 + 1#u32
      -- Then-then: 4 reduction bindings + tail
      let r0 ← c0 + c3
      let r1 ← r0 + c6
      let r2 ← r1 + c9
      r2 + w
    else
      -- Then-else: 10 heavy bindings
      let d0 ← x + 2#u32
      let d1 ← d0 + y
      let d2 ← d1 * 3#u32
      let d3 ← d2 + z
      let d4 ← d3 + w
      let d5 ← d4 + 20#u32
      let d6 ← d5 * 2#u32
      let d7 ← d6 + d0
      let d8 ← d7 + d1
      let d9 ← d8 + 1#u32
      -- Then-else: 4 reduction bindings + tail
      let s0 ← d0 + d4
      let s1 ← s0 + d7
      let s2 ← s1 + d9
      s2 + w
  else
    if flag then
      -- Else-then: 10 heavy bindings
      let e0 ← x + 3#u32
      let e1 ← e0 + z
      let e2 ← e1 * 2#u32
      let e3 ← e2 + w
      let e4 ← e3 + y
      let e5 ← e4 + 30#u32
      let e6 ← e5 * 3#u32
      let e7 ← e6 + e0
      let e8 ← e7 + e1
      let e9 ← e8 + 1#u32
      -- Else-then: 4 reduction bindings + tail
      let t0 ← e0 + e3
      let t1 ← t0 + e6
      let t2 ← t1 + e9
      t2 + y
    else
      -- Else-else: 10 heavy bindings
      let f0 ← x + 4#u32
      let f1 ← f0 + w
      let f2 ← f1 * 3#u32
      let f3 ← f2 + y
      let f4 ← f3 + z
      let f5 ← f4 + 40#u32
      let f6 ← f5 * 2#u32
      let f7 ← f6 + f0
      let f8 ← f7 + f1
      let f9 ← f8 + 1#u32
      -- Else-else: 4 reduction bindings + tail
      let u0 ← f0 + f4
      let u1 ← u0 + f7
      let u2 ← u1 + f9
      u2 + z

set_option profiler true in
#decompose test33 test33_eq
  -- 1-4: Extract 10 heavy bindings from each inner branch
  branch 0 (branch 0 (letRange 0 10)) => test33_tt_comp
  branch 0 (branch 1 (letRange 0 10)) => test33_te_comp
  branch 1 (branch 0 (letRange 0 10)) => test33_et_comp
  branch 1 (branch 1 (letRange 0 10)) => test33_ee_comp
  -- 5-8: Extract remaining from each inner branch
  branch 0 (branch 0 full) => test33_tt
  branch 0 (branch 1 full) => test33_te
  branch 1 (branch 0 full) => test33_et
  branch 1 (branch 1 full) => test33_ee
  -- 9-10: Extract full outer branches
  branch 0 full => test33_then
  branch 1 full => test33_else

-- Verify all 10 generated definitions exist
#check @test33_tt_comp
#check @test33_te_comp
#check @test33_et_comp
#check @test33_ee_comp
#check @test33_tt
#check @test33_te
#check @test33_et
#check @test33_ee
#check @test33_then
#check @test33_else
#check @test33_eq
#print axioms test33_eq

-- ============================================================================
-- Test 34: Simple match on Nat — branch navigates into match alternatives
-- ============================================================================

def test34 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

-- Use `branch 1` to enter the successor case (alt index 1), then extract lets
#decompose test34 test34_eq
  branch 1 (letRange 0 3) => test34_succ_comp

#check @test34_succ_comp
#check @test34_eq
#print axioms test34_eq

-- ============================================================================
-- Test 35: Match on Bool
-- ============================================================================

def test35 (b : Bool) : Nat :=
  match b with
  | true =>
    let x := 100
    let y := x + 200
    y
  | false =>
    let x := 300
    let y := x + 400
    y

-- Extract from true branch (alt 0) and false branch (alt 1)
#decompose test35 test35_eq
  branch 0 (letRange 0 2) => test35_true_comp
  branch 1 (letRange 0 2) => test35_false_comp

#check @test35_true_comp
#check @test35_false_comp
#check @test35_eq
#print axioms test35_eq

-- ============================================================================
-- Test 36: Match on Option
-- ============================================================================

def test36 (o : Option Nat) : Nat :=
  match o with
  | none =>
    let a := 0
    let b := a + 1
    b
  | some v =>
    let a := v + 10
    let b := a + 20
    let c := b + 30
    c

-- Extract from the some branch (alt 1), which has 1 pattern variable (v)
#decompose test36 test36_eq
  branch 1 (letRange 0 3) => test36_some_comp

#check @test36_some_comp
#check @test36_eq
#print axioms test36_eq

-- ============================================================================
-- Test 37: Match on custom enum with many constructors
-- ============================================================================

inductive Color where
  | red | green | blue | yellow

def test37 (c : Color) : Nat :=
  match c with
  | .red =>
    let a := 1
    let b := a + 2
    b
  | .green =>
    let a := 3
    let b := a + 4
    b
  | .blue =>
    let a := 5
    let b := a + 6
    b
  | .yellow =>
    let a := 7
    let b := a + 8
    b

-- Extract from each branch
#decompose test37 test37_eq
  branch 0 (letRange 0 2) => test37_red
  branch 1 (letRange 0 2) => test37_green
  branch 2 (letRange 0 2) => test37_blue
  branch 3 (letRange 0 2) => test37_yellow

#check @test37_red
#check @test37_green
#check @test37_blue
#check @test37_yellow
#check @test37_eq
#print axioms test37_eq

-- ============================================================================
-- Test 38: Match with full extraction of a branch
-- ============================================================================

def test38 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k * 2
    let b := a + 3
    b

-- Extract the full successor branch body
#decompose test38 test38_eq
  branch 1 full => test38_succ

#check @test38_succ
#check @test38_eq
#print axioms test38_eq

-- ============================================================================
-- Test 39: Nested match — match inside a match branch
-- ============================================================================

def test39 (n : Nat) (b : Bool) : Nat :=
  match n with
  | 0 => 0
  | k + 1 =>
    match b with
    | true =>
      let a := k + 100
      let b := a + 200
      b
    | false =>
      let a := k + 300
      let b := a + 400
      b

-- Navigate: outer match alt 1 → inner match alt 0 (true) → extract lets
#decompose test39 test39_eq
  branch 1 (branch 0 (letRange 0 2)) => test39_succ_true_comp
  branch 1 (branch 1 (letRange 0 2)) => test39_succ_false_comp

#check @test39_succ_true_comp
#check @test39_succ_false_comp
#check @test39_eq
#print axioms test39_eq

-- ============================================================================
-- Test 40: Monadic match — match in the Result monad
-- ============================================================================

def test40 (n : Nat) : Result Nat := do
  match n with
  | 0 => .ok 42
  | k + 1 =>
    let a ← .ok (k + 10)
    let b ← .ok (a + 1)
    .ok b

-- The match is directly at the top of the do-block body, so `branch` works directly
#decompose test40 test40_eq
  branch 1 (letRange 0 2) => test40_succ_comp

#check @test40_succ_comp
#check @test40_eq
#print axioms test40_eq

-- ============================================================================
-- Test 41: Match with struct pattern — multiple pattern variables
-- ============================================================================

structure Point where
  x : Nat
  y : Nat

def test41 (p : Point) : Nat :=
  match p with
  | ⟨x, y⟩ =>
    let a := x + y
    let b := a * 2
    let c := b + 1
    c

-- The Point match has 1 alternative with 2 pattern variables (x, y)
#decompose test41 test41_eq
  branch 0 (letRange 0 3) => test41_comp

#check @test41_comp
#check @test41_eq
#print axioms test41_eq

-- ============================================================================
-- Test 42: Match on Sum type
-- ============================================================================

def test42 (s : Nat ⊕ Bool) : Nat :=
  match s with
  | .inl n =>
    let a := n + 1
    let b := a + 2
    b
  | .inr b =>
    let x := if b then 100 else 200
    let y := x + 3
    y

-- Extract from the inl branch (alt 0, 1 pattern var) and inr branch (alt 1, 1 pattern var)
#decompose test42 test42_eq
  branch 0 (letRange 0 2) => test42_inl_comp
  branch 1 (letRange 0 2) => test42_inr_comp

#check @test42_inl_comp
#check @test42_inr_comp
#check @test42_eq
#print axioms test42_eq

-- ============================================================================
-- Test 43: Match combined with if-then-else inside a branch
-- ============================================================================

def test43 (n : Nat) (flag : Bool) : Nat :=
  match n with
  | 0 => 0
  | k + 1 =>
    if flag then
      let a := k + 10
      let b := a + 20
      b
    else
      let a := k + 30
      let b := a + 40
      b

-- Navigate into match alt 1, then into if-then-else branch 0 (then)
#decompose test43 test43_eq
  branch 1 (branch 0 (letRange 0 2)) => test43_succ_then_comp
  branch 1 (branch 1 (letRange 0 2)) => test43_succ_else_comp

#check @test43_succ_then_comp
#check @test43_succ_else_comp
#check @test43_eq
#print axioms test43_eq

-- ============================================================================
-- Test 44: Rewrite test22 using branch instead of argArg (regression check)
-- ============================================================================

-- test22 used `argArg 3 (lam 1 ...)` to navigate the match; now branch should work
def test44 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

#decompose test44 test44_eq
  branch 1 (letRange 0 3) => test44_compute

-- Verify this produces the same result as test22 did with argArg
#check @test44_compute
#check @test44_eq
#print axioms test44_eq

-- ============================================================================
-- Test 45: Big match with many branches, extracting from all — performance test
-- ============================================================================

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun

def test45 (d : Weekday) : Nat :=
  match d with
  | .mon =>
    let a := 1; let b := a + 2; let c := b + 3; let d := c + 4; let e := d + 5; e
  | .tue =>
    let a := 10; let b := a + 20; let c := b + 30; let d := c + 40; let e := d + 50; e
  | .wed =>
    let a := 100; let b := a + 200; let c := b + 300; let d := c + 400; let e := d + 500; e
  | .thu =>
    let a := 1000; let b := a + 2000; let c := b + 3000; let d := c + 4000; let e := d + 5000; e
  | .fri =>
    let a := 10000; let b := a + 20000; let c := b + 30000; let d := c + 40000; let e := d + 50000; e
  | .sat =>
    let a := 100000; let b := a + 200000; let c := b + 300000; let d := c + 400000; let e := d + 500000; e
  | .sun =>
    let a := 1000000; let b := a + 2000000; let c := b + 3000000; let d := c + 4000000; let e := d + 5000000; e

set_option profiler true in
#decompose test45 test45_eq
  branch 0 (letRange 0 5) => test45_mon
  branch 1 (letRange 0 5) => test45_tue
  branch 2 (letRange 0 5) => test45_wed
  branch 3 (letRange 0 5) => test45_thu
  branch 4 (letRange 0 5) => test45_fri
  branch 5 (letRange 0 5) => test45_sat
  branch 6 (letRange 0 5) => test45_sun

#check @test45_mon
#check @test45_tue
#check @test45_wed
#check @test45_thu
#check @test45_fri
#check @test45_sat
#check @test45_sun
#check @test45_eq
#print axioms test45_eq

-- ============================================================================
-- Test 46: Match with branch index out of bounds (error test)
-- ============================================================================

def test46 (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 2

-- Bool match has 2 alts (0 and 1); index 2 should fail
/--
error: branch 2: match has only 2 alternative(s) (0-indexed)
-/
#guard_msgs in
#decompose test46 test46_eq
  branch 2 full => test46_bad

-- ============================================================================
-- Test 47: Match on list — nil and cons with multiple pattern variables
-- ============================================================================

def test47 (l : List Nat) : Nat :=
  match l with
  | [] =>
    let a := 0
    let b := a + 1
    b
  | hd :: tl =>
    let a := hd + tl.length
    let b := a + 100
    let c := b + 200
    c

-- nil branch (alt 0): 0 pattern vars, cons branch (alt 1): 2 pattern vars (hd, tl)
#decompose test47 test47_eq
  branch 0 (letRange 0 2) => test47_nil_comp
  branch 1 (letRange 0 3) => test47_cons_comp

#check @test47_nil_comp
#check @test47_cons_comp
#check @test47_eq
#print axioms test47_eq
