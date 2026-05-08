/-
Tests for the #decompose command
-/
import Aeneas.Command.Decompose
import Aeneas.Std
import Aeneas.Do.Elab
import Aeneas.Do.Delab

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

/--
warning: #decompose: 'test1_y' has the same definition as 'test1_x' (consider reusing the same name)
-/
#guard_msgs in
#decompose test1 test1_eq
  letRange 0 3 => test1_x
  letRange 1 3 => test1_y

/--
info: def test1_x : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  x2 + 1#u32
-/
#guard_msgs in
#print test1_x
/--
info: def test1_y : U32 → Result (UScalar UScalarTy.U32) :=
fun y => do
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  y2 + 1#u32
-/
#guard_msgs in
#print test1_y
/--
info: test1_eq : ∀ (x y : U32),
  test1 x y = do
    let x3 ← test1_x x
    let y3 ← test1_y y
    x3 + y3
-/
#guard_msgs in
#check @test1_eq
/--
info: 'test1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test1_eq

-- ============================================================================
-- Test 2: Tuple return — continuation needs multiple variables
-- ============================================================================

def test2 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← 2#u32 * x
  a + b

#decompose test2 test2_eq
  letRange 0 2 => test2_aux

/--
info: def test2_aux : U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let b ← 2#u32 * x
  pure (a, b)
-/
#guard_msgs in
#print test2_aux
/--
info: test2_eq : ∀ (x : U32),
  test2 x = do
    let (a, b) ← test2_aux x
    a + b
-/
#guard_msgs in
#check @test2_eq
/--
info: 'test2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test2_eq

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

/--
warning: #decompose: 'test3_y' has the same definition as 'test3_x' (consider reusing the same name)
-/
#guard_msgs in
#decompose test3 test3_eq
  branch 0 (letRange 0 3) => test3_x
  branch 0 (letRange 1 3) => test3_y
  branch 0 full => test3_then

/--
info: def test3_x : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  x2 + 1#u32
-/
#guard_msgs in
#print test3_x
/--
info: def test3_y : U32 → Result (UScalar UScalarTy.U32) :=
fun y => do
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  y2 + 1#u32
-/
#guard_msgs in
#print test3_y
/--
info: def test3_then : U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y => do
  let x3 ← test3_x x
  let y3 ← test3_y y
  x3 + y3
-/
#guard_msgs in
#print test3_then
/--
info: test3_eq : ∀ (b : Bool) (x y : U32), test3 b x y = if b = true then test3_then x y else x + y
-/
#guard_msgs in
#check @test3_eq
/--
info: 'test3_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test3_eq

-- ============================================================================
-- Test 4: Full extraction (proof by rfl)
-- ============================================================================

def test4 (x y : U32) : Result U32 := do
  let z ← x + y
  z + 1#u32

#decompose test4 test4_eq
  full => test4_body

/--
info: def test4_body : U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y => do
  let z ← x + y
  z + 1#u32
-/
#guard_msgs in
#print test4_body
/--
info: test4_eq : ∀ (x y : U32), test4 x y = test4_body x y
-/
#guard_msgs in
#check @test4_eq
/--
info: 'test4_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test4_eq

-- ============================================================================
-- Test 5: letRange including terminal (proof by rfl)
-- ============================================================================

def test5 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 1#u32
  b + 1#u32

#decompose test5 test5_eq
  letRange 0 3 => test5_all

/--
info: def test5_all : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let b ← a + 1#u32
  b + 1#u32
-/
#guard_msgs in
#print test5_all
/--
info: test5_eq : ∀ (x : U32), test5 x = test5_all x
-/
#guard_msgs in
#check @test5_eq
/--
info: 'test5_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test5_eq

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

/--
info: def test6_aux : ℕ → ℕ :=
fun x =>
  let a := x + 1;
  let b := a + 2;
  b + 3
-/
#guard_msgs in
#print test6_aux
/--
info: test6_eq : ∀ (x : ℕ),
  test6 x =
    let c := test6_aux x;
    c + 4
-/
#guard_msgs in
#check @test6_eq
/--
info: 'test6_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test6_eq

-- ============================================================================
-- Test 7: Noncomputable functions
-- ============================================================================

noncomputable opaque wipeSlice : Slice U8 → Result Unit

noncomputable def test7 (x : U32) (s : Slice U8) : Result U32 := do
  let a ← x + 1#u32
  let _ ← wipeSlice s
  a + 2#u32

#decompose test7 test7_eq
full => test7_body

-- Verify
/--
info: 'test7_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test7_eq

-- ============================================================================
-- Test 8: Side-effect only range (monadic, continuation uses no range variables)
-- ============================================================================

noncomputable opaque sideEffect1 : U32 → Result Unit
noncomputable opaque sideEffect2 : U32 → Result Unit

noncomputable def test8 (x y : U32) : Result U32 := do
  let _ ← sideEffect1 x
  let _ ← sideEffect2 y
  pure 42#u32

-- Extract the two side-effect bindings — continuation uses none of them
#decompose test8 test8_eq
  letRange 0 2 => test8_effects

/--
info: def test8_effects : U32 → U32 → Result Unit :=
fun x y => do
  sideEffect1 x
  sideEffect2 y
  pure ()
-/
#guard_msgs in
#print test8_effects
/--
info: test8_eq : ∀ (x y : U32),
  test8 x y = do
    test8_effects x y
    pure 42#u32
-/
#guard_msgs in
#check @test8_eq
/--
info: 'test8_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test8_eq

-- ============================================================================
-- Test 9: Single binding extraction
-- ============================================================================

def test9 (x y : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← y + 1#u32
  a + b

-- Extract only the first binding
#decompose test9 test9_eq
  letRange 0 1 => test9_first

/--
info: def test9_first : U32 → Result (UScalar UScalarTy.U32) :=
fun x => x + 1#u32
-/
#guard_msgs in
#print test9_first
/--
info: test9_eq : ∀ (x y : U32),
  test9 x y = do
    let a ← test9_first x
    let b ← y + 1#u32
    a + b
-/
#guard_msgs in
#check @test9_eq
/--
info: 'test9_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test9_eq

-- ============================================================================
-- Test 10: Triple tuple return (continuation needs 3 variables)
-- ============================================================================

def test10 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  let sum ← a + b
  sum + c

#decompose test10 test10_eq
  letRange 0 3 => test10_triple

/--
info: def test10_triple : U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  pure (a, b, c)
-/
#guard_msgs in
#print test10_triple
/--
info: test10_eq : ∀ (x : U32),
  test10 x = do
    let (a, b, c) ← test10_triple x
    let sum ← a + b
    sum + c
-/
#guard_msgs in
#check @test10_eq
/--
info: 'test10_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test10_eq

-- ============================================================================
-- Test 11: Quad tuple return (4 variables needed)
-- ============================================================================

def test11 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  let d ← x + 4#u32
  let s1 ← a + b
  let s2 ← c + d
  s1 + s2

#decompose test11 test11_eq
  letRange 0 4 => test11_quad

/--
info: def test11_quad : U32 →
  Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let b ← x + 2#u32
  let c ← x + 3#u32
  let d ← x + 4#u32
  pure (a, b, c, d)
-/
#guard_msgs in
#print test11_quad
/--
info: test11_eq : ∀ (x : U32),
  test11 x = do
    let (a, b, c, d) ← test11_quad x
    let s1 ← a + b
    let s2 ← c + d
    s1 + s2
-/
#guard_msgs in
#check @test11_eq
/--
info: 'test11_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test11_eq

-- ============================================================================
-- Test 12: Mixed pure and monadic bindings
-- ============================================================================

def test12 (x : U32) : Result U32 := do
  let a := x.val     -- pure
  let b ← x + 1#u32  -- monadic
  let c := a + 1      -- pure
  let d ← b + 2#u32  -- monadic
  if c > 0 then pure d else d + 1#u32

-- Extract first 2 (one pure, one monadic)
#decompose test12 test12_eq
  letRange 0 2 => test12_mixed1
  letRange 1 2 => test12_mixed2

/--
info: def test12_mixed1 : U32 → Result (ℕ × UScalar UScalarTy.U32) :=
fun x =>
  let a := ↑x;
  do
  let b ← x + 1#u32
  pure (a, b)
-/
#guard_msgs in
#print test12_mixed1
/--
info: def test12_mixed2 : ℕ → UScalar UScalarTy.U32 → Result (ℕ × UScalar UScalarTy.U32) :=
fun a b =>
  let c := a + 1;
  do
  let d ← b + 2#u32
  pure (c, d)
-/
#guard_msgs in
#print test12_mixed2
/--
info: test12_eq : ∀ (x : U32),
  test12 x = do
    let (a, b) ← test12_mixed1 x
    let (c, d) ← test12_mixed2 a b
    if c > 0 then pure d else d + 1#u32
-/
#guard_msgs in
#check @test12_eq
/--
info: 'test12_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test12_eq

-- ============================================================================
-- Test 13: Big monadic function (20 bindings) with 4 sequential decompositions
-- Performance stress test
-- ============================================================================

def test13 (x : U32) : Result U32 := do
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
/--
warning: #decompose: 'test13_chunk2' has the same definition as 'test13_chunk1' (consider reusing the same name)
-/
#guard_msgs in
#decompose test13 test13_eq
  letRange 0 5 => test13_chunk1
  letRange 1 5 => test13_chunk2
  letRange 1 5 => test13_chunk3
  letRange 1 5 => test13_chunk4

/--
info: def test13_chunk1 : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let a0 ← x + 1#u32
  let a1 ← a0 + 1#u32
  let a2 ← a1 + 1#u32
  let a3 ← a2 + 1#u32
  a3 + 1#u32
-/
#guard_msgs in
#print test13_chunk1
/--
info: def test13_chunk2 : UScalar UScalarTy.U32 → Result (UScalar UScalarTy.U32) :=
fun a4 => do
  let a5 ← a4 + 1#u32
  let a6 ← a5 + 1#u32
  let a7 ← a6 + 1#u32
  let a8 ← a7 + 1#u32
  a8 + 1#u32
-/
#guard_msgs in
#print test13_chunk2
/--
info: def test13_chunk3 : UScalar UScalarTy.U32 → Result (UScalar UScalarTy.U32) :=
fun a4 => do
  let a9 ← test13_chunk2 a4
  let a10 ← a9 + 1#u32
  let a11 ← a10 + 1#u32
  let a12 ← a11 + 1#u32
  a12 + 1#u32
-/
#guard_msgs in
#print test13_chunk3
/--
info: def test13_chunk4 : UScalar UScalarTy.U32 → Result (UScalar UScalarTy.U32) :=
fun a4 => do
  let a13 ← test13_chunk3 a4
  let a14 ← a13 + 1#u32
  let a15 ← a14 + 1#u32
  let a16 ← a15 + 1#u32
  a16 + 1#u32
-/
#guard_msgs in
#print test13_chunk4
/--
info: test13_eq : ∀ (x : U32),
  test13 x = do
    let a4 ← test13_chunk1 x
    let a17 ← test13_chunk4 a4
    let a18 ← a17 + 1#u32
    let a19 ← a18 + 1#u32
    a19 + x
-/
#guard_msgs in
#check @test13_eq
/--
info: 'test13_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test13_eq

-- ============================================================================
-- Test 14: Big pure function (20 bindings) — performance test
-- ============================================================================

def test14 (x : Nat) : Nat :=
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
/--
warning: #decompose: 'test14_chunk2' has the same definition as 'test14_chunk1' (consider reusing the same name)
-/
#guard_msgs in
#decompose test14 test14_eq
  letRange 0 5 => test14_chunk1
  letRange 1 5 => test14_chunk2
  letRange 1 5 => test14_chunk3
  letRange 1 5 => test14_chunk4

/--
info: test14_eq : ∀ (x : ℕ),
  test14 x =
    let a4 := test14_chunk1 x;
    let a17 := test14_chunk4 a4;
    let a18 := a17 + 1;
    let a19 := a18 + 1;
    a19 + x
-/
#guard_msgs in
#check @test14_eq
/--
info: 'test14_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test14_eq

-- ============================================================================
-- Test 15: Deep pattern composition — branch+branch+letRange
-- ============================================================================

def test15 (b1 b2 : Bool) (x : U32) : Result U32 := do
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

#decompose test15 test15_eq
  branch 0 (branch 0 (letRange 0 3)) => test15_inner

/--
info: def test15_inner : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let b ← a + 2#u32
  b + 3#u32
-/
#guard_msgs in
#print test15_inner
/--
info: test15_eq : ∀ (b1 b2 : Bool) (x : U32),
  test15 b1 b2 x =
    if b1 = true then
      if b2 = true then do
        let c ← test15_inner x
        c + 4#u32
      else x + 10#u32
    else x + 20#u32
-/
#guard_msgs in
#check @test15_eq
/--
info: 'test15_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test15_eq

-- ============================================================================
-- Test 16: Pure with multiple variables needed by continuation (tuple)
-- ============================================================================

def test16 (x : Nat) : Nat :=
  let a := x + 1
  let b := x + 2
  a + b + x

#decompose test16 test16_eq
  letRange 0 2 => test16_pair

/--
info: def test16_pair : ℕ → ℕ × ℕ :=
fun x =>
  let a := x + 1;
  let b := x + 2;
  (a, b)
-/
#guard_msgs in
#print test16_pair
/--
info: test16_eq : ∀ (x : ℕ),
  test16 x =
    let a := (test16_pair x).1;
    let b := (test16_pair x).2;
    a + b + x
-/
#guard_msgs in
#check @test16_eq
/--
info: 'test16_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test16_eq

-- ============================================================================
-- Test 17: letAt pattern — extract from inside a binding's value
-- ============================================================================

def test17_helper (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 2#u32
  b + 3#u32

def test17 (x y : U32) : Result U32 := do
  let z ← test17_helper x  -- binding 0
  let w ← y + z             -- binding 1
  w + 1#u32                  -- terminal

-- Navigate to binding 0's value (test17_helper x) and extract it
-- letAt syntax requires parens: letAt 0 (full)
#decompose test17 test17_eq
  letAt 0 (full) => test17_inner

/--
info: def test17_inner : U32 → Result U32 :=
fun x => test17_helper x
-/
#guard_msgs in
#print test17_inner
/--
info: test17_eq : ∀ (x y : U32),
  test17 x y = do
    let z ← test17_inner x
    let w ← y + z
    w + 1#u32
-/
#guard_msgs in
#check @test17_eq
/--
info: 'test17_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test17_eq

-- ============================================================================
-- Test 18: dite branch — dependent if-then-else
-- ============================================================================

def test18 (n : Nat) : Nat :=
  if _h : n > 0 then
    n + 1
  else
    0

#decompose test18 test18_eq
  branch 0 full => test18_then

/--
info: def test18_then : ℕ → ℕ :=
fun n => n + 1
-/
#guard_msgs in
#print test18_then
/--
info: test18_eq : ∀ (n : ℕ), test18 n = if _h : n > 0 then test18_then n else 0
-/
#guard_msgs in
#check @test18_eq
/--
info: 'test18_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test18_eq

-- ============================================================================
-- Test 19: appFun pattern — modify the function part of an application
-- ============================================================================

def test19_inner (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let b ← a + 1#u32
  b + 1#u32

-- We use appFun to reach the function part.
-- test19_fn wraps a pure function that directly calls test19_inner.
def test19_fn (f : U32 → Result U32) (x : U32) : Result U32 :=
  f x

def test19 (x : U32) : Result U32 :=
  test19_fn test19_inner x

-- argArg 0 full: replace the first argument (test19_inner) of test19_fn
#decompose test19 test19_eq
  argArg 0 full => test19_extracted

/--
info: def test19_extracted : U32 → Result U32 :=
test19_inner
-/
#guard_msgs in
#print test19_extracted
/--
info: test19_eq : ∀ (x : U32), test19 x = test19_fn test19_extracted x
-/
#guard_msgs in
#check @test19_eq
/--
info: 'test19_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test19_eq

-- ============================================================================
-- Test 20: lam pattern — modify under lambda binders
-- ============================================================================

-- We create a function whose body is a lambda
def test20_apply (f : U32 → Result U32) (x : U32) : Result U32 := f x

def test20 (x : U32) : Result U32 :=
  test20_apply (fun y => do let z ← y + x; z + 1#u32) x

-- Navigate into the lambda argument with argArg 0 (lam 1 ...)
#decompose test20 test20_eq
  argArg 0 (lam 1 full) => test20_body

/--
info: def test20_body : U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y => do
  let z ← y + x
  z + 1#u32
-/
#guard_msgs in
#print test20_body
/--
info: test20_eq : ∀ (x : U32), test20 x = test20_apply (fun y => test20_body x y) x
-/
#guard_msgs in
#check @test20_eq
/--
info: 'test20_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test20_eq

-- ============================================================================
-- Test 21: Recursive function
-- ============================================================================

-- Recursive functions compile to Nat.brecOn/WellFounded.fix, creating complex
-- internal structures. Let's test with a simpler pattern-match function that
-- uses casesOn.
-- Note: Lean compiles `match` to `casesOn` which can be navigated with argArg.
-- For the successor case: Nat.casesOn n (zero_case) (fun n => succ_case)
-- argArg 0 = zero case, argArg 1 = succ case (then lam 1 to enter the lambda)

def test21 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

-- Match compiles to `test21.match_1 motive n zero_case succ_case`:
-- argArg 0 = motive, 1 = discriminant, 2 = zero case, 3 = succ case.
-- argArg 3 navigates to the successor branch, lam 1 enters the `fun k =>` binder
#decompose test21 test21_eq
  argArg 3 (lam 1 (letRange 0 3)) => test21_compute

/--
info: def test21_compute : ℕ → ℕ :=
fun k =>
  let a := k + 1;
  let b := a + 1;
  b + 1
-/
#guard_msgs in
#print test21_compute
/--
info: test21_eq : ∀ (n : ℕ),
  test21 n =
    match n with
    | 0 => 42
    | k.succ =>
      let c := test21_compute k;
      c + k
-/
#guard_msgs in
#check @test21_eq
/--
info: 'test21_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test21_eq

-- ============================================================================
-- Test 22: Side-effect only with interleaved monadic+pure
-- ============================================================================

noncomputable opaque log : String → Result Unit

noncomputable def test22 (x : U32) : Result U32 := do
  let _ ← log "start"
  let _ ← log "middle"
  x + 1#u32

-- Extract first 2 bindings (2 monadic side-effects, no vars needed by continuation)
#decompose test22 test22_eq
  letRange 0 2 => test22_prefix

/--
info: def test22_prefix : Result Unit :=
do
  log "start"
  log "middle"
  pure ()
-/
#guard_msgs in
#print test22_prefix
/--
info: test22_eq : ∀ (x : U32),
  test22 x = do
    test22_prefix
    x + 1#u32
-/
#guard_msgs in
#check @test22_eq
/--
info: 'test22_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test22_eq

-- ============================================================================
-- Test 23: Multiple parameters with various types
-- ============================================================================

def test23 (n : Nat) (x : U32) (s : Slice U8) (b : Bool) : Result U32 := do
  let a ← x + 1#u32
  let len : Nat := s.val.length
  let c ← if b then x + 2#u32 else pure a
  if len > n then c + 1#u32 else pure c

#decompose test23 test23_eq
  letRange 0 3 => test23_prefix

/--
info: def test23_prefix : U32 → Slice U8 → Bool → Result (ℕ × UScalar UScalarTy.U32) :=
fun x s b => do
  let a ← x + 1#u32
  let len : ℕ := (↑s).length
  let c ← if b = true then x + 2#u32 else pure a
  pure (len, c)
-/
#guard_msgs in
#print test23_prefix
/--
info: test23_eq : ∀ (n : ℕ) (x : U32) (s : Slice U8) (b : Bool),
  test23 n x s b = do
    let (len, c) ← test23_prefix x s b
    if len > n then c + 1#u32 else pure c
-/
#guard_msgs in
#check @test23_eq
/--
info: 'test23_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test23_eq

-- ============================================================================
-- Test 24: Bigger stress test — 30 bindings, 6 decomposition steps
-- ============================================================================

def test24 (x : U32) : Result U32 := do
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
/--
warning: #decompose: 'test24_chunk2' has the same definition as 'test24_chunk1' (consider reusing the same name)
-/
#guard_msgs in
#decompose test24 test24_eq
  letRange 0 5 => test24_chunk1
  letRange 1 5 => test24_chunk2
  letRange 1 5 => test24_chunk3
  letRange 1 5 => test24_chunk4
  letRange 1 5 => test24_chunk5
  letRange 1 5 => test24_chunk6

/--
info: test24_eq : ∀ (x : U32),
  test24 x = do
    let a4 ← test24_chunk1 x
    let a25 ← test24_chunk6 a4
    let a26 ← a25 + 1#u32
    let a27 ← a26 + 1#u32
    let a28 ← a27 + 1#u32
    let a29 ← a28 + 1#u32
    a29 + x
-/
#guard_msgs in
#check @test24_eq
/--
info: 'test24_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test24_eq

-- ============================================================================
-- Test 25: letRange starting in the middle — tests that outer bindings are captured
-- ============================================================================

def test25 (x : U32) : Result U32 := do
  let a ← x + 1#u32     -- binding 0
  let b ← a + 2#u32     -- binding 1
  let c ← b + 3#u32     -- binding 2
  let d ← c + a         -- binding 3 (references a from binding 0)
  let e ← d + b         -- binding 4 (references b from binding 1)
  e + 1#u32

-- Extract bindings 2-4 (which reference a, b from outside the range)
#decompose test25 test25_eq
  letRange 2 3 => test25_middle

/--
info: def test25_middle : UScalar UScalarTy.U32 → UScalar UScalarTy.U32 → Result (UScalar UScalarTy.U32) :=
fun a b => do
  let c ← b + 3#u32
  let d ← c + a
  d + b
-/
#guard_msgs in
#print test25_middle
/--
info: test25_eq : ∀ (x : U32),
  test25 x = do
    let a ← x + 1#u32
    let b ← a + 2#u32
    let e ← test25_middle a b
    e + 1#u32
-/
#guard_msgs in
#check @test25_eq
/--
info: 'test25_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test25_eq

-- ============================================================================
-- Test 26: letAt navigating to binding 1's value (deeper navigation)
-- ============================================================================

def test26_aux1 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  a + 2#u32

def test26_aux2 (y : U32) : Result U32 := do
  let b ← y + 10#u32
  b + 20#u32

def test26 (x y : U32) : Result U32 := do
  let p ← test26_aux1 x    -- binding 0
  let q ← test26_aux2 y    -- binding 1 (we will navigate into this)
  p + q

-- Navigate to binding 1's value (test26_aux2 y) and extract it
#decompose test26 test26_eq
  letAt 1 (full) => test26_extracted

/--
info: def test26_extracted : U32 → Result U32 :=
fun y => test26_aux2 y
-/
#guard_msgs in
#print test26_extracted
/--
info: test26_eq : ∀ (x y : U32),
  test26 x y = do
    let p ← test26_aux1 x
    let q ← test26_extracted y
    p + q
-/
#guard_msgs in
#check @test26_eq
/--
info: 'test26_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test26_eq

-- ============================================================================
-- Test 27: Pure function with branch — full extraction from branch body
-- ============================================================================

def test27 (b : Bool) (x : Nat) : Nat :=
  if b then
    let a := x + 1
    let b := a + 2
    let c := b + 3
    c + a
  else
    x

#decompose test27 test27_eq
  branch 0 full => test27_then

/--
info: def test27_then : ℕ → ℕ :=
fun x =>
  have a := x + 1;
  have b := a + 2;
  have c := b + 3;
  c + a
-/
#guard_msgs in
#print test27_then
/--
info: test27_eq : ∀ (b : Bool) (x : ℕ), test27 b x = if b = true then test27_then x else x
-/
#guard_msgs in
#check @test27_eq
/--
info: 'test27_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test27_eq

-- ============================================================================
-- Test 28: Pure neededFVars == 0 — range where no variables are used by continuation
-- ============================================================================

-- In pure mode, when no range variables are used, the definition is created
-- but the body is just the continuation (let-reduction makes them equal by rfl)
def test28 (x : Nat) : Nat :=
  let _a := x + 1
  let _b := x + 2
  x + 3

#decompose test28 test28_eq
  letRange 0 2 => test28_unused

/--
info: def test28_unused : ℕ → ℕ :=
fun x => x + 2
-/
#guard_msgs in
#print test28_unused
/--
info: test28_eq : ∀ (x : ℕ), test28 x = x + 3
-/
#guard_msgs in
#check @test28_eq
/--
info: 'test28_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test28_eq

-- ============================================================================
-- Test 29: Universe polymorphism
-- ============================================================================

universe u
def test29 {α : Type u} (x : α) : α :=
  let a := x
  let b := a
  b

#decompose test29 test29_eq
  letRange 0 2 => test29_aux

/--
info: def test29_aux.{u} : {α : Type u} → α → α :=
fun {α} x =>
  let a := x;
  a
-/
#guard_msgs in
#print test29_aux
/--
info: @test29_eq : ∀ {α : Type u_1} (x : α),
  test29 x =
    let b := test29_aux x;
    b
-/
#guard_msgs in
#check @test29_eq
/--
info: 'test29_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test29_eq

-- ============================================================================
-- Test 30: Branch followed by letRange on both branches
-- ============================================================================

def test30 (b : Bool) (x y : U32) : Result U32 := do
  if b then
    let a ← x + 1#u32
    let r ← a + 2#u32
    r + y
  else
    let c ← y + 10#u32
    let d ← c + 20#u32
    d + x

#decompose test30 test30_eq
  branch 0 (letRange 0 2) => test30_then_prefix
  branch 1 (letRange 0 2) => test30_else_prefix

/--
info: def test30_then_prefix : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  a + 2#u32
-/
#guard_msgs in
#print test30_then_prefix
/--
info: def test30_else_prefix : U32 → Result (UScalar UScalarTy.U32) :=
fun y => do
  let c ← y + 10#u32
  c + 20#u32
-/
#guard_msgs in
#print test30_else_prefix
/--
info: test30_eq : ∀ (b : Bool) (x y : U32),
  test30 b x y =
    if b = true then do
      let r ← test30_then_prefix x
      r + y
    else do
      let d ← test30_else_prefix y
      d + x
-/
#guard_msgs in
#check @test30_eq
/--
info: 'test30_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test30_eq

-- ============================================================================
-- Test 31: Implicit type parameters
-- ============================================================================

def test31 {n : Nat} (x : Fin n) : Nat :=
  let a := x.val + 1
  let b := a + n
  b

#decompose test31 test31_eq
  letRange 0 2 => test31_aux

/--
info: def test31_aux : {n : ℕ} → Fin n → ℕ :=
fun {n} x =>
  let a := ↑x + 1;
  a + n
-/
#guard_msgs in
#print test31_aux
/--
info: @test31_eq : ∀ {n : ℕ} (x : Fin n),
  test31 x =
    let b := test31_aux x;
    b
-/
#guard_msgs in
#check @test31_eq
/--
info: 'test31_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test31_eq

-- ============================================================================
-- Test 32: Big monadic function (66 lines) with nested if-then-else
-- Stress test: decomposed into 10 auxiliary functions, from leaves to root.
-- ============================================================================

def test32 (mode : Bool) (flag : Bool) (x y z w : U32) : Result U32 := do
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

#decompose test32 test32_eq
  -- 1-4: Extract 10 heavy bindings from each inner branch
  branch 0 (branch 0 (letRange 0 10)) => test32_tt_comp
  branch 0 (branch 1 (letRange 0 10)) => test32_te_comp
  branch 1 (branch 0 (letRange 0 10)) => test32_et_comp
  branch 1 (branch 1 (letRange 0 10)) => test32_ee_comp
  -- 5-8: Extract remaining from each inner branch
  branch 0 (branch 0 full) => test32_tt
  branch 0 (branch 1 full) => test32_te
  branch 1 (branch 0 full) => test32_et
  branch 1 (branch 1 full) => test32_ee
  -- 9-10: Extract full outer branches
  branch 0 full => test32_then
  branch 1 full => test32_else

-- Verify all 10 generated definitions exist
/--
info: def test32_tt_comp : U32 →
  U32 →
    U32 →
      U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x y z w => do
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
  pure (c0, c3, c6, c9)
-/
#guard_msgs in
#print test32_tt_comp
/--
info: def test32_te_comp : U32 →
  U32 →
    U32 →
      U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x y z w => do
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
  pure (d0, d4, d7, d9)
-/
#guard_msgs in
#print test32_te_comp
/--
info: def test32_et_comp : U32 →
  U32 →
    U32 →
      U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x y z w => do
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
  pure (e0, e3, e6, e9)
-/
#guard_msgs in
#print test32_et_comp
/--
info: def test32_ee_comp : U32 →
  U32 →
    U32 →
      U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x y z w => do
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
  pure (f0, f4, f7, f9)
-/
#guard_msgs in
#print test32_ee_comp
/--
info: def test32_tt : U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y z w => do
  let (c0, c3, c6, c9) ← test32_tt_comp x y z w
  let r0 ← c0 + c3
  let r1 ← r0 + c6
  let r2 ← r1 + c9
  r2 + w
-/
#guard_msgs in
#print test32_tt
/--
info: def test32_te : U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y z w => do
  let (d0, d4, d7, d9) ← test32_te_comp x y z w
  let s0 ← d0 + d4
  let s1 ← s0 + d7
  let s2 ← s1 + d9
  s2 + w
-/
#guard_msgs in
#print test32_te
/--
info: def test32_et : U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y z w => do
  let (e0, e3, e6, e9) ← test32_et_comp x y z w
  let t0 ← e0 + e3
  let t1 ← t0 + e6
  let t2 ← t1 + e9
  t2 + y
-/
#guard_msgs in
#print test32_et
/--
info: def test32_ee : U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun x y z w => do
  let (f0, f4, f7, f9) ← test32_ee_comp x y z w
  let u0 ← f0 + f4
  let u1 ← u0 + f7
  let u2 ← u1 + f9
  u2 + z
-/
#guard_msgs in
#print test32_ee
/--
info: def test32_then : Bool → U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun flag x y z w => if flag = true then test32_tt x y z w else test32_te x y z w
-/
#guard_msgs in
#print test32_then
/--
info: def test32_else : Bool → U32 → U32 → U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun flag x y z w => if flag = true then test32_et x y z w else test32_ee x y z w
-/
#guard_msgs in
#print test32_else
/--
info: test32_eq : ∀ (mode flag : Bool) (x y z w : U32),
  test32 mode flag x y z w = if mode = true then test32_then flag x y z w else test32_else flag x y z w
-/
#guard_msgs in
#check @test32_eq
/--
info: 'test32_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test32_eq

-- ============================================================================
-- Test 33: Simple match on Nat — branch navigates into match alternatives
-- ============================================================================

def test33 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

-- Use `branch 1` to enter the successor case (alt index 1), then extract lets
#decompose test33 test33_eq
  branch 1 (letRange 0 3) => test33_succ_comp

/--
info: def test33_succ_comp : ℕ → ℕ :=
fun k =>
  let a := k + 1;
  let b := a + 1;
  b + 1
-/
#guard_msgs in
#print test33_succ_comp
/--
info: test33_eq : ∀ (n : ℕ),
  test33 n =
    match n with
    | 0 => 42
    | k.succ =>
      let c := test33_succ_comp k;
      c + k
-/
#guard_msgs in
#check @test33_eq
/--
info: 'test33_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test33_eq

-- ============================================================================
-- Test 34: Match on Bool
-- ============================================================================

def test34 (b : Bool) : Nat :=
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
#decompose test34 test34_eq
  branch 0 (letRange 0 2) => test34_true_comp
  branch 1 (letRange 0 2) => test34_false_comp

/--
info: def test34_true_comp : ℕ :=
let x := 100;
x + 200
-/
#guard_msgs in
#print test34_true_comp
/--
info: def test34_false_comp : ℕ :=
let x := 300;
x + 400
-/
#guard_msgs in
#print test34_false_comp
/--
info: test34_eq : ∀ (b : Bool),
  test34 b =
    match b with
    | true =>
      let y := test34_true_comp;
      y
    | false =>
      let y := test34_false_comp;
      y
-/
#guard_msgs in
#check @test34_eq
/--
info: 'test34_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test34_eq

-- ============================================================================
-- Test 35: Match on Option
-- ============================================================================

def test35 (o : Option Nat) : Nat :=
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
#decompose test35 test35_eq
  branch 1 (letRange 0 3) => test35_some_comp

/--
info: def test35_some_comp : ℕ → ℕ :=
fun v =>
  let a := v + 10;
  let b := a + 20;
  b + 30
-/
#guard_msgs in
#print test35_some_comp
/--
info: test35_eq : ∀ (o : Option ℕ),
  test35 o =
    match o with
    | none =>
      have a := 0;
      have b := a + 1;
      b
    | some v =>
      let c := test35_some_comp v;
      c
-/
#guard_msgs in
#check @test35_eq
/--
info: 'test35_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test35_eq

-- ============================================================================
-- Test 36: Match on custom enum with many constructors
-- ============================================================================

inductive Color where
  | red | green | blue | yellow

def test36 (c : Color) : Nat :=
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
#decompose test36 test36_eq
  branch 0 (letRange 0 2) => test36_red
  branch 1 (letRange 0 2) => test36_green
  branch 2 (letRange 0 2) => test36_blue
  branch 3 (letRange 0 2) => test36_yellow

/--
info: def test36_red : ℕ :=
let a := 1;
a + 2
-/
#guard_msgs in
#print test36_red
/--
info: def test36_green : ℕ :=
let a := 3;
a + 4
-/
#guard_msgs in
#print test36_green
/--
info: def test36_blue : ℕ :=
let a := 5;
a + 6
-/
#guard_msgs in
#print test36_blue
/--
info: def test36_yellow : ℕ :=
let a := 7;
a + 8
-/
#guard_msgs in
#print test36_yellow
/--
info: test36_eq : ∀ (c : Color),
  test36 c =
    match c with
    | Color.red =>
      let b := test36_red;
      b
    | Color.green =>
      let b := test36_green;
      b
    | Color.blue =>
      let b := test36_blue;
      b
    | Color.yellow =>
      let b := test36_yellow;
      b
-/
#guard_msgs in
#check @test36_eq
/--
info: 'test36_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test36_eq

-- ============================================================================
-- Test 37: Match with full extraction of a branch
-- ============================================================================

def test37 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k * 2
    let b := a + 3
    b

-- Extract the full successor branch body
#decompose test37 test37_eq
  branch 1 full => test37_succ

/--
info: def test37_succ : ℕ → ℕ :=
fun k =>
  have a := k * 2;
  have b := a + 3;
  b
-/
#guard_msgs in
#print test37_succ
/--
info: test37_eq : ∀ (n : ℕ),
  test37 n =
    match n with
    | 0 => 42
    | k.succ => test37_succ k
-/
#guard_msgs in
#check @test37_eq
/--
info: 'test37_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test37_eq

-- ============================================================================
-- Test 38: Nested match — match inside a match branch
-- ============================================================================

def test38 (n : Nat) (b : Bool) : Nat :=
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
#decompose test38 test38_eq
  branch 1 (branch 0 (letRange 0 2)) => test38_succ_true_comp
  branch 1 (branch 1 (letRange 0 2)) => test38_succ_false_comp

/--
info: def test38_succ_true_comp : ℕ → ℕ :=
fun k =>
  let a := k + 100;
  a + 200
-/
#guard_msgs in
#print test38_succ_true_comp
/--
info: def test38_succ_false_comp : ℕ → ℕ :=
fun k =>
  let a := k + 300;
  a + 400
-/
#guard_msgs in
#print test38_succ_false_comp
/--
info: test38_eq : ∀ (n : ℕ) (b : Bool),
  test38 n b =
    match n with
    | 0 => 0
    | k.succ =>
      match b with
      | true =>
        let b := test38_succ_true_comp k;
        b
      | false =>
        let b := test38_succ_false_comp k;
        b
-/
#guard_msgs in
#check @test38_eq
/--
info: 'test38_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test38_eq

-- ============================================================================
-- Test 39: Monadic match — match in the Result monad
-- ============================================================================

def test39 (n : Nat) : Result Nat := do
  match n with
  | 0 => .ok 42
  | k + 1 =>
    let a ← .ok (k + 10)
    let b ← .ok (a + 1)
    .ok b

-- The match is directly at the top of the do-block body, so `branch` works directly
#decompose test39 test39_eq
  branch 1 (letRange 0 2) => test39_succ_comp

/--
info: def test39_succ_comp : ℕ → Result ℕ :=
fun k => do
  let a ← Result.ok (k + 10)
  Result.ok (a + 1)
-/
#guard_msgs in
#print test39_succ_comp
/--
info: test39_eq : ∀ (n : ℕ),
  test39 n =
    match n with
    | 0 => Result.ok 42
    | k.succ => do
      let b ← test39_succ_comp k
      Result.ok b
-/
#guard_msgs in
#check @test39_eq
/--
info: 'test39_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test39_eq

-- ============================================================================
-- Test 40: Match with struct pattern — multiple pattern variables
-- ============================================================================

structure Point where
  x : Nat
  y : Nat

def test40 (p : Point) : Nat :=
  match p with
  | ⟨x, y⟩ =>
    let a := x + y
    let b := a * 2
    let c := b + 1
    c

-- The Point match has 1 alternative with 2 pattern variables (x, y)
#decompose test40 test40_eq
  branch 0 (letRange 0 3) => test40_comp

/--
info: def test40_comp : ℕ → ℕ → ℕ :=
fun x y =>
  let a := x + y;
  let b := a * 2;
  b + 1
-/
#guard_msgs in
#print test40_comp
/--
info: test40_eq : ∀ (p : Point),
  test40 p =
    match p with
    | { x := x, y := y } =>
      let c := test40_comp x y;
      c
-/
#guard_msgs in
#check @test40_eq
/--
info: 'test40_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test40_eq

-- ============================================================================
-- Test 41: Match on Sum type
-- ============================================================================

def test41 (s : Nat ⊕ Bool) : Nat :=
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
#decompose test41 test41_eq
  branch 0 (letRange 0 2) => test41_inl_comp
  branch 1 (letRange 0 2) => test41_inr_comp

/--
info: def test41_inl_comp : ℕ → ℕ :=
fun n =>
  let a := n + 1;
  a + 2
-/
#guard_msgs in
#print test41_inl_comp
/--
info: def test41_inr_comp : Bool → ℕ :=
fun b =>
  let x := if b = true then 100 else 200;
  x + 3
-/
#guard_msgs in
#print test41_inr_comp
/--
info: test41_eq : ∀ (s : ℕ ⊕ Bool),
  test41 s =
    match s with
    | Sum.inl n =>
      let b := test41_inl_comp n;
      b
    | Sum.inr b =>
      let y := test41_inr_comp b;
      y
-/
#guard_msgs in
#check @test41_eq
/--
info: 'test41_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test41_eq

-- ============================================================================
-- Test 42: Match combined with if-then-else inside a branch
-- ============================================================================

def test42 (n : Nat) (flag : Bool) : Nat :=
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
#decompose test42 test42_eq
  branch 1 (branch 0 (letRange 0 2)) => test42_succ_then_comp
  branch 1 (branch 1 (letRange 0 2)) => test42_succ_else_comp

/--
info: def test42_succ_then_comp : ℕ → ℕ :=
fun k =>
  let a := k + 10;
  a + 20
-/
#guard_msgs in
#print test42_succ_then_comp
/--
info: def test42_succ_else_comp : ℕ → ℕ :=
fun k =>
  let a := k + 30;
  a + 40
-/
#guard_msgs in
#print test42_succ_else_comp
/--
info: test42_eq : ∀ (n : ℕ) (flag : Bool),
  test42 n flag =
    match n with
    | 0 => 0
    | k.succ =>
      if flag = true then
        let b := test42_succ_then_comp k;
        b
      else
        let b := test42_succ_else_comp k;
        b
-/
#guard_msgs in
#check @test42_eq
/--
info: 'test42_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test42_eq

-- ============================================================================
-- Test 43: Rewrite test21 using branch instead of argArg (regression check)
-- ============================================================================

-- test21 used `argArg 3 (lam 1 ...)` to navigate the match; now branch should work
def test43 (n : Nat) : Nat :=
  match n with
  | 0 => 42
  | k + 1 =>
    let a := k + 1
    let b := a + 1
    let c := b + 1
    c + k

#decompose test43 test43_eq
  branch 1 (letRange 0 3) => test43_compute

-- Verify this produces the same result as test21 did with argArg
/--
info: def test43_compute : ℕ → ℕ :=
fun k =>
  let a := k + 1;
  let b := a + 1;
  b + 1
-/
#guard_msgs in
#print test43_compute
/--
info: test43_eq : ∀ (n : ℕ),
  test43 n =
    match n with
    | 0 => 42
    | k.succ =>
      let c := test43_compute k;
      c + k
-/
#guard_msgs in
#check @test43_eq
/--
info: 'test43_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test43_eq

-- ============================================================================
-- Test 44: Big match with many branches, extracting from all — performance test
-- ============================================================================

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun

def test44 (d : Weekday) : Nat :=
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

#decompose test44 test44_eq
  branch 0 (letRange 0 5) => test44_mon
  branch 1 (letRange 0 5) => test44_tue
  branch 2 (letRange 0 5) => test44_wed
  branch 3 (letRange 0 5) => test44_thu
  branch 4 (letRange 0 5) => test44_fri
  branch 5 (letRange 0 5) => test44_sat
  branch 6 (letRange 0 5) => test44_sun

/--
info: def test44_mon : ℕ :=
let a := 1;
let b := a + 2;
let c := b + 3;
let d := c + 4;
d + 5
-/
#guard_msgs in
#print test44_mon
/--
info: def test44_tue : ℕ :=
let a := 10;
let b := a + 20;
let c := b + 30;
let d := c + 40;
d + 50
-/
#guard_msgs in
#print test44_tue
/--
info: def test44_wed : ℕ :=
let a := 100;
let b := a + 200;
let c := b + 300;
let d := c + 400;
d + 500
-/
#guard_msgs in
#print test44_wed
/--
info: def test44_thu : ℕ :=
let a := 1000;
let b := a + 2000;
let c := b + 3000;
let d := c + 4000;
d + 5000
-/
#guard_msgs in
#print test44_thu
/--
info: def test44_fri : ℕ :=
let a := 10000;
let b := a + 20000;
let c := b + 30000;
let d := c + 40000;
d + 50000
-/
#guard_msgs in
#print test44_fri
/--
info: def test44_sat : ℕ :=
let a := 100000;
let b := a + 200000;
let c := b + 300000;
let d := c + 400000;
d + 500000
-/
#guard_msgs in
#print test44_sat
/--
info: def test44_sun : ℕ :=
let a := 1000000;
let b := a + 2000000;
let c := b + 3000000;
let d := c + 4000000;
d + 5000000
-/
#guard_msgs in
#print test44_sun
/--
info: test44_eq : ∀ (d : Weekday),
  test44 d =
    match d with
    | Weekday.mon =>
      let e := test44_mon;
      e
    | Weekday.tue =>
      let e := test44_tue;
      e
    | Weekday.wed =>
      let e := test44_wed;
      e
    | Weekday.thu =>
      let e := test44_thu;
      e
    | Weekday.fri =>
      let e := test44_fri;
      e
    | Weekday.sat =>
      let e := test44_sat;
      e
    | Weekday.sun =>
      let e := test44_sun;
      e
-/
#guard_msgs in
#check @test44_eq
/--
info: 'test44_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test44_eq

-- ============================================================================
-- Test 45: Match with branch index out of bounds (error test)
-- ============================================================================

def test45 (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 2

-- Bool match has 2 alts (0 and 1); index 2 should fail
/--
error: branch 2: match has only 2 alternative(s) (0-indexed)
-/
#guard_msgs in
#decompose test45 test45_eq
  branch 2 full => test45_bad

-- ============================================================================
-- Test 46: Match on list — nil and cons with multiple pattern variables
-- ============================================================================

def test46 (l : List Nat) : Nat :=
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
#decompose test46 test46_eq
  branch 0 (letRange 0 2) => test46_nil_comp
  branch 1 (letRange 0 3) => test46_cons_comp

/--
info: def test46_nil_comp : ℕ :=
let a := 0;
a + 1
-/
#guard_msgs in
#print test46_nil_comp
/--
info: def test46_cons_comp : ℕ → List ℕ → ℕ :=
fun hd tl =>
  let a := hd + tl.length;
  let b := a + 100;
  b + 200
-/
#guard_msgs in
#print test46_cons_comp
/--
info: test46_eq : ∀ (l : List ℕ),
  test46 l =
    match l with
    | [] =>
      let b := test46_nil_comp;
      b
    | hd :: tl =>
      let c := test46_cons_comp hd tl;
      c
-/
#guard_msgs in
#check @test46_eq
/--
info: 'test46_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms test46_eq

-- ============================================================================
-- Test 47: Tuple bind with Aeneas do — pair destructuring (Function.uncurry)
-- ============================================================================


def test47 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let (b, c) ← Result.ok (a, a)
  b + c

#decompose test47 test47_eq
  letRange 0 1 => test47_prefix

/--
info: def test47_prefix : U32 → Result (UScalar UScalarTy.U32) :=
fun x => x + 1#u32
-/
#guard_msgs in
#print test47_prefix
/--
info: test47_eq : ∀ (x : U32),
  test47 x = do
    let a ← test47_prefix x
    let (b, c) ← Result.ok (a, a)
    b + c
-/
#guard_msgs in
#check @test47_eq
/--
info: 'test47_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test47_eq

-- ============================================================================
-- Test 48: Tuple bind — extracting the range AFTER the tuple bind
-- ============================================================================

def test48 (x : U32) : Result U32 := do
  let (a, b) ← Result.ok (x, x)
  let c ← a + 1#u32
  let d ← b + 2#u32
  c + d

#decompose test48 test48_eq
  letRange 1 3 => test48_suffix

/--
info: def test48_suffix : U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun a b => do
  let c ← a + 1#u32
  let d ← b + 2#u32
  c + d
-/
#guard_msgs in
#print test48_suffix
/--
info: test48_eq : ∀ (x : U32),
  test48 x = do
    let (a, b) ← Result.ok (x, x)
    test48_suffix a b
-/
#guard_msgs in
#check @test48_eq
/--
info: 'test48_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test48_eq

-- ============================================================================
-- Test 49: Triple tuple bind — 3-component destructuring
-- ============================================================================

def test49 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let (b, c, d) ← Result.ok (a, a, a)
  let r ← b + c
  r + d

#decompose test49 test49_eq
  letRange 0 1 => test49_prefix

/--
info: def test49_prefix : U32 → Result (UScalar UScalarTy.U32) :=
fun x => x + 1#u32
-/
#guard_msgs in
#print test49_prefix
/--
info: test49_eq : ∀ (x : U32),
  test49 x = do
    let a ← test49_prefix x
    let (b, c, d) ← Result.ok (a, a, a)
    let r ← b + c
    r + d
-/
#guard_msgs in
#check @test49_eq
/--
info: 'test49_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test49_eq

-- ============================================================================
-- Test 50: Tuple bind — extracting including the tuple bind itself
-- ============================================================================

def test50 (x : U32) : Result U32 := do
  let a ← x + 1#u32
  let (b, c) ← Result.ok (a, a)
  let r ← b + c
  r + 1#u32

-- Extract the first 2 bindings: a ← ..., (b, c) ← ...
#decompose test50 test50_eq
  letRange 0 2 => test50_prefix

/--
info: def test50_prefix : U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let a ← x + 1#u32
  let (b, c) ← Result.ok (a, a)
  pure (b, c)
-/
#guard_msgs in
#print test50_prefix
/--
info: test50_eq : ∀ (x : U32),
  test50 x = do
    let (b, c) ← test50_prefix x
    let r ← b + c
    r + 1#u32
-/
#guard_msgs in
#check @test50_eq
/--
info: 'test50_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test50_eq

-- ============================================================================
-- Test 51: Tuple bind with subsequent extraction — both before and after
-- ============================================================================

def test51 (x y : U32) : Result U32 := do
  let a ← x + 1#u32
  let (b, c) ← Result.ok (a, y)
  let d ← b + c
  let e ← d + 1#u32
  e + 2#u32

-- Extract only the suffix (d, e, terminal)
#decompose test51 test51_eq
  letRange 2 3 => test51_suffix

/--
info: def test51_suffix : UScalar UScalarTy.U32 → U32 → Result (UScalar UScalarTy.U32) :=
fun b c => do
  let d ← b + c
  let e ← d + 1#u32
  e + 2#u32
-/
#guard_msgs in
#print test51_suffix
/--
info: test51_eq : ∀ (x y : U32),
  test51 x y = do
    let a ← x + 1#u32
    let (b, c) ← Result.ok (a, y)
    test51_suffix b c
-/
#guard_msgs in
#check @test51_eq
/--
info: 'test51_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test51_eq

-- ============================================================================
-- Test 52: Name reuse — same extraction applied to two symmetric ranges
-- ============================================================================

def test52 (x y : U32) : Result U32 := do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  let x3 ← x2 + 1#u32
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  let y3 ← y2 + 1#u32
  x3 + y3

-- Both ranges extract the same function (add 3 to input), so name reuse should work
#decompose test52 test52_eq
  letRange 0 3 => test52_add3
  letRange 1 3 => test52_add3

/--
info: def test52_add3 : U32 → Result (UScalar UScalarTy.U32) :=
fun x => do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  x2 + 1#u32
-/
#guard_msgs in
#print test52_add3
/--
info: test52_eq : ∀ (x y : U32),
  test52 x y = do
    let x3 ← test52_add3 x
    let y3 ← test52_add3 y
    x3 + y3
-/
#guard_msgs in
#check @test52_eq
/--
info: 'test52_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test52_eq

-- ============================================================================
-- Test 53: Name reuse failure — different extractions with same name should error
-- ============================================================================

def test53 (x y : U32) : Result U32 := do
  let x1 ← x + 1#u32
  let y1 ← y + 2#u32
  x1 + y1

/--
error: #decompose: cannot apply letRange 1 1 => test53_aux: definition 'test53_aux' already exists with body
  fun x => x + 1#u32
but the new extraction produced
  fun y => y + 2#u32
which is not definitionally equal (at reducible transparency)
-/
#guard_msgs in
#decompose test53 test53_eq
  letRange 0 1 => test53_aux
  letRange 1 1 => test53_aux

-- ============================================================================
-- Test 54: Duplicate definition warning — different names, same body
-- ============================================================================

def test54 (x y : U32) : Result U32 := do
  let x1 ← x + 1#u32
  let x2 ← x1 + 1#u32
  let x3 ← x2 + 1#u32
  let y1 ← y + 1#u32
  let y2 ← y1 + 1#u32
  let y3 ← y2 + 1#u32
  x3 + y3

-- Same body extracted with different names → should warn
/--
warning: #decompose: 'test54_add3b' has the same definition as 'test54_add3a' (consider reusing the same name)
-/
#guard_msgs in
#decompose test54 test54_eq
  letRange 0 3 => test54_add3a
  letRange 1 3 => test54_add3b


-- ============================================================================
-- Test 55: Performance — 100 let bindings, 25 decompositions reusing one name
-- ============================================================================

def test55 (v1 : U32) (v2 : U32) (v3 : U32) (v4 : U32) (v5 : U32) (v6 : U32) (v7 : U32) (v8 : U32) (v9 : U32) (v10 : U32) (v11 : U32) (v12 : U32) (v13 : U32) (v14 : U32) (v15 : U32) (v16 : U32) (v17 : U32) (v18 : U32) (v19 : U32) (v20 : U32) (v21 : U32) (v22 : U32) (v23 : U32) (v24 : U32) (v25 : U32) : Result U32 := do
  let v1_1 ← v1 + 1#u32; let v1_2 ← v1_1 + 1#u32; let v1_3 ← v1_2 + 1#u32; let v1_4 ← v1_3 + 1#u32
  let v2_1 ← v2 + 1#u32; let v2_2 ← v2_1 + 1#u32; let v2_3 ← v2_2 + 1#u32; let v2_4 ← v2_3 + 1#u32
  let v3_1 ← v3 + 1#u32; let v3_2 ← v3_1 + 1#u32; let v3_3 ← v3_2 + 1#u32; let v3_4 ← v3_3 + 1#u32
  let v4_1 ← v4 + 1#u32; let v4_2 ← v4_1 + 1#u32; let v4_3 ← v4_2 + 1#u32; let v4_4 ← v4_3 + 1#u32
  let v5_1 ← v5 + 1#u32; let v5_2 ← v5_1 + 1#u32; let v5_3 ← v5_2 + 1#u32; let v5_4 ← v5_3 + 1#u32
  let v6_1 ← v6 + 1#u32; let v6_2 ← v6_1 + 1#u32; let v6_3 ← v6_2 + 1#u32; let v6_4 ← v6_3 + 1#u32
  let v7_1 ← v7 + 1#u32; let v7_2 ← v7_1 + 1#u32; let v7_3 ← v7_2 + 1#u32; let v7_4 ← v7_3 + 1#u32
  let v8_1 ← v8 + 1#u32; let v8_2 ← v8_1 + 1#u32; let v8_3 ← v8_2 + 1#u32; let v8_4 ← v8_3 + 1#u32
  let v9_1 ← v9 + 1#u32; let v9_2 ← v9_1 + 1#u32; let v9_3 ← v9_2 + 1#u32; let v9_4 ← v9_3 + 1#u32
  let v10_1 ← v10 + 1#u32; let v10_2 ← v10_1 + 1#u32; let v10_3 ← v10_2 + 1#u32; let v10_4 ← v10_3 + 1#u32
  let v11_1 ← v11 + 1#u32; let v11_2 ← v11_1 + 1#u32; let v11_3 ← v11_2 + 1#u32; let v11_4 ← v11_3 + 1#u32
  let v12_1 ← v12 + 1#u32; let v12_2 ← v12_1 + 1#u32; let v12_3 ← v12_2 + 1#u32; let v12_4 ← v12_3 + 1#u32
  let v13_1 ← v13 + 1#u32; let v13_2 ← v13_1 + 1#u32; let v13_3 ← v13_2 + 1#u32; let v13_4 ← v13_3 + 1#u32
  let v14_1 ← v14 + 1#u32; let v14_2 ← v14_1 + 1#u32; let v14_3 ← v14_2 + 1#u32; let v14_4 ← v14_3 + 1#u32
  let v15_1 ← v15 + 1#u32; let v15_2 ← v15_1 + 1#u32; let v15_3 ← v15_2 + 1#u32; let v15_4 ← v15_3 + 1#u32
  let v16_1 ← v16 + 1#u32; let v16_2 ← v16_1 + 1#u32; let v16_3 ← v16_2 + 1#u32; let v16_4 ← v16_3 + 1#u32
  let v17_1 ← v17 + 1#u32; let v17_2 ← v17_1 + 1#u32; let v17_3 ← v17_2 + 1#u32; let v17_4 ← v17_3 + 1#u32
  let v18_1 ← v18 + 1#u32; let v18_2 ← v18_1 + 1#u32; let v18_3 ← v18_2 + 1#u32; let v18_4 ← v18_3 + 1#u32
  let v19_1 ← v19 + 1#u32; let v19_2 ← v19_1 + 1#u32; let v19_3 ← v19_2 + 1#u32; let v19_4 ← v19_3 + 1#u32
  let v20_1 ← v20 + 1#u32; let v20_2 ← v20_1 + 1#u32; let v20_3 ← v20_2 + 1#u32; let v20_4 ← v20_3 + 1#u32
  let v21_1 ← v21 + 1#u32; let v21_2 ← v21_1 + 1#u32; let v21_3 ← v21_2 + 1#u32; let v21_4 ← v21_3 + 1#u32
  let v22_1 ← v22 + 1#u32; let v22_2 ← v22_1 + 1#u32; let v22_3 ← v22_2 + 1#u32; let v22_4 ← v22_3 + 1#u32
  let v23_1 ← v23 + 1#u32; let v23_2 ← v23_1 + 1#u32; let v23_3 ← v23_2 + 1#u32; let v23_4 ← v23_3 + 1#u32
  let v24_1 ← v24 + 1#u32; let v24_2 ← v24_1 + 1#u32; let v24_3 ← v24_2 + 1#u32; let v24_4 ← v24_3 + 1#u32
  let v25_1 ← v25 + 1#u32; let v25_2 ← v25_1 + 1#u32; let v25_3 ← v25_2 + 1#u32; let v25_4 ← v25_3 + 1#u32
  let s1 ← v1_4 + v2_4
  let s2 ← s1 + v3_4
  let s3 ← s2 + v4_4
  let s4 ← s3 + v5_4
  let s5 ← s4 + v6_4
  let s6 ← s5 + v7_4
  let s7 ← s6 + v8_4
  let s8 ← s7 + v9_4
  let s9 ← s8 + v10_4
  let s10 ← s9 + v11_4
  let s11 ← s10 + v12_4
  let s12 ← s11 + v13_4
  let s13 ← s12 + v14_4
  let s14 ← s13 + v15_4
  let s15 ← s14 + v16_4
  let s16 ← s15 + v17_4
  let s17 ← s16 + v18_4
  let s18 ← s17 + v19_4
  let s19 ← s18 + v20_4
  let s20 ← s19 + v21_4
  let s21 ← s20 + v22_4
  let s22 ← s21 + v23_4
  let s23 ← s22 + v24_4
  let s24 ← s23 + v25_4
  pure s24

#decompose test55 test55_eq
  letRange 0 4 => test55_add4
  letRange 1 4 => test55_add4
  letRange 2 4 => test55_add4
  letRange 3 4 => test55_add4
  letRange 4 4 => test55_add4
  letRange 5 4 => test55_add4
  letRange 6 4 => test55_add4
  letRange 7 4 => test55_add4
  letRange 8 4 => test55_add4
  letRange 9 4 => test55_add4
  letRange 10 4 => test55_add4
  letRange 11 4 => test55_add4
  letRange 12 4 => test55_add4
  letRange 13 4 => test55_add4
  letRange 14 4 => test55_add4
  letRange 15 4 => test55_add4
  letRange 16 4 => test55_add4
  letRange 17 4 => test55_add4
  letRange 18 4 => test55_add4
  letRange 19 4 => test55_add4
  letRange 20 4 => test55_add4
  letRange 21 4 => test55_add4
  letRange 22 4 => test55_add4
  letRange 23 4 => test55_add4
  letRange 24 4 => test55_add4

/--
info: 'test55_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test55_eq

-- ============================================================================
-- Test 56: Performance — if-then-else with 50 let-bindings per branch
-- ============================================================================

def test56 (b : Bool) (x y : U32) : Result U32 := do
  if b then
    let a1 ← x + 1#u32
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
    let a30 ← a29 + 1#u32
    let a31 ← a30 + 1#u32
    let a32 ← a31 + 1#u32
    let a33 ← a32 + 1#u32
    let a34 ← a33 + 1#u32
    let a35 ← a34 + 1#u32
    let a36 ← a35 + 1#u32
    let a37 ← a36 + 1#u32
    let a38 ← a37 + 1#u32
    let a39 ← a38 + 1#u32
    let a40 ← a39 + 1#u32
    let a41 ← a40 + 1#u32
    let a42 ← a41 + 1#u32
    let a43 ← a42 + 1#u32
    let a44 ← a43 + 1#u32
    let a45 ← a44 + 1#u32
    let a46 ← a45 + 1#u32
    let a47 ← a46 + 1#u32
    let a48 ← a47 + 1#u32
    let a49 ← a48 + 1#u32
    let a50 ← a49 + 1#u32
    pure a50
  else
    let b1 ← y + 2#u32
    let b2 ← b1 + 2#u32
    let b3 ← b2 + 2#u32
    let b4 ← b3 + 2#u32
    let b5 ← b4 + 2#u32
    let b6 ← b5 + 2#u32
    let b7 ← b6 + 2#u32
    let b8 ← b7 + 2#u32
    let b9 ← b8 + 2#u32
    let b10 ← b9 + 2#u32
    let b11 ← b10 + 2#u32
    let b12 ← b11 + 2#u32
    let b13 ← b12 + 2#u32
    let b14 ← b13 + 2#u32
    let b15 ← b14 + 2#u32
    let b16 ← b15 + 2#u32
    let b17 ← b16 + 2#u32
    let b18 ← b17 + 2#u32
    let b19 ← b18 + 2#u32
    let b20 ← b19 + 2#u32
    let b21 ← b20 + 2#u32
    let b22 ← b21 + 2#u32
    let b23 ← b22 + 2#u32
    let b24 ← b23 + 2#u32
    let b25 ← b24 + 2#u32
    let b26 ← b25 + 2#u32
    let b27 ← b26 + 2#u32
    let b28 ← b27 + 2#u32
    let b29 ← b28 + 2#u32
    let b30 ← b29 + 2#u32
    let b31 ← b30 + 2#u32
    let b32 ← b31 + 2#u32
    let b33 ← b32 + 2#u32
    let b34 ← b33 + 2#u32
    let b35 ← b34 + 2#u32
    let b36 ← b35 + 2#u32
    let b37 ← b36 + 2#u32
    let b38 ← b37 + 2#u32
    let b39 ← b38 + 2#u32
    let b40 ← b39 + 2#u32
    let b41 ← b40 + 2#u32
    let b42 ← b41 + 2#u32
    let b43 ← b42 + 2#u32
    let b44 ← b43 + 2#u32
    let b45 ← b44 + 2#u32
    let b46 ← b45 + 2#u32
    let b47 ← b46 + 2#u32
    let b48 ← b47 + 2#u32
    let b49 ← b48 + 2#u32
    let b50 ← b49 + 2#u32
    pure b50

#decompose test56 test56_eq
  branch 0 full => test56_then
  branch 1 full => test56_else

/--
info: 'test56_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test56_eq
