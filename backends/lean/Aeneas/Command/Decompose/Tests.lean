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
