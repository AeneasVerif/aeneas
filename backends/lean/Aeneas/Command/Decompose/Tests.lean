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
-- Test 55: Tuple-destructuring bind with letAt — regression test
-- letAt N for N > 0 should work when an earlier bind uses tuple destructuring
-- ============================================================================

namespace test55_ns
open Aeneas Aeneas.Std Result

/-- A function with a tuple-destructuring monadic bind. -/
def f (x : U32) : Result U32 := do
  let (a, b) ← (do let v ← x + 1#u32; ok (v, v))
  let c ← b + 1#u32
  c + a

-- Probe 1: trivial first-binding extraction works (no `letAt`).
#decompose f f_prefix_eq
  letRange 0 1 => f_prefix

/--
info: f_prefix_eq : ∀ (x : U32),
  f x = do
    let (a, b) ← f_prefix x
    let c ← b + 1#u32
    c + a
-/
#guard_msgs in
#check @f_prefix_eq
/--
info: def test55_ns.f_prefix : U32 → Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let (a, b) ←
    do
      let v ← x + 1#u32
      ok (v, v)
  pure (a, b)
-/
#guard_msgs in
#print f_prefix

-- Probe 2: `letAt 1 (full)` to extract the value of the *second* binding
-- (the `c ← b + 1#u32`). The first binding has tuple-destructured `(a, b)`.
#decompose f f_letat1_eq
  letAt 1 (full) => f_second_value

/--
info: f_letat1_eq : ∀ (x : U32),
  f x = do
    let (a, b) ←
      do
        let v ← x + 1#u32
        ok (v, v)
    let c ← f_second_value b
    c + a
-/
#guard_msgs in
#check @f_letat1_eq
/--
info: def test55_ns.f_second_value : UScalar UScalarTy.U32 → Result (UScalar UScalarTy.U32) :=
fun b => b + 1#u32
-/
#guard_msgs in
#print f_second_value

end test55_ns

-- ============================================================================
-- Test 56: Nested tuple-destructuring bind with letRange — regression test
-- ============================================================================

namespace test56_ns
open Aeneas Aeneas.Std Result

/-- A function with a nested tuple-destructuring monadic bind. -/
def g (x : U32) : Result U32 := do
  let ((a, b), (c, d)) ← (do
    let v ← x + 1#u32
    let w ← x + 2#u32
    ok ((v, w), (w, v)))
  let e ← a + c
  let f ← b + d
  e + f

-- letRange on the first binding works (extracts the whole tuple computation)
#decompose g g_prefix_eq
  letRange 0 1 => g_prefix

/--
info: g_prefix_eq : ∀ (x : U32),
  g x = do
    let (a, b, c, d) ← g_prefix x
    let e ← a + c
    let f ← b + d
    e + f
-/
#guard_msgs in
#check @g_prefix_eq
/--
info: def test56_ns.g_prefix : U32 →
  Result (UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32 × UScalar UScalarTy.U32) :=
fun x => do
  let (a, b, c, d) ←
    do
      let v ← x + 1#u32
      let w ← x + 2#u32
      ok ((v, w), w, v)
  pure (a, b, c, d)
-/
#guard_msgs in
#print g_prefix

end test56_ns
