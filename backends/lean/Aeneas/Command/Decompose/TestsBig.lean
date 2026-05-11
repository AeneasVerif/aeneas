/-
Big tests for the #decompose command (performance/stress tests)
-/
import Aeneas.Command.Decompose
import Aeneas.Std
import Aeneas.Do.Elab
import Aeneas.Do.Delab

open Aeneas.Std
open Aeneas.Command.Decompose

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
info: 'test14_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms test14_eq


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
info: 'test44_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms test44_eq

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
