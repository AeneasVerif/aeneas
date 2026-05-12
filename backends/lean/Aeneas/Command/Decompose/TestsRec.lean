/-
Tests for `#decompose` on recursive functions (WF recursion, partial_fixpoint,
structural recursion).
-/
import Aeneas.Command.Decompose
import Aeneas.Std
import Aeneas.Do.Elab
import Aeneas.Do.Delab

open Aeneas.Std
open Aeneas.Command.Decompose

-- ============================================================================
-- Test 1: partial_fixpoint — extract from inside the else branch
-- ============================================================================

def recPF1 (n : Nat) : Result Nat := do
  if n == 0 then .ok 0
  else
    let a ← recPF1 (n - 1)
    let b ← .ok (a + 1)
    let c ← .ok (b + 2)
    .ok (a + c)
partial_fixpoint

-- Extract the two let-bindings inside the else branch
#decompose recPF1 recPF1_eq
  branch 1 (letRange 1 2) => recPF1_add

/--
info: recPF1_eq : ∀ (n : ℕ),
  recPF1 n =
    if (n == 0) = true then Result.ok 0
    else do
      let a ← recPF1 (n - 1)
      let c ← recPF1_add a
      Result.ok (a + c)
-/
#guard_msgs in
#check @recPF1_eq
/--
info: def recPF1_add : ℕ → Result ℕ :=
fun a => do
  let b ← Result.ok (a + 1)
  Result.ok (b + 2)
-/
#guard_msgs in
#print recPF1_add
/--
info: 'recPF1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recPF1_eq

-- ============================================================================
-- Test 2: partial_fixpoint — extract from inside the then branch
-- ============================================================================

def recPF2 (n : Nat) : Result Nat := do
  if n == 0 then
    let x ← .ok 42
    let y ← .ok (x + 1)
    .ok y
  else
    let a ← recPF2 (n - 1)
    .ok (a + 1)
partial_fixpoint

#decompose recPF2 recPF2_eq
  branch 0 full => recPF2_base

/--
info: recPF2_eq : ∀ (n : ℕ),
  recPF2 n =
    if (n == 0) = true then recPF2_base
    else do
      let a ← recPF2 (n - 1)
      Result.ok (a + 1)
-/
#guard_msgs in
#check @recPF2_eq
/--
info: def recPF2_base : Result ℕ :=
do
  let x ← Result.ok 42
  let y ← Result.ok (x + 1)
  Result.ok y
-/
#guard_msgs in
#print recPF2_base

-- ============================================================================
-- Test 3: structural recursion on List — extract from the cons branch
-- ============================================================================

def recStruct : List Nat → Result Nat
  | [] => .ok 0
  | x :: xs => do
    let rest ← recStruct xs
    let inc ← .ok (rest + 1)
    .ok (x + inc)

#decompose recStruct recStruct_eq
  branch 1 (letRange 1 1) => recStruct_inc

/--
info: recStruct_eq : ∀ (x : List ℕ),
  recStruct x =
    match x with
    | [] => Result.ok 0
    | x :: xs => do
      let rest ← recStruct xs
      let inc ← recStruct_inc rest
      Result.ok (x + inc)
-/
#guard_msgs in
#check @recStruct_eq
/--
info: def recStruct_inc : ℕ → Result ℕ :=
fun rest => Result.ok (rest + 1)
-/
#guard_msgs in
#print recStruct_inc

-- ============================================================================
-- Test 4: partial_fixpoint — full extraction of the else branch
-- ============================================================================

def recPF3 (n : Nat) : Result Nat := do
  if n == 0 then .ok 0
  else
    let a ← recPF3 (n - 1)
    let b ← .ok (a + 1)
    .ok b
partial_fixpoint

#decompose recPF3 recPF3_eq
  branch 1 full => recPF3_else

/--
info: recPF3_eq : ∀ (n : ℕ), recPF3 n = if (n == 0) = true then Result.ok 0 else recPF3_else n
-/
#guard_msgs in
#check @recPF3_eq
/--
info: def recPF3_else : ℕ → Result ℕ :=
fun n => do
  let a ← recPF3 (n - 1)
  let b ← Result.ok (a + 1)
  Result.ok b
-/
#guard_msgs in
#print recPF3_else
