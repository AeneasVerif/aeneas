import Aeneas.Inv.Formula

namespace Aeneas.Inv.Test

open Lean Elab Meta Tactic

set_option linter.unusedTactic false

scoped syntax "analyze_loop" : tactic

def analyzeLoop (k : Array (FVarId × Var) → Expr → State → TacticM α) : TacticM α := do
  withMainContext do
  let tgt ← getMainTarget
  trace[Inv] "{tgt}"
  -- Dive into the loop
  let args := tgt.consumeMData.getAppArgs
  if h: args.size ≠ 3 then throwError "Expected 3 arguments, got: {args}"
  else
    let body := args[1]
    let decls ← (← getLCtx).getNonAssumptions
    let decls := decls.toArray.map LocalDecl.fvarId
    let (inputVars, state) ← State.init 0 0 decls
    let (_, state) ← FootprintM.run (footprint.expr none body) state
    trace[Inv] "{state}"
    k inputVars body state

elab "analyze_loop" : tactic => do
  analyzeLoop fun _ _body state => do
  let nfp ← do
    try pure (some (← analyzeFootprint state.toFootprint {}))
    catch _ => pure none
  trace[Inv] "Analyzed output:\n{nfp.map fun out => out.loopOutputs.toArray}"
  pure ()

attribute [inv_array_getter xs at i] getElem!
attribute [inv_array_getter xs at i] getElem
attribute [inv_array_getter 5 at 6] getElem?
attribute [inv_array_setter xs at i to v] Array.set!
attribute [inv_val self] Array.toList
attribute [inv_val self] Fin.val
attribute [inv_val val] Fin.mk
attribute [inv_val 3] pure
attribute [inv_val x] Id.run

@[inv_loop_iter {_body} [_start:_stop: += 1] input]
def loopIter {α} (_start _stop : Nat) (input : α) (_body : Nat → α → α) : α := input

@[inv_loop_iter {_body} [_start:stop: += 1] input]
def loopIterFin {α} (_start stop : Nat) (input : α) (_body : Fin stop → α → α) : α := input

@[inv_loop_iter {_body} [_start:stop: += 1] input]
def loopIterFinId {α} (_start stop : Nat) (input : α) (_body : Fin stop → α → Id α) : Id α := input

def post : α → (α → Prop) → Prop := fun _ _ => True

-- No loop
set_option trace.Inv true in
example :
  post 0
    (fun _ => True)
  := by
  analyze_loop
  simp [post]

-- Simple loop
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 #[]
      fun i (x : Array Nat) =>
      x.set! i 0)
    (fun _ => True)
  := by
  analyze_loop
  simp [post]

-- Tuple projectors
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[])
      fun i (xy : Array Nat × Array Nat) =>
      let x := xy.fst
      let y := xy.snd
      (x.set! i x[i]!, y.set! i x[i]!))
    (fun _ => True)
  := by
  analyze_loop
  simp [post]

-- Tuple with 2 elements
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[]) (fun i (xy : Array Nat × Array Nat) =>
      let (x, y) := xy
      (x.set! i x[i]!, y)))
    (fun _ => True)
  := by
  analyze_loop
  simp [post]

-- Tuple with 2 elements: checking that the constructor is handled properly
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[])
    fun i (xy : Array Nat × Array Nat) =>
    let (x, y) := xy
    let xy := (x, y)
    let (x, y) := xy
    (x.set! i x[i]!, y))
  (fun _ => True) := by
  analyze_loop
  simp [post]

-- `MProd` with 2 elements: checking that the constructor is handled properly
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 ⟨#[], #[]⟩
      fun i (xy : MProd (Array Nat) (Array Nat)) =>
      let ⟨ x, y ⟩ := xy
      ⟨ x.set! i x[i]!, y ⟩)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Tuple with 3 elements (make sure the handling of tuples is general)
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[], #[])
      fun i (xyz : Array Nat × Array Nat × Array Nat) =>
      let (x, y, z) := xyz
      (x.set! i x[i]!, y, z))
    (fun _ => True) := by
  analyze_loop
  simp [post]

inductive Either (α β : Type)
| left  : α → Either α β
| right : β → Either α β

-- Just checking that we don't crash on arbitrary match expressions
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (Either.left 32) (fun _ (e : Either Nat Nat) =>
      match e with
      | .left x => Either.right x
      | .right y => Either.left y))
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Basic operations: map i
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[])
      fun i (state : Array Nat × Array Nat) =>
      let (src, dst) := state
      let a := src[i]! + dst[i]!
      let src' := src.set! i 0
      let dst := dst.set! i a
      (src', dst))
    (fun _ => True)
     := by
  analyze_loop
  simp [post]

-- Basic operations: 2 * i, 2 * i + 1
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 (#[], #[])
      fun i (state : Array Nat × Array Nat) =>
      let (src, dst) := state
      let a := src[2 * i]! + dst[2 * i]!
      let b := src[2 * i + 1]! + dst[2 * i + 1]!
      let src := src.set! (2 * i) 0
      let src := src.set! (2 * i + 1) 0
      let dst := dst.set! (2 * i) a
      let dst := dst.set! (2 * i + 1) b
      (src, dst))
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- We are not limited to `Nat`: the following loop uses `Fin`
set_option trace.Inv true in
example :
  post (
    loopIterFin 0 32 (#[], #[])
      fun (i : Fin 32) (state : Array Nat × Array Nat) =>
      let (src, dst) := state
      let j := Fin.mk i.val i.isLt -- create a new `Fin` equal to `i`
      let a := src[2 * j]! + dst[2 * j]!
      let b := src[2 * j + 1]! + dst[2 * j + 1]!
      let src := src.set! (2 * j) 0
      let src := src.set! (2 * j + 1) 0
      let dst := dst.set! (2 * j) a
      let dst := dst.set! (2 * j + 1) b
      (src, dst))
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Monadic binds: state has one array
set_option trace.Inv true in
example :
  post (
    loopIter 0 256 #[]
      fun (i : Nat) (a : Array Nat) => Id.run do
      let a ← a.set! i 0
      pure a)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Monadic bind: state is a tuple of arrays
set_option trace.Inv true in
example :
  post (
    loopIterFinId 0 32 (#[], #[])
      fun (i : Fin 32) (state : Array Nat × Array Nat) => do
      let (src, dst) ← state
      let j ← Fin.mk i.val i.isLt
      let a ← src[2 * j]! + dst[2 * j]!
      let b ← src[2 * j + 1]! + dst[2 * j + 1]!
      let src ← src.set! (2 * j) 0
      let src ← src.set! (2 * j + 1) 0
      let dst ← dst.set! (2 * j) a
      let dst ← dst.set! (2 * j + 1) b
      pure (src, dst))
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Constant expression used for a range
set_option trace.Inv true in
example (n k : Nat) :
  post (
    loopIter 0 (2^k) n
      fun (_i : Nat) (_n : Nat) =>
      0)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Constant output (shouldn't be useful, but good for completeness)
set_option trace.Inv true in
example (n : Nat) :
  post (
    loopIter 0 256 n
      fun (_i : Nat) (_n : Nat) =>
      0)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value by 1 at every iteration
set_option trace.Inv true in
example (n : Nat) :
  post (
    loopIter 0 256 n
      fun (_ : Nat) (n : Nat) =>
      n + 1)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value by 2 at every iteration
set_option trace.Inv true in
example (n : Nat) :
  post (
    loopIter 0 256 n
      fun (_i : Nat) (n : Nat) =>
      n + 2)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value by an unknown constant at every iteration
set_option trace.Inv true in
example (n k : Nat) :
  post (
    loopIter 0 256 n
      fun (_i : Nat) (n : Nat) =>
      n + k)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value by an known constant but in an unknown range
set_option trace.Inv true in
example (n stop : Nat) :
  post (
    loopIter 0 stop n
      fun (_i : Nat) (n : Nat) =>
      n + 1)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value by an known constant but in an unknown range
set_option trace.Inv true in
example (start range n : Nat) :
  post (
    loopIter start (start + range) n
      fun (_i : Nat) (n : Nat) =>
      n + 1)
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Increment a value and modify an array in a loop
set_option trace.Inv true in
example (src : Array Nat) :
  post (
    loopIter 0 256 (0, src)
      fun (i : Nat) (state : Nat × Array Nat) =>
      let (n, a) := state
      (n + 1, a.set! i 0))
    (fun _ => True) := by
  analyze_loop
  simp [post]

-- Nested loops: simple
set_option trace.Inv true in
example (src dst : Array Nat) :
  post (
    loopIter 0 8 dst (fun i (dst : Array Nat) =>
      loopIter 0 8 dst (fun j (dst : Array Nat) =>
        dst.set! (8 * i + j) src[8 * i + j]!
        )))
    (fun _ => True)
  := by
  analyze_loop
  simp [post]

-- Nested loop: with increment
set_option trace.Inv true in
example (src : Array Nat) :
  post (
    loopIter 0 8 (0, src)
      fun (_i : Nat) (state : Nat × Array Nat) =>
      loopIter 0 8 state fun _j state =>
      let (n, a) := state
      (n + 1, a))
    (fun _ => True) := by
  analyze_loop
  simp [post]

set_option trace.Inv true in
example (src dst : Array Nat)
  (_ : src.size = 256 ∧ ∀ i < 256, src[i]! = 0)
  (_ : dst.size = 256 ∧ ∀ i < 256, dst[i]! = 1) :
  post (
    loopIter 0 8 dst (fun i (dst : Array Nat) =>
      loopIter 0 8 dst (fun j (dst : Array Nat) =>
        dst.set! (8 * i + j) src[8 * i + j]!
        )))
    (fun dst => dst.size = 256 ∧ ∀ i < 256, dst[i]! = 0)
  := by
  analyze_loop
  simp [post]

-- TODO: call a loop on an array which is not a variable (ex.: `List.replicate ...`)

set_option grind.warning false

example (P : Nat → Prop) (_ : ∀ i < 8, ∀ j < 8, P (8 * i + j)) :
  ∀ k < 64, P k := by
  intro k hk
  have : (k % 8) + 8 * (k / 8) = k := by apply Nat.mod_add_div
  have : k / 8 < 8 := by
    calc k / 8 ≤ 63 / 8 := by apply Nat.div_le_div <;> omega
         _ = 7 := by simp
         _ < 8 := by omega
  grind

example (P : Nat → Prop) (h : ∀ i < 8, P (2 * i) ∧ P (2 * i + 1)) :
  ∀ k < 16, P k := by
  intro k hk
  have : (k % 2) + 2 * (k / 2) = k := by apply Nat.mod_add_div
  have : k % 2 = 0 ∨ k % 2 = 1 := by
    have := @Nat.mod_lt k 2 (by omega)
    revert this
    native_decide +revert
  grind

example (P : Nat → Prop) (h : ∀ i < 2, P i) : P 0 ∧ P 1 := by grind

example (P : Nat → Prop) (_ : ∀ i < 8, ∀ j < 8, P (8 * i + j))
  -- This should be given by a theorem
  (h : (∀ k < 64, P k) ↔ (∀ i < 8, ∀ j < 8, P (8 * i + j))) :
  ∀ k < 64, P k := by
  grind


end Aeneas.Inv.Test
