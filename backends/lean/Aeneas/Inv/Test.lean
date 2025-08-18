import Aeneas.Inv.Inv

namespace Aeneas.Inv.Test

open Lean Elab Meta Tactic

scoped syntax "analyze_inv" : tactic

elab "analyze_inv" : tactic => do
  withMainContext do
  let tgt ← getMainTarget
  trace[Inv] "{tgt}"
  -- Dive into the loop
  let args := tgt.consumeMData.getAppArgs
  if args.size ≠ 2 then throwError "Expected one argument, got: {args.size}"
  let body := args[1]!
  -- Dive into the lambdas
  Meta.lambdaTelescope body.consumeMData fun inputs body => do
  trace[Inv] "inputs: {inputs}"
  let inputs := Std.HashSet.ofArray (inputs.map Expr.fvarId!)
  let fp : Footprint := {
    inputs,
    outputs := #[],
    provenance := Std.HashMap.emptyWithCapacity,
    footprint := #[],
  }
  let state : State := ⟨ fp ⟩
  trace[Inv] "initial state: {state}"
  let (_, state) ← FootprintM.run (footprint.expr true body) (← readThe Meta.Context) state
  trace[Inv] "{state}"

def loop (_ : α) : Prop := True

attribute [inv_array_getter xs at i] getElem!
attribute [inv_array_getter xs at i] getElem
-- TODO: `getElem?`: a problem is that we can't provide the name of the index
attribute [inv_array_setter xs at i to v] Array.set!
attribute [inv_val self] Array.toList
attribute [inv_val self] Fin.val
attribute [inv_val val] Fin.mk

set_option trace.Inv true in
example : loop (fun (x y : Array Nat) => (x.set! 0 x[0]!, y)) := by
  analyze_inv
  simp [loop]

set_option trace.Inv true in
example : loop (fun (x y : Array Nat) => (x.set! 0 x.toList[0]!, y)) := by
  analyze_inv
  simp [loop]

def loopIter (_ : Nat → α → α) : Prop := True

-- Tuple projectors
set_option trace.Inv true in
example : loopIter (fun i (xy : Array Nat × Array Nat) =>
  let x := xy.fst
  let y := xy.snd
  (x.set! i x[i]!, y.set! i x[i]!)) := by
  analyze_inv
  simp [loopIter]

-- Tuple with 2 elements
set_option trace.Inv true in
example : loopIter (fun i (xy : Array Nat × Array Nat) =>
  let (x, y) := xy
  (x.set! i x[i]!, y)) := by
  analyze_inv
  simp [loopIter]

-- Tuple with 3 elements (make sure the handling of tuples is general)
set_option trace.Inv true in
example : loopIter (fun i (xyz : Array Nat × Array Nat × Array Nat) =>
  let (x, y, z) := xyz
  (x.set! i x[i]!, y, z)) := by
  analyze_inv
  simp [loopIter]

inductive Either (α β : Type)
| left  : α → Either α β
| right : β → Either α β

-- Just checking that we don't crash on arbitrary match expressions
set_option trace.Inv true in
example {α β} : loop (fun (e : Either α β) =>
  match e with
  | .left _ => true
  | .right _ => false) := by
  analyze_inv
  simp [loop]

-- Basic operations: map i
set_option trace.Inv true in
example : loopIter (fun i (state : Array Nat × Array Nat) =>
  let (src, dst) := state
  let a := src[i]! + dst[i]!
  let src' := src.set! i 0
  let dst := dst.set! i a
  (src', dst)) := by
  analyze_inv
  simp [loopIter]

-- Basic operations: 2 * i, 2 * i + 1
set_option trace.Inv true in
example : loopIter (fun i (state : Array Nat × Array Nat) =>
  let (src, dst) := state
  let a := src[2 * i]! + dst[2 * i]!
  let b := src[2 * i + 1]! + dst[2 * i + 1]!
  let src := src.set! (2 * i) 0
  let src := src.set! (2 * i + 1) 0
  let dst := dst.set! (2 * i) a
  let dst := dst.set! (2 * i + 1) b
  (src, dst)) := by
  analyze_inv
  simp [loopIter]

-- `Fin`
set_option trace.Inv true in
example : loop (fun (i : Fin 32) (state : Array Nat × Array Nat) =>
  let (src, dst) := state
  let j := Fin.mk i.val i.isLt
  let a := src[2 * j]! + dst[2 * j]!
  let b := src[2 * j + 1]! + dst[2 * j + 1]!
  let src := src.set! (2 * j) 0
  let src := src.set! (2 * j + 1) 0
  let dst := dst.set! (2 * j) a
  let dst := dst.set! (2 * j + 1) b
  (src, dst)) := by
  analyze_inv
  simp [loop]

-- TODO: test monadic binds

-- TODO: Fin

end Aeneas.Inv.Test
