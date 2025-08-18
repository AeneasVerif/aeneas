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
attribute [inv_array_val self] Array.toList

set_option trace.Inv true in
example : loop (fun (x y : Array Nat) => (x.set! 0 x[0]!, y)) := by
  analyze_inv
  simp [loop]

set_option trace.Inv true in
example : loop (fun (x y : Array Nat) => (x.set! 0 x.toList[0]!, y)) := by
  analyze_inv
  simp [loop]

def loopIter (_ : Nat → α → α) : Prop := True

-- TODO: tuple projectors
set_option trace.Inv true in
example : loopIter (fun i (xy : Array Nat × Array Nat) =>
  let x := xy.fst
  let y := xy.snd
  (x.set! 0 x[0]!, y)) := by
  analyze_inv
  simp [loopIter]

-- TODO: handles matches over tuples
set_option trace.Inv true in
example : loopIter (fun i (xy : Array Nat × Array Nat) =>
  let (x, y) := xy
  (x.set! 0 x[0]!, y)) := by
  analyze_inv
  simp [loopIter]

-- TODO: test monadic binds

-- TODO: Fin

end Aeneas.Inv.Test
