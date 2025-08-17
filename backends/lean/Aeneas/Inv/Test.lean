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
  trace[Inv] "inputs: {inputs}\nbody: {body}"
  let fp : Footprint := {
    inputs := Std.HashSet.ofArray (inputs.map Expr.fvarId!),
    outputs := #[],
    provenance := Std.HashMap.emptyWithCapacity,
    footprint := #[],
  }
  let state : State := ⟨ fp ⟩
  let (_, state) ← FootprintM.run (footprint.expr true body) (← readThe Meta.Context) state
  trace[Inv] "{state}"

def loop (x : α) : Prop := True

attribute [inv_array_getter xs at i] getElem!
attribute [inv_array_setter xs at i to v] Array.set!

set_option trace.Inv true in
example : loop (fun (x y : Array Nat) => (x.set! x[0]! 1, y)) := by
  analyze_inv
  simp [loop]

end Aeneas.Inv.Test
