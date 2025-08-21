import Aeneas.Inv.Base

namespace Aeneas.Inv

open Lean Elab Meta
open Extensions

/-!
# Attribute: `inv_loop_iter`
Note that because we decided to initialize the extension and the attribute separately,
we can't define them in the same module.
-/

def State.init (startVarId startLoopId : Nat) (inputFVars : Array FVarId) : MetaM (Array (FVarId × Var) × State) := do
  trace[Inv] "inputs: {inputFVars.map Expr.fvar}"
  let mut fid := startVarId
  let inputVars ← do
    let lctx ← getLCtx
    let mut m : Array (FVarId × Var) := #[]
    for fv in inputFVars do
      let id := fid
      fid := fid + 1
      let decl := lctx.get! fv
      let name := m!"{decl.userName}"
      let name ← name.toString
      m := m ++ #[(fv, {id, name := some name})]
    pure m
  let inputs := Std.HashMap.ofList inputVars.toList
  let fp : Footprint := { inputs, varId := fid, loopId := startLoopId }
  pure (inputVars, ⟨ fp ⟩)

initialize loopIterAttr : ArrayAttr LoopIterDesc ← do
  initializeArrayAttr `loopIter loopIterExt
    fun ext defName stx attrKind => do
    -- Lookup the definition
    let env ← getEnv
    let some decl := env.findAsync? defName
      | throwError "Could not find definition {defName}"
    let sig := decl.sig.get
    let ty := sig.type
    -- Find where the position of the arguments
    let loop : LoopIterDesc ← MetaM.run' do
      /- Strip the quantifiers.

          We do this before elaborating the pattern because we need the universally
          quantified variables to be in the context.
      -/
      forallTelescope ty.consumeMData fun fvars _ => do
      let (body, start, stop, step, rangeKind, input) ← parseLoopIterArgs stx
      /- Find the position of every fvar id -/
      let positions ← findPositionsOfIndexOrExpr (Vector.mk #[body, input] (by simp; rfl)) fvars
      let body := positions[0]
      let input := positions[1]

      /- Process the range: -/
      let (_, state) ← State.init 0 0 (fvars.map Expr.fvarId!)
      let (start, stop, step) ← do
        withTraceNode `Inv (fun _ => pure m!"range") do
        let toExpr e : MetaM VarProjOrLit := do
          trace[Inv] "processing: {e}"
          let e' ← FootprintM.run' (footprint.expr none e) state
          trace[Inv] "footprint.expr: {e'}"
          let e' := e'.toVarProjOrLit
          match e' with
          | none => throwError "Invalid range index: {e}"
          | some v =>
            trace[Inv] "toVarProjOrLit: {e'}"
            pure v
        let start ← toExpr start
        let stop ← toExpr stop
        let step ← toExpr step
        pure (start, stop, step)

      /- Check the range expressions -/
      --let rec checkRangeExpr (e : FootprintExpr)

      pure { body, start, stop, step, rangeKind, input }
    -- Generate the key for the discrimination tree
    let key ← MetaM.run' do
      let (mvars, _) ← forallMetaTelescope ty.consumeMData
      DiscrTree.mkPath (← mkAppOptM defName (mvars.map Option.some))
    -- Store
    ScopedEnvExtension.add ext (key, defName, loop) attrKind

end Aeneas.Inv
