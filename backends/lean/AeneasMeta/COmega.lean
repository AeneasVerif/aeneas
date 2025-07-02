import Lean

example : 1 ≤ 2 := by omega

open Lean Elab Tactic Parser.Tactic Omega Meta

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. -/
def Aeneas.omegaTactic (cfg : Lean.Meta.Omega.OmegaConfig) : TacticM Unit := do
  --let declName? ← Term.getDeclName?
  liftMetaFinishingTactic fun g => do
    let some g ← g.falseOrByContra | return ()
    g.withContext do
      let type ← g.getType
      let g' ← mkFreshExprSyntheticOpaqueMVar type
      let hyps := (← getLocalHyps).toList
      trace[omega] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
      Lean.Elab.Tactic.Omega.omega hyps g'.mvarId! cfg
      -- Omega proofs are typically rather large, so hide them in a separate definition
      --let e ← mkAuxTheorem (prefix? := declName?) type (← instantiateMVarsProfiling g') (zetaDelta := true)
      g.assign (← instantiateMVarsProfiling g')
