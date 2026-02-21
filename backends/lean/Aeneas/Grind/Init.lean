import Lean
import Aeneas.Grind.Attribute

namespace Aeneas.Grind

/-- The Aeneas grind attribute -/
register_grind_attr' agrindExt agrind

open Lean Lean.Meta

/-- Adapted from `Lean.Meta.Grind.getSimpContext` -/
def getSimpContext (config : Lean.Grind.Config) : MetaM Simp.Context := do
  /- We should not modify the normalization theorems: those are sealed, builtin simp theorems which
     normalize terms into the canonical form expected by grind's internal engine. -/
  let thms ← Lean.Meta.Grind.getNormTheorems
  /- -/
  Simp.mkContext
    (config :=
      { arith := true
        zeta := config.zeta
        zetaDelta := config.zetaDelta
        -- Use `OfNat.ofNat` and `Neg.neg` for representing bitvec literals
        bitVecOfNat := false
        catchRuntime := false
        warnExponents := false
        -- `implicitDefEqProofs := true` a recurrent source of performance problems in the kernel
        implicitDefEqProofs := false })
    (simpTheorems := #[thms])
    /- We keep the default simp congruence lemmas: they should be generally useful, and at this stage we
       do not expect them to pollute the context. -/
    (congrTheorems := (← getSimpCongrTheorems))

/-- Adapted from `Lean.Meta.Grind.mkParams` -/
def mkParams (config : Lean.Grind.Config)
  (extensions : Lean.Meta.Grind.ExtensionStateArray)
  (withGroundSimprocs : Bool) :
  MetaM Lean.Meta.Grind.Params := do
  let norm ← getSimpContext config
  /- `Lean.Meta.Grind.getSimprocs` retrieves the `seval` simp procedures which are used to simplify ground
     terms (that is terms without free or meta variables) -/
  let groundNormProcs ← if withGroundSimprocs then Lean.Meta.Grind.getSimprocs else pure #[]
  /- We use the same symbol priorities to infer "good" symbols as for the regular `grind` tactic.
     At this stage we don't see why we should need different heuristics -/
  let symPrios ← Lean.Meta.Grind.getGlobalSymbolPriorities
  return { config, norm, normProcs := groundNormProcs, symPrios, extensions }

/-- The `agrind` tactic: like `grind`, but uses theorems tagged with `@[agrind]`
    (via `agrindExt`) instead of the standard `@[grind]` extension. -/
syntax (name := agrindTactic) "agrind" Lean.Parser.Tactic.optConfig
    (ppSpace "only")? (" [" Lean.Parser.Tactic.grindParam,* "]")? : tactic

def agrindEval (config : Lean.Grind.Config) (params : Grind.Params) (mvarId : Lean.MVarId) :
  Lean.Elab.Tactic.TacticM Unit := do
  mvarId.withContext do
    Lean.Meta.Grind.withProtectedMCtx config mvarId fun mvarId' => do
      let result ← Lean.Meta.Grind.main mvarId' params
      if result.hasFailed then
        throwError "`agrind` failed\n{← result.toMessageData}"

private def agrindCore (config : Lean.Grind.Config) (isOnly : Bool) (withGroundSimprocs : Bool)
    (ps : Array (Lean.TSyntax `Lean.Parser.Tactic.grindParam)) :
    Lean.Elab.Tactic.TacticM Unit := do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  mvarId.withContext do
    let baseParams ← if isOnly then
        Lean.Meta.Grind.mkOnlyParams config
      else
        mkParams config #[agrindExt.getState (← Lean.getEnv)] withGroundSimprocs
    let fullParams ← Lean.Elab.Tactic.elabGrindParams baseParams ps
                        (lax := config.lax) («only» := isOnly)
    agrindEval config fullParams mvarId
  Lean.Elab.Tactic.replaceMainGoal []

-- Note: `$[tok%$var]?` (optional binding with %) is only supported in Lean's core
-- `module prelude` files. In regular user code we use two `elab_rules` cases instead.
open Lean.Parser.Tactic in
elab_rules : tactic
  | `(tactic| agrind $config:optConfig only $[ [$params:grindParam,*] ]?) => do
    let ps := if let some ps := params then ps.getElems else #[]
    agrindCore (← Lean.Elab.Tactic.elabGrindConfig config) (isOnly := true) (withGroundSimprocs := true) ps
  | `(tactic| agrind $config:optConfig $[ [$params:grindParam,*] ]?) => do
    let ps := if let some ps := params then ps.getElems else #[]
    agrindCore (← Lean.Elab.Tactic.elabGrindConfig config) (isOnly := false) (withGroundSimprocs := true) ps

end Aeneas.Grind
