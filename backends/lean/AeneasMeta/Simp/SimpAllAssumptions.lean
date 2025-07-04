import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Main
import AeneasMeta.Simp.Simp

/-!
This file is adapted from Lean.Meta.Tactic.Simp.SimpAll.lean
We slightly modify `simpAll` to be able to simplify only a *subset* of the assumptions.
-/

namespace Aeneas.Simp

open Lean Meta

initialize registerTraceClass `Aeneas.Meta.Tactic.simp.all

open Simp (Stats SimprocsArray)

namespace SimpAll

structure Entry where
  fvarId   : FVarId -- original fvarId
  userName : Name
  id       : Origin -- id of the theorem at `SimpTheorems`
  origType : Expr
  type     : Expr
  proof    : Expr
  deriving Inhabited

structure State where
  modified     : Bool := false
  mvarId       : MVarId
  entries      : Array Entry := #[]
  ctx          : Simp.Context
  simprocs     : SimprocsArray
  usedTheorems : Simp.UsedSimps := {}
  diag         : Simp.Diagnostics := {}

abbrev M := StateRefT State MetaM

private def initEntries (fvars : Array FVarId) : M Unit := do
  let hs := fvars
  let hsNonDeps ← (← get).mvarId.getNondepPropHyps
  let mut simpThms := (← get).ctx.simpTheorems
  for h in hs do
    unless simpThms.isErased (.fvar h) do
      let localDecl ← h.getDecl
      let proof  := localDecl.toExpr
      let ctx := (← get).ctx
      simpThms ← simpThms.addTheorem (.fvar h) proof (config := ctx.indexConfig)
      modify fun s => { s with ctx := s.ctx.setSimpTheorems simpThms }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let type ← instantiateMVars localDecl.type
        let entry : Entry := { fvarId := h, userName := localDecl.userName, id := .fvar h, origType := type, type, proof }
        modify fun s => { s with entries := s.entries.push entry }

private abbrev getSimpTheorems : M SimpTheoremsArray :=
  return (← get).ctx.simpTheorems

private partial def loop (target : Bool) : M Bool := do
  modify fun s => { s with modified := false }
  let simprocs := (← get).simprocs
  -- simplify entries
  let entries := (← get).entries
  for h : i in [:entries.size] do
    let entry := entries[i]
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let simpThmsWithoutEntry := (← getSimpTheorems).eraseTheorem entry.id
    let ctx := ctx.setSimpTheorems simpThmsWithoutEntry
    let (r, stats) ← simpStep (← get).mvarId entry.proof entry.type ctx simprocs (stats := { (← get) with })
    modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag }
    match r with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- We must erase the `id` for the simplified theorem. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`.

           It is also important for avoiding identical hypotheses to simplify each other to `True`.
           Example
           ```
           ...
           h₁ : p a
           h₂ : p a
           ⊢ q a
           ```
           `h₁` is first simplified to `True`. If we don't remove `h₁` from the set of simp theorems, it will
           be used to simplify `h₂` to `True` and information is lost.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        trace[Aeneas.Meta.Tactic.simp.all] "entry.id: {← ppOrigin entry.id}, {entry.type} => {typeNew}"
        let mut simpThmsNew := (← getSimpTheorems).eraseTheorem (.fvar entry.fvarId)
        let idNew ← mkFreshId
        simpThmsNew ← simpThmsNew.addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew) (config := ctx.indexConfig)
        modify fun s => { s with
          modified         := true
          ctx              := ctx.setSimpTheorems simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := .other idNew }
        }

  if (← get).modified then
    loop target
  else
    -- We're done with the loop: simplify the target
    if target then
      let mvarId := (← get).mvarId
      let (r, stats) ← simpTarget mvarId (← get).ctx simprocs (stats := { (← get) with })
      modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag }
      match r with
      | none => return true
      | some mvarIdNew =>
        unless mvarId == mvarIdNew do
          modify fun s => { s with
            modified := true
            mvarId   := mvarIdNew
          }
        return false
    else
      return false

def main (fvars : Array FVarId) (target : Bool) :
  M (Option (Array FVarId × Std.HashMap FVarId FVarId × MVarId)) := do
  initEntries fvars
  if (← loop target) then
    return none -- close the goal
  else
    let mvarId := (← get).mvarId
    -- Prior to #2334, the logic here was to re-assert all hypotheses and call `tryClearMany` on them all.
    -- This had the effect that the order of hypotheses was sometimes modified, whether or not any where simplified.
    -- Now we only re-assert the first modified hypothesis,
    -- along with all subsequent hypotheses, so as to preserve the order of hypotheses.
    let mut toAssert := #[]
    let mut toClear := #[]
    let mut preserved := #[]
    let mut modified := false
    let mut fvarIdMap := Std.HashMap.emptyWithCapacity
    let mut toRemap := #[]
    let mut i := 0
    for e in (← get).entries do
      if e.type.isTrue then
        -- Do not assert `True` hypotheses
        toClear := toClear.push e.fvarId
      else if modified || e.type != e.origType then
        toClear := toClear.push e.fvarId
        toAssert := toAssert.push { userName := e.userName, type := e.type, value := e.proof }
        modified := true
        toRemap := toRemap.push (e.fvarId, i)
        i := i + 1
      else
        preserved := preserved.push e.fvarId
        fvarIdMap := fvarIdMap.insert e.fvarId e.fvarId
    let _ ← mvarId.withContext do trace[Aeneas.Meta.Tactic.simp.all] "preserved: {preserved.map Expr.fvar}"
    let _ ← mvarId.withContext do
      trace[Aeneas.Meta.Tactic.simp.all] "toClear: {← toClear.mapM fun fid => do pure (Expr.fvar fid, ← inferType (Expr.fvar fid))}"
    let _ ← mvarId.withContext do trace[Aeneas.Meta.Tactic.simp.all] "toRemap: {toRemap.map (Expr.fvar ∘ Prod.fst)}"
    let (freshIds, mvarId) ← mvarId.assertHypotheses toAssert
    let _ ← mvarId.withContext do trace[Aeneas.Meta.Tactic.simp.all] "freshIds: {freshIds.map Expr.fvar}"
    trace[Aeneas.Meta.Tactic.simp.all] "Before clearing: {mvarId}"
    let mvarId ← mvarId.tryClearMany toClear
    trace[Aeneas.Meta.Tactic.simp.all] "After clearing: {mvarId}"
    for (fvarId, id) in toRemap do
      fvarIdMap := fvarIdMap.insert fvarId freshIds[id]!
    pure (some (preserved ++ freshIds, fvarIdMap, mvarId))

end SimpAll

def simpAllAssumptionsAux (mvarId : MVarId) (ctx : Simp.Context) (fvars : Array FVarId) (target : Bool)
  (simprocs : SimprocsArray := #[]) (stats : Stats := {}) :
  MetaM (Option (Array FVarId × Std.HashMap FVarId FVarId × MVarId) × Stats) := do
  mvarId.withContext do
    trace[Aeneas.Meta.Tactic.simp.all] "Initial mvar: {mvarId}"
    let (r, s) ← (SimpAll.main fvars target).run { stats with mvarId, ctx, simprocs }
    if let .some (_, _, mvarIdNew) := r then
      if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
        throwError "simp_all made no progress"
    return (r, { s with })

open Utils Simp Elab Tactic in
def simpAllAssumptions (config : Simp.Config) (simpOnly : Bool) (args : SimpArgs)
  (mvarId : MVarId) (fvars : Array FVarId) (target : Bool) :
  MetaM (Option (Array FVarId × Std.HashMap FVarId FVarId × MVarId)) := do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .simpAll args
  -- Apply the simplifier
  let (result?, _) ← simpAllAssumptionsAux mvarId ctx fvars target (simprocs := simprocs)
  pure result?

open Utils Simp Elab Tactic in
def evalSimpAllAssumptions (config : Simp.Config) (simpOnly : Bool) (args : SimpArgs)
  (fvars : Array FVarId) (target : Bool) :
  TacticM (Option (Array FVarId × Std.HashMap FVarId FVarId)) := do
  match ← simpAllAssumptions config simpOnly args (← getMainGoal) fvars target with
  | none => replaceMainGoal []; pure none
  | some (fvarIds, idsMap, mvarId) => replaceMainGoal [mvarId]; pure (some (fvarIds, idsMap))

end Aeneas.Simp
