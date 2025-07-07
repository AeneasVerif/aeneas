import AeneasMeta.Utils

namespace Aeneas.Simp

open Lean Meta Elab Tactic

initialize registerTraceClass `Simp

structure SimpArgs where
  simprocs : Simp.SimprocsArray := #[]
  simpThms : Array SimpTheorems := #[]
  addSimprocs : Array Name := #[]
  declsToUnfold : Array Name := #[]
  letDeclsToUnfold : Array FVarId := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

/- This is adapted from `Lean.Elab.Tactic.tacticToDischarge` -/
def tacticToDischargeAux (tactic : TacticM Unit) : TacticM (IO.Ref Term.State × Simp.Discharge) := do
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- SH: I don't understand why we need this even though we do not do any elaboration
           (removing those wrappers leads to failures in proofs). -/
        Term.withoutModifyingElabMetaStateWithInfo do
          let ngoals ← Term.withSynthesize (postpone := .no) do
            Tactic.run mvar.mvarId! tactic
          if ngoals.isEmpty then
            let result ← instantiateMVars mvar
            if result.hasExprMVar then
              return none
            else
              return some result
          else return none
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

def tacticToDischarge (tactic : TacticM Unit) : TacticM Simp.DischargeWrapper := do
  let (ref, d) ← tacticToDischargeAux tactic
  pure (Lean.Elab.Tactic.Simp.DischargeWrapper.custom ref d)

/- Initialize a context for the `simp` function.

   The initialization of the context is adapted from `elabSimpArgs`.
   Something very annoying is that there is no function which allows to
   initialize a simp context without doing an elaboration - as a consequence
   we write our own here. -/
def mkSimpCtx (simpOnly : Bool) (config : Simp.Config) (kind : SimpKind) (args : SimpArgs) :
  MetaM (Simp.Context × Simp.SimprocsArray) := do
  -- Initialize either with the builtin simp theorems or with all the simp theorems
  let simpThms ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    else getSimpTheorems
  -- Add the equational theorems for the declarations to unfold
  let addDeclToUnfold (thms : SimpTheorems) (decl : Name) : MetaM SimpTheorems :=
    if kind == .dsimp then pure (thms.addDeclToUnfoldCore decl)
    else thms.addDeclToUnfold decl
  let simpThms ←
    args.declsToUnfold.foldlM addDeclToUnfold simpThms
  let simpThms := args.letDeclsToUnfold.foldl SimpTheorems.addLetDeclToUnfold simpThms
  -- Add the hypotheses and the rewriting theorems
  let simpThms ←
    args.hypsToUse.foldlM (fun thms fvarId =>
      -- post: TODO: don't know what that is. It seems to be true by default.
      -- inv: invert the equality
      thms.add (.fvar fvarId) #[] (mkFVar fvarId) (post := true) (inv := false)
      -- thms.eraseCore (.fvar fvar)
      ) simpThms
  -- Add the rewriting theorems to use
  let simpThms ←
    args.addSimpThms.foldlM (fun thms thmName => do
      let info ← getConstInfo thmName
      if (← isProp info.type) then
        -- post: TODO: don't know what that is
        -- inv: invert the equality
        thms.addConst thmName (post := false) (inv := false)
      else
        throwError "Not a proposition: {thmName}"
      ) simpThms
  let congrTheorems ← getSimpCongrTheorems
  let defaultSimprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let addSimprocs ← args.addSimprocs.foldlM (fun simprocs name => simprocs.add name true) defaultSimprocs
  let ctx ← Simp.mkContext config (simpTheorems := #[simpThms] ++ args.simpThms) congrTheorems
  pure (ctx, #[addSimprocs] ++ args.simprocs)

/- Adapted from `Lean.Elab.Tactic.simpLocation` so that:
   - we can use our own `Location`
   - we return the fvars which have been simplified (that is, the unmodified fvars,
     and the fresh fvars introduced because of the simplification).
     Note that we return an option: if `none`, it means that the goal was closed.
-/
def customSimpLocation (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
  (discharge? : Option Simp.Discharge := none)
  (loc : Utils.Location) : TacticM (Option (Array FVarId) × Simp.Stats) := do
  match loc with
  | .targets hyps simplifyTarget =>
    -- Custom behavior: we directly provide the fvar ids of the assumption rather than syntax
    withMainContext do
      go hyps simplifyTarget
  | .wildcard =>
    -- Simply call the regular simpLocation
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM (Option (Array FVarId) × Simp.Stats) := do
    let mvarId ← getMainGoal
    let (result?, stats) ← simpGoal mvarId ctx (simprocs := simprocs) (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    let freshFVarIds ←
      match result? with
      | none => replaceMainGoal []; pure none
      | some (fvars, mvarId) => replaceMainGoal [mvarId]; pure fvars
    /- We need to filter the `fvarIdsToSimp` to remove those which have been replaced with fresh fvars -/
    let fvars ← do
      match freshFVarIds with
      | none => pure none
      | some freshFVarIds =>
        withMainContext do
        let ctx ← getLCtx
        let ldecls := ctx.foldl (fun set decl => set.insert decl.fvarId) Std.HashSet.emptyWithCapacity
        pure (fvarIdsToSimp.filter ldecls.contains ++ freshFVarIds)
    return (fvars, stats)

/- Call the simp tactic. -/
def simpAt (simpOnly : Bool) (config : Simp.Config) (args : SimpArgs) (loc : Utils.Location) :
  TacticM (Option (Array FVarId)) := do
  withMainContext do
  withTraceNode `Simp (fun _ => pure m!"simpAt") do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .simp args
  -- Apply the simplifier
  pure ((← customSimpLocation ctx simprocs (discharge? := .none) loc).fst)

/- Adapted from `Lean.Elab.Tactic.dsimpLocation` so that:
   - we can use our own `Location`
-/
def dsimpLocation (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (loc : Utils.Location) : TacticM Unit := do
  match loc with
  | .targets fvarIds simplifyTarget =>
    withMainContext do
    go fvarIds simplifyTarget
  | .wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := withSimpDiagnostics do
    let mvarId ← getMainGoal
    let (result?, stats) ← dsimpGoal mvarId ctx simprocs (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    if tactic.simp.trace.get (← getOptions) then
      mvarId.withContext <| traceSimpCall (← getRef) stats.usedTheorems
    return stats.diag

/- Call the dsimp tactic.
   TODO: update to return the fresh fvar ids.
-/
def dsimpAt (simpOnly : Bool) (config : Simp.Config) (args : SimpArgs) (loc : Utils.Location) :
  TacticM Unit := do
  withMainContext do
  withTraceNode `Simp (fun _ => pure m!"dsimpAt") do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .dsimp args
  -- Apply the simplifier
  dsimpLocation ctx simprocs loc

-- Call the simpAll tactic
def simpAll (config : Simp.Config) (simpOnly : Bool) (args : SimpArgs) :
  TacticM Unit := do
  withMainContext do
  withTraceNode `Simp (fun _ => pure m!"simpAll") do
  -- Initialize the simp context
  let (ctx, simprocs) ← mkSimpCtx simpOnly config .simpAll args
  -- Apply the simplifier
  let (result?, _) ← Lean.Meta.simpAll (← getMainGoal) ctx (simprocs := simprocs)
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

end Aeneas.Simp
