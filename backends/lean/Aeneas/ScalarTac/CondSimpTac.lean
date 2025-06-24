import Aeneas.ScalarTac.ScalarTac

namespace Aeneas.ScalarTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Utils

structure CondSimpTacConfig where
  nonLin : Bool := false
  saturationPasses := 3

declare_config_elab elabCondSimpTacConfig CondSimpTacConfig

structure CondSimpPartialArgs where
  declsToUnfold : Array Name := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def condSimpParseArgs (tacName : String) (args : TSyntaxArray [`term, `token.«*»]) : TacticM CondSimpPartialArgs := do
  let mut declsToUnfold := #[]
  let mut addSimpThms := #[]
  let mut hypsToUse := #[]
  for arg in args do
    /- We have to make a case disjunction, because if we treat identifiers like
       terms, then Lean will not succeed in infering their implicit parameters. -/
    match arg with
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[CondSimpTac] "arg (local decl): {stx.raw}"
        if decl.isLet then
          declsToUnfold := declsToUnfold.push decl.userName
        else
          hypsToUse := hypsToUse.push decl.fvarId
      | .none =>
        -- Not a local declaration
        trace[CondSimpTac] "arg (theorem): {stx.raw}"
        let some e ← Lean.Elab.Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {arg}"
        if let .const name _ := e then
          -- Lookup the declaration to check whether it is a definition or a theorem
          match (← getEnv).find? name with
          | none => throwError m!"Could not find declaration: {name}"
          | some d =>
            match d with
            | .thmInfo _ | .axiomInfo _ =>
              addSimpThms := addSimpThms.push name
            | .defnInfo _ =>
              declsToUnfold := declsToUnfold.push name
            | _ => throwError m!"{name} is not a theorem, an axiom or a definition"
        else throwError m!"Unexpected: {arg}"
    | term => do
      trace[CondSimpTac] "term kind: {term.raw.getKind}"
      if term.raw.getKind == `token.«*» then
        trace[CondSimpTac] "found token: *"
        let decls ← (← getLCtx).getDecls
        let decls ← decls.filterMapM (
          fun d => do if ← isProp d.type then pure (some d.fvarId) else pure none)
        trace[CondSimpTac] "filtered decls: {decls.map Expr.fvar}"
        hypsToUse := hypsToUse.append decls.toArray
      else
        -- TODO: we need to make that work
        trace[CondSimpTac] "arg (term): {term}"
        throwError m!"Unimplemented: arbitrary terms are not supported yet as arguments to `{tacName}` (received: {arg})"
  pure ⟨ declsToUnfold, addSimpThms, hypsToUse ⟩

structure CondSimpArgs where
  simpThms : Array SimpTheorems := #[]
  simprocs: Simp.SimprocsArray := #[]
  declsToUnfold : Array Name := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

instance : HAppend CondSimpArgs CondSimpArgs CondSimpArgs where
  hAppend c0 c1 :=
    let ⟨ a0, b0, c0, d0, e0 ⟩ := c0
    let ⟨ a1, b1, c1, d1, e1 ⟩ := c1
    ⟨ a0 ++ a1, b0 ++ b1, c0 ++ c1, d0 ++ d1, e0 ++ e1 ⟩

def CondSimpArgs.toSimpArgs (args : CondSimpArgs) : Simp.SimpArgs := {
    simpThms := args.simpThms,
    simprocs := args.simprocs,
    declsToUnfold := args.declsToUnfold,
    addSimpThms := args.addSimpThms,
    hypsToUse := args.hypsToUse }

def condSimpTacSimp (config : Simp.Config) (args : CondSimpArgs) (loc : Utils.Location)
  (toClear : Array FVarId := #[])
  (additionalAsms : Array FVarId := #[]) (state : Option (ScalarTac.State × Array FVarId)) :
  TacticM (Option (Array FVarId)) := do
  withMainContext do
  let simpArgs := args.toSimpArgs
  let simpArgs := { simpArgs with hypsToUse := simpArgs.hypsToUse ++ additionalAsms }
  match state with
  | some (state, asms) =>
    /- Note that when calling `scalar_tac` we saturate only by looking at the target: we have
       already saturated by looking at the assumptions (we do this once and for all beforehand) -/
    let dischargeWrapper ← Simp.tacticToDischarge (incrScalarTac {saturateAssumptions := false} state toClear asms)
    dischargeWrapper.with fun discharge? => do
      -- Initialize the simp context
      let (ctx, simprocs) ← Simp.mkSimpCtx true config .simp simpArgs
      -- Apply the simplifier
      pure ((← Simp.customSimpLocation ctx simprocs discharge? loc).fst)
  | none =>
    Simp.simpAt true config simpArgs loc

/-- A helper to define tactics which perform conditional simplifications with `scalar_tac` as a discharger. -/
def condSimpTac
  (tacName : String) (config : CondSimpTacConfig)
  (simpConfig : Simp.Config) (hypsArgs args : CondSimpArgs)
  (addSimpThms : TacticM (Array FVarId)) (doFirstSimp : Bool)
  (loc : Utils.Location) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  /- Concatenate the arguments for the conditional rewritings: we only want to restrict the simplifications
     performed on the higher-order hypotheses, but we need all the simplifications performed to those to
     be applied to the rest of the context as well. -/
  let args := args ++ hypsArgs
  trace[CondSimpTac] "Initial goal: {← getMainGoal}"
  /- First duplicate the propositions in the context: we need the preprocessing of `scalar_tac` to modify
     the assumptions, but we need to preserve a copy so that we can present a clean state to the user later
     (and pretend nothing happened). Note that we do this in two times: we want to treat the simp
     theorems provided by the user in `args` separately from the other assumptions. -/
  let allAssumptions ← pure (← (← getLCtx).getAssumptions).toArray
  trace[CondSimpTac] "allAssumptions: {allAssumptions.map fun d => Expr.fvar d.fvarId}"
  let (_, hypsToUse) ← Utils.duplicateAssumptions (some args.hypsToUse)
  withMainContext do
  trace[CondSimpTac] "Goal after duplicating the hyps to use: {← getMainGoal}"
  trace[CondSimpTac] "hypsToUse: {hypsToUse.map Expr.fvar}"
  /- -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions (some (allAssumptions.map LocalDecl.fvarId))
  let toClear := oldAsms
  withMainContext do
  trace[CondSimpTac] "Goal after duplicating the assumptions: {← getMainGoal}"
  trace[CondSimpTac] "newAsms: {newAsms.map Expr.fvar}"
  /- Preprocess the assumptions -/
  let scalarConfig : ScalarTac.Config := { nonLin := config.nonLin, saturationPasses := config.saturationPasses }
  let state ← State.new scalarConfig
  /- First the hyps to use.
     Note that we do not inline the local let-declarations: we will do this only for the "regular" assumptions
     and the target. -/
  let some (_, hypsToUse) ← scalarTacPartialPreprocess scalarConfig hypsArgs.toSimpArgs state (zetaDelta := false) #[] hypsToUse false
    | trace[CondSimpTac] "Goal proven through preprocessing!"; return
  withMainContext do
  trace[CondSimpTac] "Goal after preprocessing the hyps to use ({hypsToUse.map Expr.fvar}): {← getMainGoal}"
  /- Remove the `forall'` and simplify the hyps to use -/
  let simpHypsToUseArgs := { hypsArgs with hypsToUse := #[], declsToUnfold := #[``forall'] }
  let some hypsToUse ← Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 0}
        simpHypsToUseArgs (.targets hypsToUse false)
    | trace[ScalarTac] "Goal proven by preprocessing!"; return
  let args := { args with hypsToUse }
  withMainContext do
  trace[CondSimpTac] "Goal after simplifying the preprocessed hyps to use ({hypsToUse.map Expr.fvar}): {← getMainGoal}"
  /- Preprocess the "regular" assumptions -/
  let some (state, newAsms) ← scalarTacPartialPreprocess scalarConfig (← ScalarTac.getSimpArgs) state (zetaDelta := true) #[] newAsms false
    | trace[CondSimpTac] "Goal proven through preprocessing!"; return
  withMainContext do
  trace[CondSimpTac] "Goal after the initial preprocessing: {← getMainGoal}"
  trace[CondSimpTac] "newAsms: {newAsms.map Expr.fvar}"
  /- Introduce the additional simp theorems -/
  let additionalSimpThms ← addSimpThms
  trace[CondSimpTac] "Goal after adding the additional simp assumptions: {← getMainGoal}"
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  let loc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets hyps type)
  let nloc ←
    if doFirstSimp then
      match ← condSimpTacSimp simpConfig args loc toClear additionalSimpThms none with
      | none => return
      | some freshFvarIds =>
        match loc with
        | .wildcard => pure (Utils.Location.targets freshFvarIds true)
        | .wildcard_dep => throwError "{tacName} does not support using location `Utils.Location.wildcard_dep`"
        | .targets _ type => pure (Utils.Location.targets freshFvarIds type)
    else pure loc
  trace[CondSimpTac] "Goal after simplifying: {← getMainGoal}"
  /- Simplify the targets by using `scalar_tac` as a discharger.
     TODO: scalar_tac should only be allowed to preprocess `scalarTacAsms`.
     TODO: we should preprocess those.
   -/
  let _ ← condSimpTacSimp simpConfig args nloc toClear additionalSimpThms (some (state, newAsms))
  if (← getUnsolvedGoals) == [] then return
  /- Clear the additional assumptions -/
  setGoals [← (← getMainGoal).tryClearMany hypsToUse]
  trace[CondSimpTac] "Goal after clearing the duplicated hypotheses to use: {← getMainGoal}"
  setGoals [← (← getMainGoal).tryClearMany newAsms]
  trace[CondSimpTac] "Goal after clearing the duplicated assumptions: {← getMainGoal}"
  setGoals [← (← getMainGoal).tryClearMany additionalSimpThms]
  trace[CondSimpTac] "Goal after clearing the additional theorems: {← getMainGoal}"

end Aeneas.ScalarTac
