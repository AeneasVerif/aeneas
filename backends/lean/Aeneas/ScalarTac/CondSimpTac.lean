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
  letDeclsToUnfold : Array FVarId := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def condSimpParseArgs (tacName : String) (args : TSyntaxArray [`term, `token.«*»]) :
  TacticM CondSimpPartialArgs := do
  withTraceNode `ScalarTac (fun _ => pure m!"condSimpParseArgs") do
  withMainContext do
  let mut declsToUnfold := #[]
  let mut letDeclsToUnfold := #[]
  let mut addSimpThms := #[]
  let mut hypsToUse := #[]
  for arg in args do
    /- We have to make a case disjunction, because if we treat identifiers like
       terms, then Lean will not succeed in infering their implicit parameters. -/
    match arg with
    | `($stx:ident) => do
      match (← getLCtx).findFromUserName? stx.getId with
      | .some decl =>
        trace[ScalarTac] "arg (local decl): {stx.raw}"
        if decl.isLet then
          letDeclsToUnfold := letDeclsToUnfold.push decl.fvarId
        else
          hypsToUse := hypsToUse.push decl.fvarId
      | .none =>
        -- Not a local declaration
        trace[ScalarTac] "arg (theorem): {stx.raw}"
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
      trace[ScalarTac] "term kind: {term.raw.getKind}"
      if term.raw.getKind == `token.«*» then
        trace[ScalarTac] "found token: *"
        let decls ← (← getLCtx).getDecls
        let decls ← decls.filterMapM (
          fun d => do if ← isProp d.type then pure (some d.fvarId) else pure none)
        trace[ScalarTac] "filtered decls: {decls.map Expr.fvar}"
        hypsToUse := hypsToUse.append decls.toArray
      else
        -- TODO: we need to make that work
        trace[ScalarTac] "arg (term): {term}"
        throwError m!"Unimplemented: arbitrary terms are not supported yet as arguments to `{tacName}` (received: {arg})"
  pure { declsToUnfold, letDeclsToUnfold, addSimpThms, hypsToUse }

structure CondSimpArgs where
  simpThms : Array SimpTheorems := #[]
  simprocs: Simp.SimprocsArray := #[]
  declsToUnfold : Array Name := #[]
  letDeclsToUnfold : Array FVarId := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

instance : HAppend CondSimpArgs CondSimpArgs CondSimpArgs where
  hAppend c0 c1 :=
    let ⟨ a0, b0, c0, d0, e0, f0 ⟩ := c0
    let ⟨ a1, b1, c1, d1, e1, f1 ⟩ := c1
    ⟨ a0 ++ a1, b0 ++ b1, c0 ++ c1, d0 ++ d1, e0 ++ e1, f0 ++ f1 ⟩

def CondSimpArgs.toSimpArgs (args : CondSimpArgs) : Simp.SimpArgs := {
    simpThms := args.simpThms,
    simprocs := args.simprocs,
    declsToUnfold := args.declsToUnfold,
    letDeclsToUnfold := args.letDeclsToUnfold,
    addSimpThms := args.addSimpThms,
    hypsToUse := args.hypsToUse }

def condSimpTacSimp (config : Simp.Config) (args : CondSimpArgs) (loc : Utils.Location)
  (toClear : Array FVarId := #[])
  (additionalHypsToUse : Array FVarId := #[]) (state : Option (ScalarTac.State × Array FVarId)) :
  TacticM (Option (Array FVarId)) := do
  withTraceNode `ScalarTac (fun _ => pure m!"condSimpTacSimp") do
  withMainContext do
  let simpArgs := args.toSimpArgs
  let simpArgs := { simpArgs with hypsToUse := simpArgs.hypsToUse ++ additionalHypsToUse }
  match state with
  | some (state, asms) =>
    trace[ScalarTac] "scalarTac assumptions: {asms.map Expr.fvar}"
    /- Note that when calling `scalar_tac` we saturate only by looking at the target: we have
       already saturated by looking at the assumptions (we do this once and for all beforehand)
       TODO: introducing an auxiliary theorem leads to failures.
     -/
    let dischargeWrapper ← Simp.tacticToDischarge (incrScalarTac {saturateAssumptions := false, auxTheorem := false} state toClear asms)
    dischargeWrapper.with fun discharge? => do
      -- Initialize the simp context
      let (ctx, simprocs) ← Simp.mkSimpCtx true config .simp simpArgs
      -- Apply the simplifier
      pure ((← Simp.customSimpLocation ctx simprocs discharge? loc).fst)
  | none =>
    Simp.simpAt true config simpArgs loc

structure PreprocessResult where
  args : CondSimpArgs
  toClear : Array FVarId
  hypsToUse : Array FVarId
  state : State
  oldAsms : Array FVarId
  newAsms : Array FVarId
  additionalSimpThms : Array FVarId

/-- Preprocess the goal.
    Return `none` if the preprocessing actually solves the goal.
-/
def condSimpTacPreprocess (config : CondSimpTacConfig) (hypsArgs args : CondSimpArgs)
  (addSimpThms : TacticM (Array FVarId)) : TacticM (Option PreprocessResult) := do
  withTraceNode `ScalarTac (fun _ => pure m!"condSimpTacPreprocess") do
  withMainContext do
  /- Concatenate the arguments for the conditional rewritings: we only want to restrict the simplifications
     performed on the higher-order hypotheses, but we need all the simplifications performed to those to
     be applied to the rest of the context as well. -/
  let args := args ++ hypsArgs
  traceGoalWithNode `ScalarTac  "Initial goal"
  /- First duplicate the propositions in the context: we need the preprocessing of `scalar_tac` to modify
     the assumptions, but we need to preserve a copy so that we can present a clean state to the user later
     (and pretend nothing happened). Note that we do this in two times: we want to treat the simp
     theorems provided by the user in `args` separately from the other assumptions. -/
  let allAssumptions ← pure (← (← getLCtx).getAssumptions).toArray
  trace[ScalarTac] "allAssumptions: {allAssumptions.map fun d => Expr.fvar d.fvarId}"
  let (_, hypsToUse) ← Utils.duplicateAssumptions (some args.hypsToUse)
  withMainContext do
  traceGoalWithNode `ScalarTac "Goal after duplicating the hyps to use"
  trace[ScalarTac] "hypsToUse: {hypsToUse.map Expr.fvar}"
  /- -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions (some (allAssumptions.map LocalDecl.fvarId))
  let toClear := oldAsms
  withMainContext do
  traceGoalWithNode `ScalarTac "Goal after duplicating the assumptions"
  trace[ScalarTac] "newAsms: {newAsms.map Expr.fvar}"
  /- Preprocess the assumptions -/
  let scalarConfig : ScalarTac.Config := { nonLin := config.nonLin, saturationPasses := config.saturationPasses }
  let state ← State.new scalarConfig
  /- First the hyps to use.
     Note that we do not inline the local let-declarations: we will do this only for the "regular" assumptions
     and the target. -/
  let some (_, hypsToUse) ← partialPreprocess scalarConfig hypsArgs.toSimpArgs state (zetaDelta := false) #[] hypsToUse false (postProcessSat := false)
    | trace[ScalarTac] "Goal proved through preprocessing!"; return none
  withMainContext do
  withTraceNode `ScalarTac (fun _ => pure m!"Goal after preprocessing the hyps to use ({hypsToUse.map Expr.fvar})") do
    trace[ScalarTac] "{← getMainGoal}"
  /- Remove the `forall'` and simplify the hyps to use -/
  let simpHypsToUseArgs := { hypsArgs with hypsToUse := #[], declsToUnfold := #[``forall'] }
  let some hypsToUse ← Simp.simpAt true {failIfUnchanged := false, maxDischargeDepth := 0}
        simpHypsToUseArgs (.targets hypsToUse false)
    | trace[ScalarTac] "Goal proved by preprocessing!"; return none
  let args := { args with hypsToUse }
  withMainContext do
  withTraceNode `ScalarTac (fun _ => pure m!"Goal after simplifying the preprocessed hyps to use ({hypsToUse.map Expr.fvar})") do
    trace[ScalarTac] "{← getMainGoal}"
  /- Preprocess the "regular" assumptions -/
  let some (state, newAsms) ← partialPreprocess scalarConfig (← ScalarTac.getSimpArgs) state (zetaDelta := true) #[] newAsms false (postProcessSat := false)
    | trace[ScalarTac] "Goal proved through preprocessing!"; return none
  withMainContext do
  traceGoalWithNode `ScalarTac "Goal after the initial preprocessing"
  trace[ScalarTac] "newAsms: {newAsms.map Expr.fvar}"
  /- Introduce the additional simp theorems -/
  let additionalSimpThms ← addSimpThms
  traceGoalWithNode `ScalarTac "Goal after adding the additional simp assumptions"
  pure (some { args, toClear, hypsToUse, state, oldAsms, newAsms, additionalSimpThms })

def condSimpTacCore
  (simpConfig : Simp.Config)
  (doFirstSimp : Bool)
  (loc : Utils.Location)
  (res : PreprocessResult) : TacticM (Option MVarId) := do
  withTraceNode `ScalarTac (fun _ => pure m!"CondSimpTacCore") do
  let { args, toClear, hypsToUse := _, state, oldAsms, newAsms, additionalSimpThms } := res
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  withMainContext do
  let loc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true)
    | .targets hyps type => pure (Utils.Location.targets hyps type)
  let nloc ←
    if doFirstSimp then
      match ← condSimpTacSimp simpConfig args loc (toClear := toClear) (additionalHypsToUse := additionalSimpThms) none with
      | none => trace[ScalarTac] "Goal proved through preprocessing!"; return none
      | some freshFvarIds =>
        match loc with
        | .wildcard => pure (Utils.Location.targets freshFvarIds true)
        | .targets _ type => pure (Utils.Location.targets freshFvarIds type)
    else pure loc
  traceGoalWithNode `ScalarTac "Goal after simplifying"
  /- Simplify the targets by using `scalar_tac` as a discharger. -/
  let _ ← condSimpTacSimp simpConfig args nloc (toClear := toClear) (additionalHypsToUse := additionalSimpThms) (some (state, newAsms))
  if (← getUnsolvedGoals) == [] then pure none
  else pure (some (← getMainGoal))

def condSimpTacClear (res : PreprocessResult) : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"CondSimpTacClear") do
  setGoals [← (← getMainGoal).tryClearMany res.hypsToUse]
  traceGoalWithNode `ScalarTac "Goal after clearing the duplicated hypotheses to use"
  setGoals [← (← getMainGoal).tryClearMany res.newAsms]
  traceGoalWithNode `ScalarTac "Goal after clearing the duplicated assumptions"
  setGoals [← (← getMainGoal).tryClearMany res.additionalSimpThms]
  traceGoalWithNode `ScalarTac "Goal after clearing the additional theorems"

/-- A helper to define tactics which perform conditional simplifications with `scalar_tac` as a discharger. -/
def condSimpTac
  (config : CondSimpTacConfig)
  (simpConfig : Simp.Config) (hypsArgs args : CondSimpArgs)
  (addSimpThms : TacticM (Array FVarId)) (doFirstSimp : Bool)
  (loc : Utils.Location) : TacticM Unit := do
  withTraceNode `ScalarTac (fun _ => pure m!"CondSimpTac") do
  Elab.Tactic.focus do
  /- Preprocess -/
  let some res ←
    condSimpTacPreprocess config hypsArgs args addSimpThms
    | trace[ScalarTac] "Goal proved through preprocessing!"; return -- goal proved
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  let some _ ← condSimpTacCore simpConfig doFirstSimp loc res
    | trace[ScalarTac] "Goal proved!"; return -- goal proved
  /- Clear the additional assumptions -/
  condSimpTacClear res

end Aeneas.ScalarTac
