import Aeneas.ScalarTac.ScalarTac

namespace Aeneas.ScalarTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Utils

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
        trace[Utils] "arg (local decl): {stx.raw}"
        -- Local declarations should be assumptions
        hypsToUse := hypsToUse.push decl.fvarId
      | .none =>
        -- Not a local declaration: should be a theorem
        trace[Utils] "arg (theorem): {stx.raw}"
        let some e ← Lean.Elab.Term.resolveId? stx (withInfo := true)
          | throwError m!"Could not find theorem: {arg}"
        if let .const name _ := e then
          addSimpThms := addSimpThms.push name
        else throwError m!"Unexpected: {arg}"
    | term => do
      trace[Utils] "term kind: {term.raw.getKind}"
      if term.raw.getKind == `token.«*» then
        trace[Utils] "found token: *"
        let decls ← (← getLCtx).getDecls
        let decls ← decls.filterMapM (
          fun d => do if (← inferType d.type).isProp then pure (some d.fvarId) else pure none)
        trace[Utils] "filtered decls: {decls.map Expr.fvar}"
        hypsToUse := hypsToUse.append decls.toArray
      else
        -- TODO: we need to make that work
        trace[Utils] "arg (term): {term}"
        throwError m!"Unimplemented: arbitrary terms are not supported yet as arguments to `{tacName}` (received: {arg})"
  pure ⟨ declsToUnfold, addSimpThms, hypsToUse ⟩

structure CondSimpArgs where
  simpThms : Array SimpTheorems := #[]
  simprocs: Simp.SimprocsArray := #[]
  declsToUnfold : Array Name := #[]
  addSimpThms : Array Name := #[]
  hypsToUse : Array FVarId := #[]

def condSimpTacSimp (config : Simp.Config) (args : CondSimpArgs) (loc : Utils.Location)
  (additionalAsms : Array FVarId := #[]) (dischWithScalarTac : Bool) : TacticM Unit := do
  withMainContext do
  let simpArgs : Utils.SimpArgs :=
    {simpThms := args.simpThms,
     simprocs := args.simprocs,
     declsToUnfold := args.declsToUnfold,
     addSimpThms := args.addSimpThms,
     hypsToUse := args.hypsToUse ++ additionalAsms}
  if dischWithScalarTac then
    let (ref, d) ← tacticToDischarge (← `(tactic|scalar_tac (saturate := false)))
    let dischargeWrapper := Lean.Elab.Tactic.Simp.DischargeWrapper.custom ref d
    let _ ← dischargeWrapper.with fun discharge? => do
      -- Initialize the simp context
      let (ctx, simprocs) ← Utils.mkSimpCtx true config
        .simp simpArgs
      -- Apply the simplifier
      let _ ← Utils.customSimpLocation ctx simprocs discharge? loc
  else
    Utils.simpAt true config simpArgs loc

/-- A helper to define tactics which perform conditional simplifications with `scalar_tac` as a discharger. -/
def condSimpTac
  (tacName : String) (satNonLin : Bool)
  (simpConfig : Simp.Config) (args : CondSimpArgs) (addSimpThms : TacticM (Array FVarId)) (doFirstSimp : Bool)
  (loc : Utils.Location) : TacticM Unit := do
  Elab.Tactic.focus do
  withMainContext do
  trace[Utils] "Initial goal: {← getMainGoal}"
  /- -/
  let toDuplicate ← do
    match loc with
    | .wildcard => pure none
    | .wildcard_dep => throwError "{tacName} does not support using location `Utils.Location.wildcard_dep`"
    | .targets hyps _ => pure (some hyps)
  /- Small helper.

     We use it to refresh the fvar ids after simplifying some assumptions.
     Whenever we apply a simplification to some assumptions, the only way to retrieve their new ids is
     to go through the context and filter the ids which we know do not come from the duplicated
     assumptions. -/
  let refreshFVarIds (keep ignore : Std.HashSet FVarId) : TacticM (Array FVarId) := do
    withMainContext do
    let decls := (← (← getLCtx).getDecls).toArray
    decls.filterMapM fun d => do
      if (← inferType d.type).isProp ∧ (d.fvarId ∈ keep ∨ d.fvarId ∉ ignore)
      then pure (some d.fvarId) else pure none
  let getOtherAsms (ignore : Std.HashSet FVarId) : TacticM (Array FVarId) :=
    refreshFVarIds Std.HashSet.emptyWithCapacity ignore
  /- First duplicate the propositions in the context: we will need the original ones (which mention
     integers rather than bit-vectors) for `scalar_tac` to succeed when doing the conditional rewritings. -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions toDuplicate
  let oldAsmsSet := Std.HashSet.ofArray oldAsms
  trace[Utils] "Goal after duplicating the assumptions: {← getMainGoal}"
  /- Introduce the scalar_tac assumptions - by doing it beforehand we don't have to redo it every
     time we call `scalar_tac`: as `saturate` is not compiled it saves a lot of time -/
  withMainContext do
  let scalarTacAsms ← ScalarTac.scalarTacSaturateForward true satNonLin
  trace[Utils] "Goal after saturating the context: {← getMainGoal}"
  let additionalSimpThms ← addSimpThms
  trace[Utils] "Goal after adding the additional simp assumptions: {← getMainGoal}"
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  let (loc, notLocAsms) ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true, ← getOtherAsms oldAsmsSet)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets hyps type, ← getOtherAsms (Std.HashSet.ofArray hyps))
  if doFirstSimp then
    condSimpTacSimp simpConfig args loc additionalSimpThms false
    if (← getUnsolvedGoals) == [] then return
  trace[Utils] "Goal after simplifying: {← getMainGoal}"
  /- Simplify the targets by using `scalar_tac` as a discharger -/
  let notLocAsmsSet := Std.HashSet.ofArray notLocAsms
  let nloc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets (← refreshFVarIds oldAsmsSet notLocAsmsSet) true) --, ← refreshFVarIds oldAsmsSet notLocAsmsSet)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets (← refreshFVarIds (Std.HashSet.ofArray hyps) notLocAsmsSet) type) --, ← refreshFVarIds oldAsmsSet notLocAsmsSet)
  condSimpTacSimp simpConfig args nloc additionalSimpThms true
  if (← getUnsolvedGoals) == [] then return
  /- Clear the additional assumptions -/
  Utils.clearFVarIds scalarTacAsms
  trace[Utils] "Goal after clearing the scalar_tac assumptions: {← getMainGoal}"
  Utils.clearFVarIds newAsms
  trace[Utils] "Goal after clearing the duplicated assumptions: {← getMainGoal}"
  Utils.clearFVarIds additionalSimpThms
  trace[Utils] "Goal after clearing the additional theorems: {← getMainGoal}"

end Aeneas.ScalarTac
