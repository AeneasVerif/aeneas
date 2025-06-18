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
          fun d => do if (← inferType d.type).isProp then pure (some d.fvarId) else pure none)
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
    /- Note that when calling `scalar_tac` we saturate only by looking at the target: we have
       already saturated by looking at the assumptions (we do this once and for all beforehand) -/
    let (ref, d) ← tacticToDischarge (← `(tactic|scalar_tac -saturateAssumptions))
    let dischargeWrapper := Lean.Elab.Tactic.Simp.DischargeWrapper.custom ref d
    let _ ← dischargeWrapper.with fun discharge? => do
      -- Initialize the simp context
      let (ctx, simprocs) ← Utils.mkSimpCtx true config .simp simpArgs
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
  trace[CondSimpTac] "Initial goal: {← getMainGoal}"
  /- -/
  let toDuplicate ← do
    match loc with
    | .wildcard => pure none
    | .wildcard_dep => throwError "{tacName} does not support using location `Utils.Location.wildcard_dep`"
    | .targets hyps _ => pure (some hyps)
  let getOtherAsms (ignore : Std.HashSet FVarId) : TacticM (Array FVarId) :=
    Utils.refreshFVarIds Std.HashSet.emptyWithCapacity ignore
  /- First duplicate the propositions in the context: we will need the original ones (which mention
     integers rather than bit-vectors) for `scalar_tac` to succeed when doing the conditional rewritings. -/
  let (oldAsms, newAsms) ← Utils.duplicateAssumptions toDuplicate
  let oldAsmsSet := Std.HashSet.ofArray oldAsms
  trace[CondSimpTac] "Goal after duplicating the assumptions: {← getMainGoal}"
  /- Introduce the scalar_tac assumptions - by doing this beforehand we don't have to
     redo it every time we call `scalar_tac`. TODO: also do the `simp_all`. -/
  withMainContext do
  ScalarTac.scalarTacSaturateForward { nonLin := satNonLin } fun scalarTacAsms => do
  trace[CondSimpTac] "Goal after saturating the context: {← getMainGoal}"
  let additionalSimpThms ← addSimpThms
  trace[CondSimpTac] "Goal after adding the additional simp assumptions: {← getMainGoal}"
  /- Simplify the targets (note that we preserve the new assumptions for `scalar_tac`) -/
  let (loc, notLocAsms) ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets oldAsms true, ← getOtherAsms oldAsmsSet)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets hyps type, ← getOtherAsms (Std.HashSet.ofArray hyps))
  if doFirstSimp then
    condSimpTacSimp simpConfig args loc additionalSimpThms false
    if (← getUnsolvedGoals) == [] then return
  trace[CondSimpTac] "Goal after simplifying: {← getMainGoal}"
  /- Simplify the targets by using `scalar_tac` as a discharger -/
  let notLocAsmsSet := Std.HashSet.ofArray notLocAsms
  let nloc ← do
    match loc with
    | .wildcard => pure (Utils.Location.targets (← Utils.refreshFVarIds oldAsmsSet notLocAsmsSet) true)
    | .wildcard_dep => throwError "Unreachable"
    | .targets hyps type => pure (Utils.Location.targets (← Utils.refreshFVarIds (Std.HashSet.ofArray hyps) notLocAsmsSet) type)
  condSimpTacSimp simpConfig args nloc additionalSimpThms true
  if (← getUnsolvedGoals) == [] then return
  /- Clear the additional assumptions -/
  Utils.clearFVarIds scalarTacAsms
  trace[CondSimpTac] "Goal after clearing the scalar_tac assumptions: {← getMainGoal}"
  Utils.clearFVarIds newAsms
  trace[CondSimpTac] "Goal after clearing the duplicated assumptions: {← getMainGoal}"
  Utils.clearFVarIds additionalSimpThms
  trace[CondSimpTac] "Goal after clearing the additional theorems: {← getMainGoal}"

end Aeneas.ScalarTac
