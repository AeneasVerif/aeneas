module
public import Aeneas.SepLogic.Tactic.Common
public meta import Aeneas.SepLogic.Tactic.Common
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Common

namespace IFrame

private def isWand (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``postWand 3 || e.isAppOfArity ``wand 2

/-- For `H₁ -∗ H₂` (resp. `Q₁ -∗+ Q₂`), the introduction lemma and its premise
`H₁ ∗ residual ⊢ H₂` (resp. `Q₁ ∗+ residual ⊢+ Q₂`). -/
def wandIntro? (residual wand : Expr) : MetaM (Option (Name × Expr)) := do
  let wand := wand.consumeMData
  let args := wand.getAppArgs
  if wand.isAppOfArity ``postWand 3 then
    return some (``postWand_intro,
      ← mkAppM ``postEntails #[← mkAppM ``postSep #[args[1]!, residual], args[2]!])
  if wand.isAppOfArity ``wand 2 then
    return some (``wand_intro,
      ← mkAppM ``Entails #[mkApp2 (mkConst ``sep) args[0]! residual, args[1]!])
  return none

private def provePure (discharger : Option Syntax.Tactic) (proposition : Expr) :
    TacticM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar proposition
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create a pure proof goal"
  let tactic ←
    match discharger with
    | some tactic => pure tactic
    | none =>
      `(tactic| first | grind | (simp only [isimps, *] <;> grind) | (simp_all <;> grind))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove pure assertion {proposition}"
  return proof

/-- Assign the witnesses fixed by a pure equation `⌜?w = t⌝` (or `⌜t = ?w⌝`) of the destination,
so that cancellation does not commit them greedily to the wrong atom. -/
private def solveWitnessEqs (destination : Expr) (witnesses : Array MVarId) : MetaM Unit := do
  if witnesses.isEmpty then return
  let isWitness (e : Expr) : Bool := match e.consumeMData with
    | .mvar id => witnesses.contains id
    | _ => false
  for atom in ← flatten destination do
    let atom := atom.consumeMData
    unless atom.isAppOfArity ``ipure 1 do continue
    let some (_, lhs, rhs) := (← instantiateMVars atom.appArg!).consumeMData.eq? | continue
    if isWitness lhs || isWitness rhs then
      discard <| isDefEq lhs rhs

partial def instantiateRightExists (goal : MVarId)
    (witnesses : Array MVarId := #[]) : TacticM (MVarId × Array MVarId) := do
  if ← isFrameInference goal then return (goal, witnesses)
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return (goal, witnesses)
  goal.withContext do
  let some (source, destination) ← entailment? goal | return (goal, witnesses)
  let destination ← reducePostApplication destination
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``iexists && destArgs.size = 2 do
    solveWitnessEqs destination witnesses
    return (goal, witnesses)
  let some u := destFn.constLevels!.head?
    | throwError "could not determine the universe of {destination}"
  let ι := destArgs[0]!
  let J := destArgs[1]!
  let witness ← mkFreshExprMVar ι
  let newType ← mkAppM ``Entails #[source, ← Core.betaReduce (mkApp J witness)]
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``entails_exists_r [u]) #[ι, source, J, witness, newGoal])
  instantiateRightExists newGoal.mvarId! (witnesses.push witness.mvarId!)

private partial def peelRequiredExists (required : Expr) :
    MetaM (Expr × Expr × Array MVarId) := do
  let required ← reducePostApplication required
  let (fn, args) := required.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``iexists && args.size = 2 do
    return (required, ← mkAppM ``entails_refl #[required], #[])
  let some u := fn.constLevels!.head?
    | throwError "could not determine the universe of {required}"
  let ι := args[0]!
  let J := args[1]!
  let witness ← mkFreshExprMVar ι
  let body ← Core.betaReduce (mkApp J witness)
  let (peeled, peeledEntailsBody, witnesses) ← peelRequiredExists body
  let bodyEntailsRequired := mkAppN (mkConst ``entails_exists_r [u])
    #[ι, body, J, witness, ← mkAppM ``entails_refl #[body]]
  return (peeled,
    ← mkAppM ``entails_trans #[peeledEntailsBody, bodyEntailsRequired],
    witnesses.push witness.mvarId!)

mutual

partial def proveWand (discharger : Option Syntax.Tactic)
    (residual wand : Expr) : TacticM Expr := do
  let some (lemmaName, premise) ← wandIntro? residual wand
    | throwError "expected a magic wand, got {wand}"
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let some (source, destination) ← entailment? goal
    | throwError "expected a separation-logic entailment"
  let source ← reducePostApplication source
  let destination ← reducePostApplication destination
  let sourceAtoms ← flatten source

  if let some frameMVar := ← frameMVar? destination then
    let destArgs := destination.consumeMData.getAppArgs
    let original ← reducePostApplication destArgs[0]!
    let solveWith (required weakening : Expr) (witnesses : Array MVarId) :
        TacticM Bool := do
      let requiredAtoms ← flatten required
      let some frameAtoms ← removeMatches sourceAtoms requiredAtoms
        | return false
      for witness in witnesses do
        unless ← witness.isAssigned do return false
      let frame := mkStar frameAtoms
      frameMVar.assign frame
      let cancelled := mkApp2 (mkConst ``sep) (← instantiateMVars required) frame
      let reorder ← mkAppM ``entails_of_eq #[← proveEqAC source cancelled]
      let weaken ← mkAppM ``sep_mono
        #[← instantiateMVars weakening, ← mkAppM ``entails_refl #[frame]]
      goal.assign (← mkAppM ``entails_trans #[reorder, weaken])
      return true
    let solvePeeled : TacticM Bool := do
      let (peeled, weakening, witnesses) ← peelRequiredExists original
      solveWith peeled weakening witnesses
    let openSourceExists : TacticM Bool := do
      let (sourceFn, sourceArgs) := source.consumeMData.withApp fun fn args => (fn, args)
      unless sourceFn.isConstOf ``iexists && sourceArgs.size = 2 do return false
      let some u := sourceFn.constLevels!.head? | return false
      let ι := sourceArgs[0]!
      let J := sourceArgs[1]!
      let some (body, frameFn) ← withLocalDeclD (← mkFreshUserName `x) ι fun x => do
        let innerFrame ← mkFreshExprMVar (mkConst ``IProp)
        let innerGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Entails
          #[← Core.betaReduce (mkApp J x), mkApp2 (mkConst ``sep) original innerFrame])
        try solveHimpl discharger innerGoal.mvarId! catch _ => return none
        return some (← mkLambdaFVars #[x] (← instantiateMVars innerGoal),
          ← mkLambdaFVars #[x] (← instantiateMVars innerFrame))
        | return false
      frameMVar.assign (mkApp2 (mkConst ``iexists [u]) ι frameFn)
      goal.assign (mkAppN (mkConst ``entails_exists_frame [u]) #[ι, original, J, frameFn, body])
      return true
    unless ← commitWhen (solveWith original (← mkAppM ``entails_refl #[original]) #[]) <||>
        commitWhen solvePeeled <||> commitWhen openSourceExists do
      throwError "required spatial assertions are not present in the precondition\
        \nsource: {source}\ndestination: {destination}"
  else
    let (matched, unmatched, remaining) ← matchAtoms sourceAtoms (← flatten destination)
    let mut deferredPure : Array Expr := #[]
    let mut absorbing : Option Expr := none
    for expected in unmatched do
      if expected.consumeMData.isAppOfArity ``ipure 1 then
        deferredPure := deferredPure.push expected
      else if isWand expected then
        if absorbing.isSome then
          throwError "cannot handle more than one magic wand on the right-hand \
            side\ndestination: {destination}"
        absorbing := some expected
      else
        throwError "required spatial assertions are not present\
          \nsource: {source}\ndestination: {destination}\nmissing: {expected}"
    let mut generatedPure : Array (Expr × Expr) := #[]
    for expected in deferredPure do
      let proposition ← instantiateMVars expected.consumeMData.appArg!
      generatedPure := generatedPure.push (expected, ← provePure discharger proposition)
    let matchedAssertion := mkStar matched
    let (matchedAssertion, sourceToMatched) ←
      match absorbing with
      | some absorbingAtom =>
        let residual := mkStar remaining
        let reordered := mkApp2 (mkConst ``sep) matchedAssertion residual
        let reorderProof ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
        let residualToAbsorber ← proveWand discharger residual absorbingAtom
        let absorbProof ← mkAppM ``sep_mono
          #[← mkAppM ``entails_refl #[matchedAssertion], residualToAbsorber]
        pure (mkApp2 (mkConst ``sep) matchedAssertion absorbingAtom,
          ← mkAppM ``entails_trans #[reorderProof, absorbProof])
      | none =>
        let discardedAtoms := remaining
        let proof ←
          if discardedAtoms.isEmpty then
            mkAppM ``entails_of_eq #[← proveEqAC source matchedAssertion]
          else
            let discarded := mkStar discardedAtoms
            let reordered := mkApp2 (mkConst ``sep) matchedAssertion discarded
            let reorderProof ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
            let eliminateProof ← mkAppM ``sep_elim_right
              #[matchedAssertion, discarded]
            mkAppM ``entails_trans #[reorderProof, eliminateProof]
        pure (matchedAssertion, proof)
    let mut current := matchedAssertion
    let mut insertionProof ← mkAppM ``entails_refl #[current]
    for (pureAtom, pureProof) in generatedPure do
      let insertProof ← mkAppM ``pure_sep_intro #[current, pureProof]
      insertionProof ← mkAppM ``entails_trans #[insertionProof, insertProof]
      current := mkApp2 (mkConst ``sep) pureAtom current
    let destination ← instantiateMVars destination
    let eqProof ← proveEqAC current destination
    let reorderProof ← mkAppM ``entails_of_eq #[eqProof]
    let matchedToDestination ← mkAppM ``entails_trans #[insertionProof, reorderProof]
    goal.assign (← mkAppM ``entails_trans #[sourceToMatched, matchedToDestination])

partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postEntails && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal discharger nextGoal
  else
    let pass (decomposing : Bool) : TacticM Unit := do
      let goal ← if decomposing then decompose goal else pure goal
      if ← isFrameInference goal then
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
      else
        let some goal ← pullAndRewrite goal | return
        let (goal, witnesses) ← instantiateRightExists goal
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
        for witness in witnesses do
          unless ← witness.isAssigned do
            throwError "could not determine the witness {mkMVar witness} of an existential \
              on the right-hand side"
    try pass false
    catch firstError =>
      try pass true
      catch secondError =>
        throwError "iframe failed.\n\
          {firstError.toMessageData}\n\
          and, after decomposing the assertions with `isimps`:\n\
          {secondError.toMessageData}"

end

end IFrame

/-- Prove a separation-logic entailment `H₁ ⊢ H₂` (or `Q₁ ⊢+ Q₂`) by cancelling spatial atoms. -/
syntax (name := iFrame) "iframe" (" by " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| iframe $[by $tac?]?) => Tactic.focus do withMainContext do
  let discharger : Option Syntax.Tactic := tac?.map fun tac => ⟨tac.raw⟩
  let localAsms :=
    (← (← getLCtx).getAssumptions).map LocalDecl.fvarId |>.toArray
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { hypsToUse := localAsms }
    (.targets #[] true)
  if !(← getGoals).isEmpty then
    let goal ← getMainGoal
    IFrame.solveGoal discharger goal
    replaceMainGoal []

end Aeneas.SepLogic
