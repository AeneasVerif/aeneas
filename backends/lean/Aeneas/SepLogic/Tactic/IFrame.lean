module
public import Aeneas.SepLogic.Tactic.Matchers
public meta import Aeneas.SepLogic.Tactic.Matchers
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Normalize Matchers

namespace IFrame

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

/-- Replace each `∃` atom of the destination by its body at a fresh witness metavariable, with
one reflective reordering per `∃` (no simp). -/
partial def instantiateRightExists (goal : MVarId)
    (witnesses : Array MVarId := #[]) : TacticM (MVarId × Array MVarId) := do
  if ← isFrameInference goal then return (goal, witnesses)
  let goal ← exposeGoal goal
  if ← isFrameInference goal then return (goal, witnesses)
  goal.withContext do
  let some (source, destination) ← entailment? goal | return (goal, witnesses)
  let destination ← reducePostApplication destination
  let atoms ← flatten destination
  let some i := atoms.findIdx? (·.consumeMData.isAppOfArity ``iexists 2)
    | solveWitnessEqs destination witnesses
      return (goal, witnesses)
  let atom := atoms[i]!.consumeMData
  let some u := atom.getAppFn.constLevels!.head?
    | throwError "could not determine the universe of {atom}"
  let ι := atom.appFn!.appArg!
  let J := atom.appArg!
  let witness ← mkFreshExprMVar ι
  let body ← Core.betaReduce (mkApp J witness)
  let others := atoms.eraseIdx! i
  let (reordered, newDestination, intro) :=
    if others.isEmpty then (atom, body, fun newGoal =>
      mkAppN (mkConst ``entails_exists_r [u]) #[ι, source, J, witness, newGoal])
    else
      let rest := mkStar others
      (mkApp2 (mkConst ``sep) atom rest, mkApp2 (mkConst ``sep) body rest, fun newGoal =>
        mkAppN (mkConst ``entails_exists_sep_r [u]) #[ι, source, rest, J, witness, newGoal])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Entails) source newDestination)
  let reorder := mkApp3 (mkConst ``entails_of_eq) reordered destination
    (← proveEqAC reordered destination)
  goal.assign (mkApp5 (mkConst ``entails_trans) source reordered destination
    (intro newGoal) reorder)
  instantiateRightExists newGoal.mvarId! (witnesses.push witness.mvarId!)

/-- The shared start of `iframe` and `isimp` on an entailment that is not frame inference: pull
the ∃ and ⌜⌝ of the precondition into the context, and replace the ∃ of the postcondition by
witness metavariables (returned). `none` if this closed the goal. -/
def prepareGoal (goal : MVarId) (useFacts := true) (decomposing := false) :
    TacticM (Option (MVarId × Array MVarId)) := do
  let some goal ← pullAndRewrite goal useFacts | return none
  let (goal, witnesses) ← instantiateRightExists goal
  let goal ← exposeGoal goal
  let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
  return some (goal, witnesses)

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
  if let some frameMVar := ← frameMVar? destination then
    let destArgs := destination.consumeMData.getAppArgs
    let original ← reducePostApplication destArgs[0]!
    let sourceAtoms ← flatten source
    let solveWith (required weakening : Expr) (witnesses : Array MVarId) :
        TacticM Bool := do
      let some (pairs, frameAtoms) ← matchAll sourceAtoms (← flatten required)
        | return false
      for witness in witnesses do
        unless ← witness.isAssigned do return false
      let frame := mkStar frameAtoms
      frameMVar.assign frame
      let cancelled := mkApp2 (mkConst ``sep) (← instantiateMVars required) frame
      let reorder ← mkAppM ``entails_of_eq #[← proveEqAC source cancelled pairs]
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
    solveResidual discharger (← cancelGoal goal)

/-- Prove the residual `left ⊢ right` of `cancelGoal`, where `right` may only have pure atoms,
which are proved, and one magic wand, which absorbs `left` (dropped otherwise). -/
partial def solveResidual (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let some (left, right) ← entailment? goal
    | throwError "expected a separation-logic entailment"
  let left ← reducePostApplication left
  let right ← reducePostApplication right
  let mut pures : Array Expr := #[]
  let mut absorbing : Option Expr := none
  for expected in ← flatten right do
    if expected.consumeMData.isAppOfArity ``ipure 1 then
      pures := pures.push expected
    else if isWand expected then
      if absorbing.isSome then
        throwError "cannot handle more than one magic wand on the right-hand side\
          \ndestination: {right}"
      absorbing := some expected
    else
      throwError "required spatial assertions are not present\
        \nsource: {left}\ndestination: {right}\nmissing: {expected}"
  let pureProofs ← pures.mapM fun expected => do
    provePure discharger (← instantiateMVars expected.consumeMData.appArg!)
  let (current, proof) ← match absorbing with
    | some wand => pure (wand, ← proveWand discharger left wand)
    | none => pure (mkConst `Aeneas.SepLogic.emp, mkApp (mkConst ``entails_emp_r) left)
  let mut current := current
  let mut proof := proof
  for expected in pures, pureProof in pureProofs do
    proof ← mkAppM ``entails_trans #[proof, ← mkAppM ``pure_sep_intro #[current, pureProof]]
    current := mkApp2 (mkConst ``sep) expected current
  goal.assign (← mkAppM ``entails_trans
    #[proof, ← mkAppM ``entails_of_eq #[← proveEqAC current right]])

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
        let some (goal, witnesses) ← prepareGoal goal (decomposing := decomposing) | return
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
