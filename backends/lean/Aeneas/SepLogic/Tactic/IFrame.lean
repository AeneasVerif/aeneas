module
public import Aeneas.SepLogic.Tactic.Init
public meta import Aeneas.SepLogic.Tactic.Init
public import Lean.Meta.Tactic.AC
public meta import Lean
public meta import AeneasMeta.Simp
public meta section

namespace Aeneas.SepLogic

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic

namespace IFrame

private def isConnective (e : Expr) : Bool :=
  let head := e.consumeMData.getAppFn
  head.isConstOf ``sep || head.isConstOf ``iand || head.isConstOf ``ipure ||
    head.isConstOf ``iexists || head.isConstOf `Aeneas.SepLogic.emp ||
    head.isConstOf ``wand || head.isConstOf ``postWand || head.isConstOf ``iforall

private def wand? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``postWand 3 then some true
  else if e.isAppOfArity ``wand 2 then some false
  else none

def exposeConnective? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if isConnective e then return some e
  match ← unfoldDefinition? e with
  | some e' => if isConnective e' then return some e' else return none
  | none => return none

def exposeConnective (e : Expr) : MetaM Expr :=
  return (← exposeConnective? e).getD e

partial def exposeEntailment? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Entails 2 then return some e
  match ← unfoldDefinition? e with
  | some e' => exposeEntailment? e'
  | none => return none

def mkEntailmentLike (target source destination newSource : Expr) : MetaM Expr := do
  let (fn, targetArgs) :=
    target.consumeMData.withApp fun fn args => (fn, args)
  let newSourceType ← inferType newSource
  for h : i in [:targetArgs.size] do
    let argType ← inferType targetArgs[i]
    if ← isDefEq argType newSourceType then
      let candidate := mkAppN fn (targetArgs.set! i newSource)
      if let some exposed ← exposeEntailment? candidate then
        let args := exposed.getAppArgs
        if ← isDefEq args[0]! newSource then
          if ← isDefEq args[1]! destination then
            return candidate
  let replacement := target.replace fun e =>
    if e == source then some newSource else none
  if let some exposed ← exposeEntailment? replacement then
    let args := exposed.getAppArgs
    if ← isDefEq args[0]! newSource then
      if ← isDefEq args[1]! destination then
        return replacement
  mkAppM ``Entails #[newSource, destination]

def reducePostApplication (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Lean.Core.betaReduce e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postSep && args.size = 4 then
    return mkApp2 (mkConst ``sep) (mkApp args[1]! args[3]!) args[2]!
  return e

partial def flatten (e : Expr) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return (← flatten args[0]!) ++ (← flatten args[1]!)
  if fn.isConstOf `Aeneas.SepLogic.emp then
    return #[]
  return #[e]

def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst `Aeneas.SepLogic.emp
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``sep) atom rest

def removeMatches (available required : Array Expr) :
    MetaM (Option (Array Expr)) := commitWhenSome? do
  let mut remaining := available
  for expected in required do
    let mut found := none
    for h : i in [:remaining.size] do
      if ← isDefEq expected remaining[i] then
        found := some i
        break
    let some i := found
      | return none
    remaining :=
      remaining.extract 0 i ++ remaining.extract (i + 1) remaining.size
  return some remaining

def proveEqAC (lhs rhs : Expr) : TacticM Expr := do
  let eqType ← mkEq lhs rhs
  let proof ← mkFreshExprSyntheticOpaqueMVar eqType
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create an equality proof goal"
  let tactic ← `(tactic|
    first
      | rfl
      | ac_rfl
      | (simp only [sep_emp_l_eq, sep_emp_r_eq] <;>
          first | rfl | ac_rfl))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove {eqType}"
  return proof

private def provePure (discharger : Option Syntax.Tactic) (proposition : Expr) :
    TacticM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar proposition
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create a pure proof goal"
  let tactic ←
    match discharger with
    | some tactic => pure tactic
    | none =>
      `(tactic|
        first
          | grind
          | (simp only [iris_simps, *]; done)
          | (simp only [iris_simps, *]; grind)
          | (simp_all; done)
          | (simp_all; grind))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove pure assertion {proposition}"
  return proof

/-- Is `destination` a frame-inference shape `Hcallee ∗ ?F`? Then no side may be reorganized. -/
private def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``sep && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return false
  return (← frameMVar? (← reducePostApplication args[1]!)).isSome

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Aeneas.Simp.SimpArgs) : TacticM MVarId := do
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Aeneas.Simp.simpAt simpOnly
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      args (.targets #[] true)
    match ← getGoals with
    | [] => throwError "the entailment was unexpectedly closed while normalizing it"
    | goal :: _ => pure goal
  finally
    setGoals saved

private def floatExists (goal : MVarId) : TacticM MVarId :=
  simpEntailment goal true
    { addSimpThms :=
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq] }

private def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← irisSimpExt.getTheorems] }

private partial def exposeAll (e : Expr) : MetaM Expr := do
  let e ← reducePostApplication e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``sep && args.size = 2 then
    return mkApp2 (mkConst ``sep) (← exposeAll args[0]!) (← exposeAll args[1]!)
  return e

def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let exposed ← mkAppM ``Entails #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

partial def pullLeft (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then return goal
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let (sourceFn, sourceArgs) :=
    source.consumeMData.withApp fun fn args => (fn, args)
  if sourceFn.isConstOf ``iexists && sourceArgs.size = 2 then
    let some u := sourceFn.constLevels!.head?
      | throwError "could not determine the universe of {source}"
    let ι := sourceArgs[0]!
    let J := sourceArgs[1]!
    let newType ← withLocalDeclD (← mkFreshUserName `x) ι fun x => do
      mkForallFVars #[x] (← mkAppM ``Entails #[← Core.betaReduce (mkApp J x), destination])
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``entails_exists_l [u]) #[ι, destination, J, newGoal])
    let (_, next) ← newGoal.mvarId!.intro1P
    return ← pullLeft next
  let atoms ← flatten source
  let some i := atoms.findIdx? fun atom =>
      atom.consumeMData.isAppOfArity ``ipure 1
    | return goal
  let atom := atoms[i]!
  let proposition := atom.consumeMData.appArg!
  let rest := mkStar (atoms.eraseIdx! i)
  let newType ← withLocalDeclD (← mkFreshUserName `h) proposition fun h => do
    mkForallFVars #[h] (← mkAppM ``Entails #[rest, destination])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  let extract := mkAppN (mkConst ``entails_pure_l)
    #[proposition, rest, destination, newGoal]
  let reordered := mkApp2 (mkConst ``sep) atom rest
  let reorder ← mkAppM ``entails_of_eq #[← proveEqAC source reordered]
  goal.assign (← mkAppM ``entails_trans #[reorder, extract])
  let (_, next) ← newGoal.mvarId!.intro1P
  pullLeft next

def rewritePureFacts (goal : MVarId) (facts : Array FVarId) :
    TacticM (Option MVarId) := goal.withContext do
  if facts.isEmpty then return some goal
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Aeneas.Simp.simpAt true
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      { hypsToUse := facts } (.targets #[] true)
    match ← getUnsolvedGoals with
    | [] => return none
    | [goal] => return some goal
    | _ => throwError "normalizing pure facts produced multiple goals"
  finally
    setGoals saved

partial def instantiateRightExists (goal : MVarId)
    (witnesses : Array MVarId := #[]) : TacticM (MVarId × Array MVarId) := do
  if ← isFrameInference goal then return (goal, witnesses)
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return (goal, witnesses)
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do return (goal, witnesses)
  let source := args[0]!
  let destination ← reducePostApplication args[1]!
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``iexists && destArgs.size = 2 do return (goal, witnesses)
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
  let some isPostcondition := wand? wand
    | throwError "expected a magic wand, got {wand}"
  let args := wand.consumeMData.getAppArgs
  let (lemmaName, premise) ←
    if isPostcondition then
      pure (``postWand_intro,
        ← mkAppM ``postEntails #[← mkAppM ``postSep #[args[1]!, residual], args[2]!])
    else
      pure (``wand_intro,
        ← mkAppM ``Entails #[mkApp2 (mkConst ``sep) args[0]! residual, args[1]!])
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``Entails && args.size = 2 do
    throwError "expected a separation-logic entailment"
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
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
    unless ← commitWhen (solveWith original (← mkAppM ``entails_refl #[original]) #[]) <||>
        commitWhen solvePeeled do
      throwError "required spatial assertions are not present in the precondition\
        \nsource: {source}\ndestination: {destination}"
  else
    let destinationAtoms ← flatten destination
    let mut remaining := sourceAtoms
    let mut matched : Array Expr := #[]
    let mut deferredPure : Array Expr := #[]
    let mut absorbing : Option Expr := none
    for expected in destinationAtoms do
      let mut found := none
      for h : i in [:remaining.size] do
        if ← isDefEq expected remaining[i] then
          found := some i
          break
      if let some i := found then
        matched := matched.push expected
        remaining :=
          remaining.extract 0 i ++ remaining.extract (i + 1) remaining.size
      else if expected.consumeMData.isAppOfArity ``ipure 1 then
        deferredPure := deferredPure.push expected
      else if (wand? expected).isSome then
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
        let before ← goal.withContext do
          return (← getLCtx).foldl (init := (∅ : Std.HashSet FVarId))
            fun ids decl => ids.insert decl.fvarId
        let goal ← pullLeft goal
        let facts ← goal.withContext do
          return (← (← getLCtx).getAssumptions).filterMap fun decl =>
            if before.contains decl.fvarId then none else some decl.fvarId
        let some goal ← rewritePureFacts goal facts.toArray | return
        let (goal, _) ← instantiateRightExists goal
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
    try pass false
    catch firstError =>
      try pass true
      catch secondError =>
        throwError "iframe failed.\n\
          {firstError.toMessageData}\n\
          and, after decomposing the assertions with `iris_simps`:\n\
          {secondError.toMessageData}"

partial def pullGoal (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then
    throwError "iintro_entail: this is a frame-inference goal.  Extracting anything \
      from its left-hand side would lose it from the frame, which was created in \
      an outer context; pull at the level of the specification instead, with `iintro`."
  let target ← instantiateMVars (← goal.getType)
  if target.consumeMData.isAppOfArity ``postEntails 3 then
    let (_, next) ← goal.intro1P
    pullLeft next
  else
    pullLeft goal

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

def normalizeSep : TacticM Unit := withMainContext do
  let _ ← Aeneas.Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``sep_emp_l_eq, ``sep_emp_r_eq,
          ``sep_exists_l_eq, ``sep_exists_r_eq, ``sep_assoc_eq,
          ``entails_postWand_pure_eq] }
    (.targets #[] true)

end Aeneas.SepLogic
