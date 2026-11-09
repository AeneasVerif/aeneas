module
public import Aeneas.SepLogic.Tactic.Matchers
public meta import Aeneas.SepLogic.Tactic.Matchers
public meta import Lean
public meta import AeneasMeta.Simp

/-! `iframe` proves `H₁ ⊢ H₂` / `Q₁ ⊢+ Q₂`, and infers `?F` in `step`'s goals `H ⊢ Hcallee ∗ ?F`.
It pulls left `∃`/`⌜⌝` into the context, turns right `∃` into metavariables, cancels atoms by
unification (backtracking `matchAll`), reorders with reflective AC proofs (`proveEqAC`) and proves
pure residues with `grind`. Same algorithm as CFML `xsimpl` / SPlean `xsimp`; ours adds frame
metavariables and matching up to unfolding of definitions whose body is a connective. Other
predicates stay folded: unfold them explicitly, with `irewrite` or `isimp`. -/

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
  -- without recovery, a failing `first` alternative throws instead of logging and admitting
  let goals ← try
      Term.withSynthesize <| Tactic.run proofId
        (Tactic.withoutRecover (Tactic.evalTactic tactic *> Tactic.pruneSolvedGoals))
    catch e => throwError "could not prove pure assertion {proposition}\n{e.toMessageData}"
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
def prepareGoal (goal : MVarId) (useFacts := true) :
    TacticM (Option (MVarId × Array MVarId)) := do
  let some goal ← pullAndRewrite goal useFacts | return none
  let (goal, witnesses) ← instantiateRightExists goal
  let goal ← exposeGoal goal
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

/-- `lhs ⊢ rhs` for assertions equal up to associativity and commutativity (`proveEqAC`). -/
private def entailsAC (lhs rhs : Expr) (aliases : Array (Expr × Expr) := #[]) : MetaM Expr := do
  mkAppM ``entails_of_eq #[← proveEqAC lhs rhs aliases]

/-- Extend `proof : H ⊢ current` to `H ⊢ ⌜Pₖ⌝ ∗ … ∗ ⌜P₁⌝ ∗ current`, from the atoms `⌜Pᵢ⌝` and
proofs of the `Pᵢ`. -/
private def introPures (pures proofs : Array Expr) (current proof : Expr) :
    MetaM (Expr × Expr) := do
  let mut current := current
  let mut proof := proof
  for atom in pures, hP in proofs do
    proof ← mkAppM ``entails_trans #[proof, ← mkAppM ``pure_sep_intro #[current, hP]]
    current := mkApp2 (mkConst ``sep) atom current
  return (current, proof)

/-- Frame inference by cancellation: prove `source ⊢ callee ∗ ?F` from `weakening : pre ⊢ callee`,
by matching the spatial atoms of `pre` with atoms of `source`; the unmatched atoms of `source`
become `?F`. A pure atom of `pre` is matched with a pure atom of `source` if there is one, and
proved from the context otherwise. `false` if a spatial atom or a witness stays unmatched. -/
private def frameByMatching (discharger : Option Syntax.Tactic) (goal frameMVar : MVarId)
    (source pre weakening : Expr) (witnesses : Array MVarId) : TacticM Bool := do
  let (pures, spatial) := (← flatten pre).partition (·.consumeMData.isAppOfArity ``ipure 1)
  let some (pairs, leftover) ← matchAll (← flatten source) spatial | return false
  let mut pairs := pairs
  let mut leftover := leftover
  let mut taken := spatial
  let mut toProve := #[]
  for atom in pures do
    match ← leftover.findIdxM? (isDefEq atom ·) with
    | some i =>
      pairs := pairs.push (atom, leftover[i]!)
      leftover := leftover.eraseIdx! i
      taken := taken.push atom
    | none => toProve := toProve.push atom
  -- every witness must be fixed by matching, before `provePure` sees the facts
  for witness in witnesses do
    unless ← witness.isAssigned do return false
  let proofs ← toProve.mapM fun atom => do
    provePure discharger (← instantiateMVars atom.consumeMData.appArg!)
  -- source = taken ∗ frame ⊢ toProve ∗ taken ∗ frame = pre ∗ frame ⊢ callee ∗ frame
  let frame := mkStar leftover
  let matched := mkApp2 (mkConst ``sep) (mkStar taken) frame
  let (withPures, proof) ← introPures toProve proofs matched (← entailsAC source matched pairs)
  let reorder ← entailsAC withPures (mkApp2 (mkConst ``sep) (← instantiateMVars pre) frame)
  let weaken ← mkAppM ``sep_mono #[← instantiateMVars weakening, ← mkAppM ``entails_refl #[frame]]
  frameMVar.assign frame
  goal.assign (← mkAppM ``entails_trans #[← mkAppM ``entails_trans #[proof, reorder], weaken])
  return true

mutual

partial def proveWand (discharger : Option Syntax.Tactic)
    (residual wand : Expr) : TacticM Expr := do
  let some (lemmaName, premise) ← wandIntro? residual wand
    | throwError "expected a magic wand, got {wand}"
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

/-- Prove `source ⊢ destination`: by frame inference if `destination` is `callee ∗ ?F`, otherwise
by cancelling atoms and proving the residue. -/
partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let some (source, destination) ← entailment? goal
    | throwError "expected a separation-logic entailment"
  let source ← reducePostApplication source
  let destination ← reducePostApplication destination
  match ← frameMVar? destination with
  | some frameMVar => inferFrame discharger goal frameMVar source destination
  | none => solveResidual discharger (← cancelGoal goal)

/-- Frame inference for `source ⊢ callee ∗ ?F`: cancel `callee` directly, else after replacing its
leading `∃`s by witness metavariables, else under the `∃` of `source`. -/
partial def inferFrame (discharger : Option Syntax.Tactic) (goal frameMVar : MVarId)
    (source destination : Expr) : TacticM Unit := do
  let callee ← reducePostApplication destination.consumeMData.appFn!.appArg!
  let direct :=
    frameByMatching discharger goal frameMVar source callee (← mkAppM ``entails_refl #[callee]) #[]
  let peeled : TacticM Bool := do
    let (pre, weakening, witnesses) ← peelRequiredExists callee
    if witnesses.isEmpty then return false
    frameByMatching discharger goal frameMVar source pre weakening witnesses
  unless ← commitWhen direct <||> commitWhen peeled <||>
      commitWhen (frameUnderSourceExists discharger goal frameMVar source callee) do
    throwError "required spatial assertions are not present in the precondition\
      \nsource: {source}\ndestination: {destination}"

/-- Frame inference under the `∃` of `source = ∃ x, J x`: solve `J x ⊢ callee ∗ ?F'` for a fresh
`x`, then `?F := ∃ x, ?F' x` (`entails_exists_frame`). `false` if `source` is not an `∃`. -/
partial def frameUnderSourceExists (discharger : Option Syntax.Tactic) (goal frameMVar : MVarId)
    (source callee : Expr) : TacticM Bool := do
  let (sourceFn, sourceArgs) := source.consumeMData.withApp fun fn args => (fn, args)
  unless sourceFn.isConstOf ``iexists && sourceArgs.size = 2 do return false
  let some u := sourceFn.constLevels!.head? | return false
  let ι := sourceArgs[0]!
  let J := sourceArgs[1]!
  let some (body, frameFn) ← withLocalDeclD (← mkFreshUserName `x) ι fun x => do
    let innerFrame ← mkFreshExprMVar (mkConst ``IProp)
    let innerGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Entails
      #[← Core.betaReduce (mkApp J x), mkApp2 (mkConst ``sep) callee innerFrame])
    try solveHimpl discharger innerGoal.mvarId! catch _ => return none
    return some (← mkLambdaFVars #[x] (← instantiateMVars innerGoal),
      ← mkLambdaFVars #[x] (← instantiateMVars innerFrame))
    | return false
  frameMVar.assign (mkApp2 (mkConst ``iexists [u]) ι frameFn)
  goal.assign (mkAppN (mkConst ``entails_exists_frame [u]) #[ι, callee, J, frameFn, body])
  return true

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
  let (current, proof) ← introPures pures pureProofs current proof
  goal.assign (← mkAppM ``entails_trans #[proof, ← entailsAC current right])

partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``postEntails && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal discharger nextGoal
  else if ← isFrameInference goal then
    solveHimpl discharger (← exposeGoal goal)
  else
    let some (goal, witnesses) ← prepareGoal goal | return
    solveHimpl discharger goal
    for witness in witnesses do
      unless ← witness.isAssigned do
        throwError "could not determine the witness {mkMVar witness} of an existential \
          on the right-hand side"

end

end IFrame

/-- Prove a separation-logic entailment `H₁ ⊢ H₂` (or `Q₁ ⊢+ Q₂`) by cancelling spatial atoms. -/
syntax (name := iFrame) "iframe" (" by " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| iframe $[by $tac?]?) => Tactic.focus do withMainContext do
  discard <| expectEntailment `iframe (post := true)
  let discharger : Option Syntax.Tactic := tac?.map fun tac => ⟨tac.raw⟩
  IFrame.solveGoal discharger (← getMainGoal)
  replaceMainGoal []

end Aeneas.SepLogic
