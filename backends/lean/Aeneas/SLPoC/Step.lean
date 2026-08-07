import Aeneas.SLPoC.SepLogic
import Aeneas.Tactic.Step.StepStar
import Lean.Meta.Tactic.AC

namespace Aeneas.SLPoC

open Lean Elab Meta Tactic
open scoped SepLogic

namespace SLPost

/-- Decompose a postcondition into a pure fact and the spatial resources that
remain after introducing that fact. -/
class Decomp {α : Type} (Q : SLPost α) where
  pure : α → Prop
  spatial : SLPost α
  eq : Q = fun value => ⌜pure value⌝ ∗ spatial value

instance (priority := high) (P : α → Prop) (Q : SLPost α) :
    Decomp (fun value => ⌜P value⌝ ∗ Q value) where
  pure := P
  spatial := Q
  eq := rfl

instance (priority := high) (P : α → Prop) :
    Decomp (fun value => ⌜P value⌝) where
  pure := P
  spatial := fun _ => emp
  eq := by
    funext value
    exact (hstar_hempty_r_eq _).symm

instance (priority := low) (Q : SLPost α) : Decomp Q where
  pure := fun _ => True
  spatial := Q
  eq := by
    funext value
    apply hequiv_eq
    intro h
    constructor
    · intro hQ
      exact (hstar_hpure_l True (Q value) h).mpr ⟨True.intro, hQ⟩
    · intro hStar
      exact (hstar_hpure_l True (Q value) h).mp hStar |>.2

end SLPost

attribute [step_simps, step_post_simps]
  SLPost.Decomp.pure SLPost.Decomp.spatial

/-- Bind rule used by `step`. It infers a spatial frame and exposes the pure
part of the stepped function's postcondition as a Lean hypothesis. -/
theorem triple_step_bind {α β : Type} {P Pm F : SLPre}
    {next : α → St β} {Q : SLPost β}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    [decomp : SLPost.Decomp Qm]
    (hPre : P ⊢ Pm ∗ F)
    (hNext :
      ∀ value,
        decomp.pure value →
        triple (decomp.spatial value ∗ F) (next value) Q) :
    triple P (m >>= next) Q := by
  rw [decomp.eq] at hStep
  have hFramed :
      triple P m ((fun value =>
        ⌜decomp.pure value⌝ ∗ decomp.spatial value) ∗+ F) :=
    triple_conseq (triple_frame hStep F) hPre
      (fun _ => himpl_refl _)
  apply triple_bind hFramed
  intro value
  apply triple_conseq (triple_hpure (hNext value))
  · intro h
    exact (hstar_assoc _ _ _ h).mp
  · intro _
    exact himpl_refl _

/-- Consequence/frame rule used by `step` for a terminal monadic call. -/
theorem triple_step_mono {α : Type} {P Pm F : SLPre} {Q : SLPost α}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    [decomp : SLPost.Decomp Qm]
    (hPre : P ⊢ Pm ∗ F)
    (hPost :
      ∀ value,
        decomp.pure value →
        decomp.spatial value ∗ F ⊢ Q value) :
    triple P m Q := by
  rw [decomp.eq] at hStep
  apply triple_conseq_frame hStep hPre
  intro value heap h
  have ⟨hPure, hSpatial⟩ :=
    (hstar_hpure_l (decomp.pure value)
      (decomp.spatial value ∗ F) heap).mp
      ((hstar_assoc _ _ _ heap).mp h)
  exact hPost value hPure heap hSpatial

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 5
    mk_spec_mono_preconditions := 2
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 7
    mk_spec_bind_preconditions := 2
    uncurry_elim_tactics := #[]
    qimp_elim_tactics := #[]
    to_mvcgen := none
    liftings := #[]
  }

attribute [step]
  alloc.spec read.spec update.spec free.spec
  mut_to_raw.spec end_mut_to_raw.spec

namespace SLFrame

private def reducePostApplication (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Lean.Core.betaReduce e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``qstar && args.size = 4 then
    return mkApp2 (mkConst ``hstar) (mkApp args[1]! args[3]!) args[2]!
  return e

private partial def flatten (e : Expr) : MetaM (Array Expr) := do
  let e ← reducePostApplication e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``hstar && args.size = 2 then
    return (← flatten args[0]!) ++ (← flatten args[1]!)
  if fn.isConstOf ``hempty then
    return #[]
  return #[e]

private def mkStar (atoms : Array Expr) : Expr :=
  match atoms.back? with
  | none => mkConst ``hempty
  | some last =>
    atoms.pop.foldr (init := last) fun atom rest =>
      mkApp2 (mkConst ``hstar) atom rest

private def removeMatches (available required : Array Expr) :
    MetaM (Option (Array Expr)) := do
  let mut remaining := available
  for expected in required do
    let mut found := none
    for h : i in [:remaining.size] do
      if ← isDefEq expected remaining[i] then
        found := some i
        break
    let some i := found | return none
    remaining :=
      remaining.extract 0 i ++ remaining.extract (i + 1) remaining.size
  return some remaining

private def proveEqAC (lhs rhs : Expr) : MetaM Expr := do
  let eqType ← mkEq lhs rhs
  let proof ← mkFreshExprSyntheticOpaqueMVar eqType
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create an equality proof goal"
  Lean.Meta.AC.rewriteUnnormalizedRefl proofId
  return proof

private def provePure (proposition : Expr) : TacticM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar proposition
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create a pure proof goal"
  let (goals, _) ← runTactic proofId (← `(tactic| grind))
  unless goals.isEmpty do
    throwError "could not prove pure assertion {proposition}"
  return proof

private partial def proveToEmp (atoms : Array Expr) : MetaM Expr := do
  if atoms.isEmpty then
    return ← mkAppM ``himpl_refl #[mkConst ``hempty]
  let atom := atoms[0]!
  let (fn, args) := atom.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``hpure && args.size = 1 do
    throwError "cannot discard spatial assertion {atom}; only pure assertions may be discarded"
  let atomProof ← mkAppM ``hpure_elim #[args[0]!]
  if atoms.size = 1 then
    return atomProof
  let restProof ← proveToEmp (atoms.extract 1 atoms.size)
  mkAppM ``hstar_to_emp #[atomProof, restProof]

private def solveHimpl (goal : MVarId) : TacticM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do
    throwError "expected a separation-logic entailment"
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let sourceAtoms ← flatten source

  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  let frameMVar? :=
    if destFn.isConstOf ``hstar && destArgs.size = 2 then
      match destArgs[1]!.consumeMData with
      | .mvar mvarId => some mvarId
      | _ => none
    else none
  if let some frameMVar := frameMVar? then
    if ← frameMVar.isAssigned then
      throwError "the inferred frame has already been assigned"
    let required := destArgs[0]!
    let requiredAtoms ← flatten required
    let some frameAtoms ← removeMatches sourceAtoms requiredAtoms
      | throwError "required spatial assertions are not present in the precondition"
    frameMVar.assign (mkStar frameAtoms)
    let destination ← instantiateMVars destination
    let eqProof ← proveEqAC source destination
    goal.assign (← mkAppM ``himpl_of_eq #[eqProof])
  else
    let destinationAtoms ← flatten destination
    let mut remaining := sourceAtoms
    let mut matched : Array Expr := #[]
    let mut generatedPure : Array (Expr × Expr) := #[]
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
      else
        let (expectedFn, expectedArgs) :=
          expected.consumeMData.withApp fun fn args => (fn, args)
        unless expectedFn.isConstOf ``hpure && expectedArgs.size = 1 do
          throwError "required spatial assertions are not present\nsource: {source}\ndestination: {destination}"
        let proof ← provePure expectedArgs[0]!
        generatedPure := generatedPure.push (expected, proof)
    let discardedAtoms := remaining
    let matchedAssertion := mkStar matched
    let sourceToMatched ←
      if discardedAtoms.isEmpty then
        let eqProof ← proveEqAC source matchedAssertion
        mkAppM ``himpl_of_eq #[eqProof]
      else
        let discarded := mkStar discardedAtoms
        let reordered := mkApp2 (mkConst ``hstar) matchedAssertion discarded
        let eqProof ← proveEqAC source reordered
        let reorderProof ← mkAppM ``himpl_of_eq #[eqProof]
        let discardProof ← proveToEmp discardedAtoms
        let eliminateProof ← mkAppOptM ``hstar_elim_right
          #[some matchedAssertion, some discarded, some discardProof]
        mkAppM ``himpl_trans #[reorderProof, eliminateProof]
    let mut current := matchedAssertion
    let mut insertionProof ← mkAppM ``himpl_refl #[current]
    for (pureAtom, pureProof) in generatedPure do
      let insertProof ← mkAppM ``hpure_hstar_intro #[current, pureProof]
      insertionProof ← mkAppM ``himpl_trans #[insertionProof, insertProof]
      current := mkApp2 (mkConst ``hstar) pureAtom current
    let eqProof ← proveEqAC current destination
    let reorderProof ← mkAppM ``himpl_of_eq #[eqProof]
    let matchedToDestination ← mkAppM ``himpl_trans #[insertionProof, reorderProof]
    goal.assign (← mkAppM ``himpl_trans #[sourceToMatched, matchedToDestination])

private partial def solveGoal (goal : MVarId) : TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``qimpl && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal nextGoal
  else
    solveHimpl goal

end SLFrame

/-- Infer and prove separation-logic frames. Unmatched pure assertions may be
discarded; unmatched spatial assertions are reported as an error. -/
elab "sl_frame" : tactic => withMainContext do
  let localAsms :=
    (← (← getLCtx).getAssumptions).map LocalDecl.fvarId |>.toArray
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { hypsToUse := localAsms } (.targets #[] true)
  if !(← getGoals).isEmpty then
    let goal ← getMainGoal
    SLFrame.solveGoal goal
    replaceMainGoal []

end Aeneas.SLPoC
