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
  ok.spec pure.spec
  alloc.spec read.spec update.spec free.spec
  mut_to_raw.spec end_mut_to_raw.spec

namespace SLFrame

/-- The `sl_simps` simp attribute.  `sl_frame` and `sl_pull` use it to normalize
separation-logic assertions before extracting/cancelling them: it is where the
lemmas that unfold or fold representation predicates belong (`nodes_cons`,
`nodes_snoc`, …).  This plays the role of SLF's `xchange`, except that the
rewriting is declarative instead of being spelled out at every call site. -/
initialize slSimpExt : SimpExtension ←
  registerSimpAttr `sl_simps "\
    The `sl_simps` attribute registers simp lemmas used by `sl_frame` and \
    `sl_pull` to normalize separation-logic assertions (typically, lemmas that \
    decompose a representation predicate into the cells it owns)."

private def isConnective (e : Expr) : Bool :=
  let head := e.consumeMData.getAppFn
  head.isConstOf ``hstar || head.isConstOf ``hpure ||
    head.isConstOf ``hexists || head.isConstOf ``hempty

/-- Expose the head connective (`hstar`, `hpure`, `hexists` or `hempty`) of a
separation-logic assertion, by unfolding a definition that is a mere wrapper
around one — `wellFormed s l` is `⌜…⌝ ∗ nodes l`, `isList s vs` is `∃ l, …`.

Exactly one unfolding is performed, and only when it does reveal a connective.
Representation predicates that *compute*, such as `nodes`, are deliberately left
alone: decomposing them is the job of the `sl_simps` lemmas, which would
otherwise never get a chance to fire.  Returns `none` when no connective can be
reached, so that callers keep the original assertion. -/
def exposeConnective? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if isConnective e then return some e
  match ← unfoldDefinition? e with
  | some e' => if isConnective e' then return some e' else return none
  | none => return none

@[inherit_doc exposeConnective?]
def exposeConnective (e : Expr) : MetaM Expr :=
  return (← exposeConnective? e).getD e

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

/-- Prove `lhs = rhs` when the two sides are the same separating conjunction up
to associativity, commutativity and the `emp` unit. -/
private def proveEqAC (lhs rhs : Expr) : TacticM Expr := do
  let eqType ← mkEq lhs rhs
  let proof ← mkFreshExprSyntheticOpaqueMVar eqType
  let .mvar proofId := proof.consumeMData
    | throwError "failed to create an equality proof goal"
  /- `ac_rfl` normalizes modulo associativity and commutativity but does not
     insert or erase the unit, so strip the `emp`s first when it fails. -/
  let tactic ← `(tactic|
    first
      | rfl
      | ac_rfl
      | (simp only [hstar_hempty_l_eq, hstar_hempty_r_eq] <;>
          first | rfl | ac_rfl))
  let (goals, _) ← runTactic proofId tactic
  unless goals.isEmpty do
    throwError "could not prove {eqType}"
  return proof

/-- Discharge a pure side-goal generated by the right-hand side of an
entailment.  This runs last, so the goal mentions no leftover metavariable
coming from a right-hand-side existential.

`grind` alone is not enough: the propositions typically mention the projections
of a representation predicate (`headPtr []`, `lastPtr [c]`, …), which only the
simp set computes.  `discharger` overrides the default chain; a `sym => …`
script driving a `register_sym_simp` variant is a good deterministic
alternative to the backtracking `first` below. -/
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
          | (simp only [sl_simps, *]; done)
          | (simp only [sl_simps, *]; grind)
          | (simp_all; done)
          | (simp_all; grind))
  let (goals, _) ← runTactic proofId tactic
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

/-- Is `destination` a frame-inference destination, i.e. of the shape
`Hcallee ∗ ?F` for an unassigned metavariable `?F`?

In that mode neither side of the entailment may be reorganized: anything we
extracted from the left-hand side would be lost from the frame `?F`, and could
not even be mentioned by it, since `?F` was created in an outer context.  This
is exactly the limitation of the plain frame rule that SLF's ramified frame rule
works around.

`Hcallee` may itself be an existential, in which case floating that existential
out would turn the destination into `∃ x, Hcallee' x ∗ ?F` and hide the frame:
the decision must therefore be taken *before* any normalization. -/
private def frameMVar? (destination : Expr) : MetaM (Option MVarId) := do
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``hstar && destArgs.size = 2 do return none
  match (← instantiateMVars destArgs[1]!).consumeMData with
  | .mvar mvarId => if ← mvarId.isAssigned then pure none else pure (some mvarId)
  | _ => pure none

/-- Is the goal a frame-inference goal?  See `frameMVar?`. -/
private def isFrameInference (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return false
  return (← frameMVar? (← reducePostApplication args[1]!)).isSome

private def simpEntailment (goal : MVarId) (simpOnly : Bool)
    (args : Simp.SimpArgs) : TacticM MVarId := do
  /- Restore the goals we are not working on: `Simp.simpAt` acts on the main
     goal, and dropping the others would silently remove them from the state. -/
  let saved ← getGoals
  try
    setGoals [goal]
    let _ ← Simp.simpAt simpOnly
      { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
      args (.targets #[] true)
    match ← getGoals with
    | [] => throwError "the entailment was unexpectedly closed while normalizing it"
    | goal :: _ => pure goal
  finally
    setGoals saved

/-- Float the existentials of a separating conjunction to its head, where
`pullLeft` and `instantiateRightExists` can see them.  Only used outside of
frame-inference mode: it can hide the frame metavariable behind an existential
(see `frameMVar?`). -/
private def floatExists (goal : MVarId) : TacticM MVarId :=
  simpEntailment goal true
    { addSimpThms :=
        -- Erase the `emp`s first, so that they do not get pushed under a binder.
        #[``hstar_hempty_l_eq, ``hstar_hempty_r_eq,
          ``hstar_hexists_l_eq, ``hstar_hexists_r_eq] }

/-- Decompose the representation predicates of an entailment into the cells they
own, using the `sl_simps` set.  Unlike `floatExists` this is not always
desirable, so `sl_frame` only resorts to it when the plain cancellation fails. -/
private def decompose (goal : MVarId) : TacticM MVarId := do
  simpEntailment goal false { simpThms := #[← slSimpExt.getTheorems] }

/-- SLF's `xpull`: introduce the existentials of the left-hand side and move its
pure facts into the local context.  Returns the residual goal. -/
private partial def pullLeft (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  -- In frame-inference mode the left-hand side must be preserved verbatim.
  if (← frameMVar? destination).isSome then return goal
  let (sourceFn, sourceArgs) :=
    source.consumeMData.withApp fun fn args => (fn, args)
  if sourceFn.isConstOf ``hexists && sourceArgs.size = 2 then
    let some u := sourceFn.constLevels!.head?
      | throwError "could not determine the universe of {source}"
    let ι := sourceArgs[0]!
    let J := sourceArgs[1]!
    let newType ← withLocalDeclD `x ι fun x => do
      mkForallFVars #[x] (← mkAppM ``himpl #[← Core.betaReduce (mkApp J x), destination])
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
    goal.assign (mkAppN (mkConst ``himpl_hexists_l [u]) #[ι, destination, J, newGoal])
    let (_, next) ← newGoal.mvarId!.intro1P
    return ← pullLeft next
  let atoms ← flatten source
  let some i := atoms.findIdx? fun atom =>
      atom.consumeMData.isAppOfArity ``hpure 1
    | return goal
  let atom := atoms[i]!
  let proposition := atom.consumeMData.appArg!
  let rest := mkStar (atoms.eraseIdx! i)
  let newType ← withLocalDeclD `h proposition fun h => do
    mkForallFVars #[h] (← mkAppM ``himpl #[rest, destination])
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  let extract := mkAppN (mkConst ``himpl_hpure_l)
    #[proposition, rest, destination, newGoal]
  let reordered := mkApp2 (mkConst ``hstar) atom rest
  let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
  goal.assign (← mkAppM ``himpl_trans #[reorder, extract])
  let (_, next) ← newGoal.mvarId!.intro1P
  pullLeft next

/-- SLF's right-hand-side existential instantiation: replace `∃ x, J x` by
`J ?x` for a fresh metavariable `?x`, to be determined by the cancellation
phase. -/
private partial def instantiateRightExists (goal : MVarId) : TacticM MVarId :=
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let source := args[0]!
  let destination ← reducePostApplication args[1]!
  let (destFn, destArgs) :=
    destination.consumeMData.withApp fun fn args => (fn, args)
  unless destFn.isConstOf ``hexists && destArgs.size = 2 do return goal
  let some u := destFn.constLevels!.head?
    | throwError "could not determine the universe of {destination}"
  let ι := destArgs[0]!
  let J := destArgs[1]!
  let witness ← mkFreshExprMVar ι
  let newType ← mkAppM ``himpl #[source, ← Core.betaReduce (mkApp J witness)]
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkAppN (mkConst ``himpl_hexists_r [u]) #[ι, source, J, witness, newGoal])
  instantiateRightExists newGoal.mvarId!

/-- Rewrite an assertion into an equivalent one whose connectives are all
visible, by unfolding definitions such as `wellFormed` or `isList` through the
separating conjunctions.  Only delta/beta reduction is involved, so the result is
definitionally equal to the input. -/
private partial def exposeAll (e : Expr) : MetaM Expr := do
  let e ← reducePostApplication e
  let e := (← exposeConnective? e).getD e
  let (fn, args) := e.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``hstar && args.size = 2 then
    return mkApp2 (mkConst ``hstar) (← exposeAll args[0]!) (← exposeAll args[1]!)
  return e

/-- Replace the top-level existentials of the callee precondition of a
frame-inference goal by metavariables, so that the cancellation can pick the
witnesses.  Returns the peeled assertion together with a proof that it entails
the original one.

Unlike `pullLeft`, this is sound in frame-inference mode: it introduces
metavariables, not free variables, so nothing can escape the scope of the frame
metavariable. -/
private partial def peelRequiredExists (required : Expr) :
    MetaM (Expr × Expr × Array MVarId) := do
  let required ← reducePostApplication required
  let (fn, args) := required.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``hexists && args.size = 2 do
    return (required, ← mkAppM ``himpl_refl #[required], #[])
  let some u := fn.constLevels!.head?
    | throwError "could not determine the universe of {required}"
  let ι := args[0]!
  let J := args[1]!
  let witness ← mkFreshExprMVar ι
  let body ← Core.betaReduce (mkApp J witness)
  let (peeled, peeledEntailsBody, witnesses) ← peelRequiredExists body
  let bodyEntailsRequired := mkAppN (mkConst ``himpl_hexists_r [u])
    #[ι, body, J, witness, ← mkAppM ``himpl_refl #[body]]
  return (peeled,
    ← mkAppM ``himpl_trans #[peeledEntailsBody, bodyEntailsRequired],
    witnesses.push witness.mvarId!)

/-- Put the entailment of `goal` in the exposed form computed by `exposeAll`. -/
private def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let exposed ← mkAppM ``himpl #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

private def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do
    throwError "expected a separation-logic entailment"
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
  let sourceAtoms ← flatten source

  if let some frameMVar := ← frameMVar? destination then
    let destArgs := destination.consumeMData.getAppArgs
    let original ← reducePostApplication destArgs[0]!
    /- Cancel `required` against the source and put the leftovers in the frame.
       `weakening` proves `required ⊢ original`, and `witnesses` are the
       metavariables `peelRequiredExists` introduced: the cancellation has to
       determine all of them, otherwise the proof term would be incomplete. -/
    let solveWith (required weakening : Expr) (witnesses : Array MVarId) :
        TacticM Bool := do
      let requiredAtoms ← flatten required
      let some frameAtoms ← removeMatches sourceAtoms requiredAtoms
        | return false
      for witness in witnesses do
        unless ← witness.isAssigned do return false
      let frame := mkStar frameAtoms
      frameMVar.assign frame
      let cancelled := mkApp2 (mkConst ``hstar) (← instantiateMVars required) frame
      let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC source cancelled]
      let weaken ← mkAppM ``hstar_mono
        #[← instantiateMVars weakening, ← mkAppM ``himpl_refl #[frame]]
      goal.assign (← mkAppM ``himpl_trans #[reorder, weaken])
      return true
    let state ← saveState
    /- First try the callee precondition as it stands: it may well be owned as a
       single opaque assertion (an `isList`, say) by the caller.  Only if that
       fails do we open its existentials. -/
    unless ← solveWith original (← mkAppM ``himpl_refl #[original]) #[] do
      state.restore
      let (peeled, weakening, witnesses) ← peelRequiredExists original
      unless ← solveWith peeled weakening witnesses do
        state.restore
        throwError "required spatial assertions are not present in the precondition\
          \nsource: {source}\ndestination: {destination}"
  else
    let destinationAtoms ← flatten destination
    let mut remaining := sourceAtoms
    let mut matched : Array Expr := #[]
    /- Cancellation phase.  Destination atoms that cannot be cancelled must be
       pure; we only record them here and discharge them below, once every
       metavariable introduced for a right-hand-side existential has had a
       chance to be instantiated by unification. -/
    let mut deferredPure : Array Expr := #[]
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
        unless expected.consumeMData.isAppOfArity ``hpure 1 do
          throwError "required spatial assertions are not present\
            \nsource: {source}\ndestination: {destination}\nmissing: {expected}"
        deferredPure := deferredPure.push expected
    let mut generatedPure : Array (Expr × Expr) := #[]
    for expected in deferredPure do
      let proposition ← instantiateMVars expected.consumeMData.appArg!
      generatedPure := generatedPure.push (expected, ← provePure discharger proposition)
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
    let destination ← instantiateMVars destination
    let eqProof ← proveEqAC current destination
    let reorderProof ← mkAppM ``himpl_of_eq #[eqProof]
    let matchedToDestination ← mkAppM ``himpl_trans #[insertionProof, reorderProof]
    goal.assign (← mkAppM ``himpl_trans #[sourceToMatched, matchedToDestination])

private partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``qimpl && args.size = 3 then
    let (_, nextGoal) ← goal.intro1P
    solveGoal discharger nextGoal
  else
    /- Two passes.  The first one only reorganizes the connectives; it is the one
       that succeeds when the assertion to produce is a representation predicate
       applied to a metavariable, which no rewriting could ever match.  The
       second one additionally decomposes the representation predicates with the
       `sl_simps` set, which is what is needed when the two sides of the
       entailment own the same cells but describe them differently. -/
    let pass (decomposing : Bool) : TacticM Unit := do
      let goal ← if decomposing then decompose goal else pure goal
      /- Decide here whether we are inferring a frame: `floatExists` below can
         turn `Hcallee ∗ ?F` into `∃ x, Hcallee' x ∗ ?F` and hide `?F`. -/
      if ← isFrameInference goal then
        solveHimpl discharger (← exposeGoal goal)
      else
        let goal ← pullLeft (← exposeGoal (← floatExists goal))
        let goal ← instantiateRightExists (← floatExists goal)
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
    let state ← saveState
    try pass false
    catch firstError =>
      state.restore
      try pass true
      catch secondError =>
        throwError "sl_frame failed.\n\
          {firstError.toMessageData}\n\
          and, after decomposing the assertions with `sl_simps`:\n\
          {secondError.toMessageData}"

end SLFrame

/-- Prove a separation-logic entailment `H₁ ⊢ H₂` (or a postcondition entailment
`Q₁ ⊢+ Q₂`), in the style of SLF's `xsimpl`:

1. the existentials of the left-hand side are introduced and its pure facts are
   moved into the local context (SLF's `xpull`);
2. the existentials of the right-hand side are replaced by metavariables;
3. the spatial assertions of the right-hand side are cancelled against those of
   the left-hand side, up to associativity/commutativity, which is what
   instantiates the metavariables of step 2;
4. the pure assertions left over on the right-hand side are discharged last —
   after step 3, so that they mention no leftover metavariable.

Unmatched pure assertions of the left-hand side may be discarded; unmatched
spatial assertions are reported as an error.

When the right-hand side is of the shape `H ∗ ?F` for an unassigned
metavariable `?F` (frame inference, as generated by `step`), steps 1 and 2 are
skipped: the residual resources have to end up in the frame rather than in the
local context.

`sl_frame by tac` uses `tac` instead of the default chain to discharge the pure
side-goals of step 4.  Lean's `sym => …` symbolic-simulation mode is a good
choice when the default chain is too slow or too unpredictable, since it makes
the normalization explicit instead of relying on backtracking:

```
register_sym_simp slPure where
  post := ground >> rewrite [headPtr_nil, lastPtr_nil, headPtr_cons,
    lastPtr_singleton, lastPtr_snoc] with self

example … := by
  sl_frame by sym => first ((simp slPure); finish) (simp slPure) (finish)
```
-/
syntax (name := slFrame) "sl_frame" (" by " tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| sl_frame $[by $tac?]?) => Tactic.focus do withMainContext do
  let discharger : Option Syntax.Tactic := tac?.map fun tac => ⟨tac.raw⟩
  let localAsms :=
    (← (← getLCtx).getAssumptions).map LocalDecl.fvarId |>.toArray
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { hypsToUse := localAsms,
      -- `step` states its postcondition goals through `SLPost.Decomp`.
      declsToUnfold := #[``SLPost.Decomp.pure, ``SLPost.Decomp.spatial] }
    (.targets #[] true)
  if !(← getGoals).isEmpty then
    let goal ← getMainGoal
    SLFrame.solveGoal discharger goal
    replaceMainGoal []

/-- One step of `sl_pull`: peel a quantifier or a pure fact off the precondition
of a triple.  Fails when the precondition is purely spatial.

The precondition is unfolded (`wellFormed`, `isList`, …) only as far as needed to
expose its head connective: applying `triple_hexists` or `triple_hpure` blindly
would let the unifier see through `hstar`/`hpure` down to the raw heap predicate
and peel a quantifier of the *model* instead. -/
elab "sl_pull_step" : tactic => withMainContext do
  /- Float the existentials out of the separating conjunctions and drop the
     `emp`s left behind by previous steps, so that the head connective of the
     precondition is the one we want to peel. -/
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``hstar_hexists_l_eq, ``hstar_hexists_r_eq,
          ``hstar_hempty_l_eq, ``hstar_hempty_r_eq] }
    (.targets #[] true)
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``triple && args.size = 4 do
    throwError "sl_pull_step: the goal is not a separation-logic triple"
  let precondition ← SLFrame.exposeConnective args[1]!
  let head := precondition.consumeMData.getAppFn
  let leadingPure ←
    if precondition.consumeMData.isAppOfArity ``hstar 2 then
      pure ((← SLFrame.exposeConnective precondition.consumeMData.appFn!.appArg!)
        |>.consumeMData.isAppOfArity ``hpure 1)
    else pure false
  let lemmaName ←
    if head.isConstOf ``hexists then pure ``triple_hexists
    else if head.isConstOf ``hpure then pure ``triple_hpure'
    else if leadingPure then pure ``triple_hpure
    else
      throwError "sl_pull_step: the precondition has no quantifier or pure fact \
        left to extract:\n{precondition}"
  let goal ← goal.change (← mkAppOptM ``triple #[args[0]!, precondition, args[2]!, args[3]!])
  replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels lemmaName))

/-- SLF's `xpull`, for triples: move the existentials and the pure facts of the
precondition into the local context.

`sl_pull` peels as many of them as it can, using inaccessible names.
`sl_pull p₁ ... pₙ` peels exactly `n` of them, destructuring the `i`-th one with
the `rintro` pattern `pᵢ`, e.g. `sl_pull l rfl` or `sl_pull ⟨hhead, htail⟩`. -/
syntax (name := slPull) "sl_pull" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| sl_pull $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (sl_pull_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (sl_pull_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

end Aeneas.SLPoC
