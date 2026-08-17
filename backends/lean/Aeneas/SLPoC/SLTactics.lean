import Aeneas.SLPoC.ST
import AeneasMeta.Simp
import Lean.Meta.Tactic.AC

/-!
# Separation-logic tactics

A port of the tactic automation of *Software Foundations, Volume 6: Separation
Logic Foundations* (`https://softwarefoundations.cis.upenn.edu/slf-current/`).

| SLF | Here |
|---|---|
| `\-*` / `\--*` | `-∗` (`hwand`) / `-∗+` (`qwand`) |
| `triple_ramified_frame` | `triple_ramified_frame` |
| `xsimpl` | `sl_xsimpl` (also available as `sl_frame`) |
| `\GC` | `GC` (`hgc`) |
| `xpull` | `sl_xpull` on an entailment, `sl_pull` on a triple |
| `xchange` | `sl_xchange` |
| `xval` | `sl_xval` |
| `xapp` | `sl_xapp`, and the `step`/`step*` tactics |

The book's `xwp`/`wpgen`/`xlet`/`xseq`/`xif`/`xfun` have no counterpart: they
build a characteristic formula out of a deeply embedded program, whereas here the
programs are shallowly embedded monadic terms and `step` walks them directly.
-/

namespace Aeneas.SLPoC

open Lean Elab Meta Tactic
open scoped SepLogic

/-! ## The ramified frame rule

SLF prefers the ramified frame rule over the combination of the frame rule and
the rule of consequence, because the latter needs an explicit frame `H₂` shared
between *two* subgoals: when `xsimpl` introduces a variable while proving the
first one, `H₂` — created earlier — can no longer mention it.  The wand
internalizes "what the leftover resources must do to the callee's
postcondition", and the whole obligation becomes a single entailment in which
nothing is left to guess. -/

/-- SLF's `triple_ramified_frame`. -/
theorem triple_ramified_frame {α : Type} {P Pm : SLPre} {Q Qm : SLPost α}
    {m : St α} (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ (Qm -∗+ (Q ∗+ GC))) :
    triple P m Q :=
  triple_hgc_post
    (triple_conseq_frame hStep hPre (qwand_cancel Qm (Q ∗+ GC)))

/-- The ramified frame rule, for a call followed by a continuation.  Unlike
`triple_ramified_frame` this one still mentions the resources `F` that the
callee does not need: the precondition of the continuation has to be
*synthesized*, and there is nothing for the wand to be adjoint to. -/
theorem triple_ramified_bind {α β : Type} {P Pm F : SLPre} {Qm : SLPost α}
    {next : α → St β} {Q : SLPost β} {m : St α}
    (hStep : triple Pm m Qm) (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_bind (triple_conseq (triple_frame hStep F) hPre (fun _ => himpl_refl _))
    hNext

/-! ## Decomposing a postcondition

`step` needs to expose the pure part of a specification's postcondition as an
ordinary Lean hypothesis; `Decomp` is how it is found. -/

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

/-! ## The `xsimpl` engine

`sl_xsimpl` is a port of SLF's `xsimpl`; see its documentation below for the
phases it goes through. -/

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
    head.isConstOf ``hexists || head.isConstOf ``hempty ||
    -- `hwand` is *defined* as an existential; unfolding it would be a disaster.
    head.isConstOf ``hwand || head.isConstOf ``qwand || head.isConstOf ``hforall

/-- Is `e` a magic wand?  Returns whether it is a postcondition wand. -/
private def wand? (e : Expr) : Option Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``qwand 3 then some true
  else if e.isAppOfArity ``hwand 2 then some false
  else none

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

/-- Put the entailment of `goal` in the exposed form computed by `exposeAll`. -/
private def exposeGoal (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let exposed ← mkAppM ``himpl #[← exposeAll args[0]!, ← exposeAll args[1]!]
  if exposed == target then return goal
  try goal.change exposed catch _ => pure goal

/-- SLF's `xpull`: introduce the existentials of the left-hand side and move its
pure facts into the local context.  Returns the residual goal. -/
private partial def pullLeft (goal : MVarId) : TacticM MVarId := do
  /- In frame-inference mode the left-hand side must be preserved verbatim.  The
     decision has to be taken *before* `floatExists`, which could otherwise turn
     `Hcallee ∗ ?F` into `∃ x, Hcallee' x ∗ ?F` and hide the frame. -/
  if ← isFrameInference goal then return goal
  /- Re-expose and re-float at every step: extracting a pure fact or a quantifier
     may reveal a definition (`isList`, …) hiding the next one. -/
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``himpl && args.size = 2 do return goal
  let source ← reducePostApplication args[0]!
  let destination ← reducePostApplication args[1]!
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
private partial def instantiateRightExists (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then return goal
  let goal ← floatExists (← exposeGoal goal)
  if ← isFrameInference goal then return goal
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

mutual

/-- Prove `residual ⊢ wand` by the introduction rule of the wand, and hand the
resulting entailment back to `solveGoal`. -/
partial def proveWand (discharger : Option Syntax.Tactic)
    (residual wand : Expr) : TacticM Expr := do
  let some isPostcondition := wand? wand
    | throwError "expected a magic wand, got {wand}"
  let args := wand.consumeMData.getAppArgs
  let (lemmaName, premise) ←
    if isPostcondition then
      pure (``qwand_intro,
        ← mkAppM ``qimpl #[← mkAppM ``qstar #[args[1]!, residual], args[2]!])
    else
      pure (``hwand_intro,
        ← mkAppM ``himpl #[mkApp2 (mkConst ``hstar) args[0]! residual, args[1]!])
  let premiseGoal ← mkFreshExprSyntheticOpaqueMVar premise
  solveGoal discharger premiseGoal.mvarId!
  mkAppM lemmaName #[premiseGoal]

partial def solveHimpl (discharger : Option Syntax.Tactic) (goal : MVarId) :
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
    /- Cancellation phase.  A destination atom that cannot be cancelled must be
       pure — we record it and discharge it below, once every metavariable
       introduced for a right-hand-side existential has had a chance to be
       instantiated by unification — or a magic wand, which then absorbs
       everything the cancellation leaves over.  That is what the ramified frame
       rule puts on the right in place of a frame metavariable; there can be only
       one of them. -/
    let mut deferredPure : Array Expr := #[]
    let mut absorbing : Option (Expr × Bool) := none
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
      else if expected.consumeMData.isAppOfArity ``hpure 1 then
        deferredPure := deferredPure.push expected
      else if (wand? expected).isSome then
        /- Note that we get here only when the wand could *not* be cancelled
           against an identical one on the left. -/
        if absorbing.isSome then
          throwError "cannot handle more than one magic wand on the right-hand \
            side\ndestination: {destination}"
        absorbing := some (expected, true)
      else if expected.consumeMData.isConstOf ``hgc then
        if absorbing.isSome then
          throwError "cannot handle more than one absorbing assertion on the \
            right-hand side\ndestination: {destination}"
        absorbing := some (expected, false)
      else
        throwError "required spatial assertions are not present\
          \nsource: {source}\ndestination: {destination}\nmissing: {expected}"
    let mut generatedPure : Array (Expr × Expr) := #[]
    for expected in deferredPure do
      let proposition ← instantiateMVars expected.consumeMData.appArg!
      generatedPure := generatedPure.push (expected, ← provePure discharger proposition)
    let matchedAssertion := mkStar matched
    /- `sourceToMatched : source ⊢ matchedAssertion ∗ absorbed`, where `absorbed`
       is the wand if there is one (which then swallows the residual resources),
       and `emp` otherwise (the residual resources must then be discardable). -/
    let (matchedAssertion, sourceToMatched) ←
      match absorbing with
      | some (absorbingAtom, isWand) =>
        let residual := mkStar remaining
        let reordered := mkApp2 (mkConst ``hstar) matchedAssertion residual
        let reorderProof ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
        let residualToAbsorber ←
          if isWand then
            proveWand discharger residual absorbingAtom
          else
            mkAppM ``himpl_hgc_r #[residual]
        let absorbProof ← mkAppM ``hstar_mono
          #[← mkAppM ``himpl_refl #[matchedAssertion], residualToAbsorber]
        pure (mkApp2 (mkConst ``hstar) matchedAssertion absorbingAtom,
          ← mkAppM ``himpl_trans #[reorderProof, absorbProof])
      | none =>
        let discardedAtoms := remaining
        let proof ←
          if discardedAtoms.isEmpty then
            mkAppM ``himpl_of_eq #[← proveEqAC source matchedAssertion]
          else
            let discarded := mkStar discardedAtoms
            let reordered := mkApp2 (mkConst ``hstar) matchedAssertion discarded
            let reorderProof ← mkAppM ``himpl_of_eq #[← proveEqAC source reordered]
            let discardProof ← proveToEmp discardedAtoms
            let eliminateProof ← mkAppOptM ``hstar_elim_right
              #[some matchedAssertion, some discarded, some discardProof]
            mkAppM ``himpl_trans #[reorderProof, eliminateProof]
        pure (matchedAssertion, proof)
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

partial def solveGoal (discharger : Option Syntax.Tactic) (goal : MVarId) :
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
        /- Expose before decomposing again: `sl_simps` has no lemma for the
           representation predicates themselves (`wellFormed`, `isList`, …), so
           decomposing a folded assertion is a no-op. -/
        let goal ← exposeGoal goal
        let goal ← if decomposing then exposeGoal (← decompose goal) else pure goal
        solveHimpl discharger goal
      else
        let goal ← pullLeft goal
        let goal ← instantiateRightExists goal
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

/-- SLF's `xpull`, on an entailment: only the left-hand side is touched. -/
partial def pullGoal (goal : MVarId) : TacticM MVarId := do
  if ← isFrameInference goal then
    throwError "sl_xpull: this is a frame-inference goal.  Extracting anything \
      from its left-hand side would lose it from the frame, which was created in \
      an outer context; pull at the level of the triple instead, with `sl_pull`."
  let target ← instantiateMVars (← goal.getType)
  if target.consumeMData.isAppOfArity ``qimpl 3 then
    let (_, next) ← goal.intro1P
    pullLeft next
  else
    pullLeft goal

end

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

/-- `sl_frame`, but a no-op on a goal that is not a separation-logic entailment.

`step` hands back the ghost parameters it could not determine as extra goals; a
follow-up tactic has to skip those rather than swallow every failure with `try`,
which would also hide the diagnostics of a genuine `sl_frame` failure. -/
elab "sl_frame?" : tactic => withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let head := target.consumeMData.getAppFn
  if head.isConstOf ``himpl || head.isConstOf ``qimpl then
    evalTactic (← `(tactic| sl_frame))

/-- Normalize the separating conjunctions of the goal: float the existentials out of them, drop
the `emp`s, and reassociate to the right. -/
elab "sl_norm" : tactic => withMainContext do
  let _ ← Simp.simpAt true
    { dsimp := false, failIfUnchanged := false, maxDischargeDepth := 1 }
    { addSimpThms :=
        #[``hstar_hempty_l_eq, ``hstar_hempty_r_eq,
          ``hstar_hexists_l_eq, ``hstar_hexists_r_eq, ``hstar_assoc_eq] }
    (.targets #[] true)

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
          ``hstar_hempty_l_eq, ``hstar_hempty_r_eq],
      -- `step` states its continuation goals through `SLPost.Decomp`.
      declsToUnfold := #[``SLPost.Decomp.pure, ``SLPost.Decomp.spatial] }
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
the `rintro` pattern `pᵢ`, e.g. `sl_pull l rfl` or `sl_pull ⟨hhead, htail⟩`.

Pure facts are *removed* from the precondition, which is often not what a
subsequent `sl_step` needs; use `sl_pull_keep` (which `step` runs on the goal of
every continuation) when only the local hypothesis is wanted. -/
syntax (name := slPull) "sl_pull" (ppSpace colGt rintroPat)* : tactic

macro_rules
  | `(tactic| sl_pull $ps:rintroPat*) => do
    if ps.isEmpty then
      `(tactic| repeat (sl_pull_step; rintro _))
    else
      let steps ← ps.mapM fun p => `(tactic| (sl_pull_step; rintro $p:rintroPat))
      `(tactic| ($[$steps]*))

/-- Whether a quantifier or a pure fact can be peeled off `pre` without unfolding it: an opened
representation predicate is one the frame inference of a later `step` can no longer match. -/
private def isPullable (pre : Expr) : Bool :=
  let pre := pre.consumeMData
  if pre.isAppOfArity ``hexists 2 || pre.isAppOfArity ``hpure 1 then true
  else if pre.isAppOfArity ``hstar 2 then
    pre.appFn!.appArg!.consumeMData.isAppOfArity ``hpure 1
  else false

private partial def pullPrecondition (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``triple 4 && isPullable target.getAppArgs[1]! do return goal
  setGoals [goal]
  let state ← saveState
  try
    evalTactic (← `(tactic| sl_pull_step))
  catch _ =>
    state.restore
    return goal
  let (_, goal) ← (← getMainGoal).intro1P
  pullPrecondition goal

/-- `sl_pull` restricted to what the precondition exposes without being unfolded; see
`isPullable`. -/
elab "sl_pull_shallow" : tactic => withMainContext do
  setGoals [← pullPrecondition (← getMainGoal)]

/-- One step of `sl_pull_keep`: copy the leading pure fact of the precondition of
a triple into the local context, *without* removing it from the precondition.

`sl_pull_step` consumes the fact, which is what SLF's `xpull` does but is often
the wrong thing here: the assertion has to keep it for the framing of the later
steps (this is why `sl_pull` before a `sl_step` can turn a working proof into a
failing one).  Copying is always sound, and it is what makes the pointer of a
callee's precondition (`s.head.get!`, say) reducible to the one the assertion
owns.

Fails when the fact is already in the context, so that `repeat` terminates. -/
elab "sl_pull_keep_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  unless fn.isConstOf ``triple && args.size = 4 do
    throwError "sl_pull_keep_step: the goal is not a separation-logic triple"
  let precondition ← SLFrame.exposeConnective args[1]!
  unless precondition.consumeMData.isAppOfArity ``hstar 2 do
    throwError "sl_pull_keep_step: the precondition is not a separating conjunction"
  let leading ← SLFrame.exposeConnective precondition.consumeMData.appFn!.appArg!
  unless leading.consumeMData.isAppOfArity ``hpure 1 do
    throwError "sl_pull_keep_step: the precondition does not start with a pure fact"
  let proposition := leading.consumeMData.appArg!
  if ← (← getLCtx).anyM fun decl =>
      pure !decl.isImplementationDetail <&&> isDefEq decl.type proposition then
    throwError "sl_pull_keep_step: this pure fact is already in the context"
  let exposed := mkApp2 (mkConst ``hstar) leading precondition.consumeMData.appArg!
  let goal ← goal.change (← mkAppOptM ``triple #[args[0]!, exposed, args[2]!, args[3]!])
  let [next] ← goal.apply (← mkConstWithFreshMVarLevels ``triple_hpure_keep)
    | throwError "sl_pull_keep_step: unexpected number of goals"
  let (_, next) ← next.intro1P
  /- Put the precondition back in its original, folded form: only the local
     context should record that the step happened. -/
  replaceMainGoal
    [← next.change (← mkAppOptM ``triple #[args[0]!, args[1]!, args[2]!, args[3]!])]

/-- Copy the pure facts of the precondition of a triple into the local context,
leaving the precondition untouched.  See `sl_pull_keep_step`. -/
macro "sl_pull_keep" : tactic => `(tactic| repeat (sl_pull_keep_step; rename_i _))

/-- SLF's `xsimpl`.  `sl_frame` is the same tactic under the name that describes
what `step` uses it for. -/
syntax "sl_xsimpl" (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| sl_xsimpl) => `(tactic| sl_frame)
  | `(tactic| sl_xsimpl by $tac) => `(tactic| sl_frame by $tac)

/-- SLF's `xpull`, on an entailment `H₁ ⊢ H₂` or `Q₁ ⊢+ Q₂`: introduce the
existentials of the left-hand side and move its pure facts into the local
context, leaving the right-hand side alone.

Use it when the witness the right-hand side needs depends on a variable bound on
the left: `sl_xsimpl` would otherwise pick the metavariable for the right-hand
side *before* that variable exists.  This is SLF's canonical
`(∃ n, p ↦ n) ⊢ (∃ m, p ↦ (m + 1))` example. -/
elab "sl_xpull" : tactic => Tactic.focus do withMainContext do
  replaceMainGoal [← SLFrame.pullGoal (← getMainGoal)]

/-! ## `xchange` -/

/-- The rule behind `sl_xchange`: rewrite a part of the left-hand side of an
entailment with an entailment of its own. -/
theorem himpl_xchange {H₁ H₂ H₃ H₄ : SLProp} (hPart : H₁ ⊢ H₂)
    (hRest : H₂ ∗ H₃ ⊢ H₄) : H₁ ∗ H₃ ⊢ H₄ :=
  himpl_trans (hstar_mono hPart (himpl_refl H₃)) hRest

/-- The same, for the precondition of a triple. -/
theorem triple_xchange {α : Type} {H₁ H₂ H₃ : SLPre} {Q : SLPost α} {m : St α}
    (hPart : H₁ ⊢ H₂) (hRest : triple (H₂ ∗ H₃) m Q) : triple (H₁ ∗ H₃) m Q :=
  triple_conseq hRest (hstar_mono hPart (himpl_refl H₃)) (fun _ => himpl_refl _)

namespace SLFrame

/-- Rewrite the assertion `H` (the left-hand side of an entailment, or the
precondition of a triple) using `lemma : A ⊢ B` or `lemma : A = B`, replacing the
atom `A` of `H` by `B`.  Returns the rewritten assertion and a proof of
`H ⊢ rewritten`. -/
def xchangeAssertion (assertion : Expr) (rule : Expr) : TacticM (Expr × Expr) := do
  let ruleType ← instantiateMVars (← inferType rule)
  /- Accept both an entailment and an equality, in either direction for the
     latter (SLF's `xchange` does the same). -/
  let (lhs, rhs, entailment) ←
    if ruleType.consumeMData.isAppOfArity ``himpl 2 then
      let args := ruleType.consumeMData.getAppArgs
      pure (args[0]!, args[1]!, rule)
    else if let some (_, lhs, rhs) := ruleType.consumeMData.eq? then
      pure (lhs, rhs, ← mkAppM ``himpl_of_eq #[rule])
    else
      throwError "sl_xchange expects an entailment `A ⊢ B` or an equality \
        `A = B`, got {ruleType}"
  let atoms ← flatten assertion
  /- The rewritten part may be a separating conjunction of several atoms, which
     do not have to be adjacent in `assertion`. -/
  let some restAtoms ← removeMatches atoms (← flatten lhs)
    | throwError "sl_xchange: {lhs}\nis not part of\n{assertion}"
  let rest := mkStar restAtoms
  let reordered := mkApp2 (mkConst ``hstar) (← instantiateMVars lhs) rest
  let reorder ← mkAppM ``himpl_of_eq #[← proveEqAC assertion reordered]
  let rewritten := mkApp2 (mkConst ``hstar) (← instantiateMVars rhs) rest
  let change ← mkAppM ``hstar_mono #[entailment, ← mkAppM ``himpl_refl #[rest]]
  return (rewritten, ← mkAppM ``himpl_trans #[reorder, change])

end SLFrame

/-- SLF's `xchange`: rewrite part of the current resources with an entailment.

`sl_xchange M`, for `M : A ⊢ B` (or `M : A = B`), replaces the assertion `A` by
`B` in the left-hand side of the entailment, or in the precondition of the
triple, that the goal states.  This is how a representation predicate is opened
or closed when plain cancellation cannot see through it.

Unlike `rw`, `M` need not be an equality and `A` need not occur syntactically:
it only has to be one of the `∗`-separated atoms, up to unification. -/
elab "sl_xchange" rule:term : tactic => Tactic.focus do withMainContext do
  let rule ← Tactic.elabTerm rule none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (fn, args) := target.consumeMData.withApp fun fn args => (fn, args)
  if fn.isConstOf ``himpl && args.size = 2 then
    let (rewritten, proof) ← SLFrame.xchangeAssertion args[0]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``himpl #[rewritten, args[1]!])
    goal.assign (← mkAppM ``himpl_trans #[proof, next])
    replaceMainGoal [next.mvarId!]
  else if fn.isConstOf ``triple && args.size = 4 then
    let (rewritten, proof) ← SLFrame.xchangeAssertion args[1]! rule
    let next ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppOptM ``triple #[args[0]!, rewritten, args[2]!, args[3]!])
    let qrefl ← withLocalDeclD `value args[0]! fun value => do
      mkLambdaFVars #[value] (← mkAppM ``himpl_refl #[mkApp args[3]! value])
    goal.assign (← mkAppM ``triple_conseq #[next, proof, qrefl])
    replaceMainGoal [next.mvarId!]
  else
    throwError "sl_xchange expects an entailment or a triple, got\n{target}"

/-! ## `xval` and `xapp` -/

/-- SLF's `xval`: reduce a triple about a terminal `pure v` to the entailment
`P ⊢ Q v`. -/
macro "sl_xval" : tactic => `(tactic| apply triple_pure)

/-- SLF's `xapp`: apply a specification to the goal, framing the resources it
does not need through the ramified frame rule, and discharge the resulting
entailment with `sl_xsimpl`.

`sl_xapp thm` handles a terminal call; use `step with thm` for a call followed by
a continuation. -/
syntax "sl_xapp" (ppSpace colGt term)? (" by " tacticSeq)? : tactic

macro_rules
  | `(tactic| sl_xapp $[$thm?]? $[by $tac?]?) => do
    let apply ←
      match thm? with
      | some thm => `(tactic| refine triple_ramified_frame $thm ?_)
      | none => `(tactic| refine triple_ramified_frame (by assumption) ?_)
    match tac? with
    | none => `(tactic| ($apply; sl_xsimpl))
    | some tac => `(tactic| ($apply; sl_xsimpl by $tac))

/-- Re-state an already-proved triple under a weaker (usually more abstract)
postcondition: `sl_conseq thm` keeps the precondition as is and discharges the
new postcondition with `sl_frame` for every result value. -/
macro "sl_conseq " thm:term : tactic =>
  `(tactic| (apply triple_conseq $thm (himpl_refl _) <;> (intro _ <;> sl_frame)))

end Aeneas.SLPoC
