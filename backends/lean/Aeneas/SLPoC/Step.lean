import Aeneas.SLPoC.SLTactics
import Aeneas.Tactic.Step.StepStar

/-!
# Wiring of the `step` tactic to separation-logic triples

`step`/`step*` walk a monadic program one call at a time.  For every call they
apply one of the two rules below and hand the resulting entailment to the
tactic given after `by` — in practice `sl_frame`.  Registered `pure.spec` and
`ok.spec` calls therefore use the same bind and ramified-frame automation as
other registered specifications.  `sl_pure` is the direct rule for a syntactic
terminal return when its entailment should be proved explicitly.
-/

namespace Aeneas.SLPoC

open Lean Elab Meta Tactic
open scoped SepLogic

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

/-- Rule used by `step` for a terminal monadic call: SLF's ramified frame rule.

Unlike the bind rule above it mentions no frame at all.  The leftover resources
are whatever `sl_frame` fails to cancel against `Pm`, and the wand says what they
have to achieve together with the callee's postcondition — so there is a single
obligation, with nothing left to guess.  In particular `sl_frame` is then free to
introduce the existentials and the pure facts of `P` (SLF's `xpull`), which it
must not do when a frame metavariable is in play. -/
theorem triple_step_mono {α : Type} {P Pm : SLPre} {Q : SLPost α}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ (Q ∗+ GC))) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-- `step` with `sl_frame` as the precondition discharger.

The frame has to be resolved *before* `step` reshapes the continuation, hence
`by sl_frame` rather than a `sl_frame` afterwards.  The rule for a terminal call
has a single premise, which is the *main* goal rather than a precondition and so
is out of reach of `by`; the trailing `sl_frame?` closes it, and `sl_side?` the
side conditions of the specification. -/
syntax "sl_step" Lean.Parser.Tactic.optConfig ("with" term)?
  ("as" " ⟨ " Lean.binderIdent,* " ⟩")? : tactic

/-- Normalize only beta/iota/zeta/projection redexes, then apply `triple_pure`
when the program in the goal is syntactically a terminal return.  The resulting
entailment is left exposed.  In particular this does not unfold a named pure
wrapper and bypass its registered specification. -/
syntax "sl_pure" : tactic

syntax "sl_pure_core" : tactic

elab_rules : tactic
  | `(tactic| sl_pure_core) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let (head, args) := target.consumeMData.withApp fun head args => (head, args)
      unless head.isConstOf ``triple && args.size = 4 do
        throwError "sl_pure expected a separation-logic triple"
      let program := args[2]!.consumeMData
      let programHead := program.getAppFn
      unless programHead.isConstOf ``Pure.pure ||
          programHead.isConstOf ``FFree.ok do
        throwError "sl_pure expected a syntactic terminal return"
      evalTactic (← `(tactic| apply triple_pure))

macro_rules
  | `(tactic| sl_pure) =>
    `(tactic| focus ((try simp only); sl_pure_core))

/-- Discharge a side condition `step` returns for a `Prop` argument of a
specification.  A no-op on the entailment and continuation goals, and on the
goals for ghost parameters the entailment has yet to determine.

The chain is `assumption`, `simp`, `omega`, `scalar_tac`, `grind`, and obeys the
same `aeneas.step.*` options as `step`, so `sl_step -grind` drops the last one.
`grind` is needed because a side condition such as an iterator's `valid` is often
available only behind a guard (`good = true → valid it' l`) whose discharge needs
a second hypothesis.

We do not reuse `step`'s own `agrind` (`evalAGrindWithPreprocess`): it fires the
`@[agrind]` lemma set rather than `@[grind]`, and preprocesses the hypotheses with
`scalar_tac`; both make it fail on the iterator side conditions. -/
syntax "sl_side?" Lean.Parser.Tactic.optConfig : tactic

elab_rules : tactic
  | `(tactic| sl_side? $cfg:optConfig) => withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let head := target.consumeMData.getAppFn
  if head.isConstOf ``himpl || head.isConstOf ``qimpl || head.isConstOf ``triple then
    return
  unless ← Meta.isProp target do return
  let config ← Aeneas.Step.elabPartialConfig cfg
  let mut alts : Array (TSyntax `tactic) := #[]
  if config.assumTac then alts := alts.push (← `(tactic| assumption))
  alts := alts.push (← `(tactic| simp))
  alts := alts.push (← `(tactic| omega))
  if config.scalarTac then alts := alts.push (← `(tactic| scalar_tac))
  if config.grind then alts := alts.push (← `(tactic| grind))
  /- `firstTacSolve` is what `step` uses for its own chain: it moves on unless the
     alternative leaves no goal behind. Splicing a `first` instead breaks `sl_frame`. -/
  try Aeneas.Utils.firstTacSolve (alts.toList.map fun tac => evalTactic tac)
  catch _ => pure ()

macro_rules
  | `(tactic| sl_step $cfg:optConfig $[with $th]? $[as ⟨ $ids,* ⟩]?) =>
    `(tactic| (sl_pull_keep <;>
      ((step $cfg:optConfig $[with $th]? $[as ⟨ $ids,* ⟩]? by sl_frame) <;>
      (sl_frame? <;> sl_side? $cfg:optConfig))))

/-- `step*` with `sl_frame` as the precondition discharger. -/
syntax "sl_step" noWs "*" (num)? Lean.Parser.Tactic.optConfig : tactic

macro_rules
  | `(tactic| sl_step* $[$n]? $cfg:optConfig) =>
    `(tactic| (sl_pull_keep <;>
      ((step* $[$n]? $cfg:optConfig by sl_frame) <;>
      (sl_frame? <;> sl_side? $cfg:optConfig))))

/-! ## Lemmas registered in the elimination passes of `step` -/

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

theorem triple_hexists_iff {α : Type} {ι : Sort _} {J : ι → SLPre} {m : St α}
    {Q : SLPost α} :
    triple iprop(∃ x, J x) m Q ↔ ∀ x, triple (J x) m Q := by
  constructor
  · intro hTriple x
    exact triple_conseq hTriple (himpl_hexists_r x (himpl_refl _))
      (fun _ => himpl_refl _)
  · exact triple_hexists

theorem triple_hpure_iff {α : Type} {P : Prop} {H : SLPre} {m : St α}
    {Q : SLPost α} :
    triple iprop(⌜P⌝ ∗ H) m Q ↔ (P → triple H m Q) := by
  constructor
  · intro hTriple hP
    refine triple_conseq hTriple ?_ (fun _ => himpl_refl _)
    intro h hH
    exact (hstar_hpure_l P H h).mpr ⟨hP, hH⟩
  · exact triple_hpure

theorem triple_hpure'_iff {α : Type} {P : Prop} {m : St α} {Q : SLPost α} :
    triple ⌜P⌝ m Q ↔ (P → triple emp m Q) := by
  rw [show (⌜P⌝ : SLPre) = iprop(⌜P⌝ ∗ emp) from (hstar_hempty_r_eq _).symm,
    triple_hpure_iff]

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_mono_preconditions := 0
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 7
    mk_spec_bind_preconditions := 2
    -- Eliminate the binder of an output the specification determines, and of a `Unit` output.
    uncurry_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``forall_unit, ``true_imp_iff
    ]
    -- `sl_pull` the continuation's precondition: quantifiers and pure facts become
    -- binders and hypotheses.
    qimp_elim_tactics := #[
      ``hstar_hempty_l_eq, ``hstar_hempty_r_eq,
      ``hstar_hexists_l_eq, ``hstar_hexists_r_eq, ``hstar_assoc_eq,
      ``triple_hexists_iff, ``triple_hpure_iff, ``triple_hpure'_iff,
      ``forall_unit, ``true_imp_iff
    ]
    to_mvcgen := none
    -- Liftings convert between differently stated registered specifications;
    -- they do not provide a terminal rule for `triple`.
    liftings := #[]
  }

attribute [step]
  ok.spec pure.spec
  alloc.spec read.spec update.spec free.spec
  mut_to_raw.spec end_mut_to_raw.spec

end Aeneas.SLPoC
