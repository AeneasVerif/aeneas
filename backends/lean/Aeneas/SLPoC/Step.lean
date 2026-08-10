import Aeneas.SLPoC.SLTactics
import Aeneas.Tactic.Step.StepStar

/-!
# Wiring of the `step` tactic to separation-logic triples

`step`/`step*` walk a monadic program one call at a time.  For every call they
apply one of the two rules below and hand the resulting entailment to the
tactic given after `by` — in practice `sl_frame`.
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
    (hRamified : P ⊢ Pm ∗ (Qm -∗∗ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-- `step`, followed by `sl_frame` on the goals it produces.

Because the rule for a terminal call has a single premise, that premise is the
*main* goal rather than a precondition, so `step`'s `by` tactic — which only
applies to preconditions — does not discharge it (the same convention as
`Std.WP.spec_mono'`).  `sl_step` closes it.  Ghost parameters of the
specification that the entailment has yet to determine also show up as goals
before it; `sl_frame?` skips those instead of swallowing every failure.

`<;>` (rather than `all_goals`) keeps this from reaching the goals that were
already open when `sl_step` was called. -/
macro "sl_step" args:Aeneas.Step.stepArgs : tactic =>
  `(tactic| (step $args:stepArgs <;> sl_frame?))

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
    liftings := #[] -- TODO: lift from Pure to SLProp
  }

attribute [step]
  ok.spec pure.spec
  alloc.spec read.spec update.spec free.spec
  mut_to_raw.spec end_mut_to_raw.spec

end Aeneas.SLPoC
