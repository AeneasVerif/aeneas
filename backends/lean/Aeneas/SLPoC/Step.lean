import Aeneas.SLPoC.SLTactics
import Aeneas.Tactic.Step.StepStar

/-!
# Wiring of the `step` tactic to separation-logic triples

`step`/`step*` walk a monadic program one call at a time.  For every call they
apply one of the two rules below and hand the resulting entailment to `sl_frame`,
which is registered as the `discharge_tactic` of the `triple` specification
statement.  Registered `pure.spec` and `ok.spec` calls therefore use the same bind
and ramified-frame automation as other registered specifications, terminal returns
included: `himpl_qwand_hpure_eq` collapses the wand their abstract result leaves
behind, so no separate rule is needed for them.
-/

namespace Aeneas.SLPoC

open Lean Elab Meta Tactic
open scoped SepLogic

/-- Bind rule used by `step`. It infers a spatial frame and leaves the callee's
postcondition, framed, as the precondition of the continuation. -/
theorem triple_step_bind {α β : Type} {P Pm F : SLPre}
    {next : α → St β} {Q : SLPost β}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    (hPre : P ⊢ Pm ∗ F)
    (hNext : ∀ value, triple (Qm value ∗ F) (next value) Q) :
    triple P (m >>= next) Q :=
  triple_ramified_bind hStep hPre hNext

/-- Rule used by `step` for a terminal monadic call: SLF's ramified frame rule.

Unlike the bind rule above it mentions no frame at all.  The leftover resources
are whatever `sl_frame` fails to cancel against `Pm`, and the wand says what they
have to achieve together with the callee's postcondition — so there is a single
obligation, with nothing left to guess.  In particular `sl_frame` is then free to
introduce the existentials and the pure facts of `P` (SLF's `xpull`), which it
must not do when a frame metavariable is in play. -/
theorem triple_step_mono {α : Type} {P Pm : SLPre} {Q : SLPost α}
    (m : St α) (Qm : SLPost α) (hStep : triple Pm m Qm)
    (hRamified : P ⊢ Pm ∗ (Qm -∗+ Q)) :
    triple P m Q :=
  triple_ramified_frame hStep hRamified

/-! ## Elimination passes of `step` -/

theorem forall_unit {p : Unit → Prop} : (∀ value, p value) ↔ p () :=
  ⟨fun h => h (), fun h value => match value with | () => h⟩

/-- The tactic `step` runs on the goals it prepares. A no-op on a goal which is not a triple. -/
macro "intro_triple" : tactic =>
  `(tactic| (sl_norm; sl_pull_shallow))

#register_spec_info {
    spec_name := ``triple
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``triple_step_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``triple_step_bind
    mk_spec_bind_skip_args := 7
    -- Eliminate the binder of an output the specification determines, and of a `Unit` output.
    qimp_elim_tactics := #[
      ``forall_eq, ``forall_eq',
      ``forall_unit, ``true_imp_iff
    ]
    intro_tactic := SpecInfo.tac `(tactic| intro_triple)
    -- Frame inference: proves `hPre` of the bind rule and `hRamified` of the mono rule.
    discharge_tactic := SpecInfo.tac `(tactic| sl_frame)
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
