module

public import Aeneas.Std.Heap.Notation
public import Aeneas.Tactic.Step

public section

namespace Aeneas.Std.HeapWP

open SepLogic

/-- Pure specifications preserve every owned fragment, including on accepted OOM. -/
theorem Triple.of_spec {c : Result α} {Q : α → Prop} {P : Assertion}
    (hc : WP.spec c Q) :
    Triple P c (fun result h => Q result ∧ P h) := by
  intro h F s₀ hp hd hm hi
  apply Spec.mono (Spec.of_spec hc s₀)
  rintro result s₁ ⟨hq, rfl⟩
  exact ⟨h, hd, hm, hi, hq, hp⟩

theorem Triple.step_mono {P Pm : Assertion} {Q : α → Assertion}
    (c : Result α) (Qm : α → Assertion) (hc : Triple Pm c Qm)
    (hpre : ∀ h, P h → Pm h)
    (hpost : ∀ result h, Qm result h → Q result h) :
    Triple P c Q :=
  Triple.conseq hpre hpost hc

/- A snapshot is an equality of owned fragments, not of global heaps. The
   continuation must still work with every compatible external frame. -/
theorem Triple.step_bind {P Pm : Assertion} {next : α → Result β}
    {Q : β → Assertion}
    (c : Result α) (Qm : α → Assertion) (hc : Triple Pm c Qm)
    (hpre : ∀ h, P h → Pm h)
    (hnext : ∀ result h, Qm result h →
      Triple (fun h' => h' = h) (next result) Q) :
    Triple P (Aeneas.Std.bind c next) Q := by
  apply Triple.bind (Triple.conseq hpre (fun _ _ hp => hp) hc)
  intro result h F s₀ hp hd hm hi
  exact hnext result h hp h F s₀ rfl hd hm hi

open Lean Meta Elab Tactic in
meta def prepareIntroOutputs : Aeneas.PrepareIntroOutputs := do
  withMainContext do
    let type ← instantiateMVars (← getMainTarget)
    Aeneas.Step.prepareIntroOutputsWith type (.leaf none) do
      let _ ← Aeneas.Simp.simpAt true { failIfUnchanged := false }
        { simpThms := #[← Aeneas.Step.stepSimpExt.getTheorems],
          addSimpThms := #[``true_imp_iff, ``Prod.forall,
            ``Aeneas.Step.forall_punit, ``and_imp, ``Aeneas.Step.exists_imp_named] }
        (.targets #[] true)

open Lean Elab Tactic in
meta def discharge : Aeneas.DischargeTactic := do
  evalTactic (← `(tactic|
    first
    | exact fun _ hp => hp
    | (rintro h rfl; assumption)))

#register_spec_info {
  spec_name := ``Triple
  arity := 4
  program_index := 2
  post_index := 3
  mk_spec_mono := ``Triple.step_mono
  mk_spec_mono_skip_args := 4
  mk_spec_bind := ``Triple.step_bind
  mk_spec_bind_skip_args := 6
  prepare_intro_outputs := ``prepareIntroOutputs
  discharge_tactic := some ``discharge
  to_mvcgen := none
  liftings := #[
    { from_statement := ``WP.spec
      conversion_thm := ``Triple.of_spec
      conversion_thm_inferred_args := 4 }
  ]
}

attribute [step] Triple.pure

end Aeneas.Std.HeapWP
