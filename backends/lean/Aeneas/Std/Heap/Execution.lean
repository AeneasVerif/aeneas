module

public import Aeneas.Std.Heap.Effects
import all Aeneas.Std.Primitives

@[expose] public section

namespace Aeneas.Std.HeapWP

/-- A finite successful execution of the actual Result computation.
    Each effect carries a witness for its relation; OOM, UB and divergence
    have no successful execution. This is separate from the universal WP. -/
inductive Runs : Result α → State → α → State → Prop where
  | pure (value : α) (s : State) : Runs (.ok value) s value s
  | modify {β : Type} {relation : State → β → State → Prop}
      {next : ULift β → Result α} {s₀ s₁ s₂ : State} {answer : β} {value : α}
      (transition : relation s₀ answer s₁)
      (rest : Runs (next ⟨answer⟩) s₁ value s₂) :
      Runs (.vis (.guardedModify β relation) next) s₀ value s₂

theorem Runs.bind {c : Result α} {next : α → Result β}
    (first : Runs c s₀ value s₁) (rest : Runs (next value) s₁ result s₂) :
    Runs (Std.bind c next) s₀ result s₂ := by
  induction first
  · simpa only [bind_ok] using rest
  · rename_i transition tail ih
    rw [bind_vis]
    exact Runs.modify transition (ih rest)

theorem Runs.checkedModify {relation : State → α → State → Prop}
    (transition : relation s₀ value s₁) :
    Runs (Result.checkedModify relation) s₀ value s₁ :=
  Runs.modify (answer := some value) transition (Runs.pure value s₁)

theorem Runs.allocatingModify {relation : State → α → State → Prop}
    (transition : relation s₀ value s₁) :
    Runs (Result.allocatingModify relation) s₀ value s₁ :=
  Runs.modify (answer := some value) transition (Runs.pure value s₁)

theorem Runs.guardedModify {relation : State → α → State → Prop}
    (transition : relation s₀ value s₁) :
    Runs (Result.guardedModify relation) s₀ value s₁ :=
  Runs.modify transition (Runs.pure value s₁)

unseal Result in
/-- A successful execution satisfies every universal correctness contract. -/
theorem Runs.post (run : Runs c s₀ value s₁) (correct : Spec c Q s₀) :
    Q value s₁ := by
  induction run
  · exact (Spec.pure _ _ _).mp correct
  · rename_i transition tail ih
    exact ih (Aeneas.Data.Coinductive.DWP.vis_view correct _ _ transition)

theorem Runs.not_oom : ¬ Runs (Result.oom : Result α) s₀ value s₁ :=
  fun run => run.post (Q := fun _ _ => False) Spec.oom

end Aeneas.Std.HeapWP
