module
public import Aeneas.Tactic.Step
public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.SpecParameters

/- A custom spec with an extra parameter that must be shared across binds. -/
@[irreducible] def paramSpec {α : Type} (tag : Nat) (x : Result α) (Q : α → Prop) : Prop :=
  tag = tag ∧ Std.WP.spec x Q

theorem paramSpec_mono' {α : Type} {tag : Nat} {P₁ : α → Prop} {m : Result α}
    {P₀ : α → Prop} (h : paramSpec tag m P₀) :
    Std.WP.qimp P₀ P₁ → paramSpec tag m P₁ := by
  intro hq
  unfold paramSpec at h ⊢
  exact ⟨rfl, Std.WP.spec_mono' h.2 hq⟩

def qimpParam {α β : Type} (tag : Nat) (Pₘ : α → Prop) (k : α → Result β)
    (Pₖ : β → Prop) : Prop :=
  ∀ x, Pₘ x → paramSpec tag (k x) Pₖ

theorem qimpParam_iff {α β : Type} (tag : Nat) (Pₘ : α → Prop)
    (k : α → Result β) (Pₖ : β → Prop) :
    qimpParam tag Pₘ k Pₖ ↔ ∀ x, Pₘ x → paramSpec tag (k x) Pₖ :=
  Iff.rfl

theorem paramSpec_bind' {α β : Type} {k : α → Result β} {Pₖ : β → Prop}
    {tag : Nat} {m : Result α} {Pₘ : α → Prop} :
    paramSpec tag m Pₘ →
    qimpParam tag Pₘ k Pₖ →
    paramSpec tag (Std.bind m k) Pₖ := by
  intro hm hk
  unfold paramSpec at hm ⊢
  refine ⟨rfl, Std.WP.spec_bind' hm.2 ?_⟩
  intro x hx
  have hk := hk x hx
  unfold paramSpec at hk
  exact hk.2

#register_spec_info {
    spec_name := ``paramSpec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``paramSpec_mono'
    mk_spec_mono_skip_args := 3
    mk_spec_bind := ``paramSpec_bind'
    mk_spec_bind_skip_args := 5
    uncurry_elim_tactics := #[
      ``Std.WP.qimp_spec_unit, ``Std.WP.qimp_unit,
      ``Std.WP.qimp_spec_exists, ``Std.WP.qimp_exists,
      ``Std.WP.forall_unit, ``true_imp_iff]
    qimp_elim_tactics := #[
      ``qimpParam_iff, ``Std.WP.qimp_iff,
      ``Std.WP.imp_and_iff, ``Std.uncurry_apply_pair,
      ``Std.WP.uncurry'_eq, ``Std.WP.uncurry'_pair,
      ``Std.WP.imp_exists_iff,
      ``Std.WP.forall_unit, ``true_imp_iff]
    to_mvcgen := none
    liftings := #[]
  }

def op (n : Nat) : Result Nat := ok n

@[step]
theorem op_spec (n tag : Nat) :
    paramSpec tag (op n) (fun r => r = n) := by
  simp [paramSpec, op, Std.WP.spec_ok]

def prog (a b : Nat) : Result Nat := do
  let x ← op a
  let y ← op b
  ok (x + y)

/- `step` must infer `tag` from the enclosing spec instead of exposing it as a goal. -/
example (a b tag : Nat) :
    paramSpec tag (prog a b) (fun r => r = a + b) := by
  unfold prog
  step with op_spec
  step with op_spec
  simp [paramSpec, Std.WP.spec_ok, *]

end Aeneas.Tactic.Step.Tests.SpecParameters
