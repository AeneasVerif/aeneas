module
public import Aeneas.Data.Coinductive.Effect

public section

namespace Aeneas.Data.Coinductive

universe u u' v w

structure EffectWP (E : Effect.{v}) where
  State : Type u -- the state threaded through effects
  wp : (effect : E.I) → (E.O effect → State → Prop) → (State → Prop)

variable {E : Effect.{v}} {α : Type u} {θ : EffectWP.{w, v} E}

abbrev EffectWP.Pre (θ : EffectWP E) := θ.State → Prop

abbrev EffectWP.Post (θ : EffectWP E) (α : Type u) := α → θ.State → Prop

@[expose] def entails (P P' : θ.Post α) : Prop :=
  ∀ r s, P r s → P' r s

namespace EffectWP

class Monotone (θ : EffectWP E) : Prop where
  wp_mono :
    ∀ {effect : E.I} {C C' : E.O effect → θ.State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      ∀ {s : θ.State}, θ.wp effect C s → θ.wp effect C' s

class Conjunctive (θ : EffectWP E) : Prop where
  /- Reading: if `m {C₁} ∧ m {C₂} ∧ … `, then `m {fun a s' => C₁ a s' ∧ C₂ a s' ∧ … } -/
  wp_conj :
    ∀ {effect : E.I} {s : θ.State} (Demands : (E.O effect → θ.State → Prop) → Prop),
      (∃ C, Demands C) → (∀ C, Demands C → θ.wp effect C s) →
      θ.wp effect (fun answer s' => ∀ C, Demands C → C answer s') s

class NoMiracle (θ : EffectWP E) : Prop where
  wp_noMiracle : ∀ (effect : E.I) (s : θ.State), ¬ θ.wp effect (fun _ _ => False) s

export Monotone (wp_mono)
export Conjunctive (wp_conj)
export NoMiracle (wp_noMiracle)

end EffectWP

theorem EffectWP.wp_forall [θ.Monotone] [θ.Conjunctive] {ι : Sort u'}
    {C : ι → θ.Post (E.O effect)} (i₀ : ι) (hWp : ∀ i, θ.wp effect (C i) s) :
    θ.wp effect (fun answer s' => ∀ i, C i answer s') s := by
  refine θ.wp_mono (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (θ.wp_conj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hWp i

theorem EffectWP.wp_and [θ.Monotone] [θ.Conjunctive]
    {C₁ C₂ : θ.Post (E.O effect)} (h₁ : θ.wp effect C₁ s) (h₂ : θ.wp effect C₂ s) :
    θ.wp effect (fun answer s' => C₁ answer s' ∧ C₂ answer s') s := by
  refine θ.wp_mono (fun _ _ hAll => ⟨hAll C₁ (.inl rfl), hAll C₂ (.inr rfl)⟩)
    (θ.wp_conj (fun X => X = C₁ ∨ X = C₂) ⟨C₁, .inl rfl⟩ ?_)
  rintro X (rfl | rfl)
  · exact h₁
  · exact h₂

end Aeneas.Data.Coinductive

end
