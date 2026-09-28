module
public import Aeneas.Data.Coinductive.Effect

public section

namespace Aeneas.Data.Coinductive

universe u u' v w

structure EffectWP (E : Effect.{v}) where
  State : Type u -- the state threaded through effects
  wp : (event : E.I) → (E.O event → State → Prop) → (State → Prop)

variable {E : Effect.{v}} {α : Type u} {θ : EffectWP.{w, v} E}

abbrev EffectWP.Pre (θ : EffectWP E) := θ.State → Prop

abbrev EffectWP.Post (θ : EffectWP E) (α : Type u) := α → θ.State → Prop

@[expose] def entails (P P' : θ.Post α) : Prop :=
  ∀ r s, P r s → P' r s

namespace EffectWP

class Monotone (θ : EffectWP E) : Prop where
  wp_mono :
    ∀ {event : E.I} {C C' : E.O event → θ.State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      ∀ {s : θ.State}, θ.wp event C s → θ.wp event C' s

class Conjunctive (θ : EffectWP E) : Prop where
  /- Reading: if `m {C₁} ∧ m {C₂} ∧ … `, then `m {fun a s' => C₁ a s' ∧ C₂ a s' ∧ … } -/
  wp_conj :
    ∀ {event : E.I} {s : θ.State} (Demands : (E.O event → θ.State → Prop) → Prop),
      (∃ C, Demands C) → (∀ C, Demands C → θ.wp event C s) →
      θ.wp event (fun answer s' => ∀ C, Demands C → C answer s') s

class NoMiracle (θ : EffectWP E) : Prop where
  wp_noMiracle : ∀ (event : E.I) (s : θ.State), ¬ θ.wp event (fun _ _ => False) s

export Monotone (wp_mono)
export Conjunctive (wp_conj)
export NoMiracle (wp_noMiracle)

end EffectWP

theorem EffectWP.wp_forall [θ.Monotone] [θ.Conjunctive] {ι : Sort u'}
    {C : ι → θ.Post (E.O event)} (i₀ : ι) (hWp : ∀ i, θ.wp event (C i) s) :
    θ.wp event (fun answer s' => ∀ i, C i answer s') s := by
  refine θ.wp_mono (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (θ.wp_conj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hWp i

end Aeneas.Data.Coinductive

end
