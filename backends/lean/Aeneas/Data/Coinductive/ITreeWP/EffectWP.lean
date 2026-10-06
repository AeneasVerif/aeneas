module
public import Aeneas.Data.Coinductive.Effect

/-!
# Weakest preconditions for effects

This file defines `EffectWP`, the basic building block of our generic weakest precondition (WP)
calculus for ITrees. An `EffectWP E` specifies, for every effect of `E`, how this effect
behaves in terms of a WP.
-/

public section

namespace Aeneas.Data.Coinductive

universe u u' v w

/-- The weakest precondition of the effects in `E`.

`wp effect C s` holds if performing `effect` in state `s` is guaranteed to produce an answer
and a new state satisfying `C`. -/
structure EffectWP (E : Effect.{v}) where
  State : Type u -- the state threaded through effects
  wp : (effect : E.I) → (E.O effect → State → Prop) → (State → Prop)

variable {E : Effect.{v}} {α : Type u} {θ : EffectWP.{w, v} E}

abbrev EffectWP.Pre (θ : EffectWP E) := θ.State → Prop

abbrev EffectWP.Post (θ : EffectWP E) (α : Type u) := α → θ.State → Prop

/-- Pointwise implication between postconditions. -/
@[expose] def entails (P P' : θ.Post α) : Prop :=
  ∀ r s, P r s → P' r s

namespace EffectWP

/-!
The following classes correspond to Dijkstra's original healthiness conditions for weakest
preconditions ("A Discipline of Programming", 1976): monotonicity, conjunctivity, and the Law of
the Excluded Miracle. Our `Conjunctive` generalizes Dijkstra's binary conjunctivity to arbitrary
non-empty families of postconditions.
-/

/-- The WP of every effect is monotone in its postcondition.
    This is needed to compute the fixed points of `FunctionalWP`. -/
class Monotonic (θ : EffectWP E) : Prop where
  wp_monotonic :
    ∀ {effect : E.I} {C C' : E.O effect → θ.State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      ∀ {s : θ.State}, θ.wp effect C s → θ.wp effect C' s

/-- The WP of every effect distributes over (non-empty) conjunctions of postconditions.
    Necessary for defining total and partial correctness, which require a demonic interpretation. -/
class Conjunctive (θ : EffectWP E) : Prop where
  /- Reading: if `m {C₁} ∧ m {C₂} ∧ … `, then `m {fun a s' => C₁ a s' ∧ C₂ a s' ∧ … } -/
  wp_conj :
    ∀ {effect : E.I} {s : θ.State} (Demands : (E.O effect → θ.State → Prop) → Prop),
      (∃ C, Demands C) → (∀ C, Demands C → θ.wp effect C s) →
      θ.wp effect (fun answer s' => ∀ C, Demands C → C answer s') s

/-- No effect can guarantee the unsatisfiable postcondition `False`.
    Necessary property of θ for total correctness. -/
class ExcludedMiracle (θ : EffectWP E) : Prop where
  wp_excludedMiracle : ∀ (effect : E.I) (s : θ.State), ¬ θ.wp effect (fun _ _ => False) s

export Monotonic (wp_monotonic)
export Conjunctive (wp_conj)
export ExcludedMiracle (wp_excludedMiracle)

end EffectWP

theorem EffectWP.wp_forall [θ.Monotonic] [θ.Conjunctive] {ι : Sort u'}
    {C : ι → θ.Post (E.O effect)} (i₀ : ι) (hWp : ∀ i, θ.wp effect (C i) s) :
    θ.wp effect (fun answer s' => ∀ i, C i answer s') s := by
  refine θ.wp_monotonic (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (θ.wp_conj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hWp i

end Aeneas.Data.Coinductive

end
