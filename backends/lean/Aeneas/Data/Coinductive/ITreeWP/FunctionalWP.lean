module
public import Aeneas.Data.Coinductive.ITreeWP.EffectWP
public import Aeneas.Data.Coinductive.ITree
import Mathlib.Order.FixedPoints

public section

namespace Aeneas.Data.Coinductive

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {θ : EffectWP.{w, v} E}

local infix:50 " ≤ " => entails
private theorem entails_iff_le {P P' : θ.Post α} : entails P P' ↔ LE.le P P' := Iff.rfl


abbrev ITreePred (θ : EffectWP E) (α : Type u) := θ.Post (ITree E α)

private noncomputable instance ITreePred.instCompleteLattice : CompleteLattice (ITreePred θ α) :=
  inferInstanceAs (CompleteLattice (ITree E α → θ.State → Prop))

-- EffectWP      : (event : E.I) →           (E.O event → State → Prop) → (State → Prop)
-- FunctionalWP  : (X : ITree E α -> Prop) → (E.O event → State → Prop) → (ITree E α → Prop)

/-- Lift the WP of an event (`EffectWP`) to a WP for ITrees. -/
@[expose] def FunctionalWP (allowDivergence : Prop) (θ : EffectWP E) (Q : θ.Post α)
    (X : ITreePred θ α) : ITreePred θ α :=
  fun m s =>
    ITree.cases
      (motive := fun _ => Prop)
      (fun value => Q value s)
      allowDivergence
      (fun event k => θ.wp event (fun answer s' => X (k answer) s') s)
      m

theorem FunctionalWP.ret :
    FunctionalWP allowDivergence θ Q X (.ret value) s = Q value s := by
  simp only [FunctionalWP, ITree.cases.ret]

theorem FunctionalWP.div :
    FunctionalWP allowDivergence θ Q X (ITree.div : ITree E α) s = allowDivergence := by
  simp only [FunctionalWP, ITree.cases.div]

theorem FunctionalWP.vis :
    FunctionalWP allowDivergence θ Q X (.vis event k) s =
      θ.wp event (fun answer s' => X (k answer) s') s := by
  simp only [FunctionalWP, ITree.cases.vis]

theorem FunctionalWP.mono [θ.Monotone]
    (hDiv : allowDivergence → allowDivergence')
    (hQ : Q ≤ Q')
    (hX : X ≤ X') :
    FunctionalWP allowDivergence θ Q X m s ->
      FunctionalWP allowDivergence' θ Q' X' m s := by
  cases m using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, FunctionalWP.ret]
      exact hQ value s
  | div =>
      simp only [FunctionalWP.div]
      exact hDiv
  | vis event k =>
      simp only [FunctionalWP.vis]
      exact θ.wp_mono fun answer s' => hX (k answer) s'

/-- We plug into Mathlib's generic fixed-point library. -/
private def FunctionalWP.hom (allowDivergence : Prop) (θ : EffectWP E) [θ.Monotone] (Q : θ.Post α) :
    ITreePred θ α →o ITreePred θ α :=
  ⟨FunctionalWP allowDivergence θ Q, fun _ _ hX _ _ => FunctionalWP.mono id (fun _ _ => id) hX⟩

end Aeneas.Data.Coinductive

end
