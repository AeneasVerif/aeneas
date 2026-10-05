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

-- EffectWP      : (effect : E.I) →          (E.O effect → State → Prop) → (State → Prop)
-- FunctionalWP  : (X : ITree E α -> Prop) → (E.O effect → State → Prop) → (ITree E α → Prop)

/-- `FunctionalWP` is a "one-step" weakest-precondition for ITrees,
    built from the WP of individual effects (`EffectWP`).

Given a candidate WP `X` for the continuations, `FunctionalWP allowDivergence θ Q X m s`
describes what must hold for `m` in state `s` by inspecting only its head constructor:
- `ret value`: the postcondition `Q value s` must hold;
- `div`: holds iff `allowDivergence` (i.e., whether divergence is acceptable);
- `vis effect k`: the effect WP `θ.wp effect` must guarantee that, for every answer and
  resulting state, `X` holds on the continuation `k answer`.

This functional is monotone in `X`, so it has least and greatest fixed points: the least
fixed point with `allowDivergence := False` is `DWP` (total correctness), and the greatest
fixed point with `allowDivergence := True` is `DWLP` (partial correctness). -/
@[expose] def FunctionalWP (allowDivergence : Prop) (θ : EffectWP E) (Q : θ.Post α)
    (X : ITreePred θ α) : ITreePred θ α :=
  fun m s =>
    ITree.cases
      (motive := fun _ => Prop)
      (fun value => Q value s) -- ret case
      allowDivergence          -- div case
      (fun effect k => θ.wp effect (fun answer s' => X (k answer) s') s) -- vis caes
      m

theorem FunctionalWP.ret :
    FunctionalWP allowDivergence θ Q X (.ret value) s = Q value s := by
  simp only [FunctionalWP, ITree.cases.ret]

theorem FunctionalWP.div :
    FunctionalWP allowDivergence θ Q X (ITree.div : ITree E α) s = allowDivergence := by
  simp only [FunctionalWP, ITree.cases.div]

theorem FunctionalWP.vis :
    FunctionalWP allowDivergence θ Q X (.vis effect k) s =
      θ.wp effect (fun answer s' => X (k answer) s') s := by
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
  | vis effect k =>
      simp only [FunctionalWP.vis]
      exact θ.wp_mono fun answer s' => hX (k answer) s'

/-- `FunctionalWP` bundled as a monotone map (an order homomorphism `→o`) on the complete
lattice of ITree predicates. By packaging it this way, we can leverage Mathlib's generic
fixed-point library (`OrderHom.lfp`, `OrderHom.gfp`, Knaster–Tarski) to define `DWP` and
`DWLP` and obtain their (co)induction principles for free. -/
private def FunctionalWP.hom (allowDivergence : Prop) (θ : EffectWP E) [θ.Monotone] (Q : θ.Post α) :
    ITreePred θ α →o ITreePred θ α :=
  ⟨FunctionalWP allowDivergence θ Q, fun _ _ hX _ _ => FunctionalWP.mono id (fun _ _ => id) hX⟩

end Aeneas.Data.Coinductive

end
