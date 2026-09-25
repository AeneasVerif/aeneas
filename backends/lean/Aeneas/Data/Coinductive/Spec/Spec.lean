module
public import Aeneas.Data.Coinductive.ITree
import Mathlib.Order.FixedPoints

public section

/-!
 We define total and partial correctness for interaction trees
 from a monotone weakest precondition for events.

 We form a complete lattice (`ITreePred`) with a monotone function (`SpecF`),
 which allows us to define total (`TotalSpec`) and partial correctness (`PartialSpec`)
 as the least and the greatest fixpoints following Knaster–Tarski construction.
-/

namespace Aeneas.Data.Coinductive

universe u u' v w

/-! ## Effect specifications -/

/-- A specification of the effect `E`: a state, and for each event a weakest precondition which
    is *healthy* in Dijkstra's sense: monotone, conjunctive, and excluding miracles. -/
structure EffectSpec (E : Effect.{v}) where
  State : Type u -- the state threaded through events
  wp : (event : E.I) → (E.O event → State → Prop) → (State → Prop)
  /-- Monotonicity of wp. -/
  wp_mono :
    ∀ {event : E.I} {C C' : E.O event → State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      ∀ {s : State}, wp event C s → wp event C' s
  /-- Conjunctivity:  if `e {C₁} ∧ e {C₂} ∧ … `, then `e {fun a s' => C₁ a s' ∧ C₂ a s' ∧ … }`. -/
  wp_conj :
    ∀ {event : E.I} {s : State} (Demands : (E.O event → State → Prop) → Prop),
      (∃ C, Demands C) → (∀ C, Demands C → wp event C s) →
      wp event (fun answer s' => ∀ C, Demands C → C answer s') s
  /-- Excluded miracle: no event guarantees the `False` postcondition. Without it, total
      correctness would not imply termination. -/
  wp_noMiracle : ∀ (event : E.I) (s : State), ¬ wp event (fun _ _ => False) s

variable {E : Effect.{v}} {α : Type u} {S : EffectSpec.{w, v} E}

/-- A precondition: a predicate on the initial state. -/
abbrev EffectSpec.Pre (S : EffectSpec E) := S.State → Prop

/-- A postcondition: a predicate on a return value and the final state. -/
abbrev EffectSpec.Post (S : EffectSpec E) (α : Type u) := α → S.State → Prop

/-- A predicate on an interaction tree and the current state. -/
abbrev ITreePred (S : EffectSpec E) (α : Type u) := S.Post (ITree E α)

/-- Pointwise implication between postconditions (also used for `ITreePred`s, which are
    postconditions on trees). This is the order in which fixed points are taken. -/
@[expose] def entails (P P' : S.Post α) : Prop :=
  ∀ r s, P r s → P' r s

/-- `entails` is Mathlib's order on (curried) predicates. -/
private theorem entails_iff_le {P P' : S.Post α} : entails P P' ↔ LE.le P P' := Iff.rfl


local infix:50 " ≤ " => entails

/-! ## Building the complete lattice and the monotone function -/

/-- `ITreePred S α` is a complete lattice. -/
private noncomputable instance ITreePred.instCompleteLattice : CompleteLattice (ITreePred S α) :=
  inferInstanceAs (CompleteLattice (ITree E α → S.State → Prop))

/-- `SpecF` is a family of monotone functions over `ITreePred S α`. -/
@[expose] def SpecF (allowDivergence : Prop) (S : EffectSpec E) (Q : S.Post α)
    (X : ITreePred S α) : ITreePred S α :=
  fun m s =>
    ITree.cases
      (motive := fun _ => Prop)
      (fun value => Q value s)
      allowDivergence
      (fun event k => S.wp event (fun answer s' => X (k answer) s') s)
      m

theorem SpecF.ret {Q : S.Post α} {allowDivergence : Prop} {X : ITreePred S α}
    {value : α} {s : S.State} :
    SpecF allowDivergence S Q X (.ret value) s = Q value s := by
  simp only [SpecF, ITree.cases.ret]

theorem SpecF.div {Q : S.Post α} {allowDivergence : Prop} {X : ITreePred S α}
    {s : S.State} :
    SpecF allowDivergence S Q X (ITree.div : ITree E α) s = allowDivergence := by
  simp only [SpecF, ITree.cases.div]

theorem SpecF.vis {Q : S.Post α} {allowDivergence : Prop} {X : ITreePred S α}
    {event : E.I} {k : E.O event → ITree E α} {s : S.State} :
    SpecF allowDivergence S Q X (.vis event k) s =
      S.wp event (fun answer s' => X (k answer) s') s := by
  simp only [SpecF, ITree.cases.vis]

/-- `SpecF` is monotone in all its arguments. -/
theorem SpecF.mono
    {allowDivergence allowDivergence' : Prop}
    (hDiv : allowDivergence → allowDivergence')
    {Q Q' : S.Post α}
    (hQ : Q ≤ Q')
    {X X' : ITreePred S α}
    (hX : X ≤ X')
    {m : ITree E α}
    {s : S.State} :
    SpecF allowDivergence S Q X m s -> SpecF allowDivergence' S Q' X' m s := by
  cases m using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, SpecF.ret]
      exact hQ value s
  | div =>
      simp only [SpecF.div]
      exact hDiv
  | vis event k =>
      simp only [SpecF.vis]
      exact S.wp_mono fun answer s' => hX (k answer) s'

/-- We plug into Mathlib's generic fixed-point library.
    From here on, the least/greatest fixed points and all their
    properties come from Mathlib; the proofs below just instantiate them. -/
private def SpecF.hom (allowDivergence : Prop) (S : EffectSpec E) (Q : S.Post α) :
    ITreePred S α →o ITreePred S α :=
  ⟨SpecF allowDivergence S Q, fun _ _ hX _ _ => SpecF.mono id (fun _ _ => id) hX⟩

/-! ## `TotalSpec` and its properties as a least fixed point -/

/-- `TotalSpec` is the least fixed point of `SpecF False S Q` -/
def TotalSpec (S : EffectSpec E) (Q : S.Post α) : ITreePred S α :=
  (SpecF.hom False S Q).lfp

/-- Unfolding of `TotalSpec` into its impredicative definition. -/
theorem TotalSpec.def {Q : S.Post α} {m : ITree E α} {s : S.State} :
    TotalSpec S Q m s ↔ ∀ X : ITreePred S α, SpecF False S Q X ≤ X → X m s := by
  simp [TotalSpec, OrderHom.lfp, SpecF.hom, entails_iff_le]

/-- Leastness: `TotalSpec S Q` is below every pre-fixed point of `SpecF False S Q`. -/
theorem TotalSpec.least {Q : S.Post α} {X : ITreePred S α} :
    SpecF False S Q X ≤ X -> TotalSpec S Q ≤ X :=
  OrderHom.lfp_le (SpecF.hom False S Q) (a := X)

/-- Closure (`F T ≤ T`): `TotalSpec S Q` is a pre-fixed point of `SpecF False S Q`. -/
theorem TotalSpec.intro {Q : S.Post α} {m : ITree E α} {s : S.State} :
    SpecF False S Q (TotalSpec S Q) m s -> TotalSpec S Q m s :=
  (SpecF.hom False S Q).map_lfp.le m s

/-- Unfolding (`T ≤ F T`): `TotalSpec S Q` is a post-fixed point of `SpecF False S Q`. -/
theorem TotalSpec.step {Q : S.Post α} {m : ITree E α} {s : S.State} :
    TotalSpec S Q m s -> SpecF False S Q (TotalSpec S Q) m s :=
  (SpecF.hom False S Q).map_lfp.ge m s

/-- `TotalSpec S Q` is a fixed point of `SpecF False S Q`. -/
theorem TotalSpec.fixedPoint {Q : S.Post α} {m : ITree E α} {s : S.State} :
    TotalSpec S Q m s ↔ SpecF False S Q (TotalSpec S Q) m s :=
  ⟨TotalSpec.step, TotalSpec.intro⟩

/-! ## `PartialSpec` and its properties as a greatest fixed point -/

/-- Partial correctness: the greatest fixed point of `SpecF True S Q`. -/
def PartialSpec (S : EffectSpec E) (Q : S.Post α) : ITreePred S α :=
  (SpecF.hom True S Q).gfp

/-- Unfolding of `PartialSpec` into its impredicative definition. -/
theorem PartialSpec.def {Q : S.Post α} {m : ITree E α} {s : S.State} :
    PartialSpec S Q m s ↔ ∃ X : ITreePred S α, X ≤ SpecF True S Q X ∧ X m s := by
  simp [PartialSpec, OrderHom.gfp, SpecF.hom, entails_iff_le]

/-- Greatestness: every post-fixed point of `SpecF True S Q` is below `PartialSpec S Q`. -/
theorem PartialSpec.greatest {Q : S.Post α} {X : ITreePred S α} :
    X ≤ SpecF True S Q X -> X ≤ PartialSpec S Q :=
  OrderHom.le_gfp (SpecF.hom True S Q) (a := X)

/-- Unfolding (`P ≤ G P`): `PartialSpec S Q` is a post-fixed point of `SpecF True S Q`. -/
theorem PartialSpec.step {Q : S.Post α} {m : ITree E α} {s : S.State} :
    PartialSpec S Q m s -> SpecF True S Q (PartialSpec S Q) m s :=
  (SpecF.hom True S Q).map_gfp.ge m s

/-- Introduction (`G P ≤ P`): `PartialSpec S Q` is a pre-fixed point of `SpecF True S Q`. -/
theorem PartialSpec.intro {Q : S.Post α} {m : ITree E α} {s : S.State} :
    SpecF True S Q (PartialSpec S Q) m s -> PartialSpec S Q m s :=
  (SpecF.hom True S Q).map_gfp.le m s

/-- `PartialSpec S Q` is a fixed point of `SpecF True S Q`. -/
theorem PartialSpec.fixedPoint {Q : S.Post α} {m : ITree E α} {s : S.State} :
    PartialSpec S Q m s ↔ SpecF True S Q (PartialSpec S Q) m s :=
  ⟨PartialSpec.step, PartialSpec.intro⟩

end Aeneas.Data.Coinductive

end
