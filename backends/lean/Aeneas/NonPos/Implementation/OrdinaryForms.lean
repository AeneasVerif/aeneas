module
public import Aeneas.NonPos.Implementation.Tactic
public import Aeneas.Tactic.Elab.DeriveCCPO

@[expose] public section
/-!
# The forms of the structures ordered through a tuple

A structure with a derived `CCPO` (`deriving Lean.Order.CCPO`), and a `Sigma`, are ordered by
`Aeneas.CCPO.ofEquiv e`: through the tuple `e.symm x` of their fields.  `nonpos_cont` writes a
constructor `S.mk a₁ … aₙ` as `e ⟨a₁, …, aₙ⟩`, and a projection `x.f` as a component of `e.symm x`
(`nonposOfEquiv?`); these two forms then go through `e`.
-/
namespace NonPos
open Lean.Order

universe u v w

section
variable {D : Type w} [PartialOrder D] {A : Type u} {B : Type v} [CCPO B]

/-- A map into a type ordered by `CCPO.ofEquiv e` is continuous iff it is, through `e.symm`. -/
theorem Proofs.Cont.ofEquiv_iff (e : B ≃ A) (g : D → A) :
    @Cont D A _ (Aeneas.CCPO.ofEquiv e).toPartialOrder g ↔ Cont (fun d => e.symm (g d)) := by
  constructor
  · rintro ⟨hm, hl⟩
    refine ⟨hm, fun c hc s hs => ?_⟩
    have h := hl c hc s hs
    refine ⟨h.1, fun u hu => ?_⟩
    have h2 := h.2 (e u) (fun n => by
      show e.symm (g (c n)) ⊑ e.symm (e u)
      rw [e.symm_apply_apply]; exact hu n)
    have h3 : e.symm (g s) ⊑ e.symm (e u) := h2
    rwa [e.symm_apply_apply] at h3
  · rintro ⟨hm, hl⟩
    refine ⟨hm, fun c hc s hs => ?_⟩
    have h := hl c hc s hs
    exact ⟨h.1, fun u hu => h.2 (e.symm u) hu⟩

/-- A constructor (or a tuple of `Sigma`), through `e`. -/
@[nonpos_continuous]
theorem Cont.ofEquiv_apply (e : B ≃ A) {g : D → B} (hg : Cont g) :
    @Cont D A _ (Aeneas.CCPO.ofEquiv e).toPartialOrder (fun d => e (g d)) :=
  (Proofs.Cont.ofEquiv_iff e _).2 (by simpa using hg)

/-- A projection, through `e.symm`. -/
@[nonpos_continuous]
theorem Cont.ofEquiv_symm (e : B ≃ A) {g : D → A}
    (hg : @Cont D A _ (Aeneas.CCPO.ofEquiv e).toPartialOrder g) : Cont (fun d => e.symm (g d)) :=
  (Proofs.Cont.ofEquiv_iff e g).1 hg
end

end NonPos
