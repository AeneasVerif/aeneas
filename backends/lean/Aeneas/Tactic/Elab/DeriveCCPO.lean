module
public import Lean
public import Mathlib.Tactic.ProxyType
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

@[expose] public section
/-!
# `deriving Lean.Order.CCPO` for a structure

Declares `instance : CCPO (S …) := CCPO.ofEquiv (proxy_equiv% (S …))`: Mathlib's `proxy_equiv%`
gives the bijection between `S` and the tuple of its fields, so two values of `S` are compared field
by field.  This lets the dictionary of an ordinary trait be a plain field of a `nonpos_structure`.
-/

namespace Aeneas
open Lean Elab Command Lean.Order

universe u v

/-- The `CCPO` on `A` that compares the images by `e.symm`. -/
@[reducible] def CCPO.ofEquiv {A : Sort u} {B : Sort v} [CCPO B] (e : B ≃ A) : CCPO A where
  rel x y := e.symm x ⊑ e.symm y
  rel_refl := PartialOrder.rel_refl
  rel_trans := PartialOrder.rel_trans
  rel_antisymm h₁ h₂ := e.symm.injective (PartialOrder.rel_antisymm h₁ h₂)
  has_csup {c} hc := by
    obtain ⟨s, hs⟩ := CCPO.has_csup (c := fun b => c (e b)) fun b₁ b₂ h₁ h₂ => by
      simpa only [e.symm_apply_apply] using hc _ _ h₁ h₂
    refine ⟨e s, fun x => (e.symm_apply_apply s ▸ hs (e.symm x)).trans ⟨fun h y hy => ?_, fun h b hb => ?_⟩⟩
    · exact h _ (by simpa only [e.apply_symm_apply])
    · simpa only [e.symm_apply_apply] using h _ hb

/-- The proxy type's pairs `(_ : α) × β` are compared componentwise. -/
instance {α : Type u} {β : Type v} [CCPO α] [CCPO β] : CCPO ((_ : α) × β) :=
  CCPO.ofEquiv (B := α ×' β) ⟨fun p => ⟨p.1, p.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩

meta def mkCCPOInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  unless declNames.all (isStructure (← getEnv)) do return false
  for S in declNames do
    elabCommand (← liftTermElabM do
      let indVal ← getConstInfoInduct S
      let argNames ← Deriving.mkInductArgNames indVal
      let binders ← Deriving.mkImplicitBinders argNames
      let target ← Deriving.mkInductiveApp indVal argNames
      -- (a structure with many fields needs a deep instance search)
      `(command| set_option synthInstance.maxSize 4096 in
        instance $(binders.map TSyntax.mk):bracketedBinder* : CCPO $target :=
          CCPO.ofEquiv (proxy_equiv% $target)))
  return true

meta initialize registerDerivingHandler ``Lean.Order.CCPO mkCCPOInstanceHandler

end Aeneas
