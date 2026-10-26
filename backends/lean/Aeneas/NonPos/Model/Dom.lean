module
public import Aeneas.NonPos.Domain.Basic

@[expose] public section
/-!
# Admissible types, the condition, and fixpoints

`Dom A`: a partial order on `A` with suprema of ω-chains (an unpointed ω-cpo).  `Pointed A`: it has a
least element.  `Cont f`: Scott continuity (`NonPos.Domain.Continuous`) for the orders given by `Dom`.
-/
namespace NonPos.Model
end NonPos.Model
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe u w w₁ w₂ w₃

noncomputable section
set_option warn.classDefReducibility false

/-- Admissible types: a partial order with suprema of ω-chains (used by `Cont`), which also has
suprema of all nonempty chains (used to give dictionaries a `CCPO`). -/
class Dom (A : Type w) where
  po : PartialOrder A
  os : @OmegaSup A po
  cc : @ChainComplete A po

namespace Dom
variable {A : Type w} [Dom A]

/-- The order of a `Dom` (`PartialOrder.rel` for the instance `Dom.po`). -/
abbrev le (x y : A) : Prop := @PartialOrder.rel A Dom.po x y
/-- Chains for the order of a `Dom`. -/
abbrev Chain (A : Type w) [Dom A] := @NonPos.Domain.Chain A Dom.po
/-- The supremum of a chain. -/
abbrev sup (c : Dom.Chain A) : A := @OmegaSup.sup A Dom.po Dom.os c

theorem le_refl (x : A) : le x x := @PartialOrder.rel_refl A Dom.po x
theorem le_trans {x y z : A} (h₁ : le x y) (h₂ : le y z) : le x z :=
  @PartialOrder.rel_trans A Dom.po x y z h₁ h₂
theorem le_antisymm {x y : A} (h₁ : le x y) (h₂ : le y x) : x = y :=
  @PartialOrder.rel_antisymm A Dom.po x y h₁ h₂
theorem le_sup (c : Dom.Chain A) (n : Nat) : le (c n) (sup c) := @OmegaSup.le_sup A Dom.po Dom.os c n
theorem sup_le (c : Dom.Chain A) (x : A) (h : ∀ n, le (c n) x) : le (sup c) x :=
  @OmegaSup.sup_le A Dom.po Dom.os c x h
end Dom

/-- The condition on functions: Scott continuity for the orders of `Dom`. -/
def Cont {A : Type w₁} {B : Type w₂} [inst : Dom A] [inst_1 : Dom B] (f : A → B) : Prop :=
  @Continuous A B Dom.po Dom.po Dom.os Dom.os f

/-- `A` has a least element. -/
class Pointed (A : Type w) [Dom A] : Prop where
  exists_bot : ∃ b : A, ∀ x, Dom.le b x

/-! ## Instances -/

/-- The discrete order: every type is admissible in a trivial way.  Chains are constant.
(Made a low-priority instance in `Top`, not here, so that it never shadows a specific `Dom`.) -/
@[instance_reducible] def Dom.discrete (A : Type w) : Dom A :=
  letI po : PartialOrder A :=
    { rel := Eq, rel_refl := rfl, rel_trans := fun h₁ h₂ => h₁.trans h₂, rel_antisymm := fun h _ => h }
  { po := po
    os :=
    { sup := fun c => c 0
      le_sup := fun c n => by
        show c n = c 0
        induction n with
        | zero => rfl
        | succ n ih => exact (c.step n).symm.trans ih
      sup_le := fun c x h => h 0 }
    cc := ⟨fun c hc ⟨x, hx⟩ => ⟨x, isSup_of
      (fun y hy => ((hc y x hy hx).elim id Eq.symm : y = x)) (fun u hu => hu x hx)⟩⟩ }

@[instance_reducible] def Dom.unit : Dom PUnit.{w+1} where
  po := { rel := fun _ _ => True, rel_refl := trivial, rel_trans := fun _ _ => trivial,
          rel_antisymm := fun _ _ => rfl }
  os := { sup := fun _ => PUnit.unit, le_sup := fun _ _ => trivial, sup_le := fun _ _ _ => trivial }
  cc := ⟨fun _ _ _ => ⟨PUnit.unit, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩⟩
attribute [local instance] Dom.unit

@[instance_reducible] def Dom.prod (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] : Dom (A × B) :=
  letI : PartialOrder A := Dom.po; letI : PartialOrder B := Dom.po
  letI : OmegaSup A := Dom.os; letI : OmegaSup B := Dom.os
  letI : ChainComplete A := Dom.cc; letI : ChainComplete B := Dom.cc
  { po := Domain.instPartialOrderProd, os := instOmegaSupProd, cc := instChainCompleteProd }
attribute [local instance] Dom.prod

@[instance_reducible] def Dom.pi (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] : Dom ((t : T) → B t) :=
  letI : ∀ t, PartialOrder (B t) := fun _ => Dom.po
  letI : ∀ t, OmegaSup (B t) := fun _ => Dom.os
  letI : ∀ t, ChainComplete (B t) := fun _ => Dom.cc
  { po := instOrderPi, os := instOmegaSupPi, cc := instChainCompletePi }
attribute [local instance] Dom.pi

@[instance_reducible] def Dom.pprod (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] : Dom (A ×' B) :=
  letI : PartialOrder A := Dom.po; letI : PartialOrder B := Dom.po
  letI : OmegaSup A := Dom.os; letI : OmegaSup B := Dom.os
  letI po : PartialOrder (A ×' B) :=
    { rel := fun x y => x.1 ⊑ y.1 ∧ x.2 ⊑ y.2
      rel_refl := ⟨PartialOrder.rel_refl, PartialOrder.rel_refl⟩
      rel_trans := fun h₁ h₂ => ⟨PartialOrder.rel_trans h₁.1 h₂.1, PartialOrder.rel_trans h₁.2 h₂.2⟩
      rel_antisymm := fun {x y} h₁ h₂ => by
        obtain ⟨a, b⟩ := x; obtain ⟨a', b'⟩ := y
        cases PartialOrder.rel_antisymm h₁.1 h₂.1; cases PartialOrder.rel_antisymm h₁.2 h₂.2; rfl }
  { po := po
    os :=
    { sup := fun c => ⟨OmegaSup.sup ⟨fun n => (c n).1, fun n => (c.step n).1⟩,
                       OmegaSup.sup ⟨fun n => (c n).2, fun n => (c.step n).2⟩⟩
      le_sup := fun c n => ⟨OmegaSup.le_sup ⟨fun n => (c n).1, fun n => (c.step n).1⟩ n,
                            OmegaSup.le_sup ⟨fun n => (c n).2, fun n => (c.step n).2⟩ n⟩
      sup_le := fun c x h => ⟨OmegaSup.sup_le _ _ (fun n => (h n).1), OmegaSup.sup_le _ _ (fun n => (h n).2)⟩ }
    cc := by
      letI : ChainComplete A := Dom.cc; letI : ChainComplete B := Dom.cc
      refine ⟨fun c hc hne => ?_⟩
      have h₁ : chain (image PProd.fst c) := @chain_image (A ×' B) A po Dom.po PProd.fst (fun _ _ h => h.1) c hc
      have h₂ : chain (image PProd.snd c) := @chain_image (A ×' B) B po Dom.po PProd.snd (fun _ _ h => h.2) c hc
      have hs₁ := chainSup_spec _ h₁ (image_nonempty _ hne)
      have hs₂ := chainSup_spec _ h₂ (image_nonempty _ hne)
      refine ⟨⟨chainSup _ h₁ (image_nonempty _ hne), chainSup _ h₂ (image_nonempty _ hne)⟩,
        isSup_of (fun x hx => ⟨isSup_le hs₁ ⟨x, hx, rfl⟩, isSup_le hs₂ ⟨x, hx, rfl⟩⟩) (fun u hu => ⟨?_, ?_⟩)⟩
      · exact isSup_le_of hs₁ fun _ ⟨x, hx, e⟩ => e ▸ (hu x hx).1
      · exact isSup_le_of hs₂ fun _ ⟨x, hx, e⟩ => e ▸ (hu x hx).2 }
attribute [local instance] Dom.pprod

/-- The admissible structure of a chain-complete partial order (the one `partial_fixpoint` uses). -/
theorem Dom.chain_range {A : Type w} [PartialOrder A] (c : NonPos.Domain.Chain A) :
    chain (fun x => ∃ n, c n = x) := by
  rintro x y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases Nat.le_total n m with h | h
  · exact Or.inl (c.le h)
  · exact Or.inr (c.le h)

def Dom.ofCCPO (A : Type w) [CCPO A] : Dom A where
  po := inferInstance
  os :=
    { sup := fun c => CCPO.csup (Dom.chain_range c)
      le_sup := fun c n => le_csup (Dom.chain_range c) ⟨n, rfl⟩
      sup_le := fun c x h => csup_le (Dom.chain_range c) (fun y ⟨n, hn⟩ => hn ▸ h n) }
  cc := ⟨fun _ hc _ => CCPO.has_csup hc⟩

/-- The `Dom` structure agrees with the given `CCPO`: same order, same suprema of chains. -/
class FixCompat (A : Type w) [inst : Dom A] [CCPO A] : Prop where
  le_iff : ∀ x y : A, Dom.le x y ↔ x ⊑ y

/-! ## Monads -/

/-- A monad usable for the function fields: it carries the chain-complete order `partial_fixpoint`
uses, and `bind` is continuous for it (`pure` is automatically, since its domain is discrete). -/
class NonPosMonad (M : Type u → Type u) [∀ α, CCPO (M α)] extends Monad M where
  bind_cont : ∀ {α β : Type u},
    @Cont (M α ×' (α → M β)) (M β)
      (@Dom.pprod (M α) (α → M β) (Dom.ofCCPO (M α)) (@Dom.pi α (fun _ => M β) (fun _ => Dom.ofCCPO (M β))))
      (Dom.ofCCPO (M β))
      (fun p => p.1 >>= p.2)

@[instance_reducible] def NonPosMonad.dom {M : Type u → Type u} [∀ α, CCPO (M α)] [NonPosMonad M] (α : Type u) : Dom (M α) :=
  Dom.ofCCPO (M α)
attribute [local instance] NonPosMonad.dom

end
end NonPos
