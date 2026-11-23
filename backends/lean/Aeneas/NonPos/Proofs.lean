module
public import Aeneas.NonPos.Model.Fix

@[expose] public section
/-!
# Proofs

Every theorem stated in `TrustedBase/Definitions.lean` is proved here, about the definitions of `NonPos/Model/*`.
-/
namespace NonPos.Proofs
open NonPos

universe pu v u w w₁ w₂

attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO FixCompat.pointed FixCompat.ofCCPO FixCompat.pi FixCompat.prod FixCompat.pprod
attribute [local instance] MFix.dom MFix.pointed



section MFix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
theorem unfold_fold {k : I} (x : F k (MFix F)) (h : Model.Shape.cond x) :
    Model.MFix.unfold F (Model.MFix.fold F x h) = x := Model.MFix.unfold_fold F x h
end MFix

/-! ### The forms -/
section DCont
variable {D : Type w} [Dom D]

theorem DCont.const {B : Type w₁} [Dom B] (b : B) : DCont (fun _ : D => b) := NonPos.Model.DCont.const b
theorem DCont.id : DCont (fun d : D => d) := NonPos.Model.DCont.id
theorem DCont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, DCont (fun d => f d t)) : DCont f := NonPos.Model.DCont.lam h
theorem DCont.app {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : DCont f) (t : T) : DCont (fun d => f d t) := NonPos.Model.DCont.app hf t
theorem DCont.app₂ {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A → B} {a : D → A}
    (hf : DCont f) (hc : ∀ d, DCont (f d)) (ha : DCont a) : DCont (fun d => f d (a d)) := NonPos.Model.DCont.app₂ hf hc ha
theorem DCont.pair {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A} {g : D → B}
    (hf : DCont f) (hg : DCont g) : DCont (fun d => (⟨f d, g d⟩ : A ×' B)) := NonPos.Model.DCont.ppair hf hg
theorem DCont.fst {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : DCont f) :
    DCont (fun d => (f d).1) := NonPos.Model.DCont.pfst hf
theorem DCont.snd {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : DCont f) :
    DCont (fun d => (f d).2) := NonPos.Model.DCont.psnd hf
theorem DCont.ite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : DCont t) (he : DCont e) : DCont (fun d => if c then t d else e d) := NonPos.Model.DCont.ite c ht he
theorem DCont.dite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, DCont (t h)) (he : ∀ h, DCont (e h)) : DCont (fun d => if h : c then t h d else e h d) :=
  NonPos.Model.DCont.dite c ht he

variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
theorem DCont.unfold {k : I} {f : D → MFix F k} (hf : DCont f) :
    DCont (inst_1 := Shape.dom (F := F k) (MFix F)) (fun d => Model.MFix.unfold F (f d)) := NonPos.Model.DCont.unfold F hf
theorem DCont.fold {k : I} {f : D → F k (MFix F)} (h : ∀ d, Model.Shape.cond (f d))
    (hf : DCont (inst_1 := Shape.dom (F := F k) (MFix F)) f) : DCont (fun d => Model.MFix.fold F (f d) (h d)) :=
  NonPos.Model.DCont.fold F h hf

theorem DCont.monotone {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] {f : A → B} (h : DCont f) : Lean.Order.monotone f := NonPos.Model.DCont.toMonotone h
theorem DCont.fix {α : Type w₁} [Dom α] [Lean.Order.CCPO α] [FixCompat α] {f : D → α → α}
    {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : DCont (fun p : D ×' α => f p.1 p.2)) : DCont (fun d => Lean.Order.fix (f d) (hm d)) :=
  NonPos.Model.DCont.fix (DCont.ofPProd hf)
end DCont

end NonPos.Proofs
