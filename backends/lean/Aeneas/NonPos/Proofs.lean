module
public import Aeneas.NonPos.Model.Fix

@[expose] public section
/-!
# Proofs

Every theorem stated in `Top.lean` is proved here, about the definitions of `NonPos/Model/*`.
-/
namespace NonPos.Proofs
open NonPos

universe pu v u w w₁ w₂

attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom
attribute [local instance] Pointed.unit Pointed.prod Pointed.pprod Pointed.pi Pointed.ofCCPO Pointed.monad FixCompat.pointed FixCompat.ofCCPO FixCompat.monad FixCompat.pi FixCompat.prod FixCompat.pprod
attribute [local instance] Fix.dom Shape.BotTotal.ofPointed Fix.BotTotal.ofShape Fix.pointed


section Shapes
variable {I : Type pu}

theorem pointed_const (A : Type w) [Dom A] [Pointed A] :
    ∀ D T y, (Model.Shape.const.{pu, v} (I := I) A).total D T y := Model.Shape.pointed_const A
theorem pointed_pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    ∀ D T' y, (Model.Shape.pi T G).total D T' y := Model.Shape.pointed_pi T G
theorem pointed_arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    ∀ D T y, (Model.Shape.arr k G).total D T y := Model.Shape.pointed_arr k G
theorem pointed_prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G]
    [Shape.Pointed F] [Shape.Pointed G] : ∀ D T y, (Model.Shape.prod F G).total D T y := Model.Shape.pointed_prod F G

variable (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
theorem botTotal_prod (G₁ : Fam.{pu, v} I → Type w) (G₂ : Fam.{pu, v} I → Type w₁) [Shape G₁] [Shape G₂]
    [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] :
    (Model.Shape.prod G₁ G₂).total (Fix.D F) (Fix.T F) NonPos.Domain.OmegaComplete.bottom := Model.Shape.botTotal_prod F G₁ G₂
theorem botTotal_var (k : I) [Fix.BotTotal F k] :
    (Model.Shape.var k).total (Fix.D F) (Fix.T F) NonPos.Domain.OmegaComplete.bottom := Model.Shape.botTotal_var F k
end Shapes

section Fix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
theorem unfold_fold {k : I} (x : F k (Fix F)) (h : Shape.cond x) :
    Model.Fix.unfold F (Model.Fix.fold F x h) = x := Model.Fix.unfold_fold F x h
end Fix

/-! ### The forms -/
section Cont
variable {D : Type w} [Dom D]

theorem Cont.const {B : Type w₁} [Dom B] (b : B) : Cont (fun _ : D => b) := NonPos.Model.Cont.const b
theorem Cont.id : Cont (fun d : D => d) := NonPos.Model.Cont.id
theorem Cont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f := NonPos.Model.Cont.lam h
theorem Cont.app {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := NonPos.Model.Cont.app hf t
theorem Cont.app₂ {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := NonPos.Model.Cont.app₂ hf hc ha
theorem Cont.pair {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := NonPos.Model.Cont.ppair hf hg
theorem Cont.fst {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) := NonPos.Model.Cont.pfst hf
theorem Cont.snd {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) := NonPos.Model.Cont.psnd hf
theorem Cont.ite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := NonPos.Model.Cont.ite c ht he
theorem Cont.dite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) :=
  NonPos.Model.Cont.dite c ht he
theorem Cont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u} {a : D → α}
    (ha : Cont (inst_1 := Dom.discrete α) a) : Cont (inst_1 := NonPosMonad.dom α) (fun d => (pure (a d) : M α)) :=
  NonPos.Model.Cont.pure ha
theorem Cont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : D → M α} {k : D → α → M β}
    (hm : Cont (inst_1 := NonPosMonad.dom α) m)
    (hk : ∀ a, Cont (inst_1 := NonPosMonad.dom β) (fun d => k d a)) :
    Cont (inst_1 := NonPosMonad.dom β) (fun d => m d >>= k d) := NonPos.Model.Cont.bind hm hk

variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]
theorem Cont.unfold {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (inst_1 := Shape.dom (F := F k) (Fix F)) (fun d => Model.Fix.unfold F (f d)) := NonPos.Model.Cont.unfold F hf
theorem Cont.fold {k : I} {f : D → F k (Fix F)} (h : ∀ d, Shape.cond (f d))
    (hf : Cont (inst_1 := Shape.dom (F := F k) (Fix F)) f) : Cont (fun d => Model.Fix.fold F (f d) (h d)) :=
  NonPos.Model.Cont.fold F h hf

theorem Cont.monotone {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] {f : A → B} (h : Cont f) : Lean.Order.monotone f := NonPos.Model.Cont.toMonotone h
theorem Cont.fix {α : Type w₁} [Dom α] [Lean.Order.CCPO α] [FixCompat α] {f : D → α → α}
    {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) :=
  NonPos.Model.Cont.fix (Cont.ofPProd hf)
end Cont

end NonPos.Proofs
