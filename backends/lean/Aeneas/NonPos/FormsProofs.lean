module
public import Lean
public import Aeneas.NonPos.Top

@[expose] public section
/-!
# The proofs of the forms

The forms of section 0 of `Tactic.lean`, on `Shape.Cont`, proved from the model at the orders that
the shapes give.  Not part of the trusted surface.
-/

namespace NonPos
noncomputable section

universe pu v u w w₁ w₂ w₃

section Forms
variable {I : Type pu} {H : I → (I → Type v) → Type v} [∀ k, Shape (H k)]
  {G₁ : (I → Type v) → Type w₁} [Shape G₁]

theorem Proofs.ShapeCont.const {G : (I → Type v) → Type w₂} [Shape G] (b : G (Fix H)) :
    Shape.Cont H (G₁ := G₁) (fun _ => b) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); exact Proofs.Cont.const b
theorem Proofs.ShapeCont.id : Shape.Cont H (G₁ := G₁) (G₂ := G₁) (fun d => d) := by
  letI := Shape.dom G₁ (Fix H); exact Proofs.Cont.id
theorem Proofs.ShapeCont.lam {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (h : ∀ t, Shape.Cont H (fun d => f d t)) :
    Shape.Cont H (G₂ := fun X => (t : T) → G t X) f := by
  letI := Shape.dom G₁ (Fix H); letI := fun t => Shape.dom (G t) (Fix H); exact Proofs.Cont.lam h
theorem Proofs.ShapeCont.app {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (hf : Shape.Cont H (G₂ := fun X => (t : T) → G t X) f) (t : T) :
    Shape.Cont H (fun d => f d t) := by
  letI := Shape.dom G₁ (Fix H); letI := fun t => Shape.dom (G t) (Fix H); exact Proofs.Cont.app hf t
theorem Proofs.ShapeCont.app₂ {k : I} {G : (I → Type v) → Type w₂} [Shape G] [Shape.Pointed G]
    {f : G₁ (Fix H) → Fix H k → G (Fix H)} {a : G₁ (Fix H) → Fix H k}
    (hf : Shape.Cont H (G₂ := fun X => X k → G X) f) (hc : ∀ d, Shape.Cont H (G₁ := fun X => X k) (f d))
    (ha : Shape.Cont H (G₂ := fun X => X k) a) : Shape.Cont H (fun d => f d (a d)) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); exact Proofs.Cont.app₂ hf hc ha
theorem Proofs.ShapeCont.pair {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H)} {g : G₁ (Fix H) → G' (Fix H)} (hf : Shape.Cont H f) (hg : Shape.Cont H g) :
    Shape.Cont H (G₂ := fun X => G X ×' G' X) (fun d => (⟨f d, g d⟩ : G (Fix H) ×' G' (Fix H))) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); letI := Shape.dom G' (Fix H)
  exact Proofs.Cont.pair hf hg
theorem Proofs.ShapeCont.fst {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : Shape.Cont H (G₂ := fun X => G X ×' G' X) f) : Shape.Cont H (fun d => (f d).1) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); letI := Shape.dom G' (Fix H)
  exact Proofs.Cont.fst hf
theorem Proofs.ShapeCont.snd {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [Shape G] [Shape G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : Shape.Cont H (G₂ := fun X => G X ×' G' X) f) : Shape.Cont H (fun d => (f d).2) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); letI := Shape.dom G' (Fix H)
  exact Proofs.Cont.snd hf
theorem Proofs.ShapeCont.ite {G : (I → Type v) → Type w₂} [Shape G] (c : Prop) [Decidable c] {t e : G₁ (Fix H) → G (Fix H)}
    (ht : Shape.Cont H t) (he : Shape.Cont H e) : Shape.Cont H (fun d => if c then t d else e d) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); exact Proofs.Cont.ite c ht he
theorem Proofs.ShapeCont.dite {G : (I → Type v) → Type w₂} [Shape G] (c : Prop) [Decidable c]
    {t : c → G₁ (Fix H) → G (Fix H)} {e : ¬c → G₁ (Fix H) → G (Fix H)}
    (ht : ∀ h, Shape.Cont H (t h)) (he : ∀ h, Shape.Cont H (e h)) :
    Shape.Cont H (fun d => if h : c then t h d else e h d) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); exact Proofs.Cont.dite c ht he
theorem Proofs.ShapeCont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u}
    {a : G₁ (Fix H) → α} (ha : Shape.Cont H (G₂ := fun _ => α) (iG₂ := Shape.data α) a) :
    Shape.Cont H (G₂ := fun _ => M α) (fun d => (Pure.pure (a d) : M α)) := by
  letI := Shape.dom G₁ (Fix H); exact Proofs.Cont.pure ha
theorem Proofs.ShapeCont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : G₁ (Fix H) → M α} {k : G₁ (Fix H) → α → M β}
    (hm : Shape.Cont H (G₂ := fun _ => M α) m) (hk : ∀ a, Shape.Cont H (G₂ := fun _ => M β) (fun d => k d a)) :
    Shape.Cont H (G₂ := fun _ => M β) (fun d => m d >>= k d) := by
  letI := Shape.dom G₁ (Fix H); exact Proofs.Cont.bind hm hk
theorem Proofs.ShapeCont.unfold {k : I} {g : G₁ (Fix H) → Fix H k} (hg : Shape.Cont H (G₂ := fun X => X k) g) :
    Shape.Cont H (G₂ := H k) (fun d => Fix.unfold H (g d)) := by
  letI := Shape.dom G₁ (Fix H); exact Proofs.Cont.unfold H hg
theorem Proofs.ShapeCont.fold {k : I} {f : G₁ (Fix H) → H k (Fix H)} (h : ∀ d, Shape.cond H (f d))
    (hf : Shape.Cont H (G₂ := H k) f) : Shape.Cont H (G₂ := fun X => X k) (fun d => Fix.fold H (f d) (h d)) := by
  letI := Shape.dom G₁ (Fix H); exact Proofs.Cont.fold H h hf
theorem Proofs.ShapeCont.fix {G : (I → Type v) → Type w₂} [Shape G] [Lean.Order.CCPO (G (Fix H))] [Shape.FixCompat H G]
    {f : G₁ (Fix H) → G (Fix H) → G (Fix H)} {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Shape.Cont H (G₁ := fun X => G₁ X ×' G X) (fun p => f p.1 p.2)) :
    Shape.Cont H (fun d => Lean.Order.fix (f d) (hm d)) := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G (Fix H); exact Proofs.Cont.fix hf
theorem Proofs.ShapeCont.monotone {G₂ : (I → Type v) → Type w₂} [Shape G₂] [Lean.Order.CCPO (G₁ (Fix H))]
    [Lean.Order.CCPO (G₂ (Fix H))] [Shape.FixCompat H G₁] [Shape.FixCompat H G₂] {f : G₁ (Fix H) → G₂ (Fix H)}
    (h : Shape.Cont H f) : Lean.Order.monotone f := by
  letI := Shape.dom G₁ (Fix H); letI := Shape.dom G₂ (Fix H); exact Proofs.Cont.monotone h
theorem Proofs.ShapeCont.fixCompat_pi {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    [∀ t, Lean.Order.CCPO (G t (Fix H))] [∀ t, Shape.FixCompat H (G t)] :
    Shape.FixCompat H (fun X => (t : T) → G t X) := by
  letI := fun t => Shape.dom (G t) (Fix H); exact FixCompat.pi
end Forms

end
end NonPos
