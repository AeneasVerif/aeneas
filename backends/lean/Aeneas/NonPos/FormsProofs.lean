module
public import Lean
public import Aeneas.NonPos.Top

@[expose] public section
/-!
# The forms at the orders of the model, and the proofs of the forms

Section 1 has the forms of terms on `Cont`, at the orders of the model: these are what the
`nonpos_cont` tactic applies.  Section 2 proves from them the forms of section 1 of `Tactic.lean`,
which are stated on `FixFunctor.Cont`.  Not part of the trusted surface.
-/

namespace NonPos
noncomputable section

universe pu v u w w₁ w₂ w₃

/-! ## 1. The forms, at the orders of the model (used by the tactic)

Everything the `nonpos_cont` tactic knows is one of the statements below, all of the shape
`Cont (fun d => ‹form›)`, for the orders (`Dom`) of the model.  `D` is the type of the varying
dictionary (or tuple of dictionaries).  The tactic looks up `forms` (in `Tactic.lean`) by shape;
`const`, `id`, `lam`, `app` and `app₂` have no shape to look up and are the tactic's own cases. -/

section Cont
variable {D : Type w} [Dom D]

theorem Cont.const {B : Type w₁} [Dom B] (b : B) : Cont (fun _ : D => b) := Proofs.Cont.const b
theorem Cont.id : Cont (fun d : D => d) := Proofs.Cont.id
/-- Lambda: pointwise. -/
theorem Cont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f := Proofs.Cont.lam h
/-- Application to an argument not depending on `d` (a type, a value, a fixed dictionary, ...). -/
theorem Cont.app {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := Proofs.Cont.app hf t
/-- Application to an argument depending on `d`: the function must satisfy the condition. -/
theorem Cont.app₂ {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := Proofs.Cont.app₂ hf hc ha
/-- Pairs: the field tuples of a structure, and what a mutual `partial_fixpoint` is packed into. -/
theorem Cont.pair {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := Proofs.Cont.pair hf hg
theorem Cont.fst {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) := Proofs.Cont.fst hf
theorem Cont.snd {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) := Proofs.Cont.snd hf
theorem Cont.ite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := Proofs.Cont.ite c ht he
theorem Cont.dite {B : Type w₁} [Dom B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) :=
  Proofs.Cont.dite c ht he
/-- `pure`, `bind`: this is what a supported monad provides. -/
theorem Cont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u} {a : D → α}
    (ha : Cont (inst_1 := Dom.discrete α) a) : Cont (fun d => (pure (a d) : M α)) := Proofs.Cont.pure ha
theorem Cont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : D → M α} {k : D → α → M β}
    (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) : Cont (fun d => m d >>= k d) := Proofs.Cont.bind hm hk

variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, FixFunctor (F k)]
/-- Projections out of a structure, and `mk` of fields depending on `d`. -/
theorem Cont.unfold {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (inst_1 := FixFunctor.dom (F := F k) (Fix F)) (fun d => Fix.unfold F (f d)) := Proofs.Cont.unfold F hf
theorem Cont.fold {k : I} {f : D → F k (Fix F)} (h : ∀ d, FixFunctor.cond F (f d))
    (hf : Cont (inst_1 := FixFunctor.dom (F := F k) (Fix F)) f) : Cont (fun d => Fix.fold F (f d) (h d)) :=
  Proofs.Cont.fold F h hf

/-! `Cont.fst`, `Cont.snd` and `Cont.pair` for the field tuple of a structure, at the `Dom` that the
shape of the tuple gives it (`FixFunctor.dom`, as in `Cont.unfold` and `Cont.fold`), so that a projection
out of a dictionary, and the tuple of a `mk`, are proved without comparing that `Dom` with the one
instance search builds for the whole tuple. -/
section ShapeForms
variable {G : Fam.{pu, v} I → Type w₁} {H : Fam.{pu, v} I → Type w₂} [FixFunctor G] [FixFunctor H]
  {X : Fam.{pu, v} I} [∀ k, Dom (X k)]
theorem Cont.shape_fst {f : D → G X ×' H X} (hf : Cont (inst_1 := FixFunctor.dom (fun X => G X ×' H X) X) f) :
    Cont (inst_1 := FixFunctor.dom G X) (fun d => (f d).1) :=
  @Proofs.Cont.fst D _ _ _ (FixFunctor.dom G X) (FixFunctor.dom H X) f hf
theorem Cont.shape_snd {f : D → G X ×' H X} (hf : Cont (inst_1 := FixFunctor.dom (fun X => G X ×' H X) X) f) :
    Cont (inst_1 := FixFunctor.dom H X) (fun d => (f d).2) :=
  @Proofs.Cont.snd D _ _ _ (FixFunctor.dom G X) (FixFunctor.dom H X) f hf
theorem Cont.shape_pair {f : D → G X} {g : D → H X}
    (hf : Cont (inst_1 := FixFunctor.dom G X) f) (hg : Cont (inst_1 := FixFunctor.dom H X) g) :
    Cont (inst_1 := FixFunctor.dom (fun X => G X ×' H X) X) (fun d => (⟨f d, g d⟩ : G X ×' H X)) :=
  @Proofs.Cont.pair D _ _ _ (FixFunctor.dom G X) (FixFunctor.dom H X) f g hf hg
end ShapeForms

/-- Fixed points: `partial_fixpoint` elaborates to `Lean.Order.fix`, for functions and for
self-referential dictionaries alike. -/
theorem Cont.fix {α : Type w₁} [Dom α] [Lean.Order.CCPO α] [FixCompat α] {f : D → α → α}
    {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) := Proofs.Cont.fix hf
end Cont

/-! `FixCompat α`: the `Dom` and `CCPO` structures on `α` agree.  Holds for `M α`, pointwise, and on
products: exactly the types `partial_fixpoint` recurses through. -/
instance {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : FixCompat (M α) :=
  FixCompat.monad α
instance {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] [∀ t, Lean.Order.CCPO (B t)] [∀ t, FixCompat (B t)] :
    FixCompat ((t : T) → B t) := FixCompat.pi
instance {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] : FixCompat (A ×' B) := FixCompat.pprod
instance {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, FixFunctor (F k)] (k : I) [Fix.Recursive F k] :
    FixCompat (Fix F k) := Fix.fixCompat F k

/-- `partial_fixpoint`'s monotonicity obligation, from the condition: write a self-referential
instance as `def inst : Bla Int := Bla.mk … partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)`. -/
theorem Cont.monotone {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [Lean.Order.CCPO A] [Lean.Order.CCPO B]
    [FixCompat A] [FixCompat B] {f : A → B} (h : Cont f) : Lean.Order.monotone f := Proofs.Cont.monotone h

/-! ## 2. The forms of section 1 of `Tactic.lean`, on `FixFunctor.Cont` -/

section Forms
variable {I : Type pu} {H : I → (I → Type v) → Type v} [∀ k, FixFunctor (H k)]
  {G₁ : (I → Type v) → Type w₁} [FixFunctor G₁]

theorem Proofs.ShapeCont.const {G : (I → Type v) → Type w₂} [FixFunctor G] (b : G (Fix H)) :
    FixFunctor.Cont H (G₁ := G₁) (fun _ => b) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); exact Proofs.Cont.const b
theorem Proofs.ShapeCont.id : FixFunctor.Cont H (G₁ := G₁) (G₂ := G₁) (fun d => d) := by
  letI := FixFunctor.dom G₁ (Fix H); exact Proofs.Cont.id
theorem Proofs.ShapeCont.lam {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, FixFunctor (G t)] [∀ t, FixFunctor.Methods (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (h : ∀ t, FixFunctor.Cont H (fun d => f d t)) :
    FixFunctor.Cont H (G₂ := fun X => (t : T) → G t X) f := by
  letI := FixFunctor.dom G₁ (Fix H); letI := fun t => FixFunctor.dom (G t) (Fix H); exact Proofs.Cont.lam h
theorem Proofs.ShapeCont.app {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, FixFunctor (G t)] [∀ t, FixFunctor.Methods (G t)]
    {f : G₁ (Fix H) → (t : T) → G t (Fix H)} (hf : FixFunctor.Cont H (G₂ := fun X => (t : T) → G t X) f) (t : T) :
    FixFunctor.Cont H (fun d => f d t) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := fun t => FixFunctor.dom (G t) (Fix H); exact Proofs.Cont.app hf t
theorem Proofs.ShapeCont.app₂ {k : I} {G : (I → Type v) → Type w₂} [FixFunctor G] [FixFunctor.Methods G]
    {f : G₁ (Fix H) → Fix H k → G (Fix H)} {a : G₁ (Fix H) → Fix H k}
    (hf : FixFunctor.Cont H (G₂ := fun X => X k → G X) f) (hc : ∀ d, FixFunctor.Cont H (G₁ := fun X => X k) (f d))
    (ha : FixFunctor.Cont H (G₂ := fun X => X k) a) : FixFunctor.Cont H (fun d => f d (a d)) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); exact Proofs.Cont.app₂ hf hc ha
theorem Proofs.ShapeCont.pair {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [FixFunctor G] [FixFunctor G']
    {f : G₁ (Fix H) → G (Fix H)} {g : G₁ (Fix H) → G' (Fix H)} (hf : FixFunctor.Cont H f) (hg : FixFunctor.Cont H g) :
    FixFunctor.Cont H (G₂ := fun X => G X ×' G' X) (fun d => (⟨f d, g d⟩ : G (Fix H) ×' G' (Fix H))) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); letI := FixFunctor.dom G' (Fix H)
  exact Proofs.Cont.pair hf hg
theorem Proofs.ShapeCont.fst {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [FixFunctor G] [FixFunctor G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : FixFunctor.Cont H (G₂ := fun X => G X ×' G' X) f) : FixFunctor.Cont H (fun d => (f d).1) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); letI := FixFunctor.dom G' (Fix H)
  exact Proofs.Cont.fst hf
theorem Proofs.ShapeCont.snd {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [FixFunctor G] [FixFunctor G']
    {f : G₁ (Fix H) → G (Fix H) ×' G' (Fix H)}
    (hf : FixFunctor.Cont H (G₂ := fun X => G X ×' G' X) f) : FixFunctor.Cont H (fun d => (f d).2) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); letI := FixFunctor.dom G' (Fix H)
  exact Proofs.Cont.snd hf
theorem Proofs.ShapeCont.ite {G : (I → Type v) → Type w₂} [FixFunctor G] (c : Prop) [Decidable c] {t e : G₁ (Fix H) → G (Fix H)}
    (ht : FixFunctor.Cont H t) (he : FixFunctor.Cont H e) : FixFunctor.Cont H (fun d => if c then t d else e d) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); exact Proofs.Cont.ite c ht he
theorem Proofs.ShapeCont.dite {G : (I → Type v) → Type w₂} [FixFunctor G] (c : Prop) [Decidable c]
    {t : c → G₁ (Fix H) → G (Fix H)} {e : ¬c → G₁ (Fix H) → G (Fix H)}
    (ht : ∀ h, FixFunctor.Cont H (t h)) (he : ∀ h, FixFunctor.Cont H (e h)) :
    FixFunctor.Cont H (fun d => if h : c then t h d else e h d) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); exact Proofs.Cont.dite c ht he
theorem Proofs.ShapeCont.pure {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α : Type u}
    {a : G₁ (Fix H) → α} (ha : FixFunctor.Cont H (G₂ := fun _ => α) (iG₂ := FixFunctor.data α) a) :
    FixFunctor.Cont H (G₂ := fun _ => M α) (fun d => (Pure.pure (a d) : M α)) := by
  letI := FixFunctor.dom G₁ (Fix H); exact Proofs.Cont.pure ha
theorem Proofs.ShapeCont.bind {M : Type u → Type u} [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u}
    {m : G₁ (Fix H) → M α} {k : G₁ (Fix H) → α → M β}
    (hm : FixFunctor.Cont H (G₂ := fun _ => M α) m) (hk : ∀ a, FixFunctor.Cont H (G₂ := fun _ => M β) (fun d => k d a)) :
    FixFunctor.Cont H (G₂ := fun _ => M β) (fun d => m d >>= k d) := by
  letI := FixFunctor.dom G₁ (Fix H); exact Proofs.Cont.bind hm hk
theorem Proofs.ShapeCont.unfold {k : I} {g : G₁ (Fix H) → Fix H k} (hg : FixFunctor.Cont H (G₂ := fun X => X k) g) :
    FixFunctor.Cont H (G₂ := H k) (fun d => Fix.unfold H (g d)) := by
  letI := FixFunctor.dom G₁ (Fix H); exact Proofs.Cont.unfold H hg
theorem Proofs.ShapeCont.fold {k : I} {f : G₁ (Fix H) → H k (Fix H)} (h : ∀ d, FixFunctor.cond H (f d))
    (hf : FixFunctor.Cont H (G₂ := H k) f) : FixFunctor.Cont H (G₂ := fun X => X k) (fun d => Fix.fold H (f d) (h d)) := by
  letI := FixFunctor.dom G₁ (Fix H); exact Proofs.Cont.fold H h hf
theorem Proofs.ShapeCont.fix {G : (I → Type v) → Type w₂} [FixFunctor G] [Lean.Order.CCPO (G (Fix H))] [FixFunctor.FixCompat H G]
    {f : G₁ (Fix H) → G (Fix H) → G (Fix H)} {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : FixFunctor.Cont H (G₁ := fun X => G₁ X ×' G X) (fun p => f p.1 p.2)) :
    FixFunctor.Cont H (fun d => Lean.Order.fix (f d) (hm d)) := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G (Fix H); exact Proofs.Cont.fix hf
theorem Proofs.ShapeCont.monotone {G₂ : (I → Type v) → Type w₂} [FixFunctor G₂] [Lean.Order.CCPO (G₁ (Fix H))]
    [Lean.Order.CCPO (G₂ (Fix H))] [FixFunctor.FixCompat H G₁] [FixFunctor.FixCompat H G₂] {f : G₁ (Fix H) → G₂ (Fix H)}
    (h : FixFunctor.Cont H f) : Lean.Order.monotone f := by
  letI := FixFunctor.dom G₁ (Fix H); letI := FixFunctor.dom G₂ (Fix H); exact Proofs.Cont.monotone h
theorem Proofs.ShapeCont.fixCompat_pi {T : Type w₂} {G : T → (I → Type v) → Type w₃} [∀ t, FixFunctor (G t)] [∀ t, FixFunctor.Methods (G t)]
    [∀ t, Lean.Order.CCPO (G t (Fix H))] [∀ t, FixFunctor.FixCompat H (G t)] :
    FixFunctor.FixCompat H (fun X => (t : T) → G t X) := by
  letI := fun t => FixFunctor.dom (G t) (Fix H); exact FixCompat.pi
theorem Proofs.ShapeCont.fixCompat_prod {G : (I → Type v) → Type w₂} {G' : (I → Type v) → Type w₃} [FixFunctor G]
    [FixFunctor G'] [Lean.Order.CCPO (G (Fix H))] [Lean.Order.CCPO (G' (Fix H))] [FixFunctor.FixCompat H G]
    [FixFunctor.FixCompat H G'] : FixFunctor.FixCompat H (fun X => G X ×' G' X) := by
  letI := FixFunctor.dom G (Fix H); letI := FixFunctor.dom G' (Fix H); exact FixCompat.pprod
end Forms

end
end NonPos
