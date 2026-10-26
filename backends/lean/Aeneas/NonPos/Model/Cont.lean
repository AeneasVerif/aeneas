module
public import Aeneas.NonPos.Model.Dom
import all Init.Internal.Order.Basic

@[expose] public section
/-!
# Continuity lemmas, least elements, fixpoints
-/
namespace NonPos
open NonPos.Domain NonPos.Model Lean.Order

universe u w w₁ w₂ w₃ w₄

noncomputable section
set_option warn.classDefReducibility false
attribute [local instance] Dom.unit Dom.prod Dom.pi Dom.pprod NonPosMonad.dom

/-- `letDom A, B` puts the `PartialOrder` and `OmegaSup` instances of the `Dom`s of `A`, `B` in scope. -/
syntax "letDom" term,+ : tactic
macro_rules
  | `(tactic| letDom $t:term) => `(tactic| (letI := (Dom.po : PartialOrder $t); letI := (Dom.os : OmegaSup $t)))
  | `(tactic| letDom $t:term, $ts:term,*) => `(tactic| (letDom $t; letDom $ts,*))

section Lemmas
variable {D : Type w} {A : Type w₁} {B : Type w₂} {C : Type w₃} [Dom D] [Dom A] [Dom B] [Dom C]

theorem Cont.mono {f : D → B} (h : Cont f) {x y : D} (hxy : Dom.le x y) : Dom.le (f x) (f y) :=
  @Continuous.mono D B Dom.po Dom.po Dom.os Dom.os f h x y hxy
theorem Cont.monoFn {f : D → B} (h : Cont f) : ∀ x y, Dom.le x y → Dom.le (f x) (f y) :=
  fun _ _ hxy => h.mono hxy
/-- `Cont.mono` and `Cont.sup_eq` with the `Dom`s taken from the hypothesis (no instance search). -/
theorem Cont.mono' {A : Type w₃} {B : Type w₄} {dA : Dom A} {dB : Dom B} {f : A → B} (h : @Cont A B dA dB f)
    {x y : A} (hxy : @Dom.le A dA x y) : @Dom.le B dB (f x) (f y) :=
  @Continuous.mono A B dA.po dB.po dA.os dB.os f h x y hxy
theorem Cont.sup_eq' {A : Type w₃} {B : Type w₄} {dA : Dom A} {dB : Dom B} {f : A → B} (h : @Cont A B dA dB f)
    (c : @Dom.Chain A dA) :
    f (@Dom.sup A dA c) = @Dom.sup B dB (@Chain.map A B dA.po dB.po c f (@Continuous.mono A B dA.po dB.po dA.os dB.os f h)) :=
  @Continuous.sup_eq A B dA.po dB.po dA.os dB.os f h c

theorem Cont.comp' {A : Type w₁} {B : Type w₂} {C : Type w₃} {dA : Dom A} {dB : Dom B} {dC : Dom C}
    {g : B → C} {f : A → B} (hg : @Cont B C dB dC g) (hf : @Cont A B dA dB f) : @Cont A C dA dC (fun a => g (f a)) :=
  @Continuous.comp A B C dA.po dB.po dC.po dA.os dB.os dC.os g f hg hf
theorem Cont.const' {A : Type w₁} {B : Type w₂} {dA : Dom A} {dB : Dom B} (b : B) : @Cont A B dA dB (fun _ => b) :=
  @Continuous.const A B dA.po dB.po dA.os dB.os b
theorem Cont.congr' {A : Type w₁} {B : Type w₂} {dA : Dom A} {dB : Dom B} {f g : A → B} (hf : @Cont A B dA dB f)
    (h : ∀ a, f a = g a) : @Cont A B dA dB g := by
  have : f = g := funext h
  subst this; exact hf

theorem Cont.supChain' {D : Type w₁} {B : Type w₂} {dD : Dom D} {dB : Dom B} {g : Nat → D → B}
    (hg : ∀ n, @Cont D B dD dB (g n)) (hstep : ∀ n d, @Dom.le B dB (g n d) (g (n + 1) d)) :
    @Cont D B dD dB (fun d => @Dom.sup B dB (@Chain.mk B dB.po (fun n => g n d) (fun n => hstep n d))) := by
  refine @Continuous.of_le D B dD.po dB.po dD.os dB.os _ (fun x y hxy => ?_) (fun c => ?_)
  · exact @Dom.sup_le B dB _ _ fun n => @Dom.le_trans B dB _ _ _ (Cont.mono' (hg n) hxy)
      (@Dom.le_sup B dB (@Chain.mk B dB.po (fun n => g n y) (fun n => hstep n y)) n)
  · apply @Dom.sup_le B dB
    intro n
    show @Dom.le B dB (g n (@Dom.sup D dD c)) _
    rw [Cont.sup_eq' (hg n) c]
    apply @Dom.sup_le B dB
    intro m
    refine @Dom.le_trans B dB _ _ _ ?_ (@Dom.le_sup B dB _ m)
    exact @Dom.le_sup B dB (@Chain.mk B dB.po (fun n => g n (c m)) (fun n => hstep n (c m))) n

/-- Build a continuity proof with the `Dom` instances taken from the expected type (no instance search). -/
theorem Cont.mk' {A : Type w₃} {B : Type w₄} {dA : Dom A} {dB : Dom B} (f : A → B)
    (mono : ∀ x y, @Dom.le A dA x y → @Dom.le B dB (f x) (f y))
    (sup : ∀ c : @Dom.Chain A dA, f (@Dom.sup A dA c) = @Dom.sup B dB (@Chain.map A B dA.po dB.po c f mono)) :
    @Cont A B dA dB f :=
  @Continuous.mk A B dA.po dB.po dA.os dB.os f mono sup

theorem Dom.step {A : Type w₄} [Dom A] (c : Dom.Chain A) (n : Nat) : Dom.le (c n) (c (n + 1)) :=
  @Chain.step A Dom.po c n
theorem Dom.step' {A : Type w₄} {d : Dom A} (c : @Dom.Chain A d) (n : Nat) : @Dom.le A d (c n) (c (n + 1)) :=
  @Chain.step A d.po c n
/-- A chain, with the `Dom` taken from the expected type. -/
def Dom.mkChain {A : Type w₄} {d : Dom A} (f : Nat → A) (h : ∀ n, @Dom.le A d (f n) (f (n + 1))) : @Dom.Chain A d :=
  @Chain.mk A d.po f h
theorem Dom.chain_le {A : Type w₄} [Dom A] (c : Dom.Chain A) {n m : Nat} (h : n ≤ m) : Dom.le (c n) (c m) :=
  @Chain.le A Dom.po c n m h
theorem Dom.chain_le' {A : Type w₄} {d : Dom A} (c : @Dom.Chain A d) {n m : Nat} (h : n ≤ m) : @Dom.le A d (c n) (c m) :=
  @Chain.le A d.po c n m h

theorem Cont.sup_eq {f : D → B} (h : Cont f) (c : Dom.Chain D) :
    f (Dom.sup c) = Dom.sup (@Chain.map D B Dom.po Dom.po c f (@Continuous.mono D B Dom.po Dom.po Dom.os Dom.os f h)) :=
  @Continuous.sup_eq D B Dom.po Dom.po Dom.os Dom.os f h c

theorem Model.Cont.const (b : B) : Cont (fun _ : D => b) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder B)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup B)
  Continuous.const b

theorem Model.Cont.id : Cont (fun d : D => d) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.os : OmegaSup D)
  Continuous.id

theorem Cont.comp {g : B → C} {f : D → B} (hg : Cont g) (hf : Cont f) : Cont (fun d => g (f d)) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder B); letI := (Dom.po : PartialOrder C)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup B); letI := (Dom.os : OmegaSup C)
  Continuous.comp hg hf

theorem Cont.congr {f g : D → B} (hf : Cont f) (h : ∀ d, f d = g d) : Cont g := by
  have : f = g := funext h
  subst this; exact hf

theorem Model.Cont.lam {T : Type w₃} {B : T → Type w₄} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.os : OmegaSup D)
  letI : ∀ t, PartialOrder (B t) := fun _ => Dom.po; letI : ∀ t, OmegaSup (B t) := fun _ => Dom.os
  Continuous.pi_lam h

theorem Model.Cont.app {T : Type w₃} {B : T → Type w₄} [∀ t, Dom (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.os : OmegaSup D)
  letI : ∀ t, PartialOrder (B t) := fun _ => Dom.po; letI : ∀ t, OmegaSup (B t) := fun _ => Dom.os
  Continuous.pi_app hf t

theorem Model.Cont.pair {f : D → A} {g : D → B} (hf : Cont f) (hg : Cont g) : Cont (fun d => (f d, g d)) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder A); letI := (Dom.po : PartialOrder B)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup A); letI := (Dom.os : OmegaSup B)
  Continuous.prod_mk hf hg

theorem Model.Cont.fst {f : D → A × B} (hf : Cont f) : Cont (fun d => (f d).1) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder A); letI := (Dom.po : PartialOrder B)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup A); letI := (Dom.os : OmegaSup B)
  Continuous.prod_fst hf

theorem Model.Cont.snd {f : D → A × B} (hf : Cont f) : Cont (fun d => (f d).2) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder A); letI := (Dom.po : PartialOrder B)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup A); letI := (Dom.os : OmegaSup B)
  Continuous.prod_snd hf

/-- Joint continuity from separate continuity. -/
theorem Cont.uncurry {f : D → A → B} (h₁ : ∀ a, Cont (fun d => f d a)) (h₂ : ∀ d, Cont (f d)) :
    Cont (fun p : D × A => f p.1 p.2) :=
  letI := (Dom.po : PartialOrder D); letI := (Dom.po : PartialOrder A); letI := (Dom.po : PartialOrder B)
  letI := (Dom.os : OmegaSup D); letI := (Dom.os : OmegaSup A); letI := (Dom.os : OmegaSup B)
  Continuous.of_separate h₁ h₂

theorem Model.Cont.app₂ {f : D → A → B} {a : D → A} (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) :
    Cont (fun d => f d (a d)) :=
  Cont.comp (Cont.uncurry (fun x => Cont.app hf x) hc) (Cont.pair Cont.id ha)

theorem Model.Cont.ite (c : Prop) [Decidable c] {t e : D → B} (ht : Cont t) (he : Cont e) :
    Cont (fun d => if c then t d else e d) := by
  by_cases h : c
  · simp only [h, ite_true]; exact ht
  · simp only [h, ite_false]; exact he

theorem Model.Cont.dite (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) := by
  by_cases h : c
  · simp only [h, dite_true]; exact ht h
  · simp only [h, dite_false]; exact he h

/-- `PProd` -/
theorem Model.Cont.ppair {f : D → A} {g : D → B} (hf : Cont f) (hg : Cont g) :
    Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := by
  letDom D, A, B, (A ×' B)
  refine ⟨fun x y h => ⟨hf.mono h, hg.mono h⟩, fun c => ?_⟩
  show (⟨f (OmegaSup.sup c), g (OmegaSup.sup c)⟩ : A ×' B) = ⟨_, _⟩
  rw [hf.sup_eq c, hg.sup_eq c]; rfl

theorem Model.Cont.pfst {f : D → A ×' B} (hf : Cont f) : Cont (fun d => (f d).1) := by
  letDom D, A, B, (A ×' B)
  refine ⟨fun x y h => (hf.mono h).1, fun c => ?_⟩
  show (f (OmegaSup.sup c)).1 = _
  rw [hf.sup_eq c]; rfl

theorem Model.Cont.psnd {f : D → A ×' B} (hf : Cont f) : Cont (fun d => (f d).2) := by
  letDom D, A, B, (A ×' B)
  refine ⟨fun x y h => (hf.mono h).2, fun c => ?_⟩
  show (f (OmegaSup.sup c)).2 = _
  rw [hf.sup_eq c]; rfl

/-- Joint continuity through `×` and through `×'` are interchangeable. -/
theorem Cont.toPProd {g : A → B → C} (h : Cont (fun p : A × B => g p.1 p.2)) : Cont (fun p : A ×' B => g p.1 p.2) :=
  Cont.congr (Cont.comp (g := fun p : A × B => g p.1 p.2) (f := fun p : A ×' B => (p.1, p.2)) h
    (Cont.pair (Cont.pfst Cont.id) (Cont.psnd Cont.id))) (fun _ => rfl)
theorem Cont.ofPProd {g : A → B → C} (h : Cont (fun p : A ×' B => g p.1 p.2)) : Cont (fun p : A × B => g p.1 p.2) :=
  Cont.congr (Cont.comp (g := fun p : A ×' B => g p.1 p.2) (f := fun p : A × B => ⟨p.1, p.2⟩) h
    (Cont.ppair (Cont.fst Cont.id) (Cont.snd Cont.id))) (fun _ => rfl)

omit [Dom A] in
/-- Every function out of a discrete type is continuous. -/
theorem Cont.ofDiscrete (f : A → B) : @Cont A B (Dom.discrete A) _ f := by
  letI dA : Dom A := Dom.discrete A
  letI := (dA.po : PartialOrder A); letI := (dA.os : OmegaSup A)
  letDom B
  refine ⟨fun x y h => h ▸ PartialOrder.rel_refl, fun c => ?_⟩
  have hc : ∀ n, c n = c 0 := fun n => OmegaSup.le_sup c n
  apply PartialOrder.rel_antisymm
  · exact OmegaSup.le_sup (c.map f _) 0
  · exact OmegaSup.sup_le _ _ (fun n => by show f (c n) ⊑ f (c 0); rw [hc n])

/-- The supremum of a chain of continuous functions is continuous. -/
theorem Cont.supChain {g : Nat → D → B} (hg : ∀ n, Cont (g n)) (hstep : ∀ n d, Dom.le (g n d) (g (n + 1) d)) :
    Cont (fun d => Dom.sup (A := B) (@Chain.mk B Dom.po (fun n => g n d) (fun n => hstep n d))) := by
  refine @Continuous.of_le D B Dom.po Dom.po Dom.os Dom.os _ (fun x y hxy => ?_) (fun c => ?_)
  · exact Dom.sup_le _ _ fun n => Dom.le_trans ((hg n).mono hxy)
      (Dom.le_sup (@Chain.mk B Dom.po (fun n => g n y) (fun n => hstep n y)) n)
  · apply Dom.sup_le
    intro n
    show Dom.le (g n (Dom.sup c)) _
    rw [(hg n).sup_eq c]
    apply Dom.sup_le
    intro m
    refine Dom.le_trans ?_ (Dom.le_sup _ m)
    exact Dom.le_sup (@Chain.mk B Dom.po (fun n => g n (c m)) (fun n => hstep n (c m))) n
theorem Cont.puncurry {f : D → A → B} (h₁ : ∀ a, Cont (fun d => f d a)) (h₂ : ∀ d, Cont (f d)) :
    Cont (fun p : D ×' A => f p.1 p.2) :=
  Cont.toPProd (Cont.uncurry h₁ h₂)
end Lemmas

/-! ## Least elements -/

theorem Pointed.unit : Pointed PUnit.{w+1} := ⟨⟨PUnit.unit, fun _ => trivial⟩⟩
attribute [local instance] Pointed.unit
theorem Pointed.prod (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] [Pointed A] [Pointed B] : Pointed (A × B) :=
  let ⟨a, ha⟩ := Pointed.exists_bot (A := A); let ⟨b, hb⟩ := Pointed.exists_bot (A := B)
  ⟨⟨(a, b), fun x => ⟨ha x.1, hb x.2⟩⟩⟩
attribute [local instance] Pointed.prod
theorem Pointed.pprod (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] [Pointed A] [Pointed B] : Pointed (A ×' B) :=
  let ⟨a, ha⟩ := Pointed.exists_bot (A := A); let ⟨b, hb⟩ := Pointed.exists_bot (A := B)
  ⟨⟨⟨a, b⟩, fun x => ⟨ha x.1, hb x.2⟩⟩⟩
attribute [local instance] Pointed.pprod
theorem Pointed.pi (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] [∀ t, Pointed (B t)] :
    Pointed ((t : T) → B t) :=
  ⟨⟨fun t => Classical.choose (Pointed.exists_bot (A := B t)),
    fun f t => Classical.choose_spec (Pointed.exists_bot (A := B t)) (f t)⟩⟩
attribute [local instance] Pointed.pi
theorem Pointed.ofCCPO (A : Type w) [CCPO A] : @Pointed A (Dom.ofCCPO A) :=
  letI : Dom A := Dom.ofCCPO A
  ⟨⟨Lean.Order.bot, fun x => Lean.Order.bot_le x⟩⟩
attribute [local instance] Pointed.ofCCPO
theorem Pointed.monad {M : Type u → Type u} [∀ α, CCPO (M α)] [NonPosMonad M] (α : Type u) : Pointed (M α) :=
  Pointed.ofCCPO (M α)
attribute [local instance] Pointed.monad

/-- The least element of a pointed admissible type. -/
def Dom.bot (A : Type w) [Dom A] [Pointed A] : A := Classical.choose (Pointed.exists_bot (A := A))
theorem Dom.bot_le {A : Type w} [Dom A] [Pointed A] (x : A) : Dom.le (Dom.bot A) x :=
  Classical.choose_spec (Pointed.exists_bot (A := A)) x

/-! ## Fixpoints -/

section Fix
variable {D : Type w} {A : Type w₁} [Dom D] [Dom A] [Pointed A]

/-- `f` iterated `n` times. -/
def Dom.iterate (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => f (Dom.iterate f n a)

/-- The iterates of `f` from the least element. -/
def Dom.iter (f : A → A) (hf : ∀ x y, Dom.le x y → Dom.le (f x) (f y)) : Dom.Chain A :=
  @Chain.mk A Dom.po (fun n => Dom.iterate f n (Dom.bot A)) fun n => by
    induction n with
    | zero => exact Dom.bot_le _
    | succ n ih => exact hf _ _ ih

theorem Dom.iter_succ (f : A → A) (hf) (n : Nat) : Dom.iter f hf (n + 1) = f (Dom.iter f hf n) := rfl

/-- Iterating a jointly continuous family, with the parameter varying, and taking suprema is continuous. -/
theorem Cont.iterSup {f : D → A → A} (hf : Cont (fun p : D × A => f p.1 p.2)) (hc : ∀ d, Cont (f d)) :
    Cont (fun d => Dom.sup (A := A) (Dom.iter (f d) (hc d).monoFn)) := by
  have hn : ∀ n, Cont (fun d => (Dom.iter (f d) (hc d).monoFn : Dom.Chain A) n) := by
    intro n
    induction n with
    | zero => exact Cont.const _
    | succ n ih =>
      refine Cont.congr (Cont.comp hf (Cont.pair Cont.id ih)) fun d => ?_
      exact (Dom.iter_succ (f d) _ n).symm
  exact Cont.supChain (g := fun n d => (Dom.iter (f d) (hc d).monoFn : Dom.Chain A) n) hn
    (fun n d => Dom.step (Dom.iter (f d) (hc d).monoFn) n)

end Fix

/-! ## `partial_fixpoint`'s fixpoints -/

section LeanFix
variable {D : Type w} {A : Type w₁} [Dom D] [Dom A] [CCPO A] [FixCompat A]

theorem FixCompat.le_iff' {x y : A} : Dom.le x y ↔ x ⊑ y := FixCompat.le_iff x y

/-- A continuous map between types whose `Dom` and `CCPO` agree is monotone for the `CCPO`s (the
`monotonicity` obligation of `partial_fixpoint`). -/
theorem Model.Cont.toMonotone {B : Type w} [Dom B] [CCPO B] [FixCompat B] {f : A → B} (h : Cont f) :
    Lean.Order.monotone f :=
  fun _ _ hxy => FixCompat.le_iff'.1 (h.mono (FixCompat.le_iff'.2 hxy))

theorem FixCompat.pointed : Pointed A :=
  ⟨⟨Lean.Order.bot, fun x => FixCompat.le_iff'.2 (Lean.Order.bot_le x)⟩⟩
attribute [local instance] FixCompat.pointed

/-- A supremum for `Dom` is a supremum for the `CCPO`. -/
theorem FixCompat.sup_eq_csup (c : Dom.Chain A) (hc : chain (fun x => ∃ n, c n = x)) :
    Dom.sup c = CCPO.csup hc := by
  apply is_sup_unique (c := fun x => ∃ n, c n = x)
  · intro x
    constructor
    · rintro h _ ⟨n, rfl⟩
      exact PartialOrder.rel_trans (FixCompat.le_iff'.1 (Dom.le_sup c n)) h
    · intro h
      exact FixCompat.le_iff'.1 (Dom.sup_le c x fun n => FixCompat.le_iff'.2 (h _ ⟨n, rfl⟩))
  · exact CCPO.csup_spec hc

/-- A continuous function's least fixpoint is the supremum of its iterates. -/
theorem fix_eq_iterSup (f : A → A) (hm : monotone f) (hc : Cont f) :
    fix f hm = Dom.sup (A := A) (Dom.iter f hc.monoFn) := by
  apply PartialOrder.rel_antisymm
  · -- `fix f ⊑ S` since `S` is a prefixpoint
    have hpre : f (Dom.sup (A := A) (Dom.iter f hc.monoFn)) ⊑ Dom.sup (A := A) (Dom.iter f hc.monoFn) := by
      rw [hc.sup_eq]
      apply FixCompat.le_iff'.1
      apply Dom.sup_le
      intro n
      exact Dom.le_sup (Dom.iter f hc.monoFn) (n + 1)
    apply fix_induct hm (fun x => x ⊑ Dom.sup (A := A) (Dom.iter f hc.monoFn))
    · intro c hchain h
      exact csup_le hchain h
    · intro x hx
      exact PartialOrder.rel_trans (hm _ _ hx) hpre
  · apply FixCompat.le_iff'.1
    apply Dom.sup_le
    intro n
    apply FixCompat.le_iff'.2
    induction n with
    | zero => exact FixCompat.le_iff'.1 (Dom.bot_le _)
    | succ n ih =>
      rw [Dom.iter_succ, fix_eq hm]
      exact hm _ _ ih

theorem Model.Cont.fix {f : D → A → A} {hm : ∀ d, monotone (f d)} (hf : Cont (fun p : D × A => f p.1 p.2)) :
    Cont (fun d => Lean.Order.fix (f d) (hm d)) := by
  have hc : ∀ d, Cont (f d) := fun d =>
    Cont.congr (Cont.comp (g := fun p : D × A => f p.1 p.2) (f := fun a => (d, a)) hf
      (Cont.pair (Cont.const d) Cont.id)) (fun _ => rfl)
  exact Cont.congr (Cont.iterSup hf hc) (fun d => (fix_eq_iterSup (f d) (hm d) (hc d)).symm)
end LeanFix

/-! ### `FixCompat` instances -/

theorem FixCompat.ofCCPO (A : Type w) [CCPO A] : @FixCompat A (Dom.ofCCPO A) _ :=
  letI : Dom A := Dom.ofCCPO A
  ⟨fun _ _ => Iff.rfl⟩
attribute [local instance] FixCompat.ofCCPO
theorem FixCompat.monad {M : Type u → Type u} [∀ α, CCPO (M α)] [NonPosMonad M] (α : Type u) :
    FixCompat (M α) := FixCompat.ofCCPO (M α)
attribute [local instance] FixCompat.monad
theorem FixCompat.pi {T : Type w₁} {B : T → Type w₂} [∀ t, Dom (B t)] [∀ t, CCPO (B t)] [∀ t, FixCompat (B t)] :
    FixCompat ((t : T) → B t) :=
  ⟨fun f g => forall_congr' fun t => FixCompat.le_iff (f t) (g t)⟩
attribute [local instance] FixCompat.pi
theorem FixCompat.prod {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [CCPO A] [CCPO B] [FixCompat A] [FixCompat B] :
    FixCompat (A × B) :=
  ⟨fun x y => and_congr (FixCompat.le_iff x.1 y.1) (FixCompat.le_iff x.2 y.2)⟩
attribute [local instance] FixCompat.prod
theorem FixCompat.pprod {A : Type w₁} {B : Type w₂} [Dom A] [Dom B] [CCPO A] [CCPO B] [FixCompat A] [FixCompat B] :
    FixCompat (A ×' B) :=
  ⟨fun x y => and_congr (FixCompat.le_iff x.1 y.1) (FixCompat.le_iff x.2 y.2)⟩
attribute [local instance] FixCompat.pprod

/-! ## Monads: `pure` and `bind` -/

section Monad
variable {D : Type w} [Dom D] {M : Type u → Type u} [∀ α, CCPO (M α)] [NonPosMonad M]

theorem Model.Cont.pure {α : Type u} {a : D → α} (ha : @Cont D α _ (Dom.discrete α) a) :
    Cont (fun d => (pure (a d) : M α)) :=
  @Cont.comp D α (M α) _ (Dom.discrete α) _ _ _ (Cont.ofDiscrete (fun a : α => (Pure.pure a : M α))) ha

theorem Model.Cont.bind {α β : Type u} {m : D → M α} {k : D → α → M β} (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) :
    Cont (fun d => m d >>= k d) :=
  Cont.comp NonPosMonad.bind_cont (Cont.ppair hm (Cont.lam hk))
end Monad

end
end NonPos
