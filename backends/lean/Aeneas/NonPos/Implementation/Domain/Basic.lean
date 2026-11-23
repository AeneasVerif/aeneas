module
public import Lean

@[expose] public section

/-!
# Domain theory: foundations

This file introduces the basic notions of (ω-)domain theory that we use to give a model to
Rust traits which do not satisfy Lean's positivity condition (typically: traits with a method
which takes another implementation of the same trait as argument, such as `Iterator::zip`).

We work with the `Lean.Order.PartialOrder` class (the one used by `partial_fixpoint`), so that
the `Result` monad, which already comes with such an order, can be reused directly.

The main definitions are:
- `Chain α`: increasing ω-chains;
- `OmegaComplete α`: pointed partial orders with suprema of ω-chains;
- `Continuous f`: monotone functions preserving ω-chain suprema (Scott continuity);
- `Domain`: a bundled ω-complete pointed partial order;
- `ContinuousMap A B`: bundled continuous functions between domains;
- the pointwise structure on dependent products, binary products and function spaces.

See `NonPos.Domain.Limit` for the inverse limit construction and `NonPos.Domain.Operator` for
the resolution of recursive domain equations.
-/

namespace NonPos.Domain

open Lean.Order

universe u v w x

/-! ## Chains -/

/-- An increasing ω-chain. -/
structure Chain (α : Type u) [PartialOrder α] where
  val : Nat → α
  step : ∀ n, val n ⊑ val (n + 1)

instance [PartialOrder α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.val⟩

@[ext] theorem Chain.ext [PartialOrder α] {c d : Chain α} (h : ∀ n, c n = d n) : c = d := by
  cases c
  cases d
  cases funext h
  rfl

theorem Chain.le [PartialOrder α] (c : Chain α) {n m : Nat} (h : n ≤ m) : c n ⊑ c m := by
  induction h with
  | refl => exact PartialOrder.rel_refl
  | step h ih => exact PartialOrder.rel_trans ih (c.step _)

def Chain.const [PartialOrder α] (x : α) : Chain α :=
  ⟨fun _ => x, fun _ => PartialOrder.rel_refl⟩

@[simp] theorem Chain.const_apply [PartialOrder α] (x : α) (n : Nat) : Chain.const x n = x := rfl

def Chain.map [PartialOrder α] [PartialOrder β] (c : Chain α)
    (f : α → β) (mono : monotone f) : Chain β :=
  ⟨fun n => f (c n), fun n => mono _ _ (c.step n)⟩

@[simp] theorem Chain.map_apply [PartialOrder α] [PartialOrder β] (c : Chain α)
    (f : α → β) (mono : monotone f) (n : Nat) : c.map f mono n = f (c n) := rfl

/-- Drop the first `k` elements of a chain. -/
def Chain.drop [PartialOrder α] (c : Chain α) (k : Nat) : Chain α :=
  ⟨fun n => c (k + n), fun n => c.step (k + n)⟩

@[simp] theorem Chain.drop_apply [PartialOrder α] (c : Chain α) (k n : Nat) :
    c.drop k n = c (k + n) := rfl

instance [PartialOrder α] : PartialOrder (Chain α) where
  rel c d := ∀ n, c n ⊑ d n
  rel_refl _ := PartialOrder.rel_refl
  rel_trans h₁ h₂ n := PartialOrder.rel_trans (h₁ n) (h₂ n)
  rel_antisymm h₁ h₂ := Chain.ext (fun n => PartialOrder.rel_antisymm (h₁ n) (h₂ n))

/-! ## ω-complete pointed partial orders -/

/-- A partial order with suprema of increasing ω-chains. -/
class OmegaSup (α : Type u) [PartialOrder α] where
  sup : Chain α → α
  le_sup : ∀ c n, c n ⊑ sup c
  sup_le : ∀ c x, (∀ n, c n ⊑ x) → sup c ⊑ x

/-- A pointed partial order with suprema of increasing ω-chains. -/
class OmegaComplete (α : Type u) [PartialOrder α] extends OmegaSup α where
  bottom : α
  bottom_le : ∀ x, bottom ⊑ x

section OmegaComplete

variable {α : Type u} [PartialOrder α] [OmegaSup α]

open OmegaComplete OmegaSup

theorem sup_mono (c d : Chain α) (h : ∀ n, c n ⊑ d n) : sup c ⊑ sup d :=
  sup_le c _ (fun n => PartialOrder.rel_trans (h n) (le_sup d n))

theorem sup_const (x : α) : sup (Chain.const x) = x :=
  PartialOrder.rel_antisymm
    (sup_le _ _ (fun _ => PartialOrder.rel_refl)) (le_sup (Chain.const x) 0)

theorem sup_congr {c d : Chain α} (h : ∀ n, c n = d n) : sup c = sup d :=
  congrArg sup (Chain.ext h)

/-- The supremum of a chain does not change when dropping a prefix. -/
theorem sup_drop (c : Chain α) (k : Nat) : sup (c.drop k) = sup c := by
  apply PartialOrder.rel_antisymm
  · exact OmegaSup.sup_le _ _ (fun n => le_sup c (k + n))
  · exact OmegaSup.sup_le _ _
      (fun n => PartialOrder.rel_trans (c.le (Nat.le_add_left n k)) (le_sup (c.drop k) n))

def Chain.transpose (c : Chain (Chain α)) : Chain (Chain α) where
  val m := ⟨fun n => c n m, fun n => c.step n m⟩
  step m n := (c n).step m

def Chain.sups (c : Chain (Chain α)) : Chain α :=
  ⟨fun n => sup (c n), fun n => sup_mono _ _ (c.step n)⟩

theorem sup_swap (c : Chain (Chain α)) : sup c.sups = sup c.transpose.sups := by
  apply PartialOrder.rel_antisymm
  · apply OmegaSup.sup_le
    intro n
    apply OmegaSup.sup_le
    intro m
    exact PartialOrder.rel_trans (le_sup (c.transpose m) n) (le_sup c.transpose.sups m)
  · apply OmegaSup.sup_le
    intro m
    apply OmegaSup.sup_le
    intro n
    exact PartialOrder.rel_trans (le_sup (c n) m) (le_sup c.sups n)

def Chain.diagonal (c : Chain (Chain α)) : Chain α where
  val n := c n n
  step n := PartialOrder.rel_trans (c.step n n) ((c (n + 1)).step n)

theorem sup_diagonal (c : Chain (Chain α)) : sup c.sups = sup c.diagonal := by
  apply PartialOrder.rel_antisymm
  · apply OmegaSup.sup_le
    intro n
    apply OmegaSup.sup_le
    intro m
    have first : c n m ⊑ c (max n m) m := c.le (by omega) m
    have second : c (max n m) m ⊑ c (max n m) (max n m) := (c (max n m)).le (by omega)
    exact PartialOrder.rel_trans (PartialOrder.rel_trans first second)
      (le_sup c.diagonal (max n m))
  · apply OmegaSup.sup_le
    intro n
    exact PartialOrder.rel_trans (le_sup (c n) n) (le_sup c.sups n)

/-- A supremum which is reached by an element of the chain. -/
theorem sup_eq_of_attained (c : Chain α) (n : Nat) (h : ∀ m, c m ⊑ c n) : sup c = c n :=
  PartialOrder.rel_antisymm (sup_le c _ h) (le_sup c n)

end OmegaComplete

/-! ## Continuity -/

/-- Scott continuity: a monotone function which preserves suprema of ω-chains. -/
structure Continuous {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]
    [OmegaSup α] [OmegaSup β] (f : α → β) : Prop where
  mono : monotone f
  sup_eq : ∀ c : Chain α, f (OmegaSup.sup c) = OmegaSup.sup (c.map f mono)

section Continuous

open OmegaComplete OmegaSup

variable {α : Type u} {β : Type v} {γ : Type w}
  [PartialOrder α] [PartialOrder β] [PartialOrder γ]
  [OmegaSup α] [OmegaSup β] [OmegaSup γ]

/-- In order to prove continuity it suffices to prove monotonicity and the `⊑` direction. -/
theorem Continuous.of_le {f : α → β} (mono : monotone f)
    (h : ∀ c : Chain α, f (sup c) ⊑ sup (c.map f mono)) : Continuous f :=
  ⟨mono, fun c => PartialOrder.rel_antisymm (h c)
    (sup_le _ _ (fun n => mono _ _ (le_sup c n)))⟩

theorem Continuous.sup_eq' {f : α → β} (hf : Continuous f) (c : Chain α) (d : Chain β)
    (hd : ∀ n, d n = f (c n)) : f (sup c) = sup d := by
  rw [hf.sup_eq]
  exact sup_congr (fun n => (hd n).symm)

theorem Continuous.const (x : β) : Continuous (fun (_ : α) => x) :=
  ⟨monotone_const x, fun _ => (sup_const x).symm⟩

theorem Continuous.id : Continuous (fun (x : α) => x) :=
  ⟨monotone_id, fun _ => rfl⟩

theorem Continuous.comp {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) :=
  ⟨monotone_compose hf.mono hg.mono, fun c => by rw [hf.sup_eq, hg.sup_eq]; rfl⟩

/-- Functions which do not depend on their input are continuous. -/
theorem Continuous.of_independent (f : α → β) (independent : ∀ a b, f a = f b) :
    Continuous f := by
  refine ⟨fun a b _ => PartialOrder.rel_of_eq (independent a b), fun c => ?_⟩
  rw [← sup_const (f (sup c))]
  exact congrArg sup (Chain.ext (fun n => independent _ _))

theorem Continuous.congr {f g : α → β} (hf : Continuous f) (h : ∀ x, f x = g x) : Continuous g := by
  have : f = g := funext h
  subst this
  exact hf

end Continuous

/-! ## Chain completeness

Suprema of arbitrary nonempty chains (chains as in `Lean.Order.chain`: totally ordered sets), with
`is_sup` from Lean core.  Continuity (`Continuous`) stays about ω-chains; chain completeness is only
used to give dictionaries the `CCPO` that `partial_fixpoint` needs. -/

/-- Every nonempty chain has a supremum. -/
class ChainComplete (α : Type u) [PartialOrder α] : Prop where
  has_sup : ∀ c : α → Prop, chain c → (∃ x, c x) → ∃ s, is_sup c s

/-- The image of a set under a function. -/
def image {α : Type u} {β : Type v} (f : α → β) (c : α → Prop) : β → Prop := fun y => ∃ x, c x ∧ f x = y

theorem image_nonempty {α : Type u} {β : Type v} (f : α → β) {c : α → Prop} (h : ∃ x, c x) : ∃ y, image f c y :=
  let ⟨x, hx⟩ := h; ⟨f x, x, hx, rfl⟩

section ChainComplete

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

theorem chain_image {f : α → β} (hf : monotone f) {c : α → Prop} (hc : chain c) : chain (image f c) := by
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  rcases hc x y hx hy with h | h
  · exact Or.inl (hf _ _ h)
  · exact Or.inr (hf _ _ h)


theorem isSup_le {c : α → Prop} {s : α} (h : is_sup c s) {x : α} (hx : c x) : x ⊑ s :=
  (h s).mp PartialOrder.rel_refl x hx

theorem isSup_le_of {c : α → Prop} {s u : α} (h : is_sup c s) (hu : ∀ x, c x → x ⊑ u) : s ⊑ u :=
  (h u).mpr hu

theorem isSup_of {c : α → Prop} {s : α} (h₁ : ∀ x, c x → x ⊑ s) (h₂ : ∀ u, (∀ x, c x → x ⊑ u) → s ⊑ u) :
    is_sup c s :=
  fun u => ⟨fun hs x hx => PartialOrder.rel_trans (h₁ x hx) hs, h₂ u⟩

/-- A supremum of a chain is also the supremum of the part of the chain above any of its elements. -/
theorem isSup_above {c : α → Prop} (hc : chain c) {s a : α} (ha : c a) (h : is_sup c s) :
    is_sup (fun x => c x ∧ a ⊑ x) s := by
  refine isSup_of (fun x hx => isSup_le h hx.1) (fun u hu => isSup_le_of h fun x hx => ?_)
  rcases hc x a hx ha with hxa | hax
  · exact PartialOrder.rel_trans hxa (hu a ⟨ha, PartialOrder.rel_refl⟩)
  · exact hu x ⟨hx, hax⟩

/-- An order isomorphism maps a supremum to the supremum of the image. -/
theorem isSup_image_iso {f : α → β} {g : β → α} (hf : monotone f) (hg : monotone g)
    (gf : ∀ x, g (f x) = x) (fg : ∀ y, f (g y) = y) {c : α → Prop} {s : α} (h : is_sup c s) :
    is_sup (image f c) (f s) := by
  refine isSup_of (fun _ ⟨x, hx, e⟩ => e ▸ hf _ _ (isSup_le h hx)) (fun u hu => ?_)
  have : s ⊑ g u := isSup_le_of h fun x hx => by
    rw [← gf x]; exact hg _ _ (hu _ ⟨x, hx, rfl⟩)
  rw [← fg u]; exact hf _ _ this

/-- In a chain-complete order, a choice of supremum. -/
noncomputable def chainSup [ChainComplete α] (c : α → Prop) (hc : chain c) (hne : ∃ x, c x) : α :=
  Classical.choose (ChainComplete.has_sup c hc hne)

theorem chainSup_spec [ChainComplete α] (c : α → Prop) (hc : chain c) (hne : ∃ x, c x) :
    is_sup c (chainSup c hc hne) :=
  Classical.choose_spec (ChainComplete.has_sup c hc hne)

end ChainComplete

/-! ## Bundled domains -/

/-- A bundled ω-complete pointed partial order. -/
structure Domain : Type (u + 1) where
  Carrier : Type u
  order : PartialOrder Carrier
  complete : @OmegaComplete Carrier order
  chainComplete : @ChainComplete Carrier order

attribute [instance] Domain.order Domain.complete Domain.chainComplete

instance : CoeSort Domain.{u} (Type u) := ⟨Domain.Carrier⟩

/-- Bundle a type with its instances. -/
abbrev Domain.of (α : Type u) [PartialOrder α] [OmegaComplete α] [ChainComplete α] : Domain.{u} :=
  ⟨α, inferInstance, inferInstance, inferInstance⟩

/-- Bundled continuous maps between domains. -/
structure ContinuousMap (A : Domain.{u}) (B : Domain.{v}) where
  toFun : A → B
  cont : Continuous toFun

instance : CoeFun (ContinuousMap A B) (fun _ => A → B) := ⟨ContinuousMap.toFun⟩

@[ext] theorem ContinuousMap.ext {A : Domain.{u}} {B : Domain.{v}} {f g : ContinuousMap A B}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  cases funext h
  rfl

@[simp] theorem ContinuousMap.mk_apply {A : Domain.{u}} {B : Domain.{v}} (f : A → B)
    (h : Continuous f) (x : A) : ContinuousMap.mk f h x = f x := rfl

theorem ContinuousMap.mono {A : Domain.{u}} {B : Domain.{v}} (f : ContinuousMap A B) :
    monotone f.toFun := f.cont.mono

theorem ContinuousMap.continuous {A : Domain.{u}} {B : Domain.{v}} (f : ContinuousMap A B)
    (c : Chain A) : f (OmegaSup.sup c) = OmegaSup.sup (c.map f f.mono) :=
  f.cont.sup_eq c

def ContinuousMap.id (A : Domain.{u}) : ContinuousMap A A :=
  ⟨fun x => x, Continuous.id⟩

def ContinuousMap.const (A : Domain.{u}) (B : Domain.{v}) (x : B) : ContinuousMap A B :=
  ⟨fun _ => x, Continuous.const x⟩

def ContinuousMap.comp {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (g : ContinuousMap B C) (f : ContinuousMap A B) : ContinuousMap A C :=
  ⟨fun x => g (f x), g.cont.comp f.cont⟩

@[simp] theorem ContinuousMap.comp_apply {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (g : ContinuousMap B C) (f : ContinuousMap A B) (x : A) : g.comp f x = g (f x) := rfl

@[simp] theorem ContinuousMap.id_apply {A : Domain.{u}} (x : A) : ContinuousMap.id A x = x := rfl

@[simp] theorem ContinuousMap.const_apply {A : Domain.{u}} {B : Domain.{v}} (y : B) (x : A) :
    ContinuousMap.const A B y x = y := rfl

/-! ## The function space domain -/

section FunctionSpace

open OmegaComplete OmegaSup

variable {A : Domain.{u}} {B : Domain.{v}}

instance : PartialOrder (ContinuousMap A B) where
  rel f g := ∀ x, f x ⊑ g x
  rel_refl _ := PartialOrder.rel_refl
  rel_trans h₁ h₂ x := PartialOrder.rel_trans (h₁ x) (h₂ x)
  rel_antisymm h₁ h₂ :=
    ContinuousMap.ext (fun x => PartialOrder.rel_antisymm (h₁ x) (h₂ x))

theorem ContinuousMap.rel_iff (f g : ContinuousMap A B) : (f ⊑ g) ↔ ∀ x, f x ⊑ g x := Iff.rfl

def ContinuousMap.evalChain (c : Chain (ContinuousMap A B)) (x : A) : Chain B :=
  ⟨fun n => c n x, fun n => c.step n x⟩

@[simp] theorem ContinuousMap.evalChain_apply (c : Chain (ContinuousMap A B)) (x : A) (n : Nat) :
    ContinuousMap.evalChain c x n = c n x := rfl

def ContinuousMap.sup (c : Chain (ContinuousMap A B)) : ContinuousMap A B where
  toFun := fun x => OmegaSup.sup (evalChain c x)
  cont := {
    mono := by
      intro x y h
      exact sup_mono _ _ (fun n => (c n).mono _ _ h)
    sup_eq := fun d => by
      let grid : Chain (Chain B) := {
        val := fun n => d.map (c n) (c n).mono
        step := fun n m => c.step n (d m)
      }
      calc
        OmegaSup.sup (evalChain c (OmegaSup.sup d)) =
            OmegaSup.sup grid.sups := by
          apply sup_congr
          intro n
          exact (c n).continuous d
        _ = OmegaSup.sup grid.transpose.sups := sup_swap grid
        _ = _ := rfl
  }

instance : OmegaComplete (ContinuousMap A B) where
  bottom := ContinuousMap.const A B OmegaComplete.bottom
  bottom_le := fun f x => OmegaComplete.bottom_le (f x)
  sup := ContinuousMap.sup
  le_sup := fun c n x => OmegaSup.le_sup (ContinuousMap.evalChain c x) n
  sup_le := fun c f h x =>
    OmegaSup.sup_le (ContinuousMap.evalChain c x) (f x) (fun n => h n x)

theorem ContinuousMap.sup_apply (c : Chain (ContinuousMap A B)) (x : A) :
    OmegaSup.sup c x = OmegaSup.sup (ContinuousMap.evalChain c x) := rfl

theorem ContinuousMap.bottom_apply (x : A) :
    (OmegaComplete.bottom : ContinuousMap A B) x = OmegaComplete.bottom := rfl

/-- Pointwise suprema of chains of continuous maps are continuous: the supremum over the chain and
the ω-supremum commute, since both are the least upper bound of the same family. -/
instance : ChainComplete (ContinuousMap A B) := by
  refine ⟨fun c hc hne => ?_⟩
  let ev (x : A) : B → Prop := image (fun f : ContinuousMap A B => f x) c
  have hev (x : A) : chain (ev x) := chain_image (fun _ _ h => (ContinuousMap.rel_iff _ _).1 h x) hc
  have hne' (x : A) : ∃ y, ev x y := image_nonempty _ hne
  let s (x : A) : B := chainSup (ev x) (hev x) (hne' x)
  have hs (x : A) : is_sup (ev x) (s x) := chainSup_spec _ _ _
  have smono : monotone s := fun x y hxy =>
    isSup_le_of (hs x) fun _ ⟨f, hf, e⟩ => e ▸ PartialOrder.rel_trans (f.mono _ _ hxy) (isSup_le (hs y) ⟨f, hf, rfl⟩)
  have scont : Continuous s := by
    refine Continuous.of_le smono (fun d => isSup_le_of (hs _) fun _ ⟨f, hf, e⟩ => ?_)
    subst e
    show f (sup d) ⊑ _
    rw [f.continuous d]
    exact sup_mono _ _ (fun n => isSup_le (hs (d n)) ⟨f, hf, rfl⟩)
  refine ⟨⟨s, scont⟩, isSup_of (fun f hf x => isSup_le (hs x) ⟨f, hf, rfl⟩) (fun u hu x => ?_)⟩
  exact isSup_le_of (hs x) fun _ ⟨f, hf, e⟩ => e ▸ (ContinuousMap.rel_iff _ _).1 (hu f hf) x

/-- The domain of continuous maps between two domains. -/
abbrev functionSpace (A : Domain.{u}) (B : Domain.{v}) : Domain.{max u v} :=
  Domain.of (ContinuousMap A B)

end FunctionSpace

/-! ## The unit domain -/

instance : PartialOrder PUnit.{u + 1} where
  rel _ _ := True
  rel_refl := True.intro
  rel_trans _ _ := True.intro
  rel_antisymm _ _ := Subsingleton.elim _ _

instance : OmegaComplete PUnit.{u + 1} where
  bottom := PUnit.unit
  bottom_le _ := True.intro
  sup _ := PUnit.unit
  le_sup _ _ := True.intro
  sup_le _ _ _ := True.intro

instance : ChainComplete PUnit.{u + 1} :=
  ⟨fun _ _ _ => ⟨PUnit.unit, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩⟩

abbrev unitDomain : Domain.{u} := Domain.of PUnit.{u + 1}

/-! ## Dependent products -/

section Pi

open OmegaComplete OmegaSup

variable {ι : Type w} {A : ι → Type u} [∀ j, PartialOrder (A j)]

/-- The chain of `j`-th components. -/
def Chain.coord (c : Chain ((j : ι) → A j)) (j : ι) : Chain (A j) :=
  ⟨fun n => c n j, fun n => c.step n j⟩

@[simp] theorem Chain.coord_apply (c : Chain ((j : ι) → A j)) (j : ι) (n : Nat) :
    c.coord j n = c n j := rfl

/-- The pointwise order on functions, applied at a point. -/
theorem rel_apply {f g : (j : ι) → A j} (h : f ⊑ g) (j : ι) : f j ⊑ g j := h j

instance instOmegaSupPi [∀ j, OmegaSup (A j)] : OmegaSup ((j : ι) → A j) where
  sup c j := OmegaSup.sup (c.coord j)
  le_sup c n j := OmegaSup.le_sup (c.coord j) n
  sup_le c f h j := OmegaSup.sup_le (c.coord j) (f j) (fun n => h n j)

instance instOmegaCompletePi [∀ j, OmegaComplete (A j)] : OmegaComplete ((j : ι) → A j) :=
  { instOmegaSupPi with
    bottom := fun _ => OmegaComplete.bottom
    bottom_le := fun f j => OmegaComplete.bottom_le (f j) }

instance instChainCompletePi [∀ j, ChainComplete (A j)] : ChainComplete ((j : ι) → A j) := by
  refine ⟨fun c hc hne => ?_⟩
  have hcj (j : ι) : chain (image (fun f : (j : ι) → A j => f j) c) := chain_image (fun _ _ h => rel_apply h j) hc
  let s (j : ι) : A j := chainSup _ (hcj j) (image_nonempty _ hne)
  have hs (j : ι) : is_sup (image (fun f : (j : ι) → A j => f j) c) (s j) := chainSup_spec _ _ _
  refine ⟨s, isSup_of (fun f hf j => isSup_le (hs j) ⟨f, hf, rfl⟩) (fun u hu j => ?_)⟩
  exact isSup_le_of (hs j) fun _ ⟨f, hf, e⟩ => e ▸ rel_apply (hu f hf) j

/-- In a product of chain-complete orders, a supremum of a nonempty chain is computed pointwise. -/
theorem isSup_pi_apply [∀ j, ChainComplete (A j)] {c : ((j : ι) → A j) → Prop} (hc : chain c)
    (hne : ∃ x, c x) {s : (j : ι) → A j} (h : is_sup c s) (j : ι) :
    is_sup (image (fun f : (j : ι) → A j => f j) c) (s j) := by
  have hcj (j : ι) : chain (image (fun f : (j : ι) → A j => f j) c) := chain_image (fun _ _ h => rel_apply h j) hc
  let s' (j : ι) : A j := chainSup _ (hcj j) (image_nonempty _ hne)
  have hs' (j : ι) : is_sup (image (fun f : (j : ι) → A j => f j) c) (s' j) := chainSup_spec _ _ _
  have hss' : s ⊑ s' := isSup_le_of h fun f hf j => isSup_le (hs' j) ⟨f, hf, rfl⟩
  exact isSup_of (fun _ ⟨f, hf, e⟩ => e ▸ rel_apply (isSup_le h hf) j)
    (fun u hu => PartialOrder.rel_trans (rel_apply hss' j) (isSup_le_of (hs' j) hu))

variable [∀ j, OmegaComplete (A j)]

theorem pi_sup_apply (c : Chain ((j : ι) → A j)) (j : ι) :
    OmegaSup.sup c j = OmegaSup.sup (c.coord j) := rfl

theorem pi_bottom_apply (j : ι) : (OmegaComplete.bottom : (j : ι) → A j) j = OmegaComplete.bottom := rfl

end Pi

/-- The dependent product of a family of domains. -/
abbrev piDomain {ι : Type w} (A : ι → Domain.{u}) : Domain.{max w u} :=
  Domain.of ((j : ι) → A j)

section PiMaps

variable {ι : Type w}

def piCoordinate (A : ι → Domain.{u}) (j : ι) : ContinuousMap (piDomain A) (A j) where
  toFun f := f j
  cont := ⟨fun _ _ related => related j, fun _ => rfl⟩

def piMap {A : Domain.{u}} {B : ι → Domain.{v}}
    (f : ∀ j, ContinuousMap A (B j)) : ContinuousMap A (piDomain B) where
  toFun x j := f j x
  cont := {
    mono := fun x y related j => (f j).mono _ _ related
    sup_eq := fun c => by
      funext j
      exact (f j).continuous c
  }

@[simp] theorem piCoordinate_apply (A : ι → Domain.{u}) (j : ι) (f : piDomain A) :
    piCoordinate A j f = f j := rfl

@[simp] theorem piMap_apply {A : Domain.{u}} {B : ι → Domain.{v}}
    (f : ∀ j, ContinuousMap A (B j)) (x : A) (j : ι) : piMap f x j = f j x := rfl

end PiMaps

/-! ## Binary products -/

section Prod

open OmegaComplete OmegaSup

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

instance instPartialOrderProd : PartialOrder (α × β) where
  rel x y := x.1 ⊑ y.1 ∧ x.2 ⊑ y.2
  rel_refl := ⟨PartialOrder.rel_refl, PartialOrder.rel_refl⟩
  rel_trans h₁ h₂ :=
    ⟨PartialOrder.rel_trans h₁.1 h₂.1, PartialOrder.rel_trans h₁.2 h₂.2⟩
  rel_antisymm h₁ h₂ :=
    Prod.ext (PartialOrder.rel_antisymm h₁.1 h₂.1) (PartialOrder.rel_antisymm h₁.2 h₂.2)

theorem Prod.rel_iff (x y : α × β) : (x ⊑ y) ↔ (x.1 ⊑ y.1 ∧ x.2 ⊑ y.2) := Iff.rfl

def Chain.fst (c : Chain (α × β)) : Chain α := ⟨fun n => (c n).1, fun n => (c.step n).1⟩
def Chain.snd (c : Chain (α × β)) : Chain β := ⟨fun n => (c n).2, fun n => (c.step n).2⟩

@[simp] theorem Chain.fst_apply (c : Chain (α × β)) (n : Nat) : c.fst n = (c n).1 := rfl
@[simp] theorem Chain.snd_apply (c : Chain (α × β)) (n : Nat) : c.snd n = (c n).2 := rfl

instance instOmegaSupProd [OmegaSup α] [OmegaSup β] : OmegaSup (α × β) where
  sup c := (OmegaSup.sup c.fst, OmegaSup.sup c.snd)
  le_sup c n := ⟨OmegaSup.le_sup c.fst n, OmegaSup.le_sup c.snd n⟩
  sup_le c x h :=
    ⟨OmegaSup.sup_le c.fst x.1 (fun n => (h n).1),
      OmegaSup.sup_le c.snd x.2 (fun n => (h n).2)⟩

instance instOmegaCompleteProd [OmegaComplete α] [OmegaComplete β] : OmegaComplete (α × β) :=
  { instOmegaSupProd with
    bottom := (OmegaComplete.bottom, OmegaComplete.bottom)
    bottom_le := fun x => ⟨OmegaComplete.bottom_le x.1, OmegaComplete.bottom_le x.2⟩ }

instance instChainCompleteProd [ChainComplete α] [ChainComplete β] : ChainComplete (α × β) := by
  refine ⟨fun c hc hne => ?_⟩
  have h₁ : chain (image Prod.fst c) := chain_image (fun _ _ h => ((Prod.rel_iff _ _).1 h).1) hc
  have h₂ : chain (image Prod.snd c) := chain_image (fun _ _ h => ((Prod.rel_iff _ _).1 h).2) hc
  have hs₁ := chainSup_spec _ h₁ (image_nonempty _ hne)
  have hs₂ := chainSup_spec _ h₂ (image_nonempty _ hne)
  refine ⟨(chainSup _ h₁ (image_nonempty _ hne), chainSup _ h₂ (image_nonempty _ hne)),
    isSup_of (fun x hx => ⟨isSup_le hs₁ ⟨x, hx, rfl⟩, isSup_le hs₂ ⟨x, hx, rfl⟩⟩) (fun u hu => ⟨?_, ?_⟩)⟩
  · exact isSup_le_of hs₁ fun _ ⟨x, hx, e⟩ => e ▸ ((Prod.rel_iff _ _).1 (hu x hx)).1
  · exact isSup_le_of hs₂ fun _ ⟨x, hx, e⟩ => e ▸ ((Prod.rel_iff _ _).1 (hu x hx)).2

/-- In a product of chain-complete orders, a supremum of a nonempty chain is computed componentwise. -/
theorem isSup_prod [ChainComplete α] [ChainComplete β] {c : α × β → Prop} (hc : chain c) (hne : ∃ x, c x)
    {s : α × β} (h : is_sup c s) : is_sup (image Prod.fst c) s.1 ∧ is_sup (image Prod.snd c) s.2 := by
  have h₁ : chain (image Prod.fst c) := chain_image (fun _ _ h => ((Prod.rel_iff _ _).1 h).1) hc
  have h₂ : chain (image Prod.snd c) := chain_image (fun _ _ h => ((Prod.rel_iff _ _).1 h).2) hc
  have hs₁ := chainSup_spec _ h₁ (image_nonempty _ hne)
  have hs₂ := chainSup_spec _ h₂ (image_nonempty _ hne)
  have hss : s ⊑ (chainSup _ h₁ (image_nonempty _ hne), chainSup _ h₂ (image_nonempty _ hne)) :=
    isSup_le_of h fun x hx => ⟨isSup_le hs₁ ⟨x, hx, rfl⟩, isSup_le hs₂ ⟨x, hx, rfl⟩⟩
  exact ⟨isSup_of (fun _ ⟨x, hx, e⟩ => e ▸ ((Prod.rel_iff _ _).1 (isSup_le h hx)).1)
      (fun u hu => PartialOrder.rel_trans ((Prod.rel_iff _ _).1 hss).1 (isSup_le_of hs₁ hu)),
    isSup_of (fun _ ⟨x, hx, e⟩ => e ▸ ((Prod.rel_iff _ _).1 (isSup_le h hx)).2)
      (fun u hu => PartialOrder.rel_trans ((Prod.rel_iff _ _).1 hss).2 (isSup_le_of hs₂ hu))⟩

variable [OmegaComplete α] [OmegaComplete β]

theorem prod_sup_fst (c : Chain (α × β)) : (OmegaSup.sup c).1 = OmegaSup.sup c.fst := rfl
theorem prod_sup_snd (c : Chain (α × β)) : (OmegaSup.sup c).2 = OmegaSup.sup c.snd := rfl

end Prod

/-- The product of two domains. -/
abbrev prodDomain (A : Domain.{u}) (B : Domain.{v}) : Domain.{max u v} :=
  Domain.of (A × B)

section ProdMaps

def prodFst (A : Domain.{u}) (B : Domain.{v}) : ContinuousMap (prodDomain A B) A where
  toFun x := x.1
  cont := ⟨fun _ _ h => h.1, fun _ => rfl⟩

def prodSnd (A : Domain.{u}) (B : Domain.{v}) : ContinuousMap (prodDomain A B) B where
  toFun x := x.2
  cont := ⟨fun _ _ h => h.2, fun _ => rfl⟩

def prodMap {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (f : ContinuousMap A B) (g : ContinuousMap A C) : ContinuousMap A (prodDomain B C) where
  toFun x := (f x, g x)
  cont := ⟨fun x y h => ⟨f.mono x y h, g.mono x y h⟩,
    fun c => Prod.ext (f.continuous c) (g.continuous c)⟩

@[simp] theorem prodFst_apply (A : Domain.{u}) (B : Domain.{v}) (x : prodDomain A B) :
    prodFst A B x = x.1 := rfl
@[simp] theorem prodSnd_apply (A : Domain.{u}) (B : Domain.{v}) (x : prodDomain A B) :
    prodSnd A B x = x.2 := rfl
@[simp] theorem prodMap_apply {A : Domain.{u}} {B : Domain.{v}} {C : Domain.{w}}
    (f : ContinuousMap A B) (g : ContinuousMap A C) (x : A) : prodMap f g x = (f x, g x) := rfl

end ProdMaps

/-! ## Continuity lemmas

The lemmas below are the building blocks used by the `domain_continuity` tactic (see
`NonPos.Domain.Tactic`). They are stated for arbitrary types with instances (rather than bundled
domains) so that they can be found by unification on the goals generated by the extraction.
-/

section ContinuityLemmas

open OmegaComplete OmegaSup

variable {α : Type u} [PartialOrder α] [OmegaSup α]

/-- A function into a dependent product is continuous iff all its components are. -/
theorem Continuous.pi_lam {ι : Type w} {B : ι → Type v} [∀ j, PartialOrder (B j)]
    [∀ j, OmegaSup (B j)] {f : α → (j : ι) → B j}
    (h : ∀ j, Continuous (fun x => f x j)) : Continuous f where
  mono x y hxy j := (h j).mono x y hxy
  sup_eq c := by
    funext j
    exact (h j).sup_eq c

theorem Continuous.pi_app {ι : Type w} {B : ι → Type v} [∀ j, PartialOrder (B j)]
    [∀ j, OmegaSup (B j)] {f : α → (j : ι) → B j}
    (h : Continuous f) (j : ι) : Continuous (fun x => f x j) where
  mono x y hxy := h.mono x y hxy j
  sup_eq c := congrFun (h.sup_eq c) j

theorem Continuous.pi_iff {ι : Type w} {B : ι → Type v} [∀ j, PartialOrder (B j)]
    [∀ j, OmegaSup (B j)] {f : α → (j : ι) → B j} :
    Continuous f ↔ ∀ j, Continuous (fun x => f x j) :=
  ⟨fun h j => h.pi_app j, Continuous.pi_lam⟩

theorem Continuous.prod_fst {β : Type v} {γ : Type w} [PartialOrder β] [PartialOrder γ]
    [OmegaSup β] [OmegaSup γ] {f : α → β × γ} (h : Continuous f) :
    Continuous (fun x => (f x).1) where
  mono x y hxy := (h.mono x y hxy).1
  sup_eq c := congrArg Prod.fst (h.sup_eq c)

theorem Continuous.prod_snd {β : Type v} {γ : Type w} [PartialOrder β] [PartialOrder γ]
    [OmegaSup β] [OmegaSup γ] {f : α → β × γ} (h : Continuous f) :
    Continuous (fun x => (f x).2) where
  mono x y hxy := (h.mono x y hxy).2
  sup_eq c := congrArg Prod.snd (h.sup_eq c)

theorem Continuous.prod_mk {β : Type v} {γ : Type w} [PartialOrder β] [PartialOrder γ]
    [OmegaSup β] [OmegaSup γ] {f : α → β} {g : α → γ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (f x, g x)) where
  mono x y hxy := ⟨hf.mono x y hxy, hg.mono x y hxy⟩
  sup_eq c := Prod.ext (hf.sup_eq c) (hg.sup_eq c)

/-- Evaluating a continuous map at a point which continuously depends on the input: this is
the general "application" rule (evaluation is jointly continuous). -/
theorem Continuous.cmap_apply {B : Domain.{v}} {C : Domain.{w}}
    {F : α → ContinuousMap B C} {g : α → B}
    (hF : Continuous F) (hg : Continuous g) : Continuous (fun x => F x (g x)) where
  mono x y hxy :=
    PartialOrder.rel_trans (hF.mono x y hxy (g x)) ((F y).mono _ _ (hg.mono x y hxy))
  sup_eq c := by
    rw [hF.sup_eq, hg.sup_eq]
    let grid : Chain (Chain C) := {
      val := fun n => (c.map g hg.mono).map (F (c n)) (F (c n)).mono
      step := fun n m => hF.mono _ _ (c.step n) (g (c m))
    }
    change sup (ContinuousMap.evalChain (c.map F hF.mono) (sup (c.map g hg.mono))) = _
    calc
      sup (ContinuousMap.evalChain (c.map F hF.mono) (sup (c.map g hg.mono))) =
          sup grid.sups := by
        apply sup_congr
        intro n
        exact (F (c n)).continuous (c.map g hg.mono)
      _ = sup grid.diagonal := sup_diagonal grid
      _ = _ := rfl

/-- Building a continuous map whose graph depends continuously on the input. -/
theorem Continuous.cmap_mk {B : Domain.{v}} {C : Domain.{w}}
    {F : α → B → C} (hF : ∀ b, Continuous (fun x => F x b)) (h : ∀ x, Continuous (F x)) :
    Continuous (fun x => (⟨F x, h x⟩ : ContinuousMap B C)) where
  mono x y hxy b := (hF b).mono x y hxy
  sup_eq c := by
    apply ContinuousMap.ext
    intro b
    exact (hF b).sup_eq c

/-- Continuity of a fixed continuous map, applied to a continuous argument. -/
theorem Continuous.cmap_comp {B : Domain.{v}} {C : Domain.{w}} (F : ContinuousMap B C)
    {g : α → B} (hg : Continuous g) : Continuous (fun x => F (g x)) :=
  F.cont.comp hg

/-- The `toFun` of a continuous map is continuous. -/
theorem ContinuousMap.toFun_continuous {B : Domain.{v}} {C : Domain.{w}} (F : ContinuousMap B C) :
    Continuous F.toFun := F.cont

theorem Continuous.ite {β : Type v} [PartialOrder β] [OmegaSup β]
    (p : Prop) [Decidable p] {f g : α → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => if p then f x else g x) := by
  by_cases h : p
  · simp only [h, ite_true]; exact hf
  · simp only [h, ite_false]; exact hg

theorem Continuous.dite {β : Type v} [PartialOrder β] [OmegaSup β]
    (p : Prop) [Decidable p] {f : p → α → β} {g : ¬ p → α → β}
    (hf : ∀ h, Continuous (f h)) (hg : ∀ h, Continuous (g h)) :
    Continuous (fun x => if h : p then f h x else g h x) := by
  by_cases h : p
  · simp only [h, dite_true]; exact hf h
  · simp only [h, dite_false]; exact hg h

/-- Separate continuity in each argument implies joint continuity. -/
theorem Continuous.of_separate {β : Type v} {γ : Type w} [PartialOrder β] [PartialOrder γ]
    [OmegaSup β] [OmegaSup γ] {f : α → β → γ}
    (h₁ : ∀ b, Continuous (fun a => f a b)) (h₂ : ∀ a, Continuous (f a)) :
    Continuous (fun p : α × β => f p.1 p.2) where
  mono x y hxy :=
    PartialOrder.rel_trans ((h₁ x.2).mono _ _ hxy.1) ((h₂ y.1).mono _ _ hxy.2)
  sup_eq c := by
    change f (sup c.fst) (sup c.snd) = _
    rw [(h₁ _).sup_eq]
    let grid : Chain (Chain γ) := {
      val := fun n => c.snd.map (f (c.fst n)) (h₂ (c.fst n)).mono
      step := fun n m => (h₁ (c.snd m)).mono _ _ (c.fst.step n)
    }
    calc
      sup (c.fst.map (fun a => f a (sup c.snd)) (h₁ (sup c.snd)).mono) = sup grid.sups := by
        apply sup_congr
        intro n
        exact (h₂ (c.fst n)).sup_eq c.snd
      _ = sup grid.diagonal := sup_diagonal grid
      _ = _ := rfl

end ContinuityLemmas

end NonPos.Domain
