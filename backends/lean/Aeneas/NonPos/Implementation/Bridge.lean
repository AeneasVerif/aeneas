module
public import Aeneas.NonPos.Implementation.Model.Fix
import all Init.Internal.Order.Basic

@[expose] public section
/-!
# From the model to the statements of `TrustedBase/Definitions.lean`

Not part of the trusted surface.  The model (`NonPos/Implementation/Model/`) is stated on its own classes (`Dom`, an
order with its suprema; `DCont`; `Shape`; `MFix`).  `TrustedBase/Definitions.lean` is
stated on Lean's `Lean.Order.PartialOrder` alone.  This file has what is in between:

0. the orders of the model (`Dom`) of each type, and the `Shape` of each piece;
1. `Cont`, defined from `⊑` only, and the proofs of its forms, which hold for any partial orders;
2. `Cont` and the model's `DCont` agree, where the model has a `Dom`;
3. the class `FixFunctor` (an order and a condition on the bodies of a functor, with their model),
   and the model of each piece of `TrustedBase/Definitions.lean`;
4. the fixed point `Fix`, with `fold` and `unfold`.
-/

namespace NonPos
open Lean.Order
noncomputable section

universe pu v u w w₁ w₂ w₃

/-! ## 0. The model's orders, and the `Shape` of each piece

### Admissible types

`Dom A` is the order of the type `A`, with suprema of chains; the condition is continuity for these
orders.  Every type has one in a trivial way (`Dom.discrete`, low priority); products and function
types are ordered componentwise and pointwise; `M α` by the order of a supported monad `M`.
`Pointed A` says `A` has a least element.  No instance of these classes is registered anywhere but in
this file. -/

instance (priority := low) (A : Type w) : Dom A := Dom.discrete A
instance : Dom PUnit.{w+1} := Dom.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] : Dom ((t : T) → B t) := Dom.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] : Dom (A ×' B) := Dom.pprod A B

instance : Pointed PUnit.{w+1} := Pointed.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] [∀ t, Pointed (B t)] : Pointed ((t : T) → B t) :=
  Pointed.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] [Pointed A] [Pointed B] : Pointed (A ×' B) := Pointed.pprod A B


/-! ### The `Shape` of each piece -/

section Pieces
variable {I : Type pu}

/-- `PUnit`, with its order and least element. -/
@[reducible] def Shape.unitInst : Shape (fun _ : (I → Type v) => PUnit.{w+1}) where
  cond _ := True
  sd := Model.Shape.const PUnit
@[reducible] def Shape.varInst (k : I) : Shape (fun X : (I → Type v) => X k) where
  cond _ := True
  sd := Model.Shape.var k
@[reducible] def Shape.piInst (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)] :
    Shape (fun X => (t : T) → G t X) where
  cond f := ∀ t, Model.Shape.cond (f t)
  sd := Model.Shape.pi T G
@[reducible] def Shape.arrInst (k : I) (G : (I → Type v) → Type w) [Shape G] :
    Shape (fun X => X k → G X) where
  cond {X} _ f := DCont (inst_1 := Shape.dom G X) f ∧ ∀ d, Model.Shape.cond (f d)
  sd := Model.Shape.arr k G
@[reducible] def Shape.prodInst (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G] :
    Shape (fun X => F X ×' G X) where
  cond x := Model.Shape.cond x.1 ∧ Model.Shape.cond x.2
  sd := Model.Shape.prod F G
end Pieces

/-! ### The order of the fixed point of a group -/

section MFix
variable {I : Type pu} (H : I → (I → Type v) → Type v) [∀ k, Shape (H k)]

instance (k : I) : Dom (MFix H k) := MFix.dom H k

end MFix

/-! ## 1. `Cont`, and its forms -/

/-- `s` is a least upper bound of the sequence `c`. -/
def IsLub {A : Type w} [PartialOrder A] (c : Nat → A) (s : A) : Prop :=
  (∀ n, c n ⊑ s) ∧ ∀ u, (∀ n, c n ⊑ u) → s ⊑ u

/-- The condition on functions: `f` preserves `⊑`, and the least upper bounds of increasing
sequences. -/
def Cont {A : Type w₁} {B : Type w₂} [iA : PartialOrder A] [iB : PartialOrder B] (f : A → B) : Prop :=
  (∀ x y, x ⊑ y → f x ⊑ f y) ∧
    ∀ c : Nat → A, (∀ n, c n ⊑ c (n + 1)) → ∀ s, IsLub c s → IsLub (fun n => f (c n)) (f s)

/-- The order of `PUnit`. -/
@[instance_reducible] def unitOrder : PartialOrder PUnit.{w+1} := Dom.unit.po

namespace Proofs.Cont
section
variable {D : Type w} [PartialOrder D]

theorem chain_le {A : Type w₁} [PartialOrder A] {c : Nat → A} (hc : ∀ n, c n ⊑ c (n + 1)) {n m : Nat}
    (h : n ≤ m) : c n ⊑ c m := by
  induction h with
  | refl => exact PartialOrder.rel_refl
  | step _ ih => exact PartialOrder.rel_trans ih (hc _)

theorem const {B : Type w₁} [PartialOrder B] (b : B) : Cont (fun _ : D => b) :=
  ⟨fun _ _ _ => PartialOrder.rel_refl, fun _ _ _ _ => ⟨fun _ => PartialOrder.rel_refl, fun _ hu => hu 0⟩⟩

theorem id : Cont (fun d : D => d) := ⟨fun _ _ h => h, fun _ _ _ hs => hs⟩

theorem comp {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {g : A → B} {f : D → A}
    (hg : Cont g) (hf : Cont f) : Cont (fun d => g (f d)) :=
  ⟨fun x y h => hg.1 _ _ (hf.1 x y h),
   fun c hc s hs => hg.2 (fun n => f (c n)) (fun n => hf.1 _ _ (hc n)) (f s) (hf.2 c hc s hs)⟩

theorem lam {T : Type w₁} {B : T → Type w₂} [∀ t, PartialOrder (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f :=
  ⟨fun x y hxy t => (h t).1 x y hxy,
   fun c hc s hs => ⟨fun n t => ((h t).2 c hc s hs).1 n,
     fun u hu t => ((h t).2 c hc s hs).2 (u t) (fun n => hu n t)⟩⟩

/-- A least upper bound in a function type is one at each argument: an upper bound `u` at `t` extends
to an upper bound of the functions, equal to the least one away from `t`. -/
theorem app {T : Type w₁} {B : T → Type w₂} [∀ t, PartialOrder (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := by
  refine ⟨fun x y h => hf.1 x y h t, fun c hc s hs => ⟨fun n => (hf.2 c hc s hs).1 n t, fun u hu => ?_⟩⟩
  classical
  have H := hf.2 c hc s hs
  let U : (t' : T) → B t' := fun t' => if e : t' = t then e ▸ u else f s t'
  have hUt : U t = u := dite_eq_left rfl
  have hU : ∀ n, f (c n) ⊑ U := by
    intro n t'
    by_cases e : t' = t
    · cases e; rw [hUt]; exact hu n
    · rw [show U t' = f s t' from dite_eq_right e]; exact H.1 n t'
  exact hUt ▸ H.2 U hU t

theorem app₂ {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := by
  have mono : ∀ x y, x ⊑ y → f x (a x) ⊑ f y (a y) := fun x y h =>
    PartialOrder.rel_trans ((hc x).1 _ _ (ha.1 x y h)) (hf.1 x y h (a y))
  refine ⟨mono, fun c hcc s hs => ⟨fun n => mono _ _ (hs.1 n), fun u hu => ?_⟩⟩
  have step : ∀ n, f (c n) (a s) ⊑ u := fun n =>
    ((hc (c n)).2 (fun m => a (c m)) (fun m => ha.1 _ _ (hcc m)) (a s) (ha.2 c hcc s hs)).2 u (fun m =>
      PartialOrder.rel_trans
        (PartialOrder.rel_trans (hf.1 _ _ (chain_le hcc (Nat.le_max_left n m)) (a (c m)))
          ((hc (c (max n m))).1 _ _ (ha.1 _ _ (chain_le hcc (Nat.le_max_right n m)))))
        (hu (max n m)))
  exact ((app hf (a s)).2 c hcc s hs).2 u step

theorem pair {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) :=
  ⟨fun x y h => ⟨hf.1 x y h, hg.1 x y h⟩,
   fun c hc s hs => ⟨fun n => ⟨(hf.2 c hc s hs).1 n, (hg.2 c hc s hs).1 n⟩,
     fun u hu => ⟨(hf.2 c hc s hs).2 u.1 (fun n => (hu n).1), (hg.2 c hc s hs).2 u.2 (fun n => (hu n).2)⟩⟩⟩

theorem fst {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) :=
  ⟨fun x y h => (hf.1 x y h).1,
   fun c hc s hs => ⟨fun n => ((hf.2 c hc s hs).1 n).1,
     fun u hu => ((hf.2 c hc s hs).2 ⟨u, (f s).2⟩ (fun n => ⟨hu n, ((hf.2 c hc s hs).1 n).2⟩)).1⟩⟩

theorem snd {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) :=
  ⟨fun x y h => (hf.1 x y h).2,
   fun c hc s hs => ⟨fun n => ((hf.2 c hc s hs).1 n).2,
     fun u hu => ((hf.2 c hc s hs).2 ⟨(f s).1, u⟩ (fun n => ⟨((hf.2 c hc s hs).1 n).1, hu n⟩)).2⟩⟩

theorem ite {B : Type w₁} [PartialOrder B] (c : Prop) [inst : Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := by
  cases inst with
  | isTrue h => exact ht
  | isFalse h => exact he

theorem dite {B : Type w₁} [PartialOrder B] (c : Prop) [inst : Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) := by
  cases inst with
  | isTrue h => exact ht h
  | isFalse h => exact he h

theorem monotone {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : A → B} (h : Cont f) :
    Lean.Order.monotone f := h.1

theorem fix_le {α : Type w₁} [CCPO α] {g : α → α} (hg : Lean.Order.monotone g) {z : α} (h : g z ⊑ z) :
    Lean.Order.fix g hg ⊑ z := by
  apply fix_induct hg (fun x => x ⊑ z)
  · intro c hchain h'
    exact csup_le hchain h'
  · intro x hx
    exact PartialOrder.rel_trans (hg _ _ hx) h

/-- The least fixed point of `f s` is the least upper bound `L` of those of the `f (c n)`: `L` is a
fixed point of `f s`, because `f` preserves the least upper bound of the pairs. -/
theorem fix {α : Type w₁} [CCPO α] {f : D → α → α} {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) := by
  have mono : ∀ x y, x ⊑ y → Lean.Order.fix (f x) (hm x) ⊑ Lean.Order.fix (f y) (hm y) := fun x y h =>
    fix_le (hm x) (by
      have h1 : f x (Lean.Order.fix (f y) (hm y)) ⊑ f y (Lean.Order.fix (f y) (hm y)) :=
        hf.1 ⟨x, Lean.Order.fix (f y) (hm y)⟩ ⟨y, Lean.Order.fix (f y) (hm y)⟩ ⟨h, PartialOrder.rel_refl⟩
      exact PartialOrder.rel_trans h1 (PartialOrder.rel_of_eq (fix_eq (hm y)).symm))
  refine ⟨mono, fun c hc s hs => ⟨fun n => mono _ _ (hs.1 n), fun u hu => ?_⟩⟩
  let z : Nat → α := fun n => Lean.Order.fix (f (c n)) (hm (c n))
  have hz : ∀ n, z n ⊑ z (n + 1) := fun n => mono _ _ (hc n)
  have hch : chain (fun x => ∃ n, z n = x) := by
    rintro x y ⟨n, rfl⟩ ⟨m, rfl⟩
    rcases Nat.le_total n m with h | h
    · exact Or.inl (chain_le hz h)
    · exact Or.inr (chain_le hz h)
  have hL : IsLub z (CCPO.csup hch) :=
    ⟨fun n => le_csup hch ⟨n, rfl⟩, fun u hu => csup_le hch (fun _ ⟨n, e⟩ => e ▸ hu n)⟩
  have hp : IsLub (fun n => (⟨c n, z n⟩ : D ×' α)) ⟨s, CCPO.csup hch⟩ :=
    ⟨fun n => ⟨hs.1 n, hL.1 n⟩, fun u hu => ⟨hs.2 u.1 (fun n => (hu n).1), hL.2 u.2 (fun n => (hu n).2)⟩⟩
  have h1 : IsLub (fun n => f (c n) (z n)) (f s (CCPO.csup hch)) :=
    hf.2 (fun n => ⟨c n, z n⟩) (fun n => ⟨hc n, hz n⟩) ⟨s, CCPO.csup hch⟩ hp
  have h2 : f s (CCPO.csup hch) ⊑ CCPO.csup hch :=
    h1.2 _ (fun n => PartialOrder.rel_trans (PartialOrder.rel_of_eq (fix_eq (hm (c n))).symm) (hL.1 n))
  exact PartialOrder.rel_trans (fix_le (hm s) h2) (hL.2 u hu)

end

/-! ## 2. `Cont` and the model's `DCont` -/

/-- Where the orders are those of two `Dom`s, `Cont` is the continuity of the model. -/
theorem iff_model {A : Type w₁} {B : Type w₂} (dA : Dom A) (dB : Dom B) (f : A → B) :
    @Cont A B dA.po dB.po f ↔ @DCont A B dA dB f := by
  constructor
  · intro h
    refine DCont.mk' f h.1 (fun c => ?_)
    have h1 := h.2 (fun n => c n) (fun n => Dom.step' c n) (@Dom.sup A dA c)
      ⟨fun n => @Dom.le_sup A dA c n, fun u hu => @Dom.sup_le A dA c u hu⟩
    exact @Dom.le_antisymm B dB _ _
      (h1.2 _ (fun n => @Dom.le_sup B dB (@NonPos.Domain.Chain.map A B dA.po dB.po c f h.1) n))
      (@Dom.sup_le B dB (@NonPos.Domain.Chain.map A B dA.po dB.po c f h.1) _ (fun n => h1.1 n))
  · intro h
    refine ⟨fun x y hxy => DCont.mono' h hxy, fun c hc s hs => ?_⟩
    have e : s = @Dom.sup A dA (Dom.mkChain c hc) :=
      @Dom.le_antisymm A dA _ _ (hs.2 _ (fun n => @Dom.le_sup A dA (Dom.mkChain c hc) n))
        (@Dom.sup_le A dA (Dom.mkChain c hc) s hs.1)
    have e2 := DCont.sup_eq' h (Dom.mkChain c hc)
    rw [e, e2]
    refine ⟨fun n => ?_, fun u hu => ?_⟩
    · exact @Dom.le_sup B dB (@NonPos.Domain.Chain.map A B dA.po dB.po (Dom.mkChain c hc) f _) n
    · exact @Dom.sup_le B dB (@NonPos.Domain.Chain.map A B dA.po dB.po (Dom.mkChain c hc) f _) u hu

theorem iff_dom {A : Type w₁} {B : Type w₂} [iA : PartialOrder A] [iB : PartialOrder B] (dA : Dom A) (dB : Dom B)
    (hA : dA.po = iA) (hB : dB.po = iB) (f : A → B) : Cont f ↔ @DCont A B dA dB f := by
  subst hA; subst hB; exact iff_model dA dB f

section
variable {D : Type w} [PartialOrder D]

/-- `bind` of a monad whose `bind` satisfies the condition (`hbind`). -/
theorem bind {M : Type u → Type u} [Bind M] [∀ α, PartialOrder (M α)] {α β : Type u}
    (hbind : Cont (fun p : M α ×' (α → M β) => p.1 >>= p.2))
    {m : D → M α} {k : D → α → M β} (hm : Cont m) (hk : ∀ a, Cont (fun d => k d a)) :
    Cont (fun d => m d >>= k d) :=
  comp hbind (pair hm (lam (f := fun d a => k d a) hk))

/-- `bind` satisfies the condition, from the model's continuity of `bind` (with the `Dom`s of the
`CCPO`s). -/
theorem bind_of_model {M : Type u → Type u} [Bind M] [∀ α, CCPO (M α)] {α β : Type u}
    (h : @DCont (M α ×' (α → M β)) (M β)
      (@Dom.pprod (M α) (α → M β) (Dom.ofCCPO (M α)) (@Dom.pi α (fun _ => M β) (fun _ => Dom.ofCCPO (M β))))
      (Dom.ofCCPO (M β)) (fun p => p.1 >>= p.2)) :
    Cont (fun p : M α ×' (α → M β) => p.1 >>= p.2) :=
  (iff_model (@Dom.pprod (M α) (α → M β) (Dom.ofCCPO (M α)) (@Dom.pi α (fun _ => M β) (fun _ => Dom.ofCCPO (M β))))
    (Dom.ofCCPO (M β)) _).2 h
end
end Proofs.Cont

/-! ## 3. The class `FixFunctor`, and the model of each piece -/

/-- The model of a functor `G` with the order `order` and the condition `cond` on its bodies: a
`Shape` of the model, whose order and condition are these, where the model has `Dom`s. -/
structure FixFunctor.Model {I : Type pu} (G : (I → Type v) → Type w)
    (order : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X))
    (cond : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop) where
  shape : Shape G
  order_eq : ∀ (X : I → Type v) (d : ∀ k, Dom (X k)),
    (@Shape.dom _ G shape X d).po = @order X (fun k => (d k).po)
  cond_iff : ∀ (X : I → Type v) (d : ∀ k, Dom (X k)) (x : G X),
    @Model.Shape.cond _ G shape X d x ↔ @cond X (fun k => (d k).po) x

/-- There is a model of `G` with the order `order` and the condition `cond`.  (A `Prop`, so that a
`FixFunctor` has no data but its order, and is compiled.) -/
def FixFunctor.HasModel {I : Type pu} (G : (I → Type v) → Type w)
    (order : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X))
    (cond : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop) : Prop :=
  Nonempty (FixFunctor.Model G order cond)

/-- `FixFunctor G`: the functor `G` is one the library handles.  `order` is the order of its bodies
(given the order of the structures), `cond` the condition on them; `model` is not read. -/
class FixFunctor {I : Type pu} (G : (I → Type v) → Type w) where
  order (G) : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X)
  cond : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop
  model : FixFunctor.HasModel G order cond

/-- The model of a `FixFunctor` (one of them). -/
def FixFunctor.theModel {I : Type pu} (G : (I → Type v) → Type w) [i : FixFunctor G] :
    FixFunctor.Model G i.order i.cond :=
  Classical.choice i.model

/-- The `Shape` of the model, of a `FixFunctor`. -/
@[reducible] instance FixFunctor.toShape {I : Type pu} {G : (I → Type v) → Type w} [FixFunctor G] : Shape G :=
  (FixFunctor.theModel G).shape

/-- The value of a type with a `CCPO`, as a plain field (in the model: with its least element). -/
@[reducible] def Shape.ccpoInst {I : Type pu} (A : Type w) [CCPO A] : Shape (fun _ : (I → Type v) => A) where
  cond _ := True
  sd := letI := Dom.ofCCPO A; letI := Pointed.ofCCPO A; Model.Shape.const A

/-- An argument of a type with a `CCPO`, `A → G X` (in the model: with the `Dom` of the `CCPO`). -/
@[reducible] def Shape.argInst {I : Type pu} (A : Type w₁) [CCPO A] (G : (I → Type v) → Type w) [Shape G] :
    Shape (fun X => A → G X) where
  cond {X} _ f := @DCont A (G X) (Dom.ofCCPO A) (Shape.dom G X) f ∧ ∀ a, Model.Shape.cond (f a)
  sd := letI := Dom.ofCCPO A; letI := Pointed.ofCCPO A; Model.Shape.arg A G

namespace FixFunctor.Model
variable {I : Type pu}

def ccpo (A : Type w) [i : CCPO A] : Model (fun _ : (I → Type v) => A) (fun _ _ => i.toPartialOrder) (fun _ => True) :=
  ⟨Shape.ccpoInst A, fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
def unit : Model (fun _ : (I → Type v) => PUnit.{w+1}) (fun _ _ => unitOrder) (fun _ => True) :=
  ⟨Shape.unitInst, fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
def var (k : I) : Model (fun X : (I → Type v) => X k) (fun _ i => i k) (fun _ => True) :=
  ⟨Shape.varInst k, fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩

section Pi
variable {T : Type w₁} {G : T → (I → Type v) → Type w₂}
  {o : ∀ t (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G t X)}
  {c : ∀ t {X : I → Type v} [∀ k, PartialOrder (X k)], G t X → Prop}
  (m : ∀ t, Model (G t) (o t) (c t))

def pi : Model (fun X => (t : T) → G t X)
    (fun X _ => @instOrderPi T (fun t => G t X) (fun t => o t X)) (fun f => ∀ t, c t (f t)) where
  shape := @Shape.piInst _ T G (fun t => (m t).shape)
  order_eq X d := by
    show @instOrderPi T (fun t => G t X) (fun t => (@Shape.dom _ (G t) (m t).shape X d).po) = _
    exact congrArg (@instOrderPi T (fun t => G t X)) (funext fun t => (m t).order_eq X d)
  cond_iff X d f := forall_congr' fun t => (m t).cond_iff X d (f t)
end Pi

section Arr
variable (k : I) {G : (I → Type v) → Type w}
  {o : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X)}
  {c : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop}
  (m : Model G o c)

def arr : Model (fun X => X k → G X)
    (fun X _ => @instOrderPi (X k) (fun _ => G X) (fun _ => o X))
    (fun {X} [i : ∀ k, PartialOrder (X k)] f => @Cont (X k) (G X) (i k) (o X) f ∧ ∀ d, c (f d)) where
  shape := @Shape.arrInst _ k G m.shape
  order_eq X d := by
    show @instOrderPi (X k) (fun _ => G X) (fun _ => (@Shape.dom _ G m.shape X d).po) = _
    exact congrArg (fun p => @instOrderPi (X k) (fun _ => G X) (fun _ => p)) (m.order_eq X d)
  cond_iff X d f := and_congr
    (@Proofs.Cont.iff_dom (X k) (G X) (d k).po (@o X (fun k => (d k).po)) (d k) (@Shape.dom _ G m.shape X d) rfl
      (m.order_eq X d) f).symm
    (forall_congr' fun x => m.cond_iff X d (f x))
end Arr

section Arg
variable (A : Type w₁) [i : CCPO A] {G : (I → Type v) → Type w}
  {o : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X)}
  {c : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop}
  (m : Model G o c)

def arg : Model (fun X => A → G X)
    (fun X _ => @instOrderPi A (fun _ => G X) (fun _ => o X))
    (fun {X} [∀ k, PartialOrder (X k)] f => @Cont A (G X) i.toPartialOrder (o X) f ∧ ∀ a, c (f a)) where
  shape := @Shape.argInst _ A _ G m.shape
  order_eq X d := by
    show @instOrderPi A (fun _ => G X) (fun _ => (@Shape.dom _ G m.shape X d).po) = _
    exact congrArg (fun p => @instOrderPi A (fun _ => G X) (fun _ => p)) (m.order_eq X d)
  cond_iff X d f := and_congr
    (@Proofs.Cont.iff_dom A (G X) i.toPartialOrder (@o X (fun k => (d k).po)) (Dom.ofCCPO A)
      (@Shape.dom _ G m.shape X d) rfl (m.order_eq X d) f).symm
    (forall_congr' fun x => m.cond_iff X d (f x))
end Arg

section Prod
variable {G₁ : (I → Type v) → Type w₁} {G₂ : (I → Type v) → Type w₂}
  {o₁ : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G₁ X)}
  {c₁ : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G₁ X → Prop}
  {o₂ : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G₂ X)}
  {c₂ : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G₂ X → Prop}
  (m₁ : Model G₁ o₁ c₁) (m₂ : Model G₂ o₂ c₂)

def prod : Model (fun X => G₁ X ×' G₂ X)
    (fun X _ => @instPartialOrderPProd (G₁ X) (G₂ X) (o₁ X) (o₂ X)) (fun x => c₁ x.1 ∧ c₂ x.2) where
  shape := @Shape.prodInst _ G₁ G₂ m₁.shape m₂.shape
  order_eq X d := by
    show @instPartialOrderPProd (G₁ X) (G₂ X) (@Shape.dom _ G₁ m₁.shape X d).po (@Shape.dom _ G₂ m₂.shape X d).po = _
    rw [m₁.order_eq X d, m₂.order_eq X d]
  cond_iff X d x := and_congr (m₁.cond_iff X d x.1) (m₂.cond_iff X d x.2)
end Prod
end FixFunctor.Model

/-! The pieces, as `HasModel` (what `TrustedBase/Definitions.lean` writes as `model := .ccpo A`, ...). -/
namespace FixFunctor.HasModel
variable {I : Type pu}

theorem ccpo (A : Type w) [i : CCPO A] : HasModel (fun _ : (I → Type v) => A) (fun _ _ => i.toPartialOrder) (fun _ => True) :=
  ⟨Model.ccpo A⟩
theorem unit : HasModel (fun _ : (I → Type v) => PUnit.{w+1}) (fun _ _ => unitOrder) (fun _ => True) :=
  ⟨Model.unit⟩
theorem var (k : I) : HasModel (fun X : (I → Type v) => X k) (fun _ i => i k) (fun _ => True) :=
  ⟨Model.var k⟩
theorem pi {T : Type w₁} {G : T → (I → Type v) → Type w₂}
    {o : ∀ t (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G t X)}
    {c : ∀ t {X : I → Type v} [∀ k, PartialOrder (X k)], G t X → Prop}
    (m : ∀ t, HasModel (G t) (o t) (c t)) :
    HasModel (fun X => (t : T) → G t X)
      (fun X _ => @instOrderPi T (fun t => G t X) (fun t => o t X)) (fun f => ∀ t, c t (f t)) :=
  ⟨Model.pi fun t => Classical.choice (m t)⟩
theorem arr (k : I) {G : (I → Type v) → Type w}
    {o : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X)}
    {c : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop} (m : HasModel G o c) :
    HasModel (fun X => X k → G X)
      (fun X _ => @instOrderPi (X k) (fun _ => G X) (fun _ => o X))
      (fun {X} [i : ∀ k, PartialOrder (X k)] f => @Cont (X k) (G X) (i k) (o X) f ∧ ∀ d, c (f d)) :=
  ⟨Model.arr k (Classical.choice m)⟩
theorem arg (A : Type w₁) [i : CCPO A] {G : (I → Type v) → Type w}
    {o : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G X)}
    {c : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G X → Prop} (m : HasModel G o c) :
    HasModel (fun X => A → G X)
      (fun X _ => @instOrderPi A (fun _ => G X) (fun _ => o X))
      (fun {X} [∀ k, PartialOrder (X k)] f => @Cont A (G X) i.toPartialOrder (o X) f ∧ ∀ a, c (f a)) :=
  ⟨Model.arg A (Classical.choice m)⟩
theorem prod {G₁ : (I → Type v) → Type w₁} {G₂ : (I → Type v) → Type w₂}
    {o₁ : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G₁ X)}
    {c₁ : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G₁ X → Prop}
    {o₂ : ∀ (X : I → Type v) [∀ k, PartialOrder (X k)], PartialOrder (G₂ X)}
    {c₂ : ∀ {X : I → Type v} [∀ k, PartialOrder (X k)], G₂ X → Prop}
    (m₁ : HasModel G₁ o₁ c₁) (m₂ : HasModel G₂ o₂ c₂) :
    HasModel (fun X => G₁ X ×' G₂ X)
      (fun X _ => @instPartialOrderPProd (G₁ X) (G₂ X) (o₁ X) (o₂ X)) (fun x => c₁ x.1 ∧ c₂ x.2) :=
  ⟨Model.prod (Classical.choice m₁) (Classical.choice m₂)⟩
end FixFunctor.HasModel

/-! ## 4. The fixed point -/

section Fix
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

/-- The structures of the group `F`. -/
def Fix : I → Type v := MFix F

/-- The order of structure `k`. -/
@[instance_reducible] def Fix.order (k : I) : PartialOrder (Fix F k) where
  -- (written out, so that it is compiled: its only data is the relation, a `Prop`)
  rel x y := (MFix.dom F k).po.rel x y
  rel_refl := (MFix.dom F k).po.rel_refl
  rel_trans := (MFix.dom F k).po.rel_trans
  rel_antisymm := (MFix.dom F k).po.rel_antisymm

/-- The condition of the model is the condition of the class. -/
theorem Proofs.cond_iff {k : I} (x : F k (Fix F)) :
    @Model.Shape.cond _ (F k) _ (MFix F) (MFix.dom F) x ↔ @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) x :=
  (FixFunctor.theModel (F k)).cond_iff (MFix F) (MFix.dom F) x

/-- The order of the model on the bodies is the order of the class. -/
theorem Proofs.order_eq (k : I) :
    (@Shape.dom _ (F k) _ (MFix F) (MFix.dom F)).po = @FixFunctor.order _ (F k) _ (Fix F) (Fix.order F) :=
  (FixFunctor.theModel (F k)).order_eq (MFix F) (MFix.dom F)

def Model.Fix.fold {k : I} (x : F k (Fix F)) (h : @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) x) : Fix F k :=
  Model.MFix.fold F x ((Proofs.cond_iff F x).2 h)
def Model.Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.MFix.unfold F d

theorem Proofs.unfold_fold' {k : I} (x : F k (Fix F)) (h : @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) x) :
    Model.Fix.unfold F (Model.Fix.fold F x h) = x := Model.MFix.unfold_fold F x _
theorem Proofs.cond_unfold {k : I} (d : Fix F k) :
    @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) (Model.Fix.unfold F d) :=
  (Proofs.cond_iff F _).1 (Model.MFix.cond F d)

theorem Proofs.unfold_mono {k : I} {d₁ d₂ : Fix F k} (h : (Fix.order F k).rel d₁ d₂) :
    (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)).rel (Model.Fix.unfold F d₁) (Model.Fix.unfold F d₂) :=
  Proofs.order_eq F k ▸ Model.MFix.unfold_mono F h
theorem Proofs.fold_mono {k : I} {x₁ x₂ : F k (Fix F)} (h₁ : @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) x₁)
    (h₂ : @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) x₂)
    (h : (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)).rel x₁ x₂) :
    (Fix.order F k).rel (Model.Fix.fold F x₁ h₁) (Model.Fix.fold F x₂ h₂) :=
  Model.MFix.fold_mono F _ _ (by
    show @PartialOrder.rel _ (@Shape.dom _ (F k) _ (MFix F) (MFix.dom F)).po x₁ x₂
    rw [Proofs.order_eq F k]; exact h)

/-- `unfold` satisfies the condition, as a function. -/
theorem Proofs.Cont.unfold₀ (k : I) :
    @Cont (Fix F k) (F k (Fix F)) (Fix.order F k) (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F))
      (Model.Fix.unfold F) :=
  (@Proofs.Cont.iff_dom _ _ (Fix.order F k) (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)) (MFix.dom F k)
    (@Shape.dom _ (F k) _ (MFix F) (MFix.dom F)) rfl (Proofs.order_eq F k) _).2 (Model.DCont.unfold₀ F)

theorem Proofs.Cont.unfold {D : Type w} [PartialOrder D] {k : I} {g : D → Fix F k}
    (hg : @Cont D (Fix F k) _ (Fix.order F k) g) :
    @Cont D (F k (Fix F)) _ (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)) (fun d => Model.Fix.unfold F (g d)) :=
  @Proofs.Cont.comp D _ (Fix F k) (F k (Fix F)) (Fix.order F k) (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F))
    _ g (Proofs.Cont.unfold₀ F k) hg

/-- `fold` satisfies the condition, as a function of the bodies that satisfy the condition of the
model; composed with `f`, which lands in them. -/
theorem Proofs.Cont.fold {D : Type w} [PartialOrder D] {k : I} {f : D → F k (Fix F)}
    (h : ∀ d, @FixFunctor.cond _ (F k) _ (Fix F) (Fix.order F) (f d))
    (hf : @Cont D (F k (Fix F)) _ (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)) f) :
    @Cont D (Fix F k) _ (Fix.order F k) (fun d => Model.Fix.fold F (f d) (h d)) := by
  have hf' : @Cont D (F k (MFix F)) _ (@Shape.dom _ (F k) _ (MFix F) (MFix.dom F)).po f := by
    rw [Proofs.order_eq F k]; exact hf
  let dS : Dom {x : F k (MFix F) // Model.Shape.cond (F := F k) x} :=
    Dom.subtype (@Shape.dom _ (F k) _ (MFix F) (MFix.dom F)) _ ⟨(MFix.sd F k).cond_sup _, (MFix.sd F k).cond_csup _⟩
  have hfold : @Cont _ (Fix F k) dS.po (Fix.order F k) (fun p => Model.MFix.fold F p.1 p.2) :=
    (Proofs.Cont.iff_model dS (MFix.dom F k) _).2
      (@Model.DCont.fold _ F _ _ dS k (fun p => p.1) (fun p => p.2) (DCont.subtypeVal _))
  have hpair : @Cont D _ _ dS.po (fun d => ⟨f d, (Proofs.cond_iff F _).2 (h d)⟩) :=
    ⟨fun x y hxy => hf'.1 x y hxy,
      fun c hc s hs => ⟨fun n => (hf'.2 c hc s hs).1 n, fun u hu => (hf'.2 c hc s hs).2 u.1 hu⟩⟩
  exact @Proofs.Cont.comp D _ _ (Fix F k) dS.po (Fix.order F k) _ _ hfold hpair

theorem Proofs.fold_unfold' {k : I} (d : Fix F k) :
    Model.Fix.fold F (Model.Fix.unfold F d) (Proofs.cond_unfold F d) = d := Model.MFix.fold_unfold F d

/-- A structure is compared as its body is. -/
theorem Proofs.le_iff {k : I} (d₁ d₂ : Fix F k) :
    (Fix.order F k).rel d₁ d₂ ↔
      (@FixFunctor.order _ (F k) _ (Fix F) (Fix.order F)).rel (Model.Fix.unfold F d₁) (Model.Fix.unfold F d₂) :=
  ⟨Proofs.unfold_mono F, fun h => by
    have := Proofs.fold_mono F (Proofs.cond_unfold F d₁) (Proofs.cond_unfold F d₂) h
    rwa [Proofs.fold_unfold', Proofs.fold_unfold'] at this⟩

/-- Every structure has a least element, and least upper bounds of chains. -/
theorem Proofs.has_csup (k : I) {c : Fix F k → Prop} (hc : @chain _ (Fix.order F k) c) :
    Exists (@is_sup _ (Fix.order F k) c) :=
  (@MFix.ccpo _ F _ k).has_csup hc

end Fix

end
end NonPos
