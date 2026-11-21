module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section
/-!
# `nonpos_structure`: the orders

The orders of the model (`Dom`) of each type (section 1), the `Shape` of each piece (section 2), and
the order of the fixed point of a group (section 3).  Not part of the trusted surface: `Bridge.lean`
relates these to Lean's `⊑`, on which `Top.lean` is stated.
-/

namespace NonPos
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. Admissible types, monads

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

/-- A supported monad `M` carries the chain-complete order that `partial_fixpoint` uses
(`Lean.Order.CCPO (M α)`); `NonPosMonad M` says that `bind` is continuous for it. -/
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Dom (M α) :=
  NonPosMonad.dom α
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Pointed (M α) :=
  Pointed.monad α
example (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u} :
    DCont (fun p : M α ×' (α → M β) => p.1 >>= p.2) := NonPosMonad.bind_cont

/-! ## 2. The `Shape` of each piece -/

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

/-! ## 3. Continuity at the fixed point of a group -/

section MFix
variable {I : Type pu} (H : I → (I → Type v) → Type v) [∀ k, Shape (H k)]

instance (k : I) : Dom (MFix H k) := MFix.dom H k

end MFix


end
end NonPos
