module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section
/-!
# `nonpos_structure`: the orders

Everything that `Top.lean` uses without unfolding, and which mentions the orders of the model
(`Dom`): the order of each type (section 1), the bodies of the instances that `Top.lean` states
(section 2), and continuity at the fixed point of a group (section 3).  Not part of the trusted
surface: what is proved with these is stated, and checked, in `Top.lean`.
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
    Cont (fun p : M α ×' (α → M β) => p.1 >>= p.2) := NonPosMonad.bind_cont

/-! ## 2. The bodies of the instances of `Top.lean` -/

section Pieces
variable {I : Type pu}

/-- Data, with the discrete order. -/
@[reducible] def Shape.dataInst (A : Type w) : Shape (fun _ : (I → Type v) => A) where
  cond _ := True
  sd := letI : Dom A := Dom.discrete A; Model.Shape.data A
/-- The value of a supported monad, with its order and least element. -/
@[reducible] def Shape.monadInst (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    Shape (fun _ : (I → Type v) => M α) where
  cond _ := True
  sd := Model.Shape.const (M α)
/-- `PUnit`, with its order and least element. -/
@[reducible] def Shape.unitInst : Shape (fun _ : (I → Type v) => PUnit.{w+1}) where
  cond _ := True
  sd := Model.Shape.const PUnit
/-- A dictionary of another group `H'`, with the order of dictionaries. -/
@[reducible] def Shape.dictInst {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I') :
    Shape (fun _ : (I → Type v) => Fix H' k) where
  cond _ := True
  sd := letI := Fix.dom H' k; Model.Shape.data (Fix H' k)
/-- A dictionary of another group `H'` in which `⊥` is total, with the order of dictionaries and `⊥`. -/
@[reducible] def Shape.dictPointedInst {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)]
    (k : I') [Fix.BotTotal H' k] : Shape (fun _ : (I → Type v) => Fix H' k) where
  cond _ := True
  sd := letI := Fix.dom H' k; letI := Fix.pointed (k := k) H'; Model.Shape.const (Fix H' k)
@[reducible] def Shape.varInst (k : I) : Shape (fun X : (I → Type v) => X k) where
  cond _ := True
  sd := Model.Shape.var k
@[reducible] def Shape.piInst (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)]
    [∀ t, Shape.Pointed (G t)] : Shape (fun X => (t : T) → G t X) where
  cond f := ∀ t, Model.Shape.cond (f t)
  sd := Model.Shape.pi T G
@[reducible] def Shape.arrInst (k : I) (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] :
    Shape (fun X => X k → G X) where
  cond {X} _ f := Cont (inst_1 := Shape.dom G X) f ∧ ∀ d, Model.Shape.cond (f d)
  sd := Model.Shape.arr k G
@[reducible] def Shape.prodInst (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G] :
    Shape (fun X => F X ×' G X) where
  cond x := Model.Shape.cond x.1 ∧ Model.Shape.cond x.2
  sd := Model.Shape.prod F G
theorem Shape.monadIsPointed (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    @Shape.Pointed _ (fun _ : (I → Type v) => M α) (Shape.monadInst M α) :=
  @Shape.Pointed.mk _ _ (Shape.monadInst M α) (Proofs.pointed_const (M α))
theorem Shape.unitIsPointed : @Shape.Pointed _ (fun _ : (I → Type v) => PUnit.{w+1}) Shape.unitInst :=
  @Shape.Pointed.mk _ _ Shape.unitInst (Proofs.pointed_const PUnit)
theorem Shape.dictIsPointed {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I')
    [Fix.BotTotal H' k] : @Shape.Pointed _ (fun _ : (I → Type v) => Fix H' k) (Shape.dictPointedInst H' k) :=
  @Shape.Pointed.mk _ _ (Shape.dictPointedInst H' k) (letI := Fix.dom H' k; letI := Fix.pointed (k := k) H'; Proofs.pointed_const (Fix H' k))
end Pieces

/-! ## 3. Continuity at the fixed point of a group -/

section Fix
variable {I : Type pu} (H : I → (I → Type v) → Type v) [∀ k, Shape (H k)]

instance (k : I) : Dom (Fix H k) := Fix.dom H k

/-- `f`, a function of a dictionary of the group `H`, is continuous: for the order of the
dictionaries, and the order that the shape of `G` gives to its values. -/
abbrev Fix.Cont {k : I} {G : (I → Type v) → Type w} [Shape G] (f : Fix H k → G (Fix H)) : Prop :=
  @NonPos.Cont _ _ _ (Shape.dom G (Fix H)) f
end Fix

end
end NonPos
