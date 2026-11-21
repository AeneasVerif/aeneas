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
@[reducible] def FixFunctor.dataInst (A : Type w) : FixFunctor (fun _ : (I → Type v) => A) where
  cond _ := True
  sd := letI : Dom A := Dom.discrete A; Model.FixFunctor.data A
/-- The value of a supported monad, with its order and least element. -/
@[reducible] def FixFunctor.monadInst (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    FixFunctor (fun _ : (I → Type v) => M α) where
  cond _ := True
  sd := Model.FixFunctor.const (M α)
/-- `PUnit`, with its order and least element. -/
@[reducible] def FixFunctor.unitInst : FixFunctor (fun _ : (I → Type v) => PUnit.{w+1}) where
  cond _ := True
  sd := Model.FixFunctor.const PUnit
/-- A dictionary of another group `H'`, with the order of dictionaries. -/
@[reducible] def FixFunctor.dictInst {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (H' k)] (k : I') :
    FixFunctor (fun _ : (I → Type v) => Fix H' k) where
  cond _ := True
  sd := letI := Fix.dom H' k; Model.FixFunctor.data (Fix H' k)
/-- A dictionary of another group `H'` that is `Fix.Recursive` (`⊥` is total in it), with the order of
dictionaries and `⊥`. -/
@[reducible] def FixFunctor.dictRecInst {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (H' k)]
    (k : I') [Fix.Recursive H' k] : FixFunctor (fun _ : (I → Type v) => Fix H' k) where
  cond _ := True
  sd := letI := Fix.dom H' k; letI := Fix.pointed (k := k) H'; Model.FixFunctor.const (Fix H' k)
@[reducible] def FixFunctor.varInst (k : I) : FixFunctor (fun X : (I → Type v) => X k) where
  cond _ := True
  sd := Model.FixFunctor.var k
@[reducible] def FixFunctor.piInst (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)]
    [∀ t, FixFunctor.Methods (G t)] : FixFunctor (fun X => (t : T) → G t X) where
  cond f := ∀ t, Model.FixFunctor.cond (f t)
  sd := Model.FixFunctor.pi T G
@[reducible] def FixFunctor.arrInst (k : I) (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G] :
    FixFunctor (fun X => X k → G X) where
  cond {X} _ f := Cont (inst_1 := FixFunctor.dom G X) f ∧ ∀ d, Model.FixFunctor.cond (f d)
  sd := Model.FixFunctor.arr k G
@[reducible] def FixFunctor.prodInst (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [FixFunctor F] [FixFunctor G] :
    FixFunctor (fun X => F X ×' G X) where
  cond x := Model.FixFunctor.cond x.1 ∧ Model.FixFunctor.cond x.2
  sd := Model.FixFunctor.prod F G
theorem FixFunctor.monadIsMethods (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    @FixFunctor.Methods _ (fun _ : (I → Type v) => M α) (FixFunctor.monadInst M α) :=
  @FixFunctor.Methods.mk _ _ (FixFunctor.monadInst M α) (Proofs.pointed_const (M α))
theorem FixFunctor.unitIsMethods : @FixFunctor.Methods _ (fun _ : (I → Type v) => PUnit.{w+1}) FixFunctor.unitInst :=
  @FixFunctor.Methods.mk _ _ FixFunctor.unitInst (Proofs.pointed_const PUnit)
theorem FixFunctor.dictIsMethods {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (H' k)] (k : I')
    [Fix.Recursive H' k] : @FixFunctor.Methods _ (fun _ : (I → Type v) => Fix H' k) (FixFunctor.dictRecInst H' k) :=
  @FixFunctor.Methods.mk _ _ (FixFunctor.dictRecInst H' k) (letI := Fix.dom H' k; letI := Fix.pointed (k := k) H'; Proofs.pointed_const (Fix H' k))
end Pieces

/-! ## 3. Continuity at the fixed point of a group -/

section Fix
variable {I : Type pu} (H : I → (I → Type v) → Type v) [∀ k, FixFunctor (H k)]

instance (k : I) : Dom (Fix H k) := Fix.dom H k
instance (k : I) [Fix.Recursive H k] : Pointed (Fix H k) := Fix.pointed H

/-- `f`, between two bodies over the structures of the group `H`, is continuous: for the orders
that the shapes `G₁` and `G₂` give (on a dictionary, the order of the dictionaries). -/
abbrev FixFunctor.Cont {G₁ : (I → Type v) → Type w₁} [iG₁ : FixFunctor G₁] {G₂ : (I → Type v) → Type w₂} [iG₂ : FixFunctor G₂]
    (f : G₁ (Fix H) → G₂ (Fix H)) : Prop :=
  @NonPos.Cont _ _ (FixFunctor.dom G₁ (Fix H)) (FixFunctor.dom G₂ (Fix H)) f

/-- The values of `G` over the structures of `H` are a type that `partial_fixpoint` may recurse
through: its `Lean.Order.CCPO` has the order of the shape. -/
abbrev FixFunctor.FixCompat (G : (I → Type v) → Type w) [FixFunctor G] [Lean.Order.CCPO (G (Fix H))] : Prop :=
  @NonPos.FixCompat (G (Fix H)) (FixFunctor.dom G (Fix H)) _
end Fix


end
end NonPos
