module
public import Lean
public import Aeneas.NonPos.Bridge
open Lean.Order

@[expose] public section

namespace NonPos

/-
This is the top level specification of the definitions behind the library.

Nonpositive sturctures are represented as functors. For example,
```
nonpos_structure Measure (Self : Type) : Type 1 where
  size : Self → Option Int
  combine : ∀ {Other : Type} (MeasureInst : Measure Other), Other → Self → Option Int
```

As a simplified example, we could represent this as a functor:
abbrev MeasureF (Self : Type) (Measure : Type → Type 1) : Type 1 :=
  (Self → Option Int) ×' (∀ {Other : Type}, Measure Other → Other → Self → Option Int) ×' PUnit.{2}

The set of functors for which we can take a fixpoint and get the structure type
are described by a typeclass `FixFunctor`:
-/
variable {I : Type pu} -- Index of the inductive family
example : ((I → Type v) → Type w) → Type _ := FixFunctor

/-
Later in this file, fixfunctor instances will be defined for standard type constructors
to cover the structures we want to describe. Each will have two parts visible in this
trusted base: a partial ordering for any partially ordered input, and a condition over
elements of the functor. This condition will restrict functions placed in a nonpositive
structure to prevent the contradiction noted above.
-/
example (G : (I → Type v) → Type w) [FixFunctor G] (X : I → Type v) [∀ k, PartialOrder (X k)] :
    PartialOrder (G X) := FixFunctor.order G X
example (G : (I → Type v) → Type w) [FixFunctor G] (X : I → Type v) [∀ k, PartialOrder (X k)] :
    G X → Prop := FixFunctor.cond

-- We can take a fixpoint of a functor if it satisfies FixFunctor at all indices:
variable (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]
-- For any such functor, we can take a fixpoint:
example : I → Type v := Fix F
-- `Fix F k` has an order: later in this file, it will be shown to come from the order on `F`
instance Fix.instPartialOrder (k : I) : PartialOrder (Fix F k) := Fix.order F k
-- We can unfold fixpoints, and we can fold over data satisfying the condition:
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d
noncomputable def Fix.fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond x) : Fix F k := Model.Fix.fold F x h

-- fold and unfold are inverses, and anything obtained from unfold has the
-- necessary condition to be passed back into fold:
theorem Fix.cond {k : I} (d : Fix F k) : FixFunctor.cond (Fix.unfold F d) := Proofs.cond_unfold F d
theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold' F x h
theorem Fix.fold_unfold {k : I} (d : Fix F k) :
    Fix.fold F (Fix.unfold F d) (Fix.cond F d) = d := Proofs.fold_unfold' F d
-- Fix inherits the ordering that is specified by the FixFunctor instances below:
theorem Fix.le_iff {k : I} (d₁ d₂ : Fix F k) :
    d₁ ⊑ d₂ ↔ (FixFunctor.order (F k) (Fix F)).rel (Fix.unfold F d₁) (Fix.unfold F d₂) := Proofs.le_iff F d₁ d₂


section Instances
/-
This section has instances that show that FixFunctor works at specific types.
These instances are enough to build up representations of structures as nested products.
-/
variable {I : Type pu}

-- Constant functor into type with a `CCPO` instance
instance FixFunctor.base (A : Type w) [i : CCPO A] : FixFunctor (fun _ : (I → Type v) => A) where
  order := fun _ _ => i.toPartialOrder
  cond := fun _ => True
  model := .ccpo A

-- Unit is used at end of nested pairs
instance FixFunctor.unit : FixFunctor (fun _ : (I → Type v) => PUnit.{w+1}) where
  order := fun _ _ => inferInstance
  cond := fun _ => True
  model := .unit

-- Used for structure fields that are recursive references back to the structure itself,
-- or another structure in a mutual group.
instance FixFunctor.var (k : I) : FixFunctor (fun X : (I → Type v) => X k) where
  order := fun _ i => i k
  cond := fun _ => True
  model := .var k

-- Function binders, used for fields with a function type
instance FixFunctor.pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)] :
    FixFunctor (fun X => (t : T) → G t X) where
  order := fun X _ => @instOrderPi T (fun t => G t X) (fun t => FixFunctor.order (G t) X)
  cond := fun f => ∀ t, FixFunctor.cond (f t)
  model := .pi (fun t => FixFunctor.model (G := G t))

/-
Function binders where the input is a recursive reference to the structure, or another
one in the mutual group.
This is where the continuity condition on recursive inputs must actually hold.
-/
instance FixFunctor.rec_input (k : I) (G : (I → Type v) → Type w) [FixFunctor G] : FixFunctor (fun X => X k → G X) where
  order := fun X _ => @instOrderPi (X k) (fun _ => G X) (fun _ => FixFunctor.order G X)
  cond := fun {X} _ f => Cont (iB := FixFunctor.order G X) f ∧ ∀ d, FixFunctor.cond (f d)
  model := .arr k (FixFunctor.model (G := G))

-- Used to combine fields of the structure together
instance FixFunctor.prod (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁]
    [FixFunctor G₂] : FixFunctor (fun X => G₁ X ×' G₂ X) where
  order := fun X _ => @instPartialOrderPProd (G₁ X) (G₂ X) (FixFunctor.order G₁ X) (FixFunctor.order G₂ X)
  cond := fun x => FixFunctor.cond x.1 ∧ FixFunctor.cond x.2
  model := .prod (FixFunctor.model (G := G₁)) (FixFunctor.model (G := G₂))

end Instances

section Cont
/- Above, the `rec_input` instance refers to `Cont`.
This is the condition that any function that inputs the structure being defined recursively,
and so breaks positivity, must satisfy.
It is defined on any function between partially ordered types: -/

example {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] : (A → B) → Prop := Cont

/- Cont is true of all forms that aeneas uses to model rust programs, as shown by the theorems below.
The tactic `nonpos_cont` defined in Tactic.lean uses these to prove functions continuous.
You can also register new theorems about continuity with `@[nonpos_continuous]`. -/
variable {D : Type w} [PartialOrder D]

/-- (For any `⊑` on `B`: it is not searched for, but taken from where the statement is used.) -/
theorem Cont.const {B : Type w₁} {iB : PartialOrder B} (b : B) : Cont (fun _ : D => b) := Proofs.Cont.const b
theorem Cont.id : Cont (fun d : D => d) := Proofs.Cont.id
/-- Lambda: pointwise. -/
theorem Cont.lam {T : Type w₁} {B : T → Type w₂} [∀ t, PartialOrder (B t)] {f : D → (t : T) → B t}
    (h : ∀ t, Cont (fun d => f d t)) : Cont f := Proofs.Cont.lam h
/-- Application to an argument not depending on `d` (a type, a value, a fixed dictionary, ...). -/
theorem Cont.app {T : Type w₁} {B : T → Type w₂} [∀ t, PartialOrder (B t)] {f : D → (t : T) → B t}
    (hf : Cont f) (t : T) : Cont (fun d => f d t) := Proofs.Cont.app hf t
/-- Application to an argument depending on `d`: the function must satisfy the condition. -/
theorem Cont.app₂ {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A → B} {a : D → A}
    (hf : Cont f) (hc : ∀ d, Cont (f d)) (ha : Cont a) : Cont (fun d => f d (a d)) := Proofs.Cont.app₂ hf hc ha
/-- Pairs: the field tuples of a structure, and what a mutual `partial_fixpoint` is packed into. -/
theorem Cont.pair {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A} {g : D → B}
    (hf : Cont f) (hg : Cont g) : Cont (fun d => (⟨f d, g d⟩ : A ×' B)) := Proofs.Cont.pair hf hg
theorem Cont.fst {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).1) := Proofs.Cont.fst hf
theorem Cont.snd {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] {f : D → A ×' B} (hf : Cont f) :
    Cont (fun d => (f d).2) := Proofs.Cont.snd hf
theorem Cont.ite {B : Type w₁} [PartialOrder B] (c : Prop) [Decidable c] {t e : D → B}
    (ht : Cont t) (he : Cont e) : Cont (fun d => if c then t d else e d) := Proofs.Cont.ite c ht he
theorem Cont.dite {B : Type w₁} [PartialOrder B] (c : Prop) [Decidable c] {t : c → D → B} {e : ¬c → D → B}
    (ht : ∀ h, Cont (t h)) (he : ∀ h, Cont (e h)) : Cont (fun d => if h : c then t h d else e h d) :=
  Proofs.Cont.dite c ht he
-- (`pure x` does not mention `d`, so it is `Cont.const`; bind for each supported monad is proven
-- separately with a @[nonpos_continuous] annotation)

/-- Fixed points: `partial_fixpoint` elaborates to `Lean.Order.fix`, for functions and for
self-referential dictionaries alike. -/
theorem Cont.fix {α : Type w₁} [CCPO α] {f : D → α → α} {hm : ∀ d, Lean.Order.monotone (f d)}
    (hf : Cont (fun p : D ×' α => f p.1 p.2)) : Cont (fun d => Lean.Order.fix (f d) (hm d)) := Proofs.Cont.fix hf

variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]
/-- The fields of a dictionary depending on `d` (a projection `e.m` is `(Fix.unfold F e).2. … .1`), and
`mk` of fields depending on `d` (`Measure.mk f₁ … fₙ h` is `Fix.fold F ⟨f₁, …, fₙ, ⟨⟩⟩ h`, by definition). -/
theorem Cont.unfold {k : I} {f : D → Fix F k} (hf : Cont f) :
    Cont (iB := FixFunctor.order (F k) (Fix F)) (fun d => Fix.unfold F (f d)) := Proofs.Cont.unfold F hf
theorem Cont.fold {k : I} {f : D → F k (Fix F)} (h : ∀ d, FixFunctor.cond (f d))
    (hf : Cont (iB := FixFunctor.order (F k) (Fix F)) f) : Cont (fun d => Fix.fold F (f d) (h d)) :=
  Proofs.Cont.fold F h hf
end Cont

-- Trait instances can be self-referential, so we need a CCPO instance for partial_fixpoint
instance Fix.instCCPO (k : I) : CCPO (Fix F k) where
  toPartialOrder := Fix.instPartialOrder F k
  has_csup := Proofs.has_csup F k

/-
In terms of proof checking, the above is all that is needed to specify that the
objects act as intended. However, they are noncomputable, which both means that the
`noncomputable` keyword would infect everything, and you wouldn't be able to run it as
compiled code. The below implementations fix this by providing versions for fold and
unfold which can run. They are correct only assuming that elements of Fix are only
operated on through `foldDelayed` and `unfold`. This means that actually, `foldDelayed`
must be used instead of `fold` in any code that will be compiled.
`foldDelayed` inputs a thunk to prevent a self-referential `Fix` from looping.
-/

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : FixFunctor.cond (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
/-- `fold` of the tuple `x ()`; at runtime, `x` is stored in a `Thunk` without being called. -/
@[implemented_by Fix.foldDelayedImpl]
noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : FixFunctor.cond (x ())) : Fix F k :=
  Fix.fold F (x ()) h

unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
attribute [implemented_by Fix.unfoldImpl] Fix.unfold

-- No axioms are used in the untrusted proofs and definitions:
theorem axiomCheck : True := by
  have := @Fix.cond.{0,0}; have := @Fix.unfold_fold.{0,0}; have := @Fix.fold_unfold.{0,0}
  have := @Fix.le_iff.{0,0}; have := @Fix.instCCPO.{0,0}; trivial
/-- info: 'NonPos.axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms axiomCheck
