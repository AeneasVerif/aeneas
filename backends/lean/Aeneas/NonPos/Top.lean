module
public import Lean
public import Aeneas.NonPos.Bridge

@[expose] public section
/-!
# `nonpos_structure`: the definitions

This library provides structures that refer to themselves in the arguments of their own fields, as
the dictionaries of some Rust traits do:
```
nonpos_structure Measure (A : Type) : Type 1 where
  size : A → Result Nat
  larger : ∀ B, Measure B → A → B → Result Bool
```
Lean rejects this as a `structure`, and has to: if `Measure.mk` took any function as `larger`, with
`(Measure.mk s l).larger = l`, one could prove `False`.  Programming languages have such types
all the same, because the functions of a program are not arbitrary functions.  The library follows
them: `Measure.mk` takes any `size` and `larger`, together with a proof of a condition on `larger`
(on how it uses its argument of type `Measure B`), which holds of every function that Aeneas
outputs.

## What is trusted, and what it says

* **This file** states what the library provides.  Section 1 is the one notion everything is stated
  with: the relation `⊑` of Lean's `partial_fixpoint`.  A group of structures is described by a
  functor (section 2), for which there is a type `Fix`, with `fold` (the `mk` of a structure) and
  `unfold` (its projections), inverse of each other.  The functors that are allowed are the ones
  built from a few pieces (section 3).  Section 4 is about instances that refer to themselves, and
  section 5 about compiled code.
* **`Command.lean`** has the `nonpos_structure` command, which only names these for a group of
  structures written as above.
* **Section 1 of `Tactic.lean`** states that the condition holds of every term built from the forms
  that Aeneas outputs.

Nothing else needs to be read.  The constants stated here (`Cont`, `FixFunctor`, `Fix`, ...) are
defined in `NonPos/Bridge.lean`, over the model of `NonPos/Model/`, and every statement below is
proved by a one-line reference to them, or by `Iff.rfl`: whatever those files contain, the
statements of this file hold of it, and they use no axiom of their own (section 6).

One thing is assumed of the files that are not read, since Lean lets any imported file change how a
later one is elaborated and compiled: that they do not interfere with the trusted ones.  They
declare no instance of `FixFunctor` (the instances of section 3 are the only ones, so they are what
the command finds for a group); no syntax, macro or elaborator that changes what the text of a
trusted file means; and no compiled implementation (`implemented_by`) of what the command
generates.  These are properties of the text of those files, and can be checked by searching it.
-/

namespace NonPos
open Lean.Order
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. The relation `⊑`, and the condition on functions

Every type that occurs is compared with the relation `⊑` of Lean's `Lean.Order.PartialOrder`: the
one that `partial_fixpoint` uses, for which the computation that never returns is below every
other.  On the values of a monad such as `Result` it is the monad's own; on functions and tuples it
is Lean's, pointwise and componentwise: -/

example {T : Type w₁} {B : T → Type w₂} [∀ t, PartialOrder (B t)] (f g : (t : T) → B t) :
    f ⊑ g ↔ ∀ t, f t ⊑ g t := Iff.rfl
example {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] (x y : A ×' B) :
    x ⊑ y ↔ x.1 ⊑ y.1 ∧ x.2 ⊑ y.2 := Iff.rfl

/-! Any two values of `PUnit`, which ends each tuple of fields, are related (`unitOrder`), and a
structure is compared as its fields are (section 2).  Plain data (a `Nat`) is not a field of a
structure, but it occurs as a value inside a computation (`Cont.pure`, in `Tactic.lean`), where it is
compared by equality (`discreteOrder`). -/

example (A : Type w) (x y : A) : (discreteOrder A).rel x y ↔ x = y := Iff.rfl
example (x y : PUnit.{w+1}) : unitOrder.rel x y ↔ True := Iff.rfl

/-! `Cont f` is the condition on a function `f` between two such types.  Its definition is not
needed (it says that `f` preserves `⊑`, and the least upper bounds of increasing sequences): what
matters is that it holds of the functions that Aeneas outputs, which is section 1 of `Tactic.lean`. -/

example {A : Type w₁} {B : Type w₂} [PartialOrder A] [PartialOrder B] : (A → B) → Prop := Cont

/-! ## 2. A group of structures, as a functor, and its fixed point

A group of mutually defined structures is indexed by a type `I`, with one element for each
structure of the group at each value of its parameters (for `Measure`: one element `.Measure A` for
each `A : Type`).  A family `X : I → Type v` stands for the structures themselves, and `F k X` is
the type of the fields of structure `k`, written over `X`:
```
F (.Measure A) X  =  (A → Result Nat) ×' (∀ B, X (.Measure B) → A → B → Result Bool) ×' PUnit
```
We call a value of `G X` a *body*; `F k X` is the type of the bodies of structure `k`.
`FixFunctor G` says that the functor `G` is one the library handles.  It gives two things, which
section 3 states for each functor: how two bodies are compared, given how the structures are
(`order`), and the condition on a body (`cond`). -/

section Interface
variable {I : Type pu}

example : ((I → Type v) → Type w) → Type _ := FixFunctor
example (G : (I → Type v) → Type w) [FixFunctor G] (X : I → Type v) [∀ k, PartialOrder (X k)] :
    PartialOrder (G X) := FixFunctor.order G X
example (G : (I → Type v) → Type w) [FixFunctor G] (X : I → Type v) [∀ k, PartialOrder (X k)] :
    G X → Prop := FixFunctor.cond

variable (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

/-! When every `F k` is a `FixFunctor`, `Fix F k` is structure `k`, with its `⊑`. -/

example : I → Type v := Fix F
instance Fix.instPartialOrder (k : I) : PartialOrder (Fix F k) := Fix.order F k

/-! The statements below write `⊑` on a structure and leave Lean to find the instance.  It finds the
one above, and not another one declared in a file that this one imports: -/
example (k : I) : (inferInstance : PartialOrder (Fix F k)) = Fix.instPartialOrder F k := rfl

/-! A body of structure `k` over the structures themselves, satisfying the condition, folds into
structure `k` (`fold` is the `mk` of the structure), and a structure unfolds into such a body
(`unfold` is the tuple of its projections).  (How they run is section 5.) -/

noncomputable def Fix.fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond x) : Fix F k := Model.Fix.fold F x h
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d
theorem Fix.cond {k : I} (d : Fix F k) : FixFunctor.cond (Fix.unfold F d) := Proofs.cond_unfold F d

/-! `fold` and `unfold` are inverse of each other, and a structure is compared as its body is: so
structure `k` is exactly the bodies of `k` that satisfy the condition, with their `⊑`.
(`o.rel x y` is `x ⊑ y` for the order `o`.) -/

theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold' F x h
theorem Fix.fold_unfold {k : I} (d : Fix F k) :
    Fix.fold F (Fix.unfold F d) (Fix.cond F d) = d := Proofs.fold_unfold' F d
theorem Fix.le_iff {k : I} (d₁ d₂ : Fix F k) :
    d₁ ⊑ d₂ ↔ (FixFunctor.order (F k) (Fix F)).rel (Fix.unfold F d₁) (Fix.unfold F d₂) := Proofs.le_iff F d₁ d₂

end Interface

/-! ## 3. The functors

The pieces a functor may be built from follow, each with its `order` and its `cond` (its `model` is
not read).  A body is a tuple (`prod`, ended by `unit`) of fields.  A field is a method, that is a
chain of binders (`pi`, `arr`) ending in a value of a monad (`const`); or a plain value: of a type
with a least element (`const` again: an associated constant, of type `Result T`, or a structure of
another group), or a structure of this group (`var`).  Every binder is `pi`, whether it binds a
type, a number or a dictionary of another group, except a binder of a structure of the group
itself, which is `arr`.  There is no piece for a field of plain data, such as a `Nat`.

The order is Lean's on each type, and the condition is trivial on plain fields and goes through
tuples and binders.  At an `arr`, the condition is `Cont`: the method, as a function of the
dictionary it takes. -/

section Pieces
variable {I : Type pu}

/-- A value of a type that has a `Lean.Order.CCPO` (the type of a `partial_fixpoint`: `Result α`, a
function into it, a structure of another group), as a plain field or at the end of a method. -/
instance FixFunctor.const (A : Type w) [i : CCPO A] : FixFunctor (fun _ : (I → Type v) => A) where
  order := fun _ _ => i.toPartialOrder
  cond := fun _ => True
  model := .ccpo A

/-- The end of a tuple of fields. -/
instance FixFunctor.unit : FixFunctor (fun _ : (I → Type v) => PUnit.{w+1}) where
  order := fun _ _ => unitOrder
  cond := fun _ => True
  model := .unit

/-- A structure of the group itself, `X k`, as a plain field. -/
instance FixFunctor.var (k : I) : FixFunctor (fun X : (I → Type v) => X k) where
  order := fun _ i => i k
  cond := fun _ => True
  model := .var k

/-- A binder: `(t : T) → G t X`, for any type `T` (implicit or explicit, `Type`-valued or not). -/
instance FixFunctor.pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)] :
    FixFunctor (fun X => (t : T) → G t X) where
  order := fun X _ => @instOrderPi T (fun t => G t X) (fun t => FixFunctor.order (G t) X)
  cond := fun f => ∀ t, FixFunctor.cond (f t)
  model := .pi (fun t => FixFunctor.model (G := G t))

/-- A binder of a structure of the group itself: `X k → G X`.  This is where the condition is. -/
instance FixFunctor.arr (k : I) (G : (I → Type v) → Type w) [FixFunctor G] : FixFunctor (fun X => X k → G X) where
  order := fun X _ => @instOrderPi (X k) (fun _ => G X) (fun _ => FixFunctor.order G X)
  cond := fun {X} _ f => Cont (iB := FixFunctor.order G X) f ∧ ∀ d, FixFunctor.cond (f d)
  model := .arr k (FixFunctor.model (G := G))

/-- Two fields. -/
instance FixFunctor.prod (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁]
    [FixFunctor G₂] : FixFunctor (fun X => G₁ X ×' G₂ X) where
  order := fun X _ => @instPartialOrderPProd (G₁ X) (G₂ X) (FixFunctor.order G₁ X) (FixFunctor.order G₂ X)
  cond := fun x => FixFunctor.cond x.1 ∧ FixFunctor.cond x.2
  model := .prod (FixFunctor.model (G := G₁)) (FixFunctor.model (G := G₂))

end Pieces

/-! ## 4. Instances that refer to themselves

An instance may refer to itself (`def inst : Bla Int := Bla.mk (fun x => … inst …) …`).  Aeneas
defines it, like any recursive function, with Lean's `partial_fixpoint`, which gives the least
solution of the equation for `⊑`, on a type that has a `Lean.Order.CCPO` (a `⊑` with a least element
and least upper bounds of chains).  For a function into `Result`, this is what makes it diverge
where the program loops, rather than return something else that also satisfies the equation.

Every structure has a `CCPO`, whose `⊑` is the one of section 2.  By `Fix.le_iff`, the instance that
`partial_fixpoint` defines is therefore the least one whose fields satisfy the equation, the
fields being compared as section 3 says: by the `⊑` of the monad on the values of methods, at
every argument. -/

section Recursive
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

instance Fix.instCCPO (k : I) : CCPO (Fix F k) where
  toPartialOrder := Fix.instPartialOrder F k
  has_csup := Proofs.has_csup F k

end Recursive

/-! ## 5. Running `fold` and `unfold`

In the logic, `fold` and `unfold` are the model's (`Model.Fix.fold`, `Model.Fix.unfold`).  Compiled
code never builds what the model does: at runtime a dictionary is stored as a `Thunk` of the tuple
of its fields.  So `fold` stores the tuple `x : F k (Fix F)` without evaluating it (only its static
type changes to `Fix F k`), and `unfold` forces it (and changes the type back).  The work of `fold`
is all in the logic: proving the condition, and `Fix.unfold_fold`, which says that unfolding gives
back the same tuple.

Why delayed: a self-referential dictionary `d := mk … (f d) …` (defined by `partial_fixpoint`) is
compiled by Lean as a recursive constant, and a field such as `f d` that mentions `d` outside a
lambda would otherwise be evaluated while `d` is being built, which loops.  So compiled code does
not call `fold`, which has no compiled code, but `foldDelayed` (below), which is `fold` of a tuple
given under a lambda.  The generated `mk` is `foldDelayed` of `fun _ => ⟨fields⟩` and is
`@[macro_inline]`, so at a call site the tuple ends up under that lambda, and is evaluated only
when the dictionary is first unfolded.

Compiled code is correct under these assumptions:
1. Every dictionary that exists at runtime was made by `foldDelayed`.  This holds because every other
   construction of a value of `Fix F k` (the model's constructions, including what is behind its
   `CCPO`) is noncomputable, so the compiler rejects any program that uses one.  A self-referential
   dictionary defined by `partial_fixpoint` is compiled by Lean as a recursive definition whose
   body is a `mk`, so it too is made by `foldDelayed`.
2. Compiled code reads a dictionary only through `unfold`.  This holds because the only code that
   uses the model's representation of `Fix F k` is the model, which is never compiled.
Under 1 and 2, the dictionary `unfold` receives is a `Thunk` of the tuple that `foldDelayed` was given,
and forcing it gives that tuple `x`, which is also the logical value of `unfold (fold x h)` by
`Fix.unfold_fold`; so compiled projections compute their logical values. -/

section Running
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : FixFunctor.cond (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
/-- `fold` of the tuple `x ()`; at runtime, `x` is stored in a `Thunk` without being called. -/
@[implemented_by Fix.foldDelayedImpl]
noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : FixFunctor.cond (x ())) : Fix F k :=
  Fix.fold F (x ()) h

unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
attribute [implemented_by Fix.unfoldImpl] Fix.unfold
end Running

/-! ## 6. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold
/-- info: 'NonPos.Fix.fold_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.fold_unfold
/-- info: 'NonPos.Fix.le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.le_iff

end
end NonPos
