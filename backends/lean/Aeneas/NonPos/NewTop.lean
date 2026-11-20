module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section

namespace NonPos
open Lean Elab Command Term Meta
noncomputable section

-- TODO: this is a work-in-progress, where I'm copying things piece by piece from Top.lean.

/-
This is the top level specification of a library that implements structures that
can break positivity. It allows for example the following command:
This library is written by ai. To maintain human verifiability, this single
contains the entire exposed surface of the library.

The library allows definitions like the following of structures that break positivity:

```
nonpos_structure Measure (A : Type) : Type 1 where
  size : A → Option Nat
  larger : ∀ B, Measure B → A → B → Option Bool
```

Lean doesn't allow structures to be self-referential in this way, and for good reason:
if you axiomatized `Measure` with a computation rule like `(Measure.mk s l).larger = l`,
it would allow a proof of False.  But types like this are perfectly valid in programming
languages, and the elimination rule is necessary. Instead, we will impose a continuity
condition on functions like Larger, that restricts how it can use its recursive argument.

We will describe a structure with a functor.  As a simplified example:
abbrev MeasureF (A : Type) (Measure : Type → Type 1) : Type 1 :=
  (A → Option Nat) ×' (∀ B, Measure B → A → B → Option Bool) ×' PUnit.{2}

The set of functors for which we can take a fixpoint and get the structure type
are described by a typeclass:
-/
abbrev FixFunctor := @Shape -- TODO: apply this renaming globally
abbrev FixFunctor.cond := @Shape.cond -- TODO: apply this renaming globally

example {I : Type u} : ((I → Type v) → Type w) → Type (max u (v + 1) (w + 1)) := FixFunctor

-- For any such type, we can take a fixpoint:
example {I : Type u} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]
  : I → Type v := Fix F

/-
The conditions on the arguments that are necessary to construct an element of the fixpoint
are given by a field of the typeclass. The typeclass instances later will show what this
entails for specific functors.
-/

example {I : Type u} (F : (I → Type v) → Type w) [FixFunctor F]
    (X : I → Type v) [∀ k, Dom (X k)] : F X → Prop := FixFunctor.cond

section Fix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, FixFunctor (F k)]
-- These fixpoints have

instance (k : I) : Dom (Fix F k) := Fix.dom F k
example {k : I} : F k (Fix F) → Prop := FixFunctor.cond
noncomputable def Fix.fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond x) : Fix F k := Model.Fix.fold F x h
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d
