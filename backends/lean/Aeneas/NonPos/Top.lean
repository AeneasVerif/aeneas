module
public import Lean
public import Aeneas.NonPos.Orders

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

* **This file** states what the library provides.  A group of structures is described by a functor
  (section 1); the functors that are allowed are the ones built from a few pieces (section 2);
  for these there is a type `Fix`, with `fold` (the `mk` of a structure), `unfold` (its projections),
  and `unfold (fold x) = x`.  Section 3 is about instances that refer to themselves, and section 4
  about compiled code.
* **`Command.lean`** has the `nonpos_structure` command, which only names these for a group of
  structures written as above.
* **Section 1 of `Tactic.lean`** states that the condition holds of every term built from the forms
  that Aeneas outputs.

Nothing else needs to be read.  The constants stated here (`FixFunctor`, `Fix`, `FixFunctor.cond`,
...) are defined in `NonPos/Model/`, `NonPos/Proofs.lean` and `NonPos/Orders.lean`, and every
statement below is proved by a one-line reference to them, or by `Iff.rfl`: whatever those files
contain, the statements of this file hold of it, and they use no axiom of their own (section 5).
-/

namespace NonPos
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. A group of structures, as a functor, and its fixed point

A group of mutually defined structures is indexed by a type `I`, with one element for each
structure of the group at each value of its parameters (for `Measure`: one element `.Measure A` for
each `A : Type`).  A family `X : I → Type v` stands for the structures themselves, and `F k X` is
the type of the fields of structure `k`, written over `X`:
```
F (.Measure A) X  =  (A → Result Nat) ×' (∀ B, X (.Measure B) → A → B → Result Bool) ×' PUnit
```
We call a value of `G X` a *body*; `F k X` is the type of the bodies of structure `k`.
`FixFunctor G` says that the functor `G` is one the library handles (section 2 lists them).  When
every `F k` is, `Fix F k` is structure `k`: -/

section Interface
variable {I : Type pu}

example : ((I → Type v) → Type w) → Type _ := FixFunctor
example (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)] : I → Type v := Fix F

/-! `FixFunctor.cond F x` is the condition on a body `x` over the structures of the group `F`
(what it is for each functor is in section 2). -/

example (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)] (G : (I → Type v) → Type w) [FixFunctor G] :
    G (Fix F) → Prop := FixFunctor.cond F

variable (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

/-! A body of structure `k` over the structures themselves, satisfying the condition, folds into
structure `k` (`fold` is the `mk` of the structure); unfolding gives the body back (`unfold` is the
tuple of its projections), and every unfolded body satisfies the condition.  (`foldDelayed` is how
`fold` runs: section 4.) -/

noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : FixFunctor.cond F (x ())) : Fix F k :=
  Model.Fix.fold F (x ()) h
noncomputable def Fix.fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond F x) : Fix F k :=
  Fix.foldDelayed F (fun _ => x) h
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d

theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : FixFunctor.cond F x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold F x h
theorem Fix.cond {k : I} (d : Fix F k) : FixFunctor.cond F (Fix.unfold F d) := Model.Fix.cond F d

end Interface

/-! ## 2. The functors, and the condition of each

The pieces a functor may be built from follow, each with what the condition requires of its bodies
(by `Iff.rfl`).  A body is a tuple (`prod`, ended by `unit`) of fields.  A field is a method, that
is a chain of binders (`pi`, `arr`) ending in the value of a monad (`monad`); or a plain value:
any type (`data`), a structure of another group (`dict`, `dictRec`), or a structure of this group
(`var`).  Every binder is `pi`, whether it binds a type, a number or a dictionary of another group,
except a binder of a structure of the group itself, which is `arr`.

The condition is trivial on plain fields, and goes through tuples and binders.  At an `arr`, it is
`FixFunctor.Cont`: a restriction on how a function uses the dictionary it takes.  Its definition is
not needed here: what matters is that it holds of the functions that Aeneas outputs, which is
section 1 of `Tactic.lean`.

`FixFunctor.Methods G` says that `G` may stand under a binder: what a binder returns is a
computation, so it must consist of values of the monad (and not of plain data, such as a `Nat`).
Its instances are stated with the pieces. -/

section Pieces
variable {I : Type pu} {F : I → (I → Type v) → Type v} [∀ k, FixFunctor (F k)]

example (G₁ : (I → Type v) → Type w₁) [FixFunctor G₁] (G₂ : (I → Type v) → Type w₂) [FixFunctor G₂] :
    (G₁ (Fix F) → G₂ (Fix F)) → Prop := FixFunctor.Cont F

/-- Data: any type `A` (`Nat`, `Type`, an ordinary structure, ...), as a plain field. -/
instance (priority := low) FixFunctor.data (A : Type w) : FixFunctor (fun _ : (I → Type v) => A) :=
  FixFunctor.dataInst A
theorem FixFunctor.cond_data (A : Type w) (a : A) :
    FixFunctor.cond F (G := fun _ => A) (iG := FixFunctor.data A) a ↔ True := Iff.rfl

/-- The value of a method: `M α`, for a supported monad `M` (`NonPosMonad`, e.g. `Result`). -/
instance FixFunctor.monad (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    FixFunctor (fun _ : (I → Type v) => M α) := FixFunctor.monadInst M α
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    FixFunctor.Methods (fun _ : (I → Type v) => M α) := FixFunctor.monadIsMethods M α
theorem FixFunctor.cond_monad (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u)
    (m : M α) : FixFunctor.cond F (G := fun _ => M α) (iG := FixFunctor.monad M α) m ↔ True := Iff.rfl

/-- The end of a tuple of fields. -/
instance FixFunctor.unit : FixFunctor (fun _ : (I → Type v) => PUnit.{w+1}) := FixFunctor.unitInst
instance : FixFunctor.Methods (fun _ : (I → Type v) => PUnit.{w+1}) := FixFunctor.unitIsMethods
theorem FixFunctor.cond_unit (u : PUnit.{w+1}) :
    FixFunctor.cond F (G := fun _ => PUnit.{w+1}) (iG := FixFunctor.unit) u ↔ True := Iff.rfl

/-- A structure of another group `F'` (the dictionary of a supertrait), as a plain field. -/
instance (priority := low) FixFunctor.dict {I' : Type pu} (F' : I' → (I' → Type v) → Type v)
    [∀ k, FixFunctor (F' k)] (k : I') : FixFunctor (fun _ : (I → Type v) => Fix F' k) := FixFunctor.dictInst F' k
theorem FixFunctor.cond_dict {I' : Type pu} (F' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (F' k)] (k : I')
    (d : Fix F' k) : FixFunctor.cond F (G := fun _ => Fix F' k) (iG := FixFunctor.dict F' k) d ↔ True := Iff.rfl

/-- The same, for a structure that consists of methods (`Fix.Recursive`, section 3): it may then
stand under a binder. -/
instance FixFunctor.dictRec {I' : Type pu} (F' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (F' k)] (k : I')
    [Fix.Recursive F' k] : FixFunctor (fun _ : (I → Type v) => Fix F' k) := FixFunctor.dictRecInst F' k
instance {I' : Type pu} (F' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (F' k)] (k : I') [Fix.Recursive F' k] :
    FixFunctor.Methods (fun _ : (I → Type v) => Fix F' k) := FixFunctor.dictIsMethods F' k
theorem FixFunctor.cond_dictRec {I' : Type pu} (F' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (F' k)] (k : I')
    [Fix.Recursive F' k] (d : Fix F' k) :
    FixFunctor.cond F (G := fun _ => Fix F' k) (iG := FixFunctor.dictRec F' k) d ↔ True := Iff.rfl

/-- A structure of the group itself, `X k`, as a plain field. -/
instance FixFunctor.var (k : I) : FixFunctor (fun X : (I → Type v) => X k) := FixFunctor.varInst k
theorem FixFunctor.cond_var (k : I) (d : Fix F k) : FixFunctor.cond F (G := fun X => X k) d ↔ True := Iff.rfl

/-- A binder: `(t : T) → G t X`, for any type `T` (implicit or explicit, `Type`-valued or not). -/
instance FixFunctor.pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)]
    [∀ t, FixFunctor.Methods (G t)] : FixFunctor (fun X => (t : T) → G t X) := FixFunctor.piInst T G
instance (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)] [∀ t, FixFunctor.Methods (G t)] :
    FixFunctor.Methods (fun X => (t : T) → G t X) := ⟨Proofs.pointed_pi T G⟩
theorem FixFunctor.cond_pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)]
    [∀ t, FixFunctor.Methods (G t)] (f : (t : T) → G t (Fix F)) :
    FixFunctor.cond F (G := fun X => (t : T) → G t X) f ↔ ∀ t, FixFunctor.cond F (f t) := Iff.rfl

/-- A binder of a structure of the group itself: `X k → G X`.  This is where the condition is. -/
instance FixFunctor.arr (k : I) (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G] :
    FixFunctor (fun X => X k → G X) := FixFunctor.arrInst k G
instance (k : I) (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G] :
    FixFunctor.Methods (fun X => X k → G X) := ⟨Proofs.pointed_arr k G⟩
theorem FixFunctor.cond_arr (k : I) (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G]
    (f : Fix F k → G (Fix F)) :
    FixFunctor.cond F (G := fun X => X k → G X) f ↔
      FixFunctor.Cont F (G₁ := fun X => X k) f ∧ ∀ d, FixFunctor.cond F (f d) := Iff.rfl

/-- Two fields. -/
instance FixFunctor.prod (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁]
    [FixFunctor G₂] : FixFunctor (fun X => G₁ X ×' G₂ X) := FixFunctor.prodInst G₁ G₂
instance (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁] [FixFunctor G₂]
    [FixFunctor.Methods G₁] [FixFunctor.Methods G₂] : FixFunctor.Methods (fun X => G₁ X ×' G₂ X) :=
  ⟨Proofs.pointed_prod G₁ G₂⟩
theorem FixFunctor.cond_prod (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁]
    [FixFunctor G₂] (x : G₁ (Fix F) ×' G₂ (Fix F)) :
    FixFunctor.cond F (G := fun X => G₁ X ×' G₂ X) x ↔ FixFunctor.cond F x.1 ∧ FixFunctor.cond F x.2 := Iff.rfl

end Pieces

/-! ## 3. Instances that refer to themselves

An instance may refer to itself (`def inst : Bla Int := Bla.mk (fun x => … inst …) …`).  Aeneas
defines it, like any recursive function, with Lean's `partial_fixpoint`, which gives the least
solution of the equation for the relation `⊑` that the type of the definition carries (an instance
of `Lean.Order.CCPO`).  On the values of `Result`, and pointwise on functions into them, `⊑` is
Lean's and Aeneas's own, with the computation that never returns below every other: this is what
makes a recursive function diverge where the program loops, rather than return something else that
also satisfies the equation.  This section is what is needed for the same to hold of an instance:

* which structures have a `CCPO` (`Fix.Recursive`): the ones that consist of methods;
* what their `⊑` is: the one of their fields.  `fold` and `unfold` both preserve it, where two
  bodies are compared by `FixFunctor.Le`, field by field: by the `⊑` of the monad on the values
  of methods, at every argument through binders.

With `Fix.unfold_fold`, this determines the fields of a self-referential instance: they are the
least body `x`, for `Le` and among the bodies satisfying the condition, that satisfies its equation
`x = … Fix.fold F x _ …`.  Sections 1 and 2 use this section in one place only: `Fix.Recursive`, in
`FixFunctor.dictRec`, to say which structures of another group may stand under a binder. -/

section Recursive
open Lean.Order
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

/-! `Fix.Recursive F k`: structure `k` of the group has a `CCPO`.  This holds when each of its
fields is a method (more generally, a body that may stand under a binder: `FixFunctor.Methods`) or,
as a plain field, a structure of the group that is itself `Recursive`.  `FixFunctor.Recursive F G`
says this of a body `G`.  A structure with a plain field of data is not `Recursive`. -/

instance (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G] : FixFunctor.Recursive F G :=
  FixFunctor.Recursive.ofMethods F G
instance (k : I) [Fix.Recursive F k] : FixFunctor.Recursive F (fun X => X k) := ⟨Proofs.recursive_var F k⟩
instance (G₁ : (I → Type v) → Type w) (G₂ : (I → Type v) → Type w₁) [FixFunctor G₁] [FixFunctor G₂]
    [FixFunctor.Recursive F G₁] [FixFunctor.Recursive F G₂] : FixFunctor.Recursive F (fun X => G₁ X ×' G₂ X) :=
  ⟨Proofs.recursive_prod F G₁ G₂⟩
instance (k : I) [FixFunctor.Recursive F (F k)] : Fix.Recursive F k := Fix.Recursive.ofShape F k

instance Fix.instCCPO (k : I) [Fix.Recursive F k] : CCPO (Fix F k) := Fix.ccpo F k

/-! `fold` and `unfold` preserve `⊑`. -/

example (G : (I → Type v) → Type w) [FixFunctor G] : G (Fix F) → G (Fix F) → Prop := FixFunctor.Le F

theorem Fix.unfold_mono {k : I} [Fix.Recursive F k] {d₁ d₂ : Fix F k} (h : d₁ ⊑ d₂) :
    FixFunctor.Le F (Fix.unfold F d₁) (Fix.unfold F d₂) := Model.Fix.unfold_mono F h
theorem Fix.fold_mono {k : I} [Fix.Recursive F k] {x₁ x₂ : F k (Fix F)} (h₁ : FixFunctor.cond F x₁)
    (h₂ : FixFunctor.cond F x₂) (h : FixFunctor.Le F x₁ x₂) : Fix.fold F x₁ h₁ ⊑ Fix.fold F x₂ h₂ :=
  Model.Fix.fold_mono F h₁ h₂ h

/-! `FixFunctor.Le`, for each of the pieces that a `Recursive` structure is built from (by
`Iff.rfl`).  The two other pieces of section 2 cannot be fields of one: `data` (two values of which
are compared by equality) and `dict`. -/

variable {F}

theorem FixFunctor.le_monad (M : Type u → Type u) [∀ α, CCPO (M α)] [NonPosMonad M] (α : Type u) (m₁ m₂ : M α) :
    FixFunctor.Le F (G := fun _ => M α) (iG := FixFunctor.monad M α) m₁ m₂ ↔ m₁ ⊑ m₂ := Iff.rfl
theorem FixFunctor.le_unit (u₁ u₂ : PUnit.{w+1}) :
    FixFunctor.Le F (G := fun _ => PUnit.{w+1}) (iG := FixFunctor.unit) u₁ u₂ ↔ True := Iff.rfl
theorem FixFunctor.le_dictRec {I' : Type pu} (F' : I' → (I' → Type v) → Type v) [∀ k, FixFunctor (F' k)] (k : I')
    [Fix.Recursive F' k] (d₁ d₂ : Fix F' k) :
    FixFunctor.Le F (G := fun _ => Fix F' k) (iG := FixFunctor.dictRec F' k) d₁ d₂ ↔ d₁ ⊑ d₂ := Iff.rfl
theorem FixFunctor.le_var (k : I) [Fix.Recursive F k] (d₁ d₂ : Fix F k) :
    FixFunctor.Le F (G := fun X => X k) d₁ d₂ ↔ d₁ ⊑ d₂ := Iff.rfl
theorem FixFunctor.le_pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, FixFunctor (G t)]
    [∀ t, FixFunctor.Methods (G t)] (f₁ f₂ : (t : T) → G t (Fix F)) :
    FixFunctor.Le F (G := fun X => (t : T) → G t X) f₁ f₂ ↔ ∀ t, FixFunctor.Le F (f₁ t) (f₂ t) := Iff.rfl
theorem FixFunctor.le_arr (k : I) (G : (I → Type v) → Type w) [FixFunctor G] [FixFunctor.Methods G]
    (f₁ f₂ : Fix F k → G (Fix F)) :
    FixFunctor.Le F (G := fun X => X k → G X) f₁ f₂ ↔ ∀ d, FixFunctor.Le F (f₁ d) (f₂ d) := Iff.rfl
theorem FixFunctor.le_prod (G₁ : (I → Type v) → Type w₁) (G₂ : (I → Type v) → Type w₂) [FixFunctor G₁]
    [FixFunctor G₂] (x y : G₁ (Fix F) ×' G₂ (Fix F)) :
    FixFunctor.Le F (G := fun X => G₁ X ×' G₂ X) x y ↔ FixFunctor.Le F x.1 y.1 ∧ FixFunctor.Le F x.2 y.2 := Iff.rfl

/-! The `⊑` in the statements above are found by instance search.  They are the ones of the `CCPO`
of the monad and of `Fix.instCCPO`, and not of another instance: -/

example (M : Type u → Type u) [iM : ∀ α, CCPO (M α)] (α : Type u) :
    (inferInstance : PartialOrder (M α)) = (iM α).toPartialOrder := rfl
example (k : I) [Fix.Recursive F k] :
    (inferInstance : PartialOrder (Fix F k)) = (Fix.instCCPO F k).toPartialOrder := rfl

end Recursive

/-! ## 4. Running `fold` and `unfold`

In the logic, `fold` and `unfold` are the model's (`Model.Fix.fold`, `Model.Fix.unfold`).  Compiled
code never builds what the model does: at runtime a dictionary is stored as a `Thunk` of the tuple
of its fields.  So `fold` stores the tuple `x : F k (Fix F)` without evaluating it (only its static
type changes to `Fix F k`), and `unfold` forces it (and changes the type back).  The work of `fold`
is all in the logic: proving the condition, and `Fix.unfold_fold`, which says that unfolding gives
back the same tuple.

Why delayed: a self-referential dictionary `d := mk … (f d) …` (defined by `partial_fixpoint`) is
compiled by Lean as a recursive constant, and a field such as `f d` that mentions `d` outside a
lambda would otherwise be evaluated while `d` is being built, which loops.  `fold` and the
generated `mk` are `@[macro_inline]`, so at a call site the tuple ends up under the lambda that
`fold` passes to `foldDelayed`, and is evaluated only when the dictionary is first unfolded.
(`fold` is declared `noncomputable` in section 1 and made `macro_inline` here: without the
attribute, no code that uses it compiles.)

Compiled code is correct under these assumptions:
1. Every dictionary that exists at runtime was made by `fold`.  This holds because every other
   construction of a value of `Fix F k` (the model's constructions, including what is behind its
   `CCPO`) is noncomputable, so the compiler rejects any program that uses one.  A self-referential
   dictionary defined by `partial_fixpoint` is compiled by Lean as a recursive definition whose
   body is a `fold`, so it too is made by `fold`.
2. Compiled code reads a dictionary only through `unfold`.  This holds because the only code that
   uses the model's representation of `Fix F k` is the model, which is never compiled.
3. Compiled code never reads a `FixFunctor` instance.  This holds because what an instance contains
   is read only by the model and in proofs.  The command therefore gives each generated
   `FixFunctor` instance the runtime implementation `FixFunctor.runtime`, which is never inspected.
Under 1 and 2, the dictionary `unfold` receives is a `Thunk` of the tuple `x` that `fold` was given,
and forcing it gives `x`, which is also the logical value of `unfold (fold x h)` by
`Fix.unfold_fold`; so compiled projections compute their logical values. -/

section Running
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, FixFunctor (F k)]

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : FixFunctor.cond F (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
attribute [implemented_by Fix.foldDelayedImpl] Fix.foldDelayed
attribute [implemented_by Fix.unfoldImpl] Fix.unfold
attribute [macro_inline] Fix.fold
end Running

/-- The runtime value of every generated `FixFunctor` instance (assumption 3 above: it is never read). -/
@[instance_reducible] unsafe def FixFunctor.runtime {I : Type pu} {G : (I → Type v) → Type w} : FixFunctor G :=
  unsafeCast ()

/-! ## 5. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold
/-- info: 'NonPos.Fix.fold_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.fold_mono
/-- info: 'NonPos.Fix.unfold_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_mono

end
end NonPos
