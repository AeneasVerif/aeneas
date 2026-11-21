module
public import Lean
public import Aeneas.NonPos.Proofs

@[expose] public section
/-!
# `nonpos_structure`: the definitions

With `NonPos/Command.lean`, this file is the whole trusted surface of the library.  It contains,
and only contains, the *statements* that pin down the imported constants (`Dom`, `Cont`, `Shape`,
`Fix`, ...).  `NonPos/Command.lean` has the `nonpos_structure` command, a thin wrapper around `Fix`,
and what the `nonpos_cont` tactic, which proves the condition of each structure, is expected to do.

Proofs live in `NonPos/Proofs.lean` and the definitions of the constants in `NonPos/Model/`;
neither needs to be read.  Every theorem below is proved by a one-line reference to `Proofs`.  The
tactic is in `NonPos/Tactic.lean`, which does not need to be read either.
-/

namespace NonPos
open Lean Elab Command Term Meta
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. Admissible types, the condition, monads

`Dom A` says the type `A` is admissible; `Cont f` is the condition on functions between admissible
types (the "continuity" of the goal; its definition is not needed here).  Every type is admissible in
a trivial way (`Dom.discrete`, low priority); products and function types are admissible componentwise
and pointwise; `M α` is admissible for a supported monad `M`.  `Pointed A` says `A` has a least
element: this is what makes a plain field of type `A` free of the lifting of section 2. -/

/-! No instance of these classes is registered anywhere but in this file. -/

instance (priority := low) (A : Type w) : Dom A := Dom.discrete A
instance : Dom PUnit.{w+1} := Dom.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] : Dom ((t : T) → B t) := Dom.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] : Dom (A ×' B) := Dom.pprod A B

instance : Pointed PUnit.{w+1} := Pointed.unit
instance (T : Type w₁) (B : T → Type w₂) [∀ t, Dom (B t)] [∀ t, Pointed (B t)] : Pointed ((t : T) → B t) :=
  Pointed.pi T B
instance (A : Type w₁) (B : Type w₂) [Dom A] [Dom B] [Pointed A] [Pointed B] : Pointed (A ×' B) := Pointed.pprod A B

/-- A supported monad `M` carries the chain-complete order that `partial_fixpoint` uses
(`Lean.Order.CCPO (M α)`); `NonPosMonad M` says that `bind` satisfies the condition for it. -/
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Dom (M α) :=
  NonPosMonad.dom α
instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) : Pointed (M α) :=
  Pointed.monad α
example (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] {α β : Type u} :
    Cont (fun p : M α ×' (α → M β) => p.1 >>= p.2) := NonPosMonad.bind_cont

/-! ## 2. Signatures

A group of mutually defined structures is indexed by a type `I`, whose elements are the structures
of the group applied to their parameters (`k : I` is, say, `Bla Self`).  `Fam I = I → Type v` is the
type of families `X k` that the structures range over.  The body of `k` is a functor
`F k : Fam I → Type v`, and `Shape (F k)` says that `F k` is built from the pieces below and from nothing else, and gives the condition `Shape.cond` that
`.mk` requires of a body: trivial on plain fields, pointwise through binders, componentwise on
products, and `Cont` on dictionary binders.  Every binder is treated alike: a `Type` binder, a `Nat`
binder and a dictionary binder are all `Shape.pi`, except that a binder whose type is one of the
structures being defined is `Shape.arr`.  A plain field is `Shape.const` when its type is pointed and
`Shape.data` otherwise; the body of a binder must be pointed (`Shape.Pointed`: no `Shape.data` and no
plain dictionary field in it). -/

section Shapes
variable {I : Type pu}

/-- Data: `A`, any admissible type (`Nat`, `Type`, ordinary structures, ...), as a plain field. -/
instance (priority := low) Shape.data (A : Type w) [Dom A] : Shape (fun _ : (I → Type v) => A) where
  cond _ := True
  sd := Model.Shape.data A
/-- Constant: `A`, a pointed admissible type (`M τ`, a function into one, ...), as a plain field. -/
instance Shape.const (A : Type w) [Dom A] [NonPos.Pointed A] : Shape (fun _ : Fam.{pu, v} I => A) where
  cond _ := True
  sd := Model.Shape.const A
/-- Recursive occurrence: `X k`, as a plain field. -/
instance Shape.var (k : I) : Shape (fun X : Fam.{pu, v} I => X k) where
  cond _ := True
  sd := Model.Shape.var k
/-- Binder: `(t : T) → G t X`, for any type `T` (implicit or explicit, `Type`-valued or not). -/
instance Shape.pi (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape (fun X => (t : T) → G t X) where
  cond f := ∀ t, Shape.cond (f t)
  sd := Model.Shape.pi T G
/-- Dictionary binder: `X k → G X`. -/
instance Shape.arr (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    Shape (fun X => X k → G X) where
  cond {X} _ f := Cont (inst_1 := Shape.dom (F := G) X) f ∧ ∀ d, Shape.cond (f d)
  sd := Model.Shape.arr k G
/-- Two fields. -/
instance Shape.prod (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G] :
    Shape (fun X => F X ×' G X) where
  cond x := Shape.cond x.1 ∧ Shape.cond x.2
  sd := Model.Shape.prod F G

/-! `Shape.Pointed F`: the bodies allowed under a binder.  Every plain field of `F`, at any depth, has
a pointed type: no `Shape.data` field and no plain field of a structure of the group.  For a whole
structure, this is the set of structures that consist of methods and plain fields of pointed type. -/

instance (A : Type w) [Dom A] [Pointed A] : Shape.Pointed (fun _ : Fam.{pu, v} I => A) := ⟨Proofs.pointed_const A⟩
instance (T : Type w₁) (G : T → Fam.{pu, v} I → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape.Pointed (fun X => (t : T) → G t X) := ⟨Proofs.pointed_pi T G⟩
instance (k : I) (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] :
    Shape.Pointed (fun X => X k → G X) := ⟨Proofs.pointed_arr k G⟩
instance (F : Fam.{pu, v} I → Type w₁) (G : Fam.{pu, v} I → Type w₂) [Shape F] [Shape G]
    [Shape.Pointed F] [Shape.Pointed G] : Shape.Pointed (fun X => F X ×' G X) := ⟨Proofs.pointed_prod F G⟩

/-! The order of the values of each piece (`Shape.dom`, which the condition and the fixed point are
built on) is the order of their type: that of section 1 for a plain field, that of the family for a
recursive occurrence, pointwise through binders and componentwise on products.  Without this, the
model could order a plain field differently from its type: for example with an answer rather than
`div` as the least `Result`, so that the least dictionary, which `partial_fixpoint` picks for a
self-referential instance, would have a method answering where the program loops. -/
section Orders
variable (X : (I → Type v)) [iX : ∀ k, Dom (X k)]
example (A : Type w) [d : Dom A] : @Shape.dom I (fun _ : (I → Type v) => A) (Shape.data A) X _ = d := rfl
example (A : Type w) [d : Dom A] [Pointed A] : @Shape.dom I (fun _ : (I → Type v) => A) (Shape.const A) X _ = d :=
  rfl
example (k : I) : Shape.dom (fun X : (I → Type v) => X k) X = iX k := rfl
example (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape.dom (fun X => (t : T) → G t X) X = @Dom.pi T (fun t => G t X) (fun t => Shape.dom (G t) X) := rfl
example (k : I) (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] :
    Shape.dom (fun X => X k → G X) X = @Dom.pi (X k) (fun _ => G X) (fun _ => Shape.dom G X) := rfl
example (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G] :
    Shape.dom (fun X => F X ×' G X) X = @Dom.pprod (F X) (G X) (Shape.dom F X) (Shape.dom G X) := rfl
end Orders
end Shapes

/-! ## 3. The fixed point

`Fix F k` is the structure `k` (a structure of the group at its parameters).  A body `x : F k (Fix F)`
satisfying the condition folds into it, and unfolding gives it back.  When `⊥` is total in it
(`Fix.BotTotal`: every plain field of structure `k` is pointed, or is a structure of the group in
which `⊥` is total), it is pointed and a `Lean.Order.CCPO`, so self-referential instances can be
defined with `partial_fixpoint`. -/

/-- The runtime value of every generated `Shape` instance (assumption 3 below: it is never read). -/
@[instance_reducible] unsafe def Shape.runtime {I : Type pu} {F : Fam.{pu, v} I → Type w} : Shape F := unsafeCast ()

section Fix
variable {I : Type pu} (F : I → Fam.{pu, v} I → Type v) [∀ k, Shape (F k)]

instance (k : I) : Dom (Fix F k) := Fix.dom F k

/-! `fold` and `unfold`, and how they run.

In the logic, `fold` and `unfold` are the model's (`Model.Fix.fold`, `Model.Fix.unfold`), and a
dictionary is an element of an inverse-limit domain.  Compiled code never builds that: at runtime a
dictionary is stored as a `Thunk` of the tuple of its fields.  So `fold` stores the tuple
`x : F k (Fix F)` without evaluating it (only its static type changes to `Fix F k`), and `unfold`
forces it (and changes the type back).  The work of `fold` is all in the logic: proving
`Shape.cond x`, and `Fix.unfold_fold` below, which says that unfolding gives back the same tuple.

Why delayed: a self-referential dictionary `d := mk … (f d) …` (defined by `partial_fixpoint`) is
compiled by Lean as a recursive constant, and a field such as `f d` that mentions `d` outside a
lambda would otherwise be evaluated while `d` is being built, which loops.  `fold` and the
generated `mk` are `@[macro_inline]`, so at a call site the tuple ends up under the lambda that
`fold` passes to `foldDelayed`, and is evaluated only when the dictionary is first unfolded.

Compiled code is correct under these assumptions:
1. Every dictionary that exists at runtime was made by `fold`.  This holds because every other
   construction of a value of `Fix F k` (the model's constructions, including the suprema behind
   its `CCPO`) is noncomputable, so the compiler rejects any program that uses one.  A
   self-referential dictionary defined by `partial_fixpoint` is compiled by Lean as a recursive
   definition whose body is a `fold`, so it too is made by `fold`.
2. Compiled code reads a dictionary only through `unfold`.  This holds because the only code that
   uses the model's representation of `Fix F k` is the model, which is never compiled.
3. Compiled code never reads a `Shape` instance.  This holds because its field `cond` is a `Prop`
   and its field `sd` is read only by the model.  The command therefore gives each generated
   `Shape` instance the runtime implementation `Shape.runtime`, which is never inspected.
Under 1 and 2, the dictionary `unfold` receives is a `Thunk` of the tuple `x` that `fold` was given,
and forcing it gives `x`, which is also the logical value of `unfold (fold x h)` by
`Fix.unfold_fold`; so compiled projections compute their logical values. -/

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : Shape.cond (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
/-- `fold` of the tuple `x ()`; at runtime, `x` is stored in a `Thunk` without being called. -/
@[implemented_by Fix.foldDelayedImpl]
noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : Shape.cond (x ())) : Fix F k :=
  Model.Fix.fold F (x ()) h
@[macro_inline]
def Fix.fold {k : I} (x : F k (Fix F)) (h : Shape.cond x) : Fix F k := Fix.foldDelayed F (fun _ => x) h
@[implemented_by Fix.unfoldImpl]
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d

theorem Fix.cond {k : I} (d : Fix F k) : Shape.cond (Fix.unfold F d) := Model.Fix.cond F d
theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : Shape.cond x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold F x h

/-! `Shape.BotTotal F G` and `Fix.BotTotal F k`: the structures that are `CCPO`s, so that
`partial_fixpoint` can define self-referential instances of them.  A
structure of group `F` is in this set when each of its plain fields is of pointed type or is a
structure of the group that is itself in the set; `Shape.BotTotal F G` says the same of a body `G`.
This is larger than `Shape.Pointed`, which does not admit plain dictionary fields. -/
instance (G : Fam.{pu, v} I → Type w) [Shape G] [Shape.Pointed G] : Shape.BotTotal F G := Shape.BotTotal.ofPointed F G
instance (G₁ : Fam.{pu, v} I → Type w) (G₂ : Fam.{pu, v} I → Type w₁) [Shape G₁] [Shape G₂]
    [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] : Shape.BotTotal F (fun X => G₁ X ×' G₂ X) := ⟨Proofs.botTotal_prod F G₁ G₂⟩
instance (k : I) [Fix.BotTotal F k] : Shape.BotTotal F (fun X => X k) := ⟨Proofs.botTotal_var F k⟩
instance (k : I) [Shape.BotTotal F (F k)] : Fix.BotTotal F k := Fix.BotTotal.ofShape F k
instance (k : I) [Fix.BotTotal F k] : Pointed (Fix F k) := Fix.pointed F
instance (k : I) [Fix.BotTotal F k] : Lean.Order.CCPO (Fix F k) := Fix.ccpo F k
end Fix

/-! ## 4. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold

end
end NonPos
