module
public import Lean
public import Aeneas.NonPos.Orders

@[expose] public section
/-!
# `nonpos_structure`: the definitions

With `NonPos/Command.lean`, this file is the whole trusted surface of the library.  It contains,
and only contains, the *statements* that pin down the imported constants (`Shape`, `Fix`,
`Shape.cond`, ...).  `NonPos/Command.lean` has the `nonpos_structure` command, a thin wrapper around `Fix`,
and what the `nonpos_cont` tactic, which proves the condition of each structure, is expected to do.

Proofs live in `NonPos/Proofs.lean`, the definitions of the constants in `NonPos/Model/`, and the
orders of the model with the bodies of the instances below in `NonPos/Orders.lean`; none of them
needs to be read.  Every theorem below is proved by a one-line reference to them, or by `Iff.rfl`.  The
tactic is in `NonPos/Tactic.lean`, which does not need to be read either.
-/

namespace NonPos
open Lean Elab Command Term Meta
noncomputable section

universe pu v u w w₁ w₂

/-! ## 1. Shapes

A group of mutually defined structures is indexed by a type `I`, whose elements are the structures
of the group applied to their parameters (`k : I` is, say, `Bla Self`).  A family `X : I → Type v`
stands for the structures, and the body of `k` is a functor `F k : (I → Type v) → Type v` (the tuple
of its fields over `X`).  `Shape (F k)` says that `F k` is built from the pieces below and from
nothing else; what each piece requires of a body is stated right after it.  Every binder is treated alike: a
`Type` binder, a `Nat` binder and a dictionary binder are all `Shape.pi`, except that a binder whose
type is one of the structures being defined is `Shape.arr`.  The rest are plain fields: the value of
a method (`Shape.monad`), the end of the tuple (`Shape.unit`), a dictionary of another group
(`Shape.dict`), or any other type (`Shape.data`).  The body of a binder must be pointed
(`Shape.Pointed`: built from `Shape.monad`, `Shape.unit` and pointed dictionaries only). -/

section Shapes
variable {I : Type pu}

/-! `Shape.cond H x` is the condition of a body `x : G (Fix H)` over the structures of the group
`H`: for `G = H k`, the condition for folding `x` into `Fix H k` (section 2).  After each piece is
what it requires of a body (by `Iff.rfl`): trivial on plain fields, pointwise through binders,
componentwise on products, and continuity (`Fix.Cont`) on dictionary binders. -/

example (H : I → (I → Type v) → Type v) [∀ k, Shape (H k)] (G : (I → Type v) → Type w) [Shape G] :
    G (Fix H) → Prop := Shape.cond H

variable {H : I → (I → Type v) → Type v} [∀ k, Shape (H k)]

/-- Data: `A`, any type (`Nat`, `Type`, ordinary structures, ...), as a plain field. -/
instance (priority := low) Shape.data (A : Type w) : Shape (fun _ : (I → Type v) => A) := Shape.dataInst A
theorem Shape.cond_data (A : Type w) (a : A) :
    Shape.cond H (G := fun _ => A) (iG := Shape.data A) a ↔ True := Iff.rfl
/-- The value of a method: `M α`, for a supported monad `M` (`NonPosMonad`, e.g. `Result`). -/
instance Shape.monad (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    Shape (fun _ : (I → Type v) => M α) := Shape.monadInst M α
theorem Shape.cond_monad (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) (m : M α) :
    Shape.cond H (G := fun _ => M α) (iG := Shape.monad M α) m ↔ True := Iff.rfl
/-- The end of a tuple of fields. -/
instance Shape.unit : Shape (fun _ : (I → Type v) => PUnit.{w+1}) := Shape.unitInst
theorem Shape.cond_unit (u : PUnit.{w+1}) : Shape.cond H (G := fun _ => PUnit.{w+1}) (iG := Shape.unit) u ↔ True :=
  Iff.rfl
/-- A dictionary of another group `H'` (a supertrait), as a plain field. -/
instance (priority := low) Shape.dict {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I') :
    Shape (fun _ : (I → Type v) => Fix H' k) := Shape.dictInst H' k
theorem Shape.cond_dict {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I') (d : Fix H' k) :
    Shape.cond H (G := fun _ => Fix H' k) (iG := Shape.dict H' k) d ↔ True := Iff.rfl
/-- The same, when `⊥` is total in `Fix H' k` (so that it may appear under a binder). -/
instance Shape.dictPointed {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I')
    [Fix.BotTotal H' k] : Shape (fun _ : (I → Type v) => Fix H' k) := Shape.dictPointedInst H' k
theorem Shape.cond_dictPointed {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I')
    [Fix.BotTotal H' k] (d : Fix H' k) :
    Shape.cond H (G := fun _ => Fix H' k) (iG := Shape.dictPointed H' k) d ↔ True := Iff.rfl
/-- Recursive occurrence: `X k`, as a plain field. -/
instance Shape.var (k : I) : Shape (fun X : (I → Type v) => X k) := Shape.varInst k
theorem Shape.cond_var (k : I) (d : Fix H k) : Shape.cond H (G := fun X => X k) d ↔ True := Iff.rfl
/-- Binder: `(t : T) → G t X`, for any type `T` (implicit or explicit, `Type`-valued or not). -/
instance Shape.pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape (fun X => (t : T) → G t X) := Shape.piInst T G
theorem Shape.cond_pi (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)]
    (f : (t : T) → G t (Fix H)) :
    Shape.cond H (G := fun X => (t : T) → G t X) f ↔ ∀ t, Shape.cond H (f t) := Iff.rfl
/-- Dictionary binder: `X k → G X`. -/
instance Shape.arr (k : I) (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] :
    Shape (fun X => X k → G X) := Shape.arrInst k G
theorem Shape.cond_arr (k : I) (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] (f : Fix H k → G (Fix H)) :
    Shape.cond H (G := fun X => X k → G X) f ↔ Fix.Cont H f ∧ ∀ d, Shape.cond H (f d) := Iff.rfl
/-- Two fields. -/
instance Shape.prod (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G] :
    Shape (fun X => F X ×' G X) := Shape.prodInst F G
theorem Shape.cond_prod (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G]
    (x : F (Fix H) ×' G (Fix H)) :
    Shape.cond H (G := fun X => F X ×' G X) x ↔ Shape.cond H x.1 ∧ Shape.cond H x.2 := Iff.rfl

/-! `Shape.Pointed F`: the bodies allowed under a binder.  Every plain field of `F`, at any depth, has
a least element: no `Shape.data` field and no plain field of a structure of the group.  For a whole
structure, this is the set of structures that consist of methods and plain fields of pointed type. -/

instance (M : Type u → Type u) [∀ α, Lean.Order.CCPO (M α)] [NonPosMonad M] (α : Type u) :
    Shape.Pointed (fun _ : (I → Type v) => M α) := Shape.monadIsPointed M α
instance : Shape.Pointed (fun _ : (I → Type v) => PUnit.{w+1}) := Shape.unitIsPointed
instance {I' : Type pu} (H' : I' → (I' → Type v) → Type v) [∀ k, Shape (H' k)] (k : I') [Fix.BotTotal H' k] :
    Shape.Pointed (fun _ : (I → Type v) => Fix H' k) := Shape.dictIsPointed H' k
instance (T : Type w₁) (G : T → (I → Type v) → Type w₂) [∀ t, Shape (G t)] [∀ t, Shape.Pointed (G t)] :
    Shape.Pointed (fun X => (t : T) → G t X) := ⟨Proofs.pointed_pi T G⟩
instance (k : I) (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] :
    Shape.Pointed (fun X => X k → G X) := ⟨Proofs.pointed_arr k G⟩
instance (F : (I → Type v) → Type w₁) (G : (I → Type v) → Type w₂) [Shape F] [Shape G]
    [Shape.Pointed F] [Shape.Pointed G] : Shape.Pointed (fun X => F X ×' G X) := ⟨Proofs.pointed_prod F G⟩
end Shapes

/-! ## 2. The fixed point

`Fix F k` is the structure `k` (a structure of the group at its parameters).  A body `x : F k (Fix F)`
satisfying the condition `Shape.cond F x` (section 1) folds into it, and unfolding gives it back.  When `⊥` is total in it
(`Fix.BotTotal`: every plain field of structure `k` is pointed, or is a structure of the group in
which `⊥` is total), it is pointed and a `Lean.Order.CCPO`, so self-referential instances can be
defined with `partial_fixpoint`. -/

/-- The runtime value of every generated `Shape` instance (assumption 3 below: it is never read). -/
@[instance_reducible] unsafe def Shape.runtime {I : Type pu} {F : (I → Type v) → Type w} : Shape F := unsafeCast ()

section Fix
variable {I : Type pu} (F : I → (I → Type v) → Type v) [∀ k, Shape (F k)]


/-! `fold` and `unfold`, and how they run.

In the logic, `fold` and `unfold` are the model's (`Model.Fix.fold`, `Model.Fix.unfold`), and a
dictionary is an element of an inverse-limit domain.  Compiled code never builds that: at runtime a
dictionary is stored as a `Thunk` of the tuple of its fields.  So `fold` stores the tuple
`x : F k (Fix F)` without evaluating it (only its static type changes to `Fix F k`), and `unfold`
forces it (and changes the type back).  The work of `fold` is all in the logic: proving
`Shape.cond F x`, and `Fix.unfold_fold` below, which says that unfolding gives back the same tuple.

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

unsafe def Fix.foldDelayedImpl {k : I} (x : Unit → F k (Fix F)) (_ : Shape.cond F (x ())) : Fix F k :=
  unsafeCast (Thunk.mk x)
unsafe def Fix.unfoldImpl {k : I} (d : Fix F k) : F k (Fix F) := (unsafeCast d : Thunk (F k (Fix F))).get
/-- `fold` of the tuple `x ()`; at runtime, `x` is stored in a `Thunk` without being called. -/
@[implemented_by Fix.foldDelayedImpl]
noncomputable def Fix.foldDelayed {k : I} (x : Unit → F k (Fix F)) (h : Shape.cond F (x ())) : Fix F k :=
  Model.Fix.fold F (x ()) h
@[macro_inline]
def Fix.fold {k : I} (x : F k (Fix F)) (h : Shape.cond F x) : Fix F k := Fix.foldDelayed F (fun _ => x) h
@[implemented_by Fix.unfoldImpl]
noncomputable def Fix.unfold {k : I} (d : Fix F k) : F k (Fix F) := Model.Fix.unfold F d

theorem Fix.cond {k : I} (d : Fix F k) : Shape.cond F (Fix.unfold F d) := Model.Fix.cond F d
theorem Fix.unfold_fold {k : I} (x : F k (Fix F)) (h : Shape.cond F x) :
    Fix.unfold F (Fix.fold F x h) = x := Proofs.unfold_fold F x h

/-! `Shape.BotTotal F G` and `Fix.BotTotal F k`: the structures that are `CCPO`s, so that
`partial_fixpoint` can define self-referential instances of them.  A
structure of group `F` is in this set when each of its plain fields is of pointed type or is a
structure of the group that is itself in the set; `Shape.BotTotal F G` says the same of a body `G`.
This is larger than `Shape.Pointed`, which does not admit plain dictionary fields. -/
instance (G : (I → Type v) → Type w) [Shape G] [Shape.Pointed G] : Shape.BotTotal F G := Shape.BotTotal.ofPointed F G
instance (G₁ : (I → Type v) → Type w) (G₂ : (I → Type v) → Type w₁) [Shape G₁] [Shape G₂]
    [Shape.BotTotal F G₁] [Shape.BotTotal F G₂] : Shape.BotTotal F (fun X => G₁ X ×' G₂ X) := ⟨Proofs.botTotal_prod F G₁ G₂⟩
instance (k : I) [Fix.BotTotal F k] : Shape.BotTotal F (fun X => X k) := ⟨Proofs.botTotal_var F k⟩
instance (k : I) [Shape.BotTotal F (F k)] : Fix.BotTotal F k := Fix.BotTotal.ofShape F k
instance (k : I) [Fix.BotTotal F k] : Pointed (Fix F k) := Fix.pointed F
instance (k : I) [Fix.BotTotal F k] : Lean.Order.CCPO (Fix F k) := Fix.ccpo F k
end Fix

/-! ## 3. Axioms

Everything above, with its proofs and model, uses only the standard axioms (no `sorry`, no
axiom of the library's own).  The build fails if this changes. -/

/-- info: 'NonPos.Fix.unfold_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fix.unfold_fold

end
end NonPos
