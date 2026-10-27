module
public import Aeneas.NonPos.Tests.Test

@[expose] public section
-- see the comment on this option in `Test.lean`
set_option backward.proofsInPublic true
/-!
# The iterator trait family, as Aeneas would compile it from its declaration

This mirrors what Aeneas emitted for a hand-written copy of the std iterator traits
(`AeneasTests/exp6`, `exp7a`), with `Option` in place of `Result`: associated types are parameters,
trait clauses are dictionary binders, supertraits are plain dictionary fields, provided methods are
separate `.default` definitions, and impls that use provided methods refer to themselves.
-/
namespace NonPos.TestIter
open NonPos Lean.Order NonPos.Test

/-! ## Aeneas's loop combinator -/

inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α)
  | done (v : β)

def loop {α β : Type} (body : α → Option (ControlFlow α β)) (x : α) : Option β := do
  match ← body x with
  | .cont x => loop body x
  | .done x => pure x
partial_fixpoint

/-! ## The trait declarations (exp6) -/

mutual
nonpos_structure MyIntoIterator (Self : Type) (Self_Item : Type) (Self_IntoIter : Type) : Type 1 where
  MyIteratorInst : MyIterator Self_IntoIter Self_Item
  into_iter : Self → Option Self_IntoIter
nonpos_structure MyIterator (Self : Type) (Self_Item : Type) : Type 1 where
  next : Self → Option (Option Self_Item × Self)
  zip_count : ∀ {U : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
    (MyIntoIteratorInst : MyIntoIterator U Clause0_Item Clause0_IntoIter), Self → U → Option (Nat × Self)
  rev_first : ∀ (MyDoubleEndedInst : MyDoubleEnded Self Self_Item), Self → Option (Option Self_Item)
  collect : ∀ {B : Type} (MyFromIteratorInst : MyFromIterator B Self_Item), Self → Option B
nonpos_structure MyDoubleEnded (Self : Type) (Self_Clause0_Item : Type) : Type 1 where
  MyIteratorInst : MyIterator Self Self_Clause0_Item
  next_back : Self → Option (Option Self_Clause0_Item × Self)
nonpos_structure MyFromIterator (Self : Type) (A : Type) : Type 1 where
  from_iter : ∀ {T : Type} (MyIteratorInst : MyIterator T A), T → Option Self
end

/-! ## Provided methods -/

def MyIterator.zip_count.default_loop.body {Self U Clause0_Item Clause1_Item Clause1_IntoIter : Type}
    (MyIteratorInst : MyIterator Self Clause0_Item)
    (MyIntoIteratorInst : MyIntoIterator U Clause1_Item Clause1_IntoIter)
    (self : Self) (o : Clause1_IntoIter) (n : Nat) :
    Option (ControlFlow (Self × Clause1_IntoIter × Nat) (Nat × Self)) := do
  let (o1, self1) ← MyIteratorInst.next self
  let (o2, o3) ← MyIntoIteratorInst.MyIteratorInst.next o
  match o1 with
  | none => pure (.done (n, self1))
  | some _ =>
    match o2 with
    | none => pure (.done (n, self1))
    | some _ => pure (.cont (self1, o3, n + 1))

def MyIterator.zip_count.default_loop {Self U Clause0_Item Clause1_Item Clause1_IntoIter : Type}
    (MyIteratorInst : MyIterator Self Clause0_Item)
    (MyIntoIteratorInst : MyIntoIterator U Clause1_Item Clause1_IntoIter)
    (self : Self) (o : Clause1_IntoIter) (n : Nat) : Option (Nat × Self) :=
  loop (fun (self1, o1, n1) => MyIterator.zip_count.default_loop.body MyIteratorInst MyIntoIteratorInst self1 o1 n1)
    (self, o, n)

def MyIterator.zip_count.default {Self U Clause0_Item Clause1_Item Clause1_IntoIter : Type}
    (MyIteratorInst : MyIterator Self Clause0_Item)
    (MyIntoIteratorInst : MyIntoIterator U Clause1_Item Clause1_IntoIter)
    (self : Self) (other : U) : Option (Nat × Self) := do
  let o ← MyIntoIteratorInst.into_iter other
  MyIterator.zip_count.default_loop MyIteratorInst MyIntoIteratorInst self o 0

def MyIterator.rev_first.default {Self Item : Type} (MyDoubleEndedInst : MyDoubleEnded Self Item)
    (self : Self) : Option (Option Item) := do
  let (r, _) ← MyDoubleEndedInst.next_back self
  pure r

def MyIterator.collect.default {Self B Clause0_Item : Type} (MyIteratorInst : MyIterator Self Clause0_Item)
    (MyFromIteratorInst : MyFromIterator B Clause0_Item) (self : Self) : Option B :=
  MyFromIteratorInst.from_iter MyIteratorInst self

/-! ## Impls for `Count` -/

structure Count where
  n : Nat
deriving DecidableEq, Repr

def Count.MyIterator.next (self : Count) : Option (Option Nat × Count) :=
  if self.n = 0 then pure (none, self) else pure (some (self.n - 1), { n := self.n - 1 })

/-- Aeneas emits this as `impl_def`, because the provided methods take the impl itself. -/
def Count.MyIterator : MyIterator Count Nat :=
  MyIterator.mk Count.MyIterator.next
    (fun {U Clause0_Item Clause0_IntoIter : Type} (MyIntoIteratorInst : MyIntoIterator U Clause0_Item Clause0_IntoIter) =>
      MyIterator.zip_count.default Count.MyIterator MyIntoIteratorInst)
    (fun (MyDoubleEndedInst : MyDoubleEnded Count Nat) => MyIterator.rev_first.default MyDoubleEndedInst)
    (fun {B : Type} (MyFromIteratorInst : MyFromIterator B Nat) =>
      MyIterator.collect.default Count.MyIterator MyFromIteratorInst)
    (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)

def Count.MyDoubleEnded : MyDoubleEnded Count Nat :=
  MyDoubleEnded.mk Count.MyIterator Count.MyIterator.next (by nonpos_cont)

def Count.MyIntoIterator : MyIntoIterator Count Nat Count :=
  MyIntoIterator.mk Count.MyIterator (fun self => pure self) (by nonpos_cont)

def Nat.MyFromIterator.from_iter_loop.body {T : Type} (MyIteratorInst : MyIterator T Nat) (iter : T) (acc : Nat) :
    Option (ControlFlow (T × Nat) Nat) := do
  let (o, iter1) ← MyIteratorInst.next iter
  match o with
  | none => pure (.done acc)
  | some x => pure (.cont (iter1, acc + x))

def Nat.MyFromIterator.from_iter {T : Type} (MyIteratorInst : MyIterator T Nat) (iter : T) : Option Nat :=
  loop (fun (iter1, acc1) => Nat.MyFromIterator.from_iter_loop.body MyIteratorInst iter1 acc1) (iter, 0)

def Nat.MyFromIterator : MyFromIterator Nat Nat :=
  MyFromIterator.mk (fun {T : Type} (MyIteratorInst : MyIterator T Nat) => Nat.MyFromIterator.from_iter MyIteratorInst)
    (by nonpos_cont)

/-! ## A generic, self-referential impl (exp7a: `impl<I: MyIterator> MyIterator for Peek<I>`) -/

structure Peek (I : Type) (Clause0_Item : Type) where
  inner : I
  buf : Option (Option Clause0_Item)

def Peek.MyIterator.next {I Clause0_Item : Type} (MyIteratorInst : MyIterator I Clause0_Item)
    (self : Peek I Clause0_Item) : Option (Option Clause0_Item × Peek I Clause0_Item) := do
  let (r, i) ← MyIteratorInst.next self.inner
  pure (r, { self with inner := i })

def Peek.MyIterator {I Clause0_Item : Type} (MyIteratorInst : MyIterator I Clause0_Item) :
    MyIterator (Peek I Clause0_Item) Clause0_Item :=
  MyIterator.mk (Peek.MyIterator.next MyIteratorInst)
    (fun {U A B : Type} (inst : MyIntoIterator U A B) => MyIterator.zip_count.default (Peek.MyIterator MyIteratorInst) inst)
    (fun inst => MyIterator.rev_first.default inst)
    (fun {B : Type} inst => MyIterator.collect.default (Peek.MyIterator MyIteratorInst) inst)
    (by nonpos_cont)
partial_fixpoint monotonicity Cont.monotone (by nonpos_cont)

/-- The generic impl is continuous in its dictionary parameter, so it can be used inside other
self-referential impls. -/
example {I Item : Type} : Cont (fun inst : MyIterator I Item => Peek.MyIterator inst) := by nonpos_cont

/-! ## Compiled evaluation -/

#guard Count.MyIterator.zip_count Count.MyIntoIterator ⟨3⟩ ⟨5⟩ = some (3, ⟨0⟩)
#guard Count.MyIterator.collect Nat.MyFromIterator ⟨4⟩ = some 6
#guard Count.MyIterator.rev_first Count.MyDoubleEnded ⟨4⟩ = some (some 3)
#guard (Peek.MyIterator Count.MyIterator).collect Nat.MyFromIterator ⟨⟨4⟩, none⟩ = some 6

end NonPos.TestIter
