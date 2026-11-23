module
public import Aeneas.NonPos.TrustedBase.Command
public import Aeneas.NonPos.TrustedBase.Result
-- for `#guard`
meta import Aeneas.Std.Primitives

@[expose] public section
/-!
Runtime tests: dictionaries must also evaluate correctly, not only typecheck.
-/
namespace NonPos.RuntimeTest
open NonPos Aeneas.Std Result

/-! ## A field returning another structure's dictionary

A function whose result is a dictionary, stored in a dictionary.  (This is the shape of a mutual
group of impls and functions, aeneas#1264, packed as a structure.) -/

nonpos_structure Counter (Self : Type) : Type 1 where
  next : Self → Result Nat

nonpos_structure Maker : Type 1 where
  make : Nat → Counter Nat

def Maker.inst : Maker := Maker.mk
  (fun n => Counter.mk (fun s => ok (s + n)) (by nonpos_cont))
  (by nonpos_cont)

#guard ((Maker.inst.make 1).next 2).reducesTo 3

/-! ## A mutual group of a function and an impl

A default method that goes through an adapter's impl, and the adapter's impl, which contains the
default method (aeneas#1264, as for `Iterator::try_collect`): packed as one structure, whose
condition says that each member is continuous in its dictionary input. -/

nonpos_structure It (Self : Type) : Type 1 where
  next : Self → Result (Option Nat × Self)
  count : Self → Result Nat

structure Wrap (I : Type) where
  inner : I

nonpos_structure CountGroup : Type 1 where
  count_default : ∀ {Self : Type}, It Self → Self → Result Nat
  wrap : ∀ {I : Type}, It I → It (Wrap I)

def CountGroup.inst : CountGroup := CountGroup.mk
  (fun inst s => do
      let (o, _) ← (CountGroup.inst.wrap inst).next ⟨s⟩
      match o with
      | none => ok 0
      | some _ => ok 1)
  (fun inst => It.mk
      (fun w => do let (o, i) ← inst.next w.inner; ok (o, ⟨i⟩))
      (CountGroup.inst.count_default (CountGroup.inst.wrap inst))
      (by nonpos_cont 5000))
  (by nonpos_cont 5000)
partial_fixpoint monotonicity NonPos.Cont.monotone (by nonpos_cont 5000)

def It.count.default {Self : Type} (inst : It Self) (s : Self) : Result Nat :=
  CountGroup.inst.count_default inst s
def Wrap.Insts.It {I : Type} (inst : It I) : It (Wrap I) := CountGroup.inst.wrap inst

/-- An impl using the default, defined after the group. -/
def Nat.Insts.It : It Nat := It.mk
  (fun n => ok (some n, n + 1))
  (It.count.default Nat.Insts.It)
  (by nonpos_cont 5000)
partial_fixpoint monotonicity NonPos.Cont.monotone (by nonpos_cont 5000)

#guard (Nat.Insts.It.count 3).reducesTo 1
#guard ((Wrap.Insts.It Nat.Insts.It).count ⟨3⟩).reducesTo 1

end NonPos.RuntimeTest
