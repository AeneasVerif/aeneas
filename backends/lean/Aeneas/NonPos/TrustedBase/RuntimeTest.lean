module
public import Aeneas.NonPos.TrustedBase.Command
public import Aeneas.NonPos.TrustedBase.Result
-- for `#guard`
meta import Aeneas.Std.Primitives

@[expose] public section
/-!
This file tests that nonpos_structures run correctly through compiled code.
-/
namespace NonPos.RuntimeTest
open NonPos Aeneas.Std Result

nonpos_structure Counter : Type 1 where
  next : Nat → Result Nat

structure Maker where
  make : Nat → Counter

def maker : Maker := ⟨fun n => Counter.mk (fun s => ok (s + n)) (by nonpos_cont)⟩

#guard ((maker.make 1).next 2).reducesTo 3

end NonPos.RuntimeTest
