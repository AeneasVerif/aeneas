import Aeneas.TraitDefault.Init

namespace Aeneas.TraitDefault.Test

namespace Test1

  /-! ## Test: basic structure with trait_default -/

  structure Trait where
    N : Nat
    P : Nat
    Q : Nat := 5
    R : Nat := N + 1

  @[trait_default]
  def Trait.P.default (self : Trait) : Nat := self.N + 3

  def Inst : Trait := {
    N := 5
    P := 3
  }

  /-- Test -/
  @[simp]
  impl_def TraitInst : Trait := {
    N := 5
    P := Trait.P.default TraitInst,
  }

  /-- Test -/
  impl_def TraitInst1 : Trait := {
    N := 5,
    P := Trait.P.default TraitInst1
  }

end Test1

namespace Test2

  /-! ## Test: parameterized structures -/

  structure Trait1 (N : Nat) (α : Type u) where
    A := N
    B := A + N
    C : Bool
    D : Nat
    E : α

  @[trait_default]
  def Trait1.D.default (self : Trait1 N α) : Nat :=
    self.A + self.B

  impl_def Trait1Inst (n : Nat) : Trait1 n Bool := {
    C := true
    D := Trait1.D.default (Trait1Inst n)
    E := true
  }

end Test2

namespace Test3

  structure Trait1 (N : Nat) (α : Type u) where
    A := N
    B := A + N
    C : Bool
    D : Nat
    E : α

  @[irreducible, trait_default]
  def Trait1.D.default (self : Trait1 N α) : Nat :=
    self.A + self.B

  impl_def Trait1Inst (n : Nat) : Trait1 n Bool := {
    C := true
    D := Trait1.D.default (Trait1Inst n)
    E := true
  }

end Test3

end Aeneas.TraitDefault.Test
