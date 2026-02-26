import Aeneas.TraitDefault.Init

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
