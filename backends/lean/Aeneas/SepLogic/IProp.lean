module
public import Aeneas.Std.Heap
public import Aeneas.Std.HeapLemmas
@[expose] public section

namespace Aeneas.SepLogic

universe u

open Aeneas.Std (Heap)

/-- Heap predicates, closed under heap extension (affine). -/
structure IProp where
  holds : Heap → Prop
  up_closed : ∀ {h h' : Heap}, holds h → Heap.Sub h h' → holds h'

instance : CoeFun IProp (fun _ => Heap → Prop) :=
  ⟨IProp.holds⟩

syntax:max "iprop(" term ")" : term
macro_rules
  | `(iprop(($P))) => `(iprop($P))
  | `(iprop($H)) => `($H)

@[ext]
theorem IProp.ext {H₁ H₂ : IProp} (hIff : ∀ h, H₁ h ↔ H₂ h) : H₁ = H₂ := by
  obtain ⟨holds₁, _⟩ := H₁
  obtain ⟨holds₂, _⟩ := H₂
  have hEq : holds₁ = holds₂ := funext fun h => propext (hIff h)
  subst hEq
  rfl

abbrev IPre := IProp

abbrev IPost (α : Type u) := α → IProp

def Entails (H₁ H₂ : IProp) : Prop :=
  ∀ h, H₁ h → H₂ h

syntax:25 term:29 " ⊢ " term:25 : term
macro_rules
  | `($P ⊢ $Q) => `(Entails $P $Q)

structure BiEntails (H₁ H₂ : IProp) : Prop where
  mp : Entails H₁ H₂
  mpr : Entails H₂ H₁

syntax:25 term:29 " ⊣⊢ " term:29 : term
macro_rules
  | `($P ⊣⊢ $Q) => `(BiEntails $P $Q)

/-- Owns nothing; being affine, it holds of every heap. -/
def emp : IProp where
  holds _ := True
  up_closed := fun _ _ => trivial

notation "emp" => emp

def ipure (P : Prop) : IProp where
  holds _ := P
  up_closed := fun hP _ => hP

syntax "⌜" term "⌝" : term
macro_rules
  | `(⌜$P⌝) => `(ipure $P)

/-- Owns the heap fragment `A`, and says nothing about the other slots. -/
def owns (A : Heap) : IProp where
  holds h := Heap.Sub A h
  up_closed := fun hSub hExtend => hSub.trans hExtend

/-- The overloaded `↦` of pointers and buffers. -/
class PointsTo (ρ : Type u) (β : outParam (Type v)) where
  pointsTo : ρ → β → IProp

notation:50 r:50 " ↦ " value:50 => PointsTo.pointsTo r value

/-- Additive conjunction: both assertions hold of the same heap fragment. -/
def iand (P Q : IProp) : IProp where
  holds h := P h ∧ Q h
  up_closed := fun hPQ hSub =>
    ⟨P.up_closed hPQ.1 hSub, Q.up_closed hPQ.2 hSub⟩

macro_rules
  | `(iprop($P ∧ $Q)) => `(iand iprop($P) iprop($Q))

def sep (H₁ H₂ : IProp) : IProp where
  holds h :=
    ∃ h₁ h₂,
      Heap.compatible h₁ h₂ ∧
      h = h₁ ∪ h₂ ∧
      H₁ h₁ ∧
      H₂ h₂
  up_closed := by
    rintro h h' ⟨h₁, h₂, hDisjoint, rfl, hH₁, hH₂⟩ hExtend
    obtain ⟨h₂', hDisjoint', rfl, hExtend'⟩ := Heap.Sub.split hDisjoint hExtend
    exact ⟨h₁, h₂', hDisjoint', rfl, hH₁, H₂.up_closed hH₂ hExtend'⟩

infixr:35 " ∗ " => sep
macro_rules
  | `(iprop($P ∗ $Q)) => `(iprop($P) ∗ iprop($Q))

def iexists {α : Sort _} (J : α → IProp) : IProp where
  holds h := ∃ x, J x h
  up_closed := fun ⟨x, hJ⟩ hExtend => ⟨x, (J x).up_closed hJ hExtend⟩

macro_rules
  | `(iprop(∃ $x:ident, $H)) => `(iexists fun $x => iprop($H))
  | `(iprop(∃ $x:ident : $type, $H)) =>
      `(iexists fun ($x : $type) => iprop($H))
  | `(iprop(∃ ($x:ident : $type), $H)) =>
      `(iexists fun ($x : $type) => iprop($H))

def postSep {α : Type u} (Q : IPost α) (H : IProp) :
    IPost α :=
  fun value => sep (Q value) H

infixr:40 " ∗+ " => postSep

def postEntails {α : Type u} (Q₁ Q₂ : IPost α) : Prop :=
  ∀ value, Entails (Q₁ value) (Q₂ value)

syntax:25 term:29 " ⊢+ " term:25 : term
macro_rules
  | `($P ⊢+ $Q) => `(postEntails $P $Q)

def iforall {ι : Sort _} (J : ι → IProp) : IProp where
  holds h := ∀ x, J x h
  up_closed := fun hJ hExtend x => (J x).up_closed (hJ x) hExtend

macro_rules
  | `(iprop(∀ $x:ident, $H)) => `(iforall fun $x => iprop($H))
  | `(iprop(∀ $x:ident : $type, $H)) =>
      `(iforall fun ($x : $type) => iprop($H))
  | `(iprop(∀ ($x:ident : $type), $H)) =>
      `(iforall fun ($x : $type) => iprop($H))

/-- Separating implication (magic wand). -/
def wand (H₁ H₂ : IProp) : IProp where
  holds h :=
    ∀ h', Heap.compatible h h' → H₁ h' → H₂ (h ∪ h')
  up_closed := by
    intro h hBig hWand hExtend h' hDisjoint hH₁
    have hDisjoint' : Heap.compatible h h' :=
      Heap.Sub.disjoint_of_sub hExtend hDisjoint
    exact H₂.up_closed (hWand h' hDisjoint' hH₁)
      (Heap.Sub.union_mono_left hExtend hDisjoint)

infixr:25 " -∗ " => wand
macro_rules
  | `(iprop($P -∗ $Q)) => `(iprop($P) -∗ iprop($Q))

/-- The magic wand between postconditions; a heap predicate, not a postcondition. -/
def postWand {α : Type u} (Q₁ Q₂ : IPost α) : IProp :=
  iforall fun value => wand (Q₁ value) (Q₂ value)

infixr:25 " -∗+ " => postWand

end Aeneas.SepLogic
