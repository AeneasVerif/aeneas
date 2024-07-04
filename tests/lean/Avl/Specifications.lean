import Avl.Tree

namespace Primitives

namespace Result

def map {A B: Type} (x: Result A) (f: A -> B): Result B := match x with
| .ok y => .ok (f y)
| .fail e => .fail e
| .div => .div

@[inline]
def isok {A: Type} : Result A -> Bool
| .ok _ => true
| .fail _ => false
| .div => false

@[inline]
def get? {A: Type}: (r: Result A) -> isok r -> A
| .ok x, _ => x

end Result

end Primitives

namespace avl

@[simp]
def Ordering.toLeanOrdering (o: avl.Ordering): _root_.Ordering := match o with
| .Less => .lt
| .Equal => .eq
| .Greater => .gt

def Ordering.ofLeanOrdering (o: _root_.Ordering): avl.Ordering := match o with
| .lt => .Less
| .eq => .Equal
| .gt => .Greater

@[simp]
def Ordering.toDualOrdering (o: avl.Ordering): avl.Ordering := match o with
| .Less => .Greater
| .Equal => .Equal
| .Greater => .Less

@[simp]
theorem Ordering.toLeanOrdering.injEq (x y: avl.Ordering): (x.toLeanOrdering = y.toLeanOrdering) = (x = y) := by
  apply propext
  cases x <;> cases y <;> simp

@[simp]
theorem ite_eq_lt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = .Less) = if c then a = .Less else b = .Less := by
  by_cases c <;> simp [*]

@[simp]
theorem ite_eq_eq_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = .Equal) = if c then a = .Equal else b = .Equal := by
  by_cases c <;> simp [*]

@[simp]
theorem ite_eq_gt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = .Greater) = if c then a = .Greater else b = .Greater := by
  by_cases c <;> simp [*]

end avl

namespace Specifications

open Primitives
open Result

variable {T: Type} (H: outParam (avl.Ord T))

@[simp]
def _root_.Ordering.toDualOrdering (o: _root_.Ordering): _root_.Ordering := match o with
| .lt => .gt
| .eq => .eq
| .gt => .lt


@[simp]
theorem toDualOrderingOfToLeanOrdering (o: avl.Ordering): o.toDualOrdering.toLeanOrdering = o.toLeanOrdering.toDualOrdering := by
  cases o <;> simp

@[simp]
theorem toDualOrderingIdempotency (o: _root_.Ordering): o.toDualOrdering.toDualOrdering = o := by
  cases o <;> simp

-- TODO: reason about raw bundling vs. refined bundling.
-- raw bundling: hypothesis with Rust extracted objects.
-- refined bundling: lifted hypothesis with Lean native objects.
class OrdSpec [Ord T] where
  infallible: ∀ a b, ∃ (o: avl.Ordering), H.cmp a b = .ok o ∧ compare a b = o.toLeanOrdering

class OrdSpecSymmetry [O: Ord T] extends OrdSpec H where
  symmetry: ∀ a b, O.compare a b = (O.opposite.compare a b).toDualOrdering

-- Must be R decidableRel and an equivalence relationship?
class OrdSpecRel [O: Ord T] (R: outParam (T -> T -> Prop)) extends OrdSpec H where
  equivalence: ∀ a b, H.cmp a b = .ok .Equal -> R a b

class OrdSpecLinearOrderEq [O: Ord T] extends OrdSpecSymmetry H, OrdSpecRel H Eq

theorem infallible [Ord T] [OrdSpec H]: ∀ a b, ∃ o, H.cmp a b = .ok o := fun a b => by
  obtain ⟨ o, ⟨ H, _ ⟩ ⟩ := OrdSpec.infallible a b
  exact ⟨ o, H ⟩

instance: Coe (avl.Ordering) (_root_.Ordering) where
  coe a := a.toLeanOrdering

theorem rustCmpEq [Ord T] [O: OrdSpec H]: H.cmp a b = .ok o <-> compare a b = o.toLeanOrdering := by
  apply Iff.intro
  . intro Hcmp
    obtain ⟨ o', ⟨ Hcmp', Hcompare ⟩ ⟩ := O.infallible a b
    rw [Hcmp', ok.injEq] at Hcmp
    simp [Hcompare, Hcmp', Hcmp]
  . intro Hcompare
    obtain ⟨ o', ⟨ Hcmp', Hcompare' ⟩ ⟩ := O.infallible a b
    rw [Hcompare', avl.Ordering.toLeanOrdering.injEq] at Hcompare
    simp [Hcompare.symm, Hcmp']


theorem oppositeOfOpposite {x y: _root_.Ordering}: x.toDualOrdering = y ↔ x = y.toDualOrdering := by
  cases x <;> cases y <;> simp
theorem oppositeRustOrder [Ord T] [Spec: OrdSpecSymmetry H] {a b}: H.cmp b a = .ok o ↔ H.cmp a b = .ok o.toDualOrdering := by
  rw [rustCmpEq, Spec.symmetry, compare, Ord.opposite, oppositeOfOpposite, rustCmpEq, toDualOrderingOfToLeanOrdering]

theorem ltOfRustOrder
  [LO: LinearOrder T]
  [Spec: OrdSpec H]:
  ∀ a b, H.cmp a b = .ok .Less -> a < b := by
  intros a b
  intro Hcmp
  -- why the typeclass search doesn't work here?
  refine' (@compare_lt_iff_lt T LO).1 _
  obtain ⟨ o, ⟨ Hcmp', Hcompare ⟩ ⟩ := Spec.infallible a b
  simp only [Hcmp', ok.injEq] at Hcmp
  simp [Hcompare, Hcmp, avl.Ordering.toLeanOrdering]

theorem gtOfRustOrder
  [LinearOrder T]
  [Spec: OrdSpecSymmetry H]:
  ∀ a b, H.cmp a b = .ok .Greater -> b < a := by
  intros a b
  intro Hcmp
  refine' @ltOfRustOrder _ H _ Spec.toOrdSpec _ _ _
  rewrite [oppositeRustOrder]
  simp [Hcmp]

end Specifications
