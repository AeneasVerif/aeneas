import Avl.Funs
open Aeneas Std Result

namespace avl

@[simp]
def Ordering.toLeanOrdering (o: avl.Ordering): _root_.Ordering := match o with
| .Less => .lt
| .Equal => .eq
| .Greater => .gt

@[simp]
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

variable {T: Type} (H: outParam (Ord T))

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
class OrdSpec [_root_.Ord T] where
  infallible: ∀ a b, H.cmp a b ⦃ o => compare a b = o.toLeanOrdering ⦄

class OrdSpecSymmetry [O: _root_.Ord T] extends OrdSpec H where
  symmetry: ∀ a b, O.compare a b = (O.opposite.compare a b).toDualOrdering

-- Must be R decidableRel and an equivalence relationship?
class OrdSpecRel [O: _root_.Ord T] (R: outParam (T -> T -> Prop)) extends OrdSpec H where
  equivalence: ∀ a b, H.cmp a b = .ok .Equal -> R a b

class OrdSpecLinearOrderEq [O: _root_.Ord T] extends OrdSpecSymmetry H, OrdSpecRel H Eq

theorem infallible [_root_.Ord T] [OrdSpec H]: ∀ a b, H.cmp a b ⦃ _ => True ⦄ := fun a b => by
  step with OrdSpec.infallible

instance: Coe (avl.Ordering) (_root_.Ordering) where
  coe a := a.toLeanOrdering

/-- Stated semantically.  `H.cmp a b = .ok o` is a claim about the *shape* of the
computation, and a `spec` no longer implies one: it rules out failure and
divergence, but not an event.  `H.cmp a b ⦃ o' => o' = o ⦄` says what the
syntactic form was being used to say -- the comparison evaluates to `o`. -/
theorem rustCmpEq [_root_.Ord T] [O: OrdSpec H]:
    H.cmp a b ⦃ o' => o' = o ⦄ <-> compare a b = o.toLeanOrdering := by
  apply Iff.intro
  . intro Hcmp
    obtain ⟨ o', Ho', Hcompare ⟩ :=
      WP.spec_exists (WP.spec_and Hcmp (O.infallible a b))
    rw [Hcompare, Ho']
  . intro Hcompare
    refine WP.spec_mono (O.infallible a b) fun o' Ho' => ?_
    rw [Ho', avl.Ordering.toLeanOrdering.injEq] at Hcompare
    exact Hcompare


theorem oppositeOfOpposite {x y: _root_.Ordering}: x.toDualOrdering = y ↔ x = y.toDualOrdering := by
  cases x <;> cases y <;> simp
theorem oppositeRustOrder [_root_.Ord T] [Spec: OrdSpecSymmetry H] {a b}:
    H.cmp b a ⦃ o' => o' = o ⦄ ↔ H.cmp a b ⦃ o' => o' = o.toDualOrdering ⦄ := by
  rw [rustCmpEq, Spec.symmetry, compare, Ord.opposite, oppositeOfOpposite, rustCmpEq, toDualOrderingOfToLeanOrdering]

theorem ltOfRustOrder
  [LO: LinearOrder T]
  [Spec: OrdSpec H]:
  ∀ a b, H.cmp a b ⦃ o => o = .Less ⦄ -> a < b := by
  intros a b
  intro Hcmp
  -- why the typeclass search doesn't work here?
  refine' (@compare_lt_iff_lt T LO).1 _
  have Hcompare := (rustCmpEq H).mp Hcmp
  simp [Hcompare, avl.Ordering.toLeanOrdering]

theorem gtOfRustOrder
  [LinearOrder T]
  [Spec: OrdSpecSymmetry H]:
  ∀ a b, H.cmp a b ⦃ o => o = .Greater ⦄ -> b < a := by
  intros a b
  intro Hcmp
  refine' @ltOfRustOrder _ H _ Spec.toOrdSpec _ _ _
  rewrite [oppositeRustOrder]
  simpa using Hcmp

-- TODO: move to standard library
@[simp]
theorem compare_eq_lt_iff [LinOrd : LinearOrder T] (x y : T) :
  compare x y = Ordering.lt ↔ x < y := by
  grind [LinOrd.compare_eq_compareOfLessAndEq, compareOfLessAndEq]

-- TODO: move to standard library
@[simp]
theorem compare_eq_equal_iff [LinOrd : LinearOrder T] (x y : T) :
  compare x y = Ordering.eq ↔ x = y := by
  grind [LinOrd.compare_eq_compareOfLessAndEq, compareOfLessAndEq]

-- TODO: move to standard library
@[simp]
theorem compare_eq_gt_iff [LinOrd : LinearOrder T] (x y : T) :
  compare x y = Ordering.gt ↔ y < x := by
  grind [LinOrd.compare_eq_compareOfLessAndEq, compareOfLessAndEq]

end avl
