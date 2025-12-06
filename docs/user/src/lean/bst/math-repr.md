# Picking mathematical representations

While defining binary search trees and its operations, we needed to assume that `T`, the type of elements, supported a comparison operation:

```rust,noplayground
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}

impl Ord for u32 {
    fn cmp(&self, other: &Self) -> Ordering {
        if *self < *other {
            Ordering::Less
        } else if *self == *other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}
```

To be able to verify that the binary search tree works the way we expect, we need two ingredients:

- figure out what is the mathematical representation of the order we need for the binary search tree: in the invariant section, we chose `LinearOrder T` which is a total order over `T`. It's sufficient to build a theory of *sound* binary search trees.

- ensure that actual trait implementations satisfy our mathematical refinement we need for our verification: prove that the `u32` implementation of `Ord` yields to a `LinearOrder U32` in Lean.

## Why is it necessary to care about `Ord` ?

Consider this implementation of `Ord` for `u32`:

```rust,noplayground
impl Ord for u32 {
    fn cmp(&self, other: &Self) -> Ordering {
        if *self == 5924 { panic!(); }
        
        if *self < *other {
            Ordering::Less
        } else if *self == *other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}
```

A `u32` tree based on that implementation will not have any issue as long as we never insert `5924` in there.

From this, trait implementations have load-bearing consequences on the correctness of more complicated structures such as a tree and the verification needs to take them into account to ensure a complete correctness.

Furthermore, this problem can arise if the mathematical representation chosen is too ideal: that is, no trait implementation can be written such that it fulfills the mathematical representation chosen, or, **worse**, there's no such mathematical object *at all*.

If a whole verification is constructed on the top of an *impossible-to-fulfill-in-practice* mathematical representation, large changes may be necessary to repair the representation.

## Scalar theory in Aeneas

Aeneas provides a generic `Scalar` type mirroring some of the Rust scalar theory, i.e. scalar operations such as additions and multiplications are mirrored faithfully.

In Rust, scalars does not form an ideal mathematical structure, that is: `U64` is not \(( \mathbb{N} \)).

Likewise, additions of `U64` is well-defined as long as the result is contained in a `U64`, which means that the addition is fallible. 

In practice, Rust will panic if addition overflows unexpectedly (i.e. the code makes no use of explicit overflowing addition operators), the extraction reflects this behavior by having most operations returns a `Result (Scalar ScalarTy)` where `ScalarTy` are the word sizes, e.g. `.U32`.

Nonetheless, Rust scalars do enjoy bits of mathematical structure such as linear order definitions and panic-freedomness with their default trait implementations.

## A linear order over `Scalar .U32`

Here, we will give an example of a `LinearOrder` definition for the Aeneas scalars:

```lean
instance ScalarU32DecidableLE : DecidableRel (· ≤ · : U32 -> U32 -> Prop) := by
  simp [instLEScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance : LinearOrder (Scalar .U32) where
  le_antisymm := fun a b Hab Hba => by
    apply (Scalar.eq_equiv a b).2; exact (Int.le_antisymm ((Scalar.le_equiv _ _).1 Hab) ((Scalar.le_equiv _ _).1 Hba))
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H 
    left; exact (Scalar.le_equiv _ _).2 H 
    right; exact (Scalar.le_equiv _ _).2 H
  decidableLE := ScalarU32DecidableLE
```

This definition just exploits the fact that Aeneas' scalars can be injected in \(( \mathbb{Z} \)) and that various properties can be transferred back'n'forth via an equivalence theorem.

This definition is part of the Aeneas standard library, so you usually do not have to write your own definitions.

If you find a missing generic definition that could be useful in general, do not hesitate to send a pull request to the Aeneas project.

## An bundling of Rust orders in Lean world

Nonetheless, the previous definition is insufficient on its own, as a user can provide its own `Ord` implementation, we need to bundle a user-provided `Ord` implementation with a verification-provided `Ord` specification.

Consider the following:

```lean
variable {T: Type} (H: outParam (verification.Ord T))

-- Panic-freedomness of the Rust `Ord` implementation `H`
class OrdSpec [Ord T] where
  infallible: ∀ a b, ∃ (o: verification.Ordering), H.cmp a b = .ok o ∧ compare a b = o.toLeanOrdering

-- `a ≤ b <-> b ≥ a`
class OrdSpecSymmetry [O: Ord T] extends OrdSpec H where
  symmetry: ∀ a b, O.compare a b = (O.opposite.compare a b).toDualOrdering

-- A generalized equality specification
class OrdSpecRel [O: Ord T] (R: outParam (T -> T -> Prop)) extends OrdSpec H where
  equivalence: ∀ a b, H.cmp a b = .ok .Equal -> R a b

-- We specialize the previous specifications to the case of the equivalence relation `=`, equality.
class OrdSpecLinearOrderEq [O: Ord T] extends OrdSpecSymmetry H, OrdSpecRel H Eq
```

With all those pieces, we only need to prove that the extracted `OrdU32` implementation fulfills `OrdSpecLinearOrderEq` which is one of the pre-requisite to benefit from a formal verification of binary search trees over Rust `u32` scalars.

Here's a solution to that proof:

```lean
instance : OrdSpecLinearOrderEq OrdU32 where
  infallible := fun a b => by
    unfold Ord.cmp
    unfold OrdU32
    unfold OrdU32.cmp
    rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    if hlt : a < b then 
      use .Less
      simp [hlt]
    else
      if heq: a = b
      then
      use .Equal
      simp [hlt]
      rw [heq]
      else
        use .Greater
        simp [hlt, heq]
  symmetry := fun a b => by
    rw [Ordering.toDualOrdering, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    rw [compare, Ord.opposite]
    simp [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    split_ifs with hab hba hba' hab' hba'' _ hba₃ _ <;> tauto
    exact lt_irrefl _ (lt_trans hab hba)
    rw [hba'] at hab; exact lt_irrefl _ hab
    rw [hab'] at hba''; exact lt_irrefl _ hba''
    -- The order is total, therefore, we have at least one case where we are comparing something.
    cases (lt_trichotomy a b) <;> tauto
  equivalence := fun a b => by
    unfold Ord.cmp
    unfold OrdU32
    unfold OrdU32.cmp
    simp only []
    split_ifs <;> simp only [Result.ok.injEq, not_false_eq_true, neq_imp, IsEmpty.forall_iff]; tauto; try assumption
```

Proving panic-freedomness, symmetry and equality comes from definition unfolding and going through the Rust code which is equal to a 'canonical' definition of `compare` assuming the existence of an linear order.

Therefore, we just reuse the linear order properties to finish most of those proofs once all definitions are unfolded.
