import Plausible
import Aeneas.Std.Scalar.Core
import Aeneas.Std.SliceDef
import Aeneas.Std.Vec
import Aeneas.Std.Array.Array
import Aeneas.Std.WP

/-! # `Plausible` instances for Aeneas `Std` types

`SampleableExt`/`Decidable` instances so `plausible` can property-test spec theorems over
Aeneas-extracted types. Counter-examples are printed via each type's `SampleableExt.proxy`
`Repr`. -/

open Plausible

namespace Aeneas.Std

universe u

/-! ## Scalars -/

/-- Sample a `UScalar` uniformly over `[0, UScalar.max ty]`. -/
private def genUScalar (ty : UScalarTy) : Gen Nat := do
  let ⟨m, _⟩ ← Gen.choose Nat 0 (UScalar.max ty) (Nat.zero_le _)
  pure m

instance UScalar.sampleableExt {ty : UScalarTy} : SampleableExt (UScalar ty) where
  proxy := Nat
  sample := ⟨genUScalar ty⟩
  interp n := ⟨BitVec.ofNat _ n⟩

/-- Sample an `IScalar` uniformly over `[IScalar.min ty, IScalar.max ty]`. -/
private def genIScalar (ty : IScalarTy) : Gen Int := do
  have h : IScalar.min ty ≤ IScalar.max ty := by
    have : (0 : Int) < 2 ^ (ty.numBits - 1) := by positivity
    grind [IScalar.min, IScalar.max]
  let ⟨m, _⟩ ← Gen.choose Int (IScalar.min ty) (IScalar.max ty) h
  pure m

instance IScalar.sampleableExt {ty : IScalarTy} : SampleableExt (IScalar ty) where
  proxy := Int
  sample := ⟨genIScalar ty⟩
  interp z := ⟨BitVec.ofInt _ z⟩

/-! ## `Slice` / `Vec` -/

/-- Interpret a proxy list as a length-bounded `Slice`/`Vec`. -/
private def interpBoundedList {α : Type u} [SampleableExt α]
    (l : List (SampleableExt.proxy α)) : { l : List α // l.length ≤ Usize.max } :=
  let l' := l.map SampleableExt.interp
  if h : l'.length ≤ Usize.max then ⟨l', h⟩ else ⟨[], Nat.zero_le _⟩

instance Slice.sampleableExt {α : Type u} [SampleableExt α] : SampleableExt (Slice α) where
  proxy := List (SampleableExt.proxy α)
  sample := inferInstance
  interp := interpBoundedList

instance alloc.vec.Vec.sampleableExt {α : Type u} [SampleableExt α] :
    SampleableExt (alloc.vec.Vec α) where
  proxy := List (SampleableExt.proxy α)
  sample := inferInstance
  interp := interpBoundedList

/-! ## `Array α n` -/

/-- Generate a list of `m` independently sampled elements. -/
private def genFixedList {β : Type u} [Arbitrary β] :
    (m : Nat) → Gen { l : List β // l.length = m }
  | 0 => pure ⟨[], rfl⟩
  | m + 1 => do
    let x ← Arbitrary.arbitrary
    let ⟨xs, h⟩ ← genFixedList m
    pure ⟨x :: xs, by simp [h]⟩

/-- Shrink one element at a time; `List.set` preserves the fixed length. -/
private def shrinkFixedList {β : Type u} [Shrinkable β] {m : Nat}
    (x : { l : List β // l.length = m }) : List { l : List β // l.length = m } :=
  (List.finRange x.val.length).flatMap fun ⟨i, hi⟩ =>
    (Shrinkable.shrink (x.val.get ⟨i, hi⟩)).map fun x' =>
      ⟨x.val.set i x', by simp [x.property]⟩

instance Array.sampleableExt {α : Type u} {n : Usize} [SampleableExt α] :
    SampleableExt (Array α n) where
  proxy := { l : List (SampleableExt.proxy α) // l.length = n.val }
  proxyRepr := ⟨fun x prec => reprPrec x.val prec⟩
  shrink := ⟨shrinkFixedList⟩
  sample := ⟨genFixedList n.val⟩
  interp x := ⟨x.val.map SampleableExt.interp, by simp [x.property]⟩

/-! ## `Result` / `Error` -/

instance Error.shrinkable : Shrinkable Error where shrink _ := []

instance Error.Arbitrary : Arbitrary Error where
  arbitrary := Gen.elements
    [.assertionFailure, .integerOverflow, .divisionByZero, .arrayOutOfBounds,
     .maximumSizeExceeded, .panic, .undef] (by decide)

instance Result.sampleableExt {α : Type u} [SampleableExt α] : SampleableExt (Result α) where
  proxy := Result (SampleableExt.proxy α)
  shrink := ⟨fun _ => []⟩
  sample := ⟨do
    match ← Gen.choose Nat 0 2 (by omega) with
    | ⟨0, _⟩ => .ok <$> Arbitrary.arbitrary
    | ⟨1, _⟩ => .fail <$> Arbitrary.arbitrary
    | _      => pure .div⟩
  interp
    | .ok x => .ok (SampleableExt.interp x)
    | .fail e => .fail e
    | .div => .div

/-! ## Deciding hypotheses & goals so `plausible` can evaluate specs -/

/- `WP.spec x p = theta x p`: `ok v` reduces to `p v`, `fail`/`div` to `False`. -/
instance WP.decidableSpec {α : Type u} {x : Result α} {p : WP.Post α} [∀ a, Decidable (p a)] :
    Decidable (WP.spec x p) := by
  unfold WP.spec WP.theta WP.wp_return
  split <;> infer_instance

/- `plausible` wraps quantifiers in `NamedBinder` so a bounded `∀` hypothesis with `Nat` index needs
the following two instances. -/

/- Strip a `NamedBinder` wrapper. -/
instance NamedBinder.decidable {s : String} {P : Prop} [Decidable P] :
    Decidable (NamedBinder s P) := ‹Decidable P›

/- The shape `plausible` generates for a bounded-∀ hypothesis `∀ i < n, Q i`. The wrapped body
hides the bound, so core's `Nat.decidableBallLT` can't fire directly; reduce to `Fin n`. -/
instance NamedBinder.decidableBallLT {n : Nat} {Q : Nat → Prop} [DecidablePred Q] {s : String} :
    Decidable (∀ i : Nat, NamedBinder s (i < n → Q i)) :=
  decidable_of_iff (∀ j : Fin n, Q j.val) ⟨fun h i hi => h ⟨i, hi⟩, fun h j => h j.val j.isLt⟩


end Aeneas.Std
