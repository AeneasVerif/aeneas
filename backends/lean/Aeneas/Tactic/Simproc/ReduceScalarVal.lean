module
public import Aeneas.Std.Scalar.Core

public section

/-!
# Simprocs for the value of scalar literals

The `seval` simprocs below turn the `.val` of a literal `UScalar`/`IScalar` value into a literal
`Nat`/`Int` value. This helps `grind`'s arithmetic procedures to recognize them as literal values.

They are the equivalent of the `reduceOfNat` simprocs for Lean's machine integers in
https://github.com/leanprover/lean4/blob/52edefc/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.lean
-/

namespace Aeneas.ReduceScalarVal

open Lean Meta
open Aeneas.Std

/-- Ground normalization of `(UScalar.ofNatCore n h).val` to the literal `n`. -/
simproc [seval] reduceUScalarOfNatCoreVal (UScalar.val (UScalar.ofNatCore _ _)) := fun e => do
  let_expr UScalar.val _ v := e | return .continue
  /- The scalar literal notations go through the reducible `UScalar.ofNat`, so we have to unfold
     before matching. -/
  let_expr UScalar.ofNatCore _ n h := ← whnfR v | return .continue
  let some _ ← getNatValue? n | return .continue
  return .done { expr := n, proof? := some (← mkAppM ``UScalar.ofNatCore_val_eq #[h]) }

/-- Ground normalization of `(IScalar.ofIntCore n h).val` to the literal `n`. -/
simproc [seval] reduceIScalarOfIntCoreVal (IScalar.val (IScalar.ofIntCore _ _)) := fun e => do
  let_expr IScalar.val _ v := e | return .continue
  /- The scalar literal notations go through the reducible `IScalar.ofInt`, so we have to unfold
     before matching. -/
  let_expr IScalar.ofIntCore _ n h := ← whnfR v | return .continue
  let some _ ← getIntValue? n | return .continue
  return .done { expr := n, proof? := some (← mkAppM ``IScalar.ofInt_val_eq #[h]) }

example : (UScalar.ofNatCore (ty := .U32) 3 (by decide)).val = 3 := by simp only [seval]
example : (IScalar.ofIntCore (ty := .I32) (-3) (by decide)).val = -3 := by simp only [seval]

/- The simprocs only fire on literals: a symbolic value is left alone. -/
example (x y : Nat) (h : x + y < 2^32) : (UScalar.ofNatCore (ty := .U32) (x + y) h).val = x + y := by
  fail_if_success simp only [seval]
  simp

example (x y : Int) (h : -2^31 ≤ x + y ∧ x + y < 2^31) :
  (IScalar.ofIntCore (ty := .I32) (x + y) h).val = x + y := by
  fail_if_success simp only [seval]
  simp

end Aeneas.ReduceScalarVal
