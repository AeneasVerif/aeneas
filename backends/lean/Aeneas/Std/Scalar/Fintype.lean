import Aeneas.Std.Scalar.Core
import Mathlib.Data.Fintype.Basic

/-! # `Fintype` instances for the scalar types

`UScalar ty` / `IScalar ty` wrap a `BitVec`, so they are finite. A `Fintype` instance makes
quantified properties over them decidable. -/

namespace Aeneas.Std

/-- `UScalar ty` is equivalent to `Fin (2 ^ ty.numBits)`. -/
def UScalar.equivFin {ty : UScalarTy} : UScalar ty ≃ Fin (2 ^ ty.numBits) where
  toFun x := x.bv.toFin
  invFun k := ⟨BitVec.ofFin k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `IScalar ty` is equivalent to `Fin (2 ^ ty.numBits)`. -/
def IScalar.equivFin {ty : IScalarTy} : IScalar ty ≃ Fin (2 ^ ty.numBits) where
  toFun x := x.bv.toFin
  invFun k := ⟨BitVec.ofFin k⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (ty : UScalarTy) : Fintype (UScalar ty) := Fintype.ofEquiv _ UScalar.equivFin.symm
instance (ty : IScalarTy) : Fintype (IScalar ty) := Fintype.ofEquiv _ IScalar.equivFin.symm

end Aeneas.Std
