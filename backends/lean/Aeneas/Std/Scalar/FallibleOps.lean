import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Std.Scalar.Ops.Div
import Aeneas.Std.Scalar.Ops.Rem
import Aeneas.Std.Scalar.Bitwise

/-!
# Fallible Arithmetic Notations

Scalar arithmetic operations that can fail (overflow, division by zero) currently use
standard operator notation (`+`, `-`, `*`, `/`, `%`, `<<<`, `>>>`), returning `Result`.
This conflicts with the convention that `+` etc. are total operations.

This module introduces `+?`, `-?`, `*?`, `/?`, `%?`, `<<?`, `>>?` notations for the
fallible versions, so that `+`, `-`, etc. can eventually be reserved for infallible
(e.g., wrapping) operations.

The existing `HAdd`/`HSub`/etc. instances returning `Result` are kept for backward
compatibility but are intended to be deprecated in a future release.
-/

namespace Aeneas.Std

/-!
## Type classes
-/

class HAddCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAddCheck : α → β → γ

class HSubCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSubCheck : α → β → γ

class HMulCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMulCheck : α → β → γ

class HDivCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hDivCheck : α → β → γ

class HModCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hModCheck : α → β → γ

class HShiftLeftCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftLeftCheck : α → β → γ

class HShiftRightCheck (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftRightCheck : α → β → γ

/-!
## Notations
-/

infixl:65 " +? " => HAddCheck.hAddCheck
infixl:65 " -? " => HSubCheck.hSubCheck
infixl:70 " *? " => HMulCheck.hMulCheck
infixl:70 " /? " => HDivCheck.hDivCheck
infixl:70 " %? " => HModCheck.hModCheck
infixl:75 " <<? " => HShiftLeftCheck.hShiftLeftCheck
infixl:75 " >>? " => HShiftRightCheck.hShiftRightCheck

/-!
## Instances: Arithmetic
-/

instance {ty} : HAddCheck (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAddCheck := UScalar.add

instance {ty} : HAddCheck (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hAddCheck := IScalar.add

instance {ty} : HSubCheck (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hSubCheck := UScalar.sub

instance {ty} : HSubCheck (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hSubCheck := IScalar.sub

instance {ty} : HMulCheck (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMulCheck := UScalar.mul

instance {ty} : HMulCheck (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hMulCheck := IScalar.mul

instance {ty} : HDivCheck (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hDivCheck := UScalar.div

instance {ty} : HDivCheck (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hDivCheck := IScalar.div

instance {ty} : HModCheck (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hModCheck := UScalar.rem

instance {ty} : HModCheck (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hModCheck := IScalar.rem

/-!
## Instances: Shifts
-/

instance {ty0 ty1} : HShiftLeftCheck (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftLeftCheck := UScalar.shiftLeft_UScalar

instance {ty0 ty1} : HShiftLeftCheck (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftLeftCheck := UScalar.shiftLeft_IScalar

instance {ty0 ty1} : HShiftLeftCheck (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftLeftCheck := IScalar.shiftLeft_UScalar

instance {ty0 ty1} : HShiftLeftCheck (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftLeftCheck := IScalar.shiftLeft_IScalar

instance {ty0 ty1} : HShiftRightCheck (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftRightCheck := UScalar.shiftRight_UScalar

instance {ty0 ty1} : HShiftRightCheck (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftRightCheck := UScalar.shiftRight_IScalar

instance {ty0 ty1} : HShiftRightCheck (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftRightCheck := IScalar.shiftRight_UScalar

instance {ty0 ty1} : HShiftRightCheck (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftRightCheck := IScalar.shiftRight_IScalar

/-!
## Equivalence lemmas

These lemmas ensure `step` and `simp` can see through the new notations.
-/

@[simp] theorem UScalar.hAddCheck_eq {ty} (x y : UScalar ty) : x +? y = x + y := rfl
@[simp] theorem IScalar.hAddCheck_eq {ty} (x y : IScalar ty) : x +? y = x + y := rfl
@[simp] theorem UScalar.hSubCheck_eq {ty} (x y : UScalar ty) : x -? y = x - y := rfl
@[simp] theorem IScalar.hSubCheck_eq {ty} (x y : IScalar ty) : x -? y = x - y := rfl
@[simp] theorem UScalar.hMulCheck_eq {ty} (x y : UScalar ty) : x *? y = x * y := rfl
@[simp] theorem IScalar.hMulCheck_eq {ty} (x y : IScalar ty) : x *? y = x * y := rfl
@[simp] theorem UScalar.hDivCheck_eq {ty} (x y : UScalar ty) : x /? y = x / y := rfl
@[simp] theorem IScalar.hDivCheck_eq {ty} (x y : IScalar ty) : x /? y = x / y := rfl
@[simp] theorem UScalar.hModCheck_eq {ty} (x y : UScalar ty) : x %? y = x % y := rfl
@[simp] theorem IScalar.hModCheck_eq {ty} (x y : IScalar ty) : x %? y = x % y := rfl

@[simp] theorem UScalar.hShiftLeftCheck_UScalar_eq {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) : x <<? y = x <<< y := rfl
@[simp] theorem UScalar.hShiftLeftCheck_IScalar_eq {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) : x <<? y = x <<< y := rfl
@[simp] theorem IScalar.hShiftLeftCheck_UScalar_eq {ty0 ty1} (x : IScalar ty0) (y : UScalar ty1) : x <<? y = x <<< y := rfl
@[simp] theorem IScalar.hShiftLeftCheck_IScalar_eq {ty0 ty1} (x : IScalar ty0) (y : IScalar ty1) : x <<? y = x <<< y := rfl

@[simp] theorem UScalar.hShiftRightCheck_UScalar_eq {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) : x >>? y = x >>> y := rfl
@[simp] theorem UScalar.hShiftRightCheck_IScalar_eq {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) : x >>? y = x >>> y := rfl
@[simp] theorem IScalar.hShiftRightCheck_UScalar_eq {ty0 ty1} (x : IScalar ty0) (y : UScalar ty1) : x >>? y = x >>> y := rfl
@[simp] theorem IScalar.hShiftRightCheck_IScalar_eq {ty0 ty1} (x : IScalar ty0) (y : IScalar ty1) : x >>? y = x >>> y := rfl

end Aeneas.Std
