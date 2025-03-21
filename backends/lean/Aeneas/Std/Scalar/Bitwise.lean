import Aeneas.Std.Scalar.Core
import Aeneas.ScalarTac
import Aeneas.Std.Core
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith

/-!
# Bitwise Operations: Definitions
-/

/-!
Bit shifts
-/
def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.shiftLeft s ⟩
  else fail .integerOverflow

def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.ushiftRight s ⟩
  else fail .integerOverflow

def UScalar.shiftLeft_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.val

def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.val

def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.shiftLeft s ⟩
  else fail .integerOverflow

def IScalar.shiftRight {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.sshiftRight s ⟩
  else fail .integerOverflow

def IScalar.shiftLeft_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftLeft s.val

def IScalar.shiftRight_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftRight s.val

def IScalar.shiftLeft_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.val ≥ 0 then
    x.shiftLeft s.toNat
  else fail .integerOverflow

def IScalar.shiftRight_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.val ≥ 0 then
    x.shiftRight s.toNat
  else fail .integerOverflow

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_IScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (UScalar ty1) (Result (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (IScalar ty1) (Result (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_IScalar x y

/-!
Bitwise and
-/
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv &&& y.bv ⟩

def IScalar.and {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv &&& y.bv ⟩

instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y

instance {ty} : HAnd (IScalar ty) (IScalar ty) (IScalar ty) where
  hAnd x y := IScalar.and x y

/-!
Bitwise or
-/
def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv ||| y.bv ⟩

def IScalar.or {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv ||| y.bv ⟩

instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y

instance {ty} : HOr (IScalar ty) (IScalar ty) (IScalar ty) where
  hOr x y := IScalar.or x y

/-!
Xor
-/
def UScalar.xor {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv ||| y.bv ⟩

def IScalar.xor {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv ||| y.bv ⟩

instance {ty} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor x y := UScalar.xor x y

instance {ty} : HXor (IScalar ty) (IScalar ty) (IScalar ty) where
  hXor x y := IScalar.xor x y

/-!
Not
-/
def UScalar.not {ty} (x : UScalar ty) : UScalar ty := ⟨ ~~~x.bv ⟩

def IScalar.not {ty} (x : IScalar ty) : IScalar ty := ⟨ ~~~x.bv ⟩

instance {ty} : Complement (UScalar ty) where
  complement x := UScalar.not x

instance {ty} : Complement (IScalar ty) where
  complement x := IScalar.not x

/-!
# Bitwise Operations: Theorems
-/


/-!
## Bit shifts
-/

theorem UScalar.ShiftRight_val_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.val < ty0.numBits) :
  ∃ z, x >>> y = ok z ∧
  z.val = x.val >>> y.val
  := by
  simp only [HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight, hy, reduceIte]
  simp only [BitVec.ushiftRight_eq, ok.injEq, _root_.exists_eq_left', val]
  simp [HShiftRight.hShiftRight, BitVec.ushiftRight]

theorem UScalar.ShiftRight_bv_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.val < ty0.numBits) :
  ∃ z, x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by
  simp only [HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight, hy, reduceIte]
  simp only [BitVec.ushiftRight_eq, ok.injEq, _root_.exists_eq_left', val]

@[progress] theorem U8.ShiftRight_bv_spec (x : U8) (y : UScalar ty1) (hy : y.val < 8) :
  ∃ (z : U8), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp [*]

@[progress] theorem U16.ShiftRight_bv_spec (x : U16) (y : UScalar ty1) (hy : y.val < 16) :
  ∃ (z : U16), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp [*]

@[progress] theorem U32.ShiftRight_bv_spec (x : U32) (y : UScalar ty1) (hy : y.val < 32) :
  ∃ (z : U32), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp [*]

@[progress] theorem U64.ShiftRight_bv_spec (x : U64) (y : UScalar ty1) (hy : y.val < 64) :
  ∃ (z : U64), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp [*]

@[progress] theorem U128.ShiftRight_bv_spec (x : U128) (y : UScalar ty1) (hy : y.val < 128) :
  ∃ (z : U128), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp [*]

@[progress] theorem Usize.ShiftRight_bv_spec (x : Usize) (y : UScalar ty1) (hy : y.val < UScalarTy.Usize.numBits) :
  ∃ (z : Usize), x >>> y = ok z ∧ z.bv = x.bv >>> y.val
  := by apply UScalar.ShiftRight_bv_spec; simp only [*]

theorem UScalar.ShiftRight_IScalar_bv_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.val) (hy1 : y.val < ty0.numBits) :
  ∃ z, x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [HShiftRight.hShiftRight, shiftRight_IScalar, shiftRight, hy0, hy1, reduceIte]
  simp only [BitVec.ushiftRight_eq, ok.injEq, _root_.exists_eq_left', val]

@[progress] theorem U8.ShiftRight_IScalar_bv_spec (x : U8) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 8) :
  ∃ (z : U8), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp [*]

@[progress] theorem U16.ShiftRight_IScalar_bv_spec (x : U16) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 16) :
  ∃ (z : U16), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp [*]

@[progress] theorem U32.ShiftRight_IScalar_bv_spec (x : U32) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 32) :
  ∃ (z : U32), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp [*]

@[progress] theorem U64.ShiftRight_IScalar_bv_spec (x : U64) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 64) :
  ∃ (z : U64), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp [*]

@[progress] theorem U128.ShiftRight_IScalar_bv_spec (x : U128) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 128) :
  ∃ (z : U128), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp [*]

@[progress] theorem Usize.ShiftRight_IScalar_bv_spec (x : Usize) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < UScalarTy.Usize.numBits) :
  ∃ (z : Usize), x >>> y = ok z ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_bv_spec <;> simp only [*]

theorem UScalar.ShiftLeft_val_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.val < ty0.numBits) :
  ∃ z, x <<< y = ok z ∧
  z.val = (x.val <<< y.val) % 2^ty0.numBits
  := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte]
  simp only [BitVec.shiftLeft_eq, ok.injEq, _root_.exists_eq_left', val]
  simp [ShiftLeft.shiftLeft]

theorem UScalar.ShiftLeft_bv_eq {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.val < ty0.numBits) :
  ∃ z, x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte]
  simp only [BitVec.shiftLeft_eq, ok.injEq, _root_.exists_eq_left', val]

@[progress] theorem U8.ShiftLeft_bv_spec (x : U8) (y : UScalar ty1) (hy : y.val < 8) :
  ∃ (z : U8), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp [*]

@[progress] theorem U16.ShiftLeft_bv_spec (x : U16) (y : UScalar ty1) (hy : y.val < 16) :
  ∃ (z : U16), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp [*]

@[progress] theorem U32.ShiftLeft_bv_spec (x : U32) (y : UScalar ty1) (hy : y.val < 32) :
  ∃ (z : U32), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp [*]

@[progress] theorem U64.ShiftLeft_bv_spec (x : U64) (y : UScalar ty1) (hy : y.val < 64) :
  ∃ (z : U64), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp [*]

@[progress] theorem U128.ShiftLeft_bv_spec (x : U128) (y : UScalar ty1) (hy : y.val < 128) :
  ∃ (z : U128), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp [*]

@[progress] theorem Usize.ShiftLeft_bv_spec (x : Usize) (y : UScalar ty1) (hy : y.val < UScalarTy.Usize.numBits) :
  ∃ (z : Usize), x <<< y = ok z ∧ z.bv = x.bv <<< y.val
  := by apply UScalar.ShiftLeft_bv_eq; simp only [*]

theorem UScalar.ShiftLeft_IScalar_val_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.val) (hy1 : y.val < ty0.numBits) :
  ∃ z, x <<< y = ok z ∧
  z.val = (x.val <<< y.toNat) % 2^ty0.numBits
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft, hy0, hy1, reduceIte]
  simp only [BitVec.shiftLeft_eq, ok.injEq, _root_.exists_eq_left', val]
  simp [ShiftLeft.shiftLeft]

theorem UScalar.ShiftLeft_IScalar_bv_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.val) (hy : y.val < ty0.numBits) :
  ∃ z, x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft, hy0, hy1, reduceIte]
  simp only [BitVec.shiftLeft_eq, ok.injEq, _root_.exists_eq_left', val]

@[progress] theorem U8.ShiftLeft_IScalar_bv_spec (x : U8) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 8) :
  ∃ (z : U8), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp [*]

@[progress] theorem U16.ShiftLeft_IScalar_bv_spec (x : U16) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 16) :
  ∃ (z : U16), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp [*]

@[progress] theorem U32.ShiftLeft_IScalar_bv_spec (x : U32) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 32) :
  ∃ (z : U32), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp [*]

@[progress] theorem U64.ShiftLeft_IScalar_bv_spec (x : U64) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 64) :
  ∃ (z : U64), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp [*]

@[progress] theorem U128.ShiftLeft_IScalar_bv_spec (x : U128) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < 128) :
  ∃ (z : U128), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp [*]

@[progress] theorem Usize.ShiftLeft_IScalar_bv_spec (x : Usize) (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < UScalarTy.Usize.numBits) :
  ∃ (z : Usize), x <<< y = ok z ∧ z.bv = x.bv <<< y.toNat
  := by apply UScalar.ShiftLeft_IScalar_bv_spec <;> simp only [*]

/-!
## Bitwise And, Or
-/

@[progress]
theorem UScalar.and_spec {ty} (x y : UScalar ty) :
  ∃ z, toResult (x &&& y) = ok z ∧
  z.val = (x &&& y).val ∧
  z.bv = x.bv &&& y.bv := by
  simp [toResult]
  rfl

@[progress]
theorem UScalar.or_spec {ty} (x y : UScalar ty) :
  ∃ z, toResult (x ||| y) = ok z ∧ z.val = (x ||| y).val ∧ z.bv = x.bv||| y.bv := by
  simp [toResult]
  rfl

@[progress]
theorem IScalar.and_spec {ty} (x y : IScalar ty) :
  ∃ z, toResult (x &&& y) = ok z ∧ z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv := by
  simp [toResult]
  rfl

@[progress]
theorem IScalar.or_spec {ty} (x y : IScalar ty) :
  ∃ z, toResult (x ||| y) = ok z ∧ z.val = (x ||| y).val ∧ z.bv = x.bv||| y.bv := by
  simp [toResult]
  rfl

@[simp, bvify_simps] theorem UScalar.bv_and {ty} (x y : UScalar ty) : (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp, bvify_simps] theorem UScalar.bv_or {ty} (x y : UScalar ty) : (x ||| y).bv = x.bv ||| y.bv := by rfl
@[simp, bvify_simps] theorem IScalar.bv_and {ty} (x y : IScalar ty) : (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp, bvify_simps] theorem IScalar.bv_or {ty} (x y : IScalar ty) : (x ||| y).bv = x.bv ||| y.bv := by rfl

end Aeneas.Std
