import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Bitwise Operations: Definitions
-/

/-!
Bit shifts
-/
def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.shiftLeft s ⟩
  else fail .integerOverflow

def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.ushiftRight s ⟩
  else fail .integerOverflow

def UScalar.shiftLeft_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftLeft s.toNat

def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.shiftLeft s ⟩
  else fail .integerOverflow

def IScalar.shiftRight {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  Result (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.toBitVec.sshiftRight s ⟩
  else fail .integerOverflow

def IScalar.shiftLeft_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftLeft s.toNat

def IScalar.shiftRight_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  Result (IScalar ty) :=
  x.shiftRight s.toNat

def IScalar.shiftLeft_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
    x.shiftLeft s.toNat
  else fail .integerOverflow

def IScalar.shiftRight_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  Result (IScalar ty) :=
  if s.toInt ≥ 0 then
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
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec &&& y.toBitVec ⟩

def IScalar.and {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec &&& y.toBitVec ⟩

instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y

instance {ty} : HAnd (IScalar ty) (IScalar ty) (IScalar ty) where
  hAnd x y := IScalar.and x y

/-!
Bitwise or
-/
def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec ||| y.toBitVec ⟩

def IScalar.or {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec ||| y.toBitVec ⟩

instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y

instance {ty} : HOr (IScalar ty) (IScalar ty) (IScalar ty) where
  hOr x y := IScalar.or x y

/-!
Xor
-/
def UScalar.xor {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec ^^^ y.toBitVec ⟩

def IScalar.xor {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec ^^^ y.toBitVec ⟩

instance {ty} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor x y := UScalar.xor x y

instance {ty} : HXor (IScalar ty) (IScalar ty) (IScalar ty) where
  hXor x y := IScalar.xor x y

/-!
Not
-/
def UScalar.not {ty} (x : UScalar ty) : UScalar ty := ⟨ ~~~x.toBitVec ⟩

def IScalar.not {ty} (x : IScalar ty) : IScalar ty := ⟨ ~~~x.toBitVec ⟩

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

theorem UScalar.ShiftRight_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1)
  (hy : y.toNat < ty0.numBits) :
  (x >>> y) ⦃ z =>
    z.toNat = x.toNat >>> y.toNat ∧
    z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by
  simp only [spec_ok, HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight, hy, reduceIte]
  simp only [BitVec.ushiftRight_eq, toNat]
  simp only [HShiftRight.hShiftRight, BitVec.ushiftRight, toBitVec_toNat, BitVec.toNat_ofNatLT, and_self]

uscalar @[step] theorem «%S».ShiftRight_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.toNat < %BitWidth) :
  (x >>> y) ⦃ z => z.toNat = x.toNat >>> y.toNat ∧ z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by apply UScalar.ShiftRight_spec; simp [*]

theorem UScalar.ShiftRight_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.toNat) (hy1 : y.toNat < ty0.numBits) :
  (x >>> y) ⦃ z => z.toNat = x.toNat >>> y.toNat ∧ z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [spec_ok, HShiftRight.hShiftRight, shiftRight_IScalar, shiftRight, hy1, reduceIte]
  simp only [BitVec.ushiftRight_eq, toNat, Nat.instShiftRight]
  simp only [IScalar.toNat, BitVec.toNat_ushiftRight, toBitVec_toNat, Nat.shiftRight_eq, and_self]

uscalar @[step] theorem «%S».ShiftRight_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.toNat) (hy : y.toNat < %BitWidth) :
  (x >>> y) ⦃ z => z.toNat = x.toNat >>> y.toNat ∧ z.toBitVec = x.toBitVec >>> y.toNat ⦄
  := by apply UScalar.ShiftRight_IScalar_spec <;> simp [*]

theorem UScalar.ShiftLeft_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) (size : Nat)
  (hy : y.toNat < ty0.numBits) (hsize : size = UScalar.size ty0) :
  (x <<< y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % size ∧
  z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by
  simp only [spec_ok, HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte, hsize, UScalar.size]
  simp only [BitVec.shiftLeft_eq, toNat]
  simp only [toBitVec_toNat, BitVec.toNat_shiftLeft, ShiftLeft.shiftLeft, Nat.shiftLeft_eq', and_self]

uscalar @[step] theorem «%S».ShiftLeft_spec {ty1} (x : «%S») (y : UScalar ty1) (hy : y.toNat < %BitWidth) :
  (x <<< y) ⦃ z => z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧ z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by apply UScalar.ShiftLeft_spec <;> simp [*]

theorem UScalar.ShiftLeft_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) (size : Nat)
  (hy0 : 0 ≤ y.toNat) (hy1 : y.toNat < ty0.numBits) (hsize : size = UScalar.size ty0) :
  (x <<< y) ⦃ z =>
  z.toNat = (x.toNat <<< y.toNat) % size ∧
  z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [spec_ok,HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft, hy1, reduceIte, hsize,
    UScalar.size]
  simp only [BitVec.shiftLeft_eq, toNat]
  simp only [IScalar.toNat, BitVec.toNat_shiftLeft, toBitVec_toNat, ShiftLeft.shiftLeft,
    Nat.shiftLeft_eq', and_self]

uscalar @[step] theorem «%S».ShiftLeft_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.toNat) (hy : y.toNat < %BitWidth) :
  (x <<< y) ⦃ z => z.toNat = (x.toNat <<< y.toNat) % «%S».size ∧ z.toBitVec = x.toBitVec <<< y.toNat ⦄
  := by apply UScalar.ShiftLeft_IScalar_spec <;> simp [*]

/-!
## Bitwise And, Or
-/

@[step]
theorem UScalar.and_spec {ty} (x y : UScalar ty) :
  lift (x &&& y) ⦃ z => z.toNat = (x &&& y).toNat ∧ z.toBitVec = x.toBitVec &&& y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem UScalar.or_spec {ty} (x y : UScalar ty) :
  lift (x ||| y) ⦃ z => z.toNat = (x ||| y).toNat ∧ z.toBitVec = x.toBitVec ||| y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem UScalar.xor_spec {ty} (x y : UScalar ty) :
  lift (x ^^^ y) ⦃ z => z.toNat = (x ^^^ y).toNat ∧ z.toBitVec = x.toBitVec ^^^ y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem IScalar.and_spec {ty} (x y : IScalar ty) :
  lift (x &&& y) ⦃ z => z.toInt = (x &&& y).toInt ∧ z.toBitVec = x.toBitVec &&& y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem IScalar.or_spec {ty} (x y : IScalar ty) :
  lift (x ||| y) ⦃ z => z.toInt = (x ||| y).toInt ∧ z.toBitVec = x.toBitVec ||| y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem IScalar.xor_spec {ty} (x y : IScalar ty) :
  lift (x ^^^ y) ⦃ z => z.toInt = (x ^^^ y).toInt ∧ z.toBitVec = x.toBitVec ^^^ y.toBitVec ⦄ := by
  simp [lift]
  rfl

@[step]
theorem UScalar.not_spec {ty} (x : UScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

@[step]
theorem IScalar.not_spec {ty} (x : IScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

@[simp, bvify, grind =, agrind =] theorem UScalar.toBitVec_and {ty} (x y : UScalar ty) : (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.toBitVec_or {ty} (x y : UScalar ty) : (x ||| y).toBitVec = x.toBitVec ||| y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.toBitVec_xor {ty} (x y : UScalar ty) : (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.toBitVec_not {ty} (x : UScalar ty) : (~~~x).toBitVec = ~~~x.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.toBitVec_and {ty} (x y : IScalar ty) : (x &&& y).toBitVec = x.toBitVec &&& y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.toBitVec_or {ty} (x y : IScalar ty) : (x ||| y).toBitVec = x.toBitVec ||| y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.toBitVec_xor {ty} (x y : IScalar ty) : (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.toBitVec_not {ty} (x : IScalar ty) : (~~~x).toBitVec = ~~~x.toBitVec := by rfl

@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.toNat_and {ty} (x y : UScalar ty) : (x &&& y).toNat = x.toNat &&& y.toNat := by rfl
@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.toNat_or {ty} (x y : UScalar ty) : (x ||| y).toNat = x.toNat ||| y.toNat := by rfl
@[simp, scalar_tac_simps, grind =, agrind =] theorem UScalar.toNat_xor {ty} (x y : UScalar ty) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by rfl

end Aeneas.Std
