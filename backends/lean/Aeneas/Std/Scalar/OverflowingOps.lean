import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

/-!
# Overflowing Operations
-/

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ BitVec.ofNat _ (x.val + y.val) ⟩, 2^ty.numBits ≤ x.val + y.val)

def IScalar.overflowing_add (ty : IScalarTy) (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ BitVec.ofInt _ (x.val + y.val) ⟩,
     ¬ (-2^(ty.numBits -1) ≤ x.val + y.val ∧ x.val + y.val < 2^ty.numBits))

/- [core::num::{u8}::overflowing_add] -/
def core.num.U8.overflowing_add := @UScalar.overflowing_add .U8

/- [core::num::{u16}::overflowing_add] -/
def core.num.U16.overflowing_add := @UScalar.overflowing_add .U16

/- [core::num::{u32}::overflowing_add] -/
def core.num.U32.overflowing_add := @UScalar.overflowing_add .U32

/- [core::num::{u64}::overflowing_add] -/
def core.num.U64.overflowing_add := @UScalar.overflowing_add .U64

/- [core::num::{u128}::overflowing_add] -/
def core.num.U128.overflowing_add := @UScalar.overflowing_add .U128

/- [core::num::{usize}::overflowing_add] -/
def core.num.Usize.overflowing_add := @UScalar.overflowing_add .Usize

/- [core::num::{i8}::overflowing_add] -/
def core.num.I8.overflowing_add := @IScalar.overflowing_add .I8

/- [core::num::{i16}::overflowing_add] -/
def core.num.I16.overflowing_add := @IScalar.overflowing_add .I16

/- [core::num::{i32}::overflowing_add] -/
def core.num.I32.overflowing_add := @IScalar.overflowing_add .I32

/- [core::num::{i64}::overflowing_add] -/
def core.num.I64.overflowing_add := @IScalar.overflowing_add .I64

/- [core::num::{i128}::overflowing_add] -/
def core.num.I128.overflowing_add := @IScalar.overflowing_add .I128

/- [core::num::{isize}::overflowing_add] -/
def core.num.Isize.overflowing_add := @IScalar.overflowing_add .Isize

attribute [-simp] Bool.exists_bool

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max ty then
    z.fst.val + UScalar.size ty = x.val + y.val ∧
    z.snd = true
  else
    z.fst.val = x.val + y.val ∧
    z.snd = false
  := by
  simp [overflowing_add]
  simp only [val, BitVec.toNat_ofNat, max]
  split <;> rename_i hLt
  . split_conjs
    . have : (x.bv.toNat + y.bv.toNat) % 2^ty.numBits =
             (x.bv.toNat + y.bv.toNat - 2^ty.numBits) % 2^ty.numBits := by
        rw [Nat.mod_eq_sub_mod]
        omega
      rw [this]; clear this

      have := @Nat.mod_eq_of_lt (x.bv.toNat + y.bv.toNat - 2^ty.numBits) (2^ty.numBits) (by omega)
      rw [this]; clear this
      simp [size]
      scalar_tac
    . omega
  . split_conjs
    . apply Nat.mod_eq_of_lt
      omega
    . omega

@[progress_pure overflowing_add x y]
theorem core.num.U8.overflowing_add_eq (x y : U8) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .U8 then z.fst.val + UScalar.size .U8 = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

@[progress_pure overflowing_add x y]
theorem core.num.U16.overflowing_add_eq (x y : U16) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .U16 then z.fst.val + UScalar.size .U16 = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

@[progress_pure overflowing_add x y]
theorem core.num.U32.overflowing_add_eq (x y : U32) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .U32 then z.fst.val + UScalar.size .U32 = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

@[progress_pure overflowing_add x y]
theorem core.num.U64.overflowing_add_eq (x y : U64) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .U64 then z.fst.val + UScalar.size .U64 = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

@[progress_pure overflowing_add x y]
theorem core.num.U128.overflowing_add_eq (x y : U128) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .U128 then z.fst.val + UScalar.size .U128 = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

@[progress_pure overflowing_add x y]
theorem core.num.Usize.overflowing_add_eq (x y : Usize) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .Usize then z.fst.val + UScalar.size .Usize = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

end Aeneas.Std
