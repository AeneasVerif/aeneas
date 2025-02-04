import Lean
import Lean.Meta.Tactic.Simp
import Aeneas.Std.Core
import Aeneas.Std.Core
import Aeneas.Diverge.Core
import Aeneas.Progress.Core
import Aeneas.ScalarTac.IntTac

namespace Aeneas

namespace Std

-- Deactivate the warnings which appear when we use `#assert`
set_option linter.hashCommand false

/-!
# Machine Integers

Because they tend to behave quite differently, we have two classes of machine integers: one for
signed integers, and another for unsigned integers. Inside of each class, we factor out definitions.
-/

open Result Error
open System.Platform.getNumBits

-- TODO: is there a way of only importing System.Platform.getNumBits?
@[simp] def size_num_bits : Nat := System.Platform.numBits

-- Remark: Lean seems to use < for the comparisons with the upper bounds by convention.

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

/-- Kinds of signed integers -/
inductive IScalarTy where
| Isize
| I8
| I16
| I32
| I64
| I128

def UScalarTy.bitWidth (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => size_num_bits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

def IScalarTy.bitWidth (ty : IScalarTy) : Nat :=
  match ty with
  | Isize => size_num_bits
  | I8 => 8
  | I16 => 16
  | I32 => 32
  | I64 => 64
  | I128 => 128

@[simp] theorem UScalarTy.Usize_bitWidth_eq : Usize.bitWidth = size_num_bits := by rfl
@[simp] theorem UScalarTy.U8_bitWidth_eq    : U8.bitWidth    = 8 := by rfl
@[simp] theorem UScalarTy.U16_bitWidth_eq   : U16.bitWidth   = 16 := by rfl
@[simp] theorem UScalarTy.U32_bitWidth_eq   : U32.bitWidth   = 32 := by rfl
@[simp] theorem UScalarTy.U64_bitWidth_eq   : U64.bitWidth   = 64 := by rfl
@[simp] theorem UScalarTy.U128_bitWidth_eq  : U128.bitWidth  = 128 := by rfl

@[simp] theorem IScalarTy.Isize_bitWidth_eq : Isize.bitWidth = size_num_bits := by rfl
@[simp] theorem IScalarTy.I8_bitWidth_eq    : I8.bitWidth    = 8 := by rfl
@[simp] theorem IScalarTy.I16_bitWidth_eq   : I16.bitWidth   = 16 := by rfl
@[simp] theorem IScalarTy.I32_bitWidth_eq   : I32.bitWidth   = 32 := by rfl
@[simp] theorem IScalarTy.I64_bitWidth_eq   : I64.bitWidth   = 64 := by rfl
@[simp] theorem IScalarTy.I128_bitWidth_eq  : I128.bitWidth  = 128 := by rfl

/-! The "normalized" bounds, that we use in practice -/
def I8.min   : Int := -128
def I8.max   : Int := 127
def I16.min  : Int := -32768
def I16.max  : Int := 32767
def I32.min  : Int := -2147483648
def I32.max  : Int := 2147483647
def I64.min  : Int := -9223372036854775808
def I64.max  : Int := 9223372036854775807
def I128.min : Int := -170141183460469231731687303715884105728
def I128.max : Int := 170141183460469231731687303715884105727

def U8.max   : Nat := 255
def U16.max  : Nat := 65535
def U32.max  : Nat := 4294967295
def U64.max  : Nat := 18446744073709551615
def U128.max : Nat := 340282366920938463463374607431768211455

/-! The "structured" bounds, expressed in terms of powers of two. -/

def UScalar.smax (ty : UScalarTy) : ℕ := 2^ty.bitWidth - 1
def IScalar.smin (ty : IScalarTy) : ℤ := -2^(ty.bitWidth - 1)
def IScalar.smax (ty : IScalarTy) : ℤ := 2^(ty.bitWidth - 1) - 1

def Isize.refined_min : { n:Int // n = I32.min ∨ n = I64.min } :=
  ⟨ IScalar.smin .Isize, by
    simp [IScalar.smin]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Isize.refined_max : { n:Int // n = I32.max ∨ n = I64.max } :=
  ⟨ IScalar.smax .Isize, by
    simp [IScalar.smax]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Usize.refined_max : { n:Nat // n = U32.max ∨ n = U64.max } :=
  ⟨ UScalar.smax .Usize, by
    simp [UScalar.smax]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Isize.min := Isize.refined_min.val
def Isize.max := Isize.refined_max.val
def Usize.max := Usize.refined_max.val

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.max, refined_max, UScalar.smax]
  cases System.Platform.numBits_eq <;>
  unfold System.Platform.numBits at * <;> simp [*] <;> decide

theorem Isize.bounds_eq :
  (Isize.min = I32.min ∧ Isize.max = I32.max)
  ∨ (Isize.min = I64.min ∧ Isize.max = I64.max) := by
  simp [Isize.min, Isize.max, refined_min, refined_max, IScalar.smin, IScalar.smax]
  cases System.Platform.numBits_eq <;>
  unfold System.Platform.numBits at * <;> simp [*] <;> decide

def UScalar.max (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => Usize.max
  | .U8    => U8.max
  | .U16   => U16.max
  | .U32   => U32.max
  | .U64   => U64.max
  | .U128  => U128.max

def IScalar.min (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.min
  | .I8    => I8.min
  | .I16   => I16.min
  | .I32   => I32.min
  | .I64   => I64.min
  | .I128  => I128.min

def IScalar.max (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.max
  | .I8    => I8.max
  | .I16   => I16.max
  | .I32   => I32.max
  | .I64   => I64.max
  | .I128  => I128.max

def UScalar.smax_eq (ty : UScalarTy) : UScalar.max ty = UScalar.smax ty := by cases ty <;> rfl
def IScalar.smin_eq (ty : IScalarTy) : IScalar.min ty = IScalar.smin ty := by cases ty <;> rfl
def IScalar.smax_eq (ty : IScalarTy) : IScalar.max ty = IScalar.smax ty := by cases ty <;> rfl

theorem UScalar.bounds_eq (ty : UScalarTy) : UScalar.max ty = UScalar.smax ty := by
  dcases ty <;> rfl

theorem IScalar.bounds_eq (ty : IScalarTy) : IScalar.min ty = IScalar.smin ty ∧ IScalar.max ty = IScalar.smax ty := by
  dcases ty <;> split_conjs <;> rfl

/-
"Conservative" bounds

We use those because we can't compare to the isize bounds (which can't
reduce at compile-time). Whenever we perform an arithmetic operation like
addition we need to check that the result is in bounds: we first compare
to the conservative bounds, which reduce, then compare to the real bounds.
This is useful for the various #asserts that we want to reduce at
type-checking time. -/

def UScalar.cMax (ty : UScalarTy) : Int :=
  match ty with
  | .Usize => UScalar.max .U32
  | _ => UScalar.max ty

def IScalar.cMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.min .I32
  | _ => IScalar.min ty

def IScalar.cMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.max .I32
  | _ => IScalar.max ty

theorem UScalar.cMax_bound ty : UScalar.cMax ty ≤ UScalar.max ty := by
  cases ty <;> (simp [UScalar.max, UScalar.cMax] at *; try decide)
  have h := Usize.refined_max.property
  cases h <;> simp [*, Usize.max]; decide

theorem UScalar.cMax_suffices ty (h : x ≤ UScalar.cMax ty) : x ≤ UScalar.max ty := by
  have := UScalar.cMax_bound ty
  omega

theorem IScalar.min_lt_max (ty : IScalarTy) : IScalar.min ty < IScalar.max ty := by
  cases ty <;> simp [IScalar.min, IScalar.max] <;> try decide
  simp [Isize.min, Isize.max]
  have h1 := Isize.refined_min.property
  have h2 := Isize.refined_max.property
  cases h1 <;> cases h2 <;> simp [*] <;> decide

theorem IScalar.min_le_max (ty : IScalarTy) : IScalar.min ty ≤ IScalar.max ty := by
  have := IScalar.min_lt_max ty
  int_tac

theorem IScalar.cMin_bound ty : IScalar.min ty ≤ IScalar.cMin ty := by
  cases ty <;> (simp [IScalar.min, IScalar.max, IScalar.cMin, IScalar.cMax] at *; try decide)
  have h := Isize.refined_min.property
  cases h <;> simp [*, Isize.min]
  decide

theorem IScalar.cMax_bound ty : IScalar.cMax ty ≤ IScalar.max ty := by
  cases ty <;> (simp [IScalar.min, IScalar.max, IScalar.cMin, IScalar.cMax] at *; try decide)
  have h := Isize.refined_max.property
  cases h <;> simp [*, Isize.max]; decide

theorem IScalar.cMin_suffices ty (h : IScalar.cMin ty ≤ x) : IScalar.min ty ≤ x := by
  have := IScalar.cMin_bound ty
  omega

theorem IScalar.cMax_suffices ty (h : x ≤ IScalar.cMax ty) : x ≤ IScalar.max ty := by
  have := IScalar.cMax_bound ty
  omega

/-- The unsigned scalar type.

    Underneath, we simply use a bit-vector.
-/
structure UScalar (ty : UScalarTy) where
  bv : BitVec ty.bitWidth
deriving Repr, BEq, DecidableEq

def UScalar.val {ty} (x : UScalar ty) : ℕ := x.bv.toNat

def UScalar.hBounds {ty} (x : UScalar ty) : x.val ≤ UScalar.max ty := by
  dcases h: x.bv
  simp [h, val, bounds_eq, smax]
  omega

def UScalar.hmax {ty} (x : UScalar ty) : x.val ≤ UScalar.max ty := x.hBounds

/-- The signed scalar type.

    Underneath, we simply use a bit-vector.
 -/
structure IScalar (ty : IScalarTy) where
  bv : BitVec ty.bitWidth
deriving Repr, BEq, DecidableEq

def IScalar.val {ty} (x : IScalar ty) : ℤ := x.bv.toInt

def IScalar.hBounds {ty} (x : IScalar ty) : IScalar.min ty ≤ x.val ∧ x.val ≤ IScalar.max ty := by
  match x with
  | ⟨ ⟨ fin ⟩ ⟩ =>
    simp [val, bounds_eq, smin, smax, BitVec.toInt]
    dcases ty <;> simp at * <;> try omega
    have hFinLt := fin.isLt
    cases h: System.Platform.numBits_eq <;> simp_all only [IScalarTy.Isize_bitWidth_eq,
      size_num_bits, true_or, Nat.add_one_sub_one] <;>
    omega

def IScalar.hmin {ty} (x : IScalar ty) : IScalar.min ty ≤ x.val := x.hBounds.left
def IScalar.hmax {ty} (x : IScalar ty) : x.val ≤ IScalar.max ty  := x.hBounds.right

instance {ty} : BEq (UScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : BEq (IScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : LawfulBEq (UScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp [BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance {ty} : LawfulBEq (IScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp[BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.val

instance (ty : IScalarTy) : CoeOut (IScalar ty) Int where
  coe := λ v => v.val

/- Activate the ↑ notation -/
attribute [coe] UScalar.val IScalar.val

theorem IScalar.bound_suffices (ty : IScalarTy) (x : Int) :
  IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty ->
  IScalar.min ty ≤ x ∧ x ≤ IScalar.max ty
  :=
  λ h => by
  apply And.intro <;> have hmin := IScalar.cMin_bound ty <;> have hmax := IScalar.cMax_bound ty <;> omega

theorem UScalar.bound_suffices (ty : UScalarTy) (x : Nat) :
  x ≤ UScalar.cMax ty -> x ≤ UScalar.max ty
  :=
  λ h => by have hmax := UScalar.cMax_bound ty; omega

/- TODO: remove? Having a check on the bounds is a good sanity check, and it allows to prove
   nice theorems like `(ofIntCore x ..).val = x`, though `BitVec` also has powerful simplification lemmas. -/
def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (_ : x ≤ UScalar.max ty) : UScalar ty :=
  { bv := BitVec.ofNat _ x }

-- TODO: remove?
def IScalar.ofIntCore {ty : IScalarTy} (x : Int) (_ : IScalar.min ty ≤ x ∧ x ≤ IScalar.max ty) : IScalar ty :=
  { bv := BitVec.ofInt _ x }

@[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore x (UScalar.bound_suffices ty x hInBounds)

@[reducible] def IScalar.ofInt {ty : IScalarTy} (x : Int)
  (hInBounds : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty := by decide) : IScalar ty :=
  IScalar.ofIntCore x (IScalar.bound_suffices ty x hInBounds)

@[simp] abbrev UScalar.inBounds (ty : UScalarTy) (x : Nat) : Prop :=
  x ≤ UScalar.max ty

@[simp] abbrev IScalar.inBounds (ty : IScalarTy) (x : Int) : Prop :=
  IScalar.min ty ≤ x ∧ x ≤ IScalar.max ty

@[simp] abbrev UScalar.check_bounds (ty : UScalarTy) (x : Nat) : Bool :=
  x ≤ UScalar.cMax ty || x ≤ UScalar.max ty

@[simp] abbrev IScalar.check_bounds (ty : IScalarTy) (x : Int) : Bool :=
  (IScalar.cMin ty ≤ x || IScalar.min ty ≤ x) ∧ (x ≤ IScalar.cMax ty || x ≤ IScalar.max ty)

/- Discussion:
   This coercion can be slightly annoying at times, because if we write
   something like `u = 3` (where `u` is, for instance, as `U32`), then instead of
   coercing `u` to `Int`, Lean will lift `3` to `U32`).
   For now we deactivate it.

-- TODO(raitobezarius): the inbounds constraint is a bit ugly as we can pretty trivially
-- discharge the lhs on ≥ 0.
instance {ty: ScalarTy} [InBounds ty (Int.ofNat n)]: OfNat (Scalar ty) (n: ℕ) where
  ofNat := Scalar.ofInt n
-/

theorem UScalar.check_bounds_imp_inBounds {ty : UScalarTy} {x : Nat}
  (h: UScalar.check_bounds ty x) :
  UScalar.inBounds ty x := by
  simp at *
  have hbmax := UScalar.cMax_bound ty
  cases h <;> omega

theorem UScalar.check_bounds_eq_inBounds (ty : UScalarTy) (x : Nat) :
  UScalar.check_bounds ty x ↔ UScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

theorem IScalar.check_bounds_imp_inBounds {ty : IScalarTy} {x : Int}
  (h: IScalar.check_bounds ty x) :
  IScalar.inBounds ty x := by
  simp at *
  have ⟨ hmin, hmax ⟩ := h
  have hbmin := IScalar.cMin_bound ty
  have hbmax := IScalar.cMax_bound ty
  cases hmin <;> cases hmax <;> apply And.intro <;> omega

theorem IScalar.check_bounds_eq_inBounds (ty : IScalarTy) (x : Int) :
  IScalar.check_bounds ty x ↔ IScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

def UScalar.tryMkOpt (ty : UScalarTy) (x : Nat) : Option (UScalar ty) :=
  if h:UScalar.check_bounds ty x then
    some (UScalar.ofNatCore x (UScalar.check_bounds_imp_inBounds h))
  else none

def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

def IScalar.tryMkOpt (ty : IScalarTy) (x : Int) : Option (IScalar ty) :=
  if h:IScalar.check_bounds ty x then
    some (IScalar.ofIntCore x (IScalar.check_bounds_imp_inBounds h))
  else none

def IScalar.tryMk (ty : IScalarTy) (x : Int) : Result (IScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

theorem UScalar.tryMk_eq (ty : UScalarTy) (x : Nat) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  simp [tryMk, ofOption, tryMkOpt, ofNatCore]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp [UScalar.val, UScalarTy.bitWidth, max] at *
  dcases ty <;> simp_all [U8.max, U16.max, U32.max, U64.max, U128.max, Usize.max, Usize.refined_max, smax] <;> try omega
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

@[simp] theorem UScalar.tryMk_eq_div (ty : UScalarTy) (x : Nat) :
  tryMk ty x = div ↔ False := by
  simp [tryMk, ofOption, tryMkOpt]
  split_ifs <;> simp

theorem IScalar.tryMk_eq (ty : IScalarTy) (x : Int) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  simp [tryMk, ofOption, tryMkOpt, ofIntCore]
  have h := check_bounds_eq_inBounds ty x
  split_ifs <;> simp_all
  simp [IScalar.val, IScalarTy.bitWidth, min, max] at *
  dcases ty <;>
  simp_all [I8.min, I16.min, I32.min, I64.min, I128.min, Isize.min,
            I8.max, I16.max, I32.max, I64.max, I128.max, Isize.max,
            Isize.refined_min, smin, Isize.refined_max, smax] <;>
  simp [Int.bmod] <;> split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

@[simp] theorem IScalar.tryMk_eq_div (ty : IScalarTy) (x : Int) :
  tryMk ty x = div ↔ False := by
  simp [tryMk, ofOption, tryMkOpt]
  split_ifs <;> simp

@[simp] theorem UScalar.zero_in_cbounds {ty : UScalarTy} : 0 ≤ UScalar.cMax ty := by
  cases ty <;> simp [UScalar.cMax, UScalar.max]

@[simp] theorem IScalar.zero_in_cbounds {ty : IScalarTy} : IScalar.cMin ty ≤ 0 ∧ 0 ≤ IScalar.cMax ty := by
  cases ty <;> simp [IScalar.cMax, IScalar.cMin, IScalar.max, IScalar.min] <;> decide

/-! The scalar types. -/
@[reducible] def Usize := UScalar .Usize
@[reducible] def U8    := UScalar .U8
@[reducible] def U16   := UScalar .U16
@[reducible] def U32   := UScalar .U32
@[reducible] def U64   := UScalar .U64
@[reducible] def U128  := UScalar .U128
@[reducible] def Isize := IScalar .Isize
@[reducible] def I8    := IScalar .I8
@[reducible] def I16   := IScalar .I16
@[reducible] def I32   := IScalar .I32
@[reducible] def I64   := IScalar .I64
@[reducible] def I128  := IScalar .I128

/-!  ofNatCore -/
-- TODO: typeclass?
def Usize.ofNatCore := @UScalar.ofNatCore .Usize
def U8.ofNatCore    := @UScalar.ofNatCore .U8
def U16.ofNatCore   := @UScalar.ofNatCore .U16
def U32.ofNatCore   := @UScalar.ofNatCore .U32
def U64.ofNatCore   := @UScalar.ofNatCore .U64
def U128.ofNatCore  := @UScalar.ofNatCore .U128

/-!  ofIntCore -/
def Isize.ofIntCore := @IScalar.ofIntCore .Isize
def I8.ofIntCore    := @IScalar.ofIntCore .I8
def I16.ofIntCore   := @IScalar.ofIntCore .I16
def I32.ofIntCore   := @IScalar.ofIntCore .I32
def I64.ofIntCore   := @IScalar.ofIntCore .I64
def I128.ofIntCore  := @IScalar.ofIntCore .I128

/-!  ofNat -/
-- TODO: typeclass?
abbrev Usize.ofNat := @UScalar.ofNat .Usize
abbrev U8.ofNat    := @UScalar.ofNat .U8
abbrev U16.ofNat   := @UScalar.ofNat .U16
abbrev U32.ofNat   := @UScalar.ofNat .U32
abbrev U64.ofNat   := @UScalar.ofNat .U64
abbrev U128.ofNat  := @UScalar.ofNat .U128

/-!  ofInt -/
abbrev Isize.ofInt := @IScalar.ofInt .Isize
abbrev I8.ofInt    := @IScalar.ofInt .I8
abbrev I16.ofInt   := @IScalar.ofInt .I16
abbrev I32.ofInt   := @IScalar.ofInt .I32
abbrev I64.ofInt   := @IScalar.ofInt .I64
abbrev I128.ofInt  := @IScalar.ofInt .I128

@[simp] theorem UScalar.ofNat_val_eq {ty} (h : x ≤ UScalar.max ty) : (UScalar.ofNatCore x h).val = x := by
  simp [UScalar.ofNat, UScalar.ofNatCore, UScalar.val, max]
  dcases ty <;> simp_all [U8.max, U16.max, U32.max, U64.max, U128.max, Usize.max, Usize.refined_max, smax, max] <;> try omega
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

@[simp] theorem Usize.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.Usize) : (Usize.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem U8.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.U8) : (U8.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem U16.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.U16) : (U16.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem U32.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.U32) : (U32.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem U64.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.U64) : (U64.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem U128.ofNat_val_eq (h : x ≤ UScalar.max UScalarTy.U128) : (U128.ofNatCore x h).val = x := by
  apply UScalar.ofNat_val_eq h

@[simp] theorem IScalar.ofInt_val_eq {ty} (h : IScalar.min ty ≤ x ∧ x ≤ IScalar.max ty) : (IScalar.ofIntCore x h).val = x := by
  simp [IScalar.ofInt, IScalar.ofIntCore, IScalar.val, min, max]
  dcases ty <;>
  simp_all [I8.min, I16.min, I32.min, I64.min, I128.min, Isize.min,
            I8.max, I16.max, I32.max, I64.max, I128.max, Isize.max,
            Isize.refined_min, smin, Isize.refined_max, smax, min, max] <;>
  simp [Int.bmod] <;> split <;> (try omega) <;>
  cases h: System.Platform.numBits_eq <;> simp_all <;> omega

@[simp] theorem Isize.ofInt_val_eq (h : IScalar.min IScalarTy.Isize ≤ x ∧ x ≤ IScalar.max IScalarTy.Isize) : (Isize.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

@[simp] theorem I8.ofInt_val_eq (h : IScalar.min IScalarTy.I8 ≤ x ∧ x ≤ IScalar.max IScalarTy.I8) : (I8.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

@[simp] theorem I16.ofInt_val_eq (h : IScalar.min IScalarTy.I16 ≤ x ∧ x ≤ IScalar.max IScalarTy.I16) : (I16.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

@[simp] theorem I32.ofInt_val_eq (h : IScalar.min IScalarTy.I32 ≤ x ∧ x ≤ IScalar.max IScalarTy.I32) : (I32.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

@[simp] theorem I64.ofInt_val_eq (h : IScalar.min IScalarTy.I64 ≤ x ∧ x ≤ IScalar.max IScalarTy.I64) : (I64.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

@[simp] theorem I128.ofInt_val_eq (h : IScalar.min IScalarTy.I128 ≤ x ∧ x ≤ IScalar.max IScalarTy.I128) : (I128.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq h

instance (ty : UScalarTy) : Inhabited (UScalar ty) := by
  constructor; cases ty <;> apply (UScalar.ofNat 0)

instance (ty : IScalarTy) : Inhabited (IScalar ty) := by
  constructor; cases ty <;> apply (IScalar.ofInt 0)

@[reducible] def core_usize_min : Usize := UScalar.ofNatCore 0 (by simp)
@[reducible] def core_usize_max : Usize := UScalar.ofNatCore Usize.max (by simp [UScalar.max])
@[reducible] def core_u8_min : U8 := UScalar.ofNat 0
@[reducible] def core_u8_max : U8 := UScalar.ofNat U8.max
@[reducible] def core_u16_min : U16 := UScalar.ofNat 0
@[reducible] def core_u16_max : U16 := UScalar.ofNat U16.max
@[reducible] def core_u32_min : U32 := UScalar.ofNat 0
@[reducible] def core_u32_max : U32 := UScalar.ofNat U32.max
@[reducible] def core_u64_min : U64 := UScalar.ofNat 0
@[reducible] def core_u64_max : U64 := UScalar.ofNat U64.max
@[reducible] def core_u128_min : U128 := UScalar.ofNat 0
@[reducible] def core_u128_max : U128 := UScalar.ofNat U128.max

@[reducible] def core_isize_min : Isize := IScalar.ofIntCore Isize.min (by simp [IScalar.min, IScalar.max]; apply (IScalar.min_le_max .Isize))
@[reducible] def core_isize_max : Isize := IScalar.ofIntCore Isize.max (by simp [IScalar.min, IScalar.max]; apply (IScalar.min_le_max .Isize))
@[reducible] def core_i8_min : I8 := IScalar.ofInt I8.min
@[reducible] def core_i8_max : I8 := IScalar.ofInt I8.max
@[reducible] def core_i16_min : I16 := IScalar.ofInt I16.min
@[reducible] def core_i16_max : I16 := IScalar.ofInt I16.max
@[reducible] def core_i32_min : I32 := IScalar.ofInt I32.min
@[reducible] def core_i32_max : I32 := IScalar.ofInt I32.max
@[reducible] def core_i64_min : I64 := IScalar.ofInt I64.min
@[reducible] def core_i64_max : I64 := IScalar.ofInt I64.max
@[reducible] def core_i128_min : I128 := IScalar.ofInt I128.min
@[reducible] def core_i128_max : I128 := IScalar.ofInt I128.max

/-! Comparisons -/
instance {ty} : LT (UScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (UScalar ty) where le a b := LE.le a.val b.val

instance {ty} : LT (IScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (IScalar ty) where le a b := LE.le a.val b.val

/- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
   we may want to use it to substitute `y` with `x` somewhere. -/
theorem UScalar.eq_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ (↑x : Nat) = ↑y := by
  cases x; cases y; simp_all [UScalar.val, BitVec.toNat_eq]

@[simp] theorem UScalar.eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := (eq_equiv x y).mpr

@[simp] theorem UScalar.lt_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x < y ↔ (↑x : Nat) < ↑y := by
  rw [LT.lt, instLTUScalar]

@[simp] theorem UScalar.lt_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp] theorem UScalar.le_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x ≤ y ↔ (↑x : Nat) ≤ ↑y := by
  rw [LE.le, instLEUScalar]

@[simp] theorem UScalar.le_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

theorem IScalar.eq_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all [IScalar.val]
  constructor <;> intro <;>
  first | simp [*] | apply BitVec.eq_of_toInt_eq; simp [*]

@[simp] theorem IScalar.eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

@[simp] theorem IScalar.lt_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by
  rw [LT.lt, instLTIScalar]

@[simp] theorem IScalar.lt_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp] theorem IScalar.le_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by simp [LE.le]

@[simp] theorem IScalar.le_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

instance UScalar.decLt {ty} (a b : UScalar ty) : Decidable (LT.lt a b) := Nat.decLt ..
instance UScalar.decLe {ty} (a b : UScalar ty) : Decidable (LE.le a b) := Nat.decLe ..
instance IScalar.decLt {ty} (a b : IScalar ty) : Decidable (LT.lt a b) := Int.decLt ..
instance IScalar.decLe {ty} (a b : IScalar ty) : Decidable (LE.le a b) := Int.decLe ..

theorem UScalar.eq_of_val_eq {ty} : ∀ {i j : UScalar ty}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem IScalar.eq_of_val_eq {ty} : ∀ {i j : IScalar ty}, Eq i.val j.val → Eq i j := by
  intro i j hEq
  dcases i; dcases j
  simp [IScalar.val] at hEq; simp
  apply BitVec.eq_of_toInt_eq; assumption

theorem UScalar.val_eq_of_eq {ty} {i j : UScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl
theorem IScalar.val_eq_of_eq {ty} {i j : IScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl

theorem UScalar.ne_of_val_ne {ty} {i j : UScalar ty} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

theorem IScalar.ne_of_val_ne {ty} {i j : IScalar ty} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance (ty : UScalarTy) : DecidableEq (UScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (UScalar.eq_of_val_eq h)
    | isFalse h => isFalse (UScalar.ne_of_val_ne h)

instance (ty : IScalarTy) : DecidableEq (IScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (IScalar.eq_of_val_eq h)
    | isFalse h => isFalse (IScalar.ne_of_val_ne h)

@[simp] theorem UScalar.neq_to_neq_val {ty} : ∀ {i j : UScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

@[simp] theorem IScalar.neq_to_neq_val {ty} : ∀ {i j : IScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

@[simp]
theorem UScalar.val_not_eq_imp_not_eq (x y : UScalar ty) (h : ScalarTac.Nat.not_eq x.val y.val) :
  ¬ x = y := by
  simp_all; int_tac

@[simp]
theorem IScalar.val_not_eq_imp_not_eq (x y : IScalar ty) (h : ScalarTac.Int.not_eq x.val y.val) :
  ¬ x = y := by
  simp_all; int_tac

instance (ty: UScalarTy) : Preorder (UScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans ((UScalar.le_equiv _ _).1 Hab) ((UScalar.le_equiv _ _).1 Hbc))
  lt_iff_le_not_le := fun a b => by
    trans (a: Nat) < (b: Nat); exact (UScalar.lt_equiv _ _)
    trans (a: Nat) ≤ (b: Nat) ∧ ¬ (b: Nat) ≤ (a: Nat); exact lt_iff_le_not_le
    repeat rewrite [← UScalar.le_equiv]; rfl

instance (ty: IScalarTy) : Preorder (IScalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans ((IScalar.le_equiv _ _).1 Hab) ((IScalar.le_equiv _ _).1 Hbc))
  lt_iff_le_not_le := fun a b => by
    trans (a: Int) < (b: Int); exact (IScalar.lt_equiv _ _)
    trans (a: Int) ≤ (b: Int) ∧ ¬ (b: Int) ≤ (a: Int); exact lt_iff_le_not_le
    repeat rewrite [← IScalar.le_equiv]; rfl

instance (ty: UScalarTy) : PartialOrder (UScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    UScalar.eq_imp _ _ ((@le_antisymm Nat _ _ _ ((UScalar.le_equiv a b).1 Hab) ((UScalar.le_equiv b a).1 Hba)))

instance (ty: IScalarTy) : PartialOrder (IScalar ty) where
  le_antisymm := fun a b Hab Hba =>
    IScalar.eq_imp _ _ ((@le_antisymm Int _ _ _ ((IScalar.le_equiv a b).1 Hab) ((IScalar.le_equiv b a).1 Hba)))

instance UScalarDecidableLE (ty: UScalarTy) : DecidableRel (· ≤ · : UScalar ty -> UScalar ty -> Prop) := by
  simp [instLEUScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance IScalarDecidableLE (ty: IScalarTy) : DecidableRel (· ≤ · : IScalar ty -> IScalar ty -> Prop) := by
  simp [instLEIScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance (ty: UScalarTy) : LinearOrder (UScalar ty) where
  le_total := fun a b => by
    rcases (Nat.le_total a b) with H | H
    left; exact (UScalar.le_equiv _ _).2 H
    right; exact (UScalar.le_equiv _ _).2 H
  decidableLE := UScalarDecidableLE ty

instance (ty: IScalarTy) : LinearOrder (IScalar ty) where
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact (IScalar.le_equiv _ _).2 H
    right; exact (IScalar.le_equiv _ _).2 H
  decidableLE := IScalarDecidableLE ty

/-! Coercion theorems

    This is helpful whenever you want to "push" casts to the innermost nodes
    and make the cast normalization happen more magically. -/

@[simp, norm_cast]
theorem UScalar.coe_max {ty: UScalarTy} (a b: UScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℕ) := by
  -- TODO: there should be a shorter way to prove this.
  rw [max_def, max_def]
  split_ifs <;> simp_all

@[simp, norm_cast]
theorem IScalar.coe_max {ty: IScalarTy} (a b: IScalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  -- TODO: there should be a shorter way to prove this.
  rw [max_def, max_def]
  split_ifs <;> simp_all

/-! Max theory -/
-- TODO: do the min theory later on.

theorem UScalar.zero_le {ty} (x: UScalar ty): UScalar.ofNat 0 (by simp) ≤ x := by simp

@[simp]
theorem UScalar.max_left_zero_eq {ty} (x: UScalar ty):
  Max.max (UScalar.ofNat 0 (by simp)) x = x := max_eq_right (UScalar.zero_le x)

@[simp]
theorem UScalar.max_right_zero_eq {ty} (x: UScalar ty):
  Max.max x (UScalar.ofNat 0 (by simp)) = x := max_eq_left (UScalar.zero_le x)

/-! Some conversions -/
@[simp] abbrev I8.toNat    (x : I8) : Nat := x.val.toNat
@[simp] abbrev I16.toNat   (x : I16) : Nat := x.val.toNat
@[simp] abbrev I32.toNat   (x : I32) : Nat := x.val.toNat
@[simp] abbrev I64.toNat   (x : I64) : Nat := x.val.toNat
@[simp] abbrev I128.toNat  (x : I128) : Nat := x.val.toNat
@[simp] abbrev Isize.toNat (x : Isize) : Nat := x.val.toNat

def U8.bv (x : U8)   : BitVec 8 := UScalar.bv x
def U16.bv (x : U16) : BitVec 16 := UScalar.bv x
def U32.bv (x : U32) : BitVec 32 := UScalar.bv x
def U64.bv (x : U64) : BitVec 64 := UScalar.bv x
def U128.bv (x : U128) : BitVec 128 := UScalar.bv x
def Usize.bv (x : Usize) : BitVec size_num_bits := UScalar.bv x

def I8.bv (x : I8) : BitVec 8 := IScalar.bv x
def I16.bv (x : I16) : BitVec 16 := IScalar.bv x
def I32.bv (x : I32) : BitVec 32 := IScalar.bv x
def I64.bv (x : I64) : BitVec 64 := IScalar.bv x
def I128.bv (x : I128) : BitVec 128 := IScalar.bv x
def Isize.bv (x : Isize) : BitVec size_num_bits := IScalar.bv x

@[simp] theorem UScalar.bv_toNat_eq {ty : UScalarTy} (x : UScalar ty) :
  (UScalar.bv x).toNat  = x.val := by
  simp [val]

@[simp] theorem U8.bv_toNat_eq (x : U8) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp] theorem U16.bv_toNat_eq (x : U16) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp] theorem U32.bv_toNat_eq (x : U32) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp] theorem U64.bv_toNat_eq (x : U64) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp] theorem U128.bv_toNat_eq (x : U128) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq
@[simp] theorem Usize.bv_toNat_eq (x : Usize) : x.bv.toNat = x.val := by apply UScalar.bv_toNat_eq

@[simp] theorem IScalar.bv_toInt_eq {ty : IScalarTy} (x : IScalar ty) :
  (IScalar.bv x).toInt  = x.val := by
  simp [val]

@[simp] theorem I8.bv_toInt_eq (x : I8) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp] theorem I16.bv_toInt_eq (x : I16) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp] theorem I32.bv_toInt_eq (x : I32) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp] theorem I64.bv_toInt_eq (x : I64) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp] theorem I128.bv_toInt_eq (x : I128) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq
@[simp] theorem Isize.bv_toInt_eq (x : Isize) : x.bv.toInt = x.val := by apply IScalar.bv_toInt_eq

end Std

end Aeneas
