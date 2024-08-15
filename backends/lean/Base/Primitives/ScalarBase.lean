import Lean
import Lean.Meta.Tactic.Simp
import Base.Primitives.Base
import Base.Primitives.Core
import Base.Diverge.Base
import Base.Progress.Base
import Base.Arith.Int

namespace Primitives

-- Deactivate the warnings which appear when we use `#assert`
set_option linter.hashCommand false

----------------------
-- MACHINE INTEGERS --
----------------------

-- We redefine our machine integers types.

-- For Isize/Usize, we reuse `getNumBits` from `USize`. You cannot reduce `getNumBits`
-- using the simplifier, meaning that proofs do not depend on the compile-time value of
-- USize.size. (Lean assumes 32 or 64-bit platforms, and Rust doesn't really support, at
-- least officially, 16-bit microcontrollers, so this seems like a fine design decision
-- for now.)

-- Note from Chris Bailey: "If there's more than one salient property of your
-- definition then the subtyping strategy might get messy, and the property part
-- of a subtype is less discoverable by the simplifier or tactics like
-- library_search." So, we will not add refinements on the return values of the
-- operations defined on Primitives, but will rather rely on custom lemmas to
-- invert on possible return values of the primitive operations.

-- Machine integer constants, done via `ofNatCore`, which requires a proof that
-- the `Nat` fits within the desired integer type. We provide a custom tactic.

open Result Error
open System.Platform.getNumBits

-- TODO: is there a way of only importing System.Platform.getNumBits?
--
@[simp] def size_num_bits : Nat := (System.Platform.getNumBits ()).val

-- Remark: Lean seems to use < for the comparisons with the upper bounds by convention.

-- The "structured" bounds
def Isize.smin : Int := - (HPow.hPow 2 (size_num_bits - 1))
def Isize.smax : Int := (HPow.hPow 2 (size_num_bits - 1)) - 1
def I8.smin    : Int := - (HPow.hPow 2 7)
def I8.smax    : Int := HPow.hPow 2 7 - 1
def I16.smin   : Int := - (HPow.hPow 2 15)
def I16.smax   : Int := HPow.hPow 2 15 - 1
def I32.smin   : Int := -(HPow.hPow 2 31)
def I32.smax   : Int := HPow.hPow 2 31 - 1
def I64.smin   : Int := -(HPow.hPow 2 63)
def I64.smax   : Int := HPow.hPow 2 63 - 1
def I128.smin  : Int := -(HPow.hPow 2 127)
def I128.smax  : Int := HPow.hPow 2 127 - 1
def Usize.smin : Int := 0
def Usize.smax : Int := HPow.hPow 2 size_num_bits - 1
def U8.smin    : Int := 0
def U8.smax    : Int := HPow.hPow 2 8 - 1
def U16.smin   : Int := 0
def U16.smax   : Int := HPow.hPow 2 16 - 1
def U32.smin   : Int := 0
def U32.smax   : Int := HPow.hPow 2 32 - 1
def U64.smin   : Int := 0
def U64.smax   : Int := HPow.hPow 2 64 - 1
def U128.smin  : Int := 0
def U128.smax  : Int := HPow.hPow 2 128 - 1

-- The "normalized" bounds, that we use in practice
def I8.min    : Int   := -128
def I8.max    : Int   := 127
def I16.min   : Int  := -32768
def I16.max   : Int  := 32767
def I32.min   : Int  := -2147483648
def I32.max   : Int  := 2147483647
def I64.min   : Int  := -9223372036854775808
def I64.max   : Int  := 9223372036854775807
def I128.min  : Int := -170141183460469231731687303715884105728
def I128.max  : Int := 170141183460469231731687303715884105727
@[simp]
def U8.min    : Int   := 0
def U8.max    : Int   := 255
@[simp]
def U16.min   : Int  := 0
def U16.max   : Int  := 65535
@[simp]
def U32.min   : Int  := 0
def U32.max   : Int  := 4294967295
@[simp]
def U64.min   : Int  := 0
def U64.max   : Int  := 18446744073709551615
@[simp]
def U128.min  : Int := 0
def U128.max  : Int := 340282366920938463463374607431768211455
@[simp]
def Usize.min : Int := 0

def Isize.refined_min : { n:Int // n = I32.min ∨ n = I64.min } :=
  ⟨ Isize.smin, by
    simp [Isize.smin]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Isize.refined_max : { n:Int // n = I32.max ∨ n = I64.max } :=
  ⟨ Isize.smax, by
    simp [Isize.smax]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Usize.refined_max : { n:Int // n = U32.max ∨ n = U64.max } :=
  ⟨ Usize.smax, by
    simp [Usize.smax]
    cases System.Platform.numBits_eq <;>
    unfold System.Platform.numBits at * <;> simp [*] <;> decide ⟩

def Isize.min := Isize.refined_min.val
def Isize.max := Isize.refined_max.val
def Usize.max := Usize.refined_max.val

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.min, Usize.max, refined_max, smin, smax]
  cases System.Platform.numBits_eq <;>
  unfold System.Platform.numBits at * <;> simp [*] <;> decide

theorem Isize.bounds_eq :
  (Isize.min = I32.min ∧ Isize.max = I32.max)
  ∨ (Isize.min = I64.min ∧ Isize.max = I64.max) := by
  simp [Isize.min, Isize.max, refined_min, refined_max, smin, smax]
  cases System.Platform.numBits_eq <;>
  unfold System.Platform.numBits at * <;> simp [*] <;> decide

inductive ScalarTy :=
| Isize
| I8
| I16
| I32
| I64
| I128
| Usize
| U8
| U16
| U32
| U64
| U128

@[reducible]
def ScalarTy.isSigned (ty : ScalarTy) : Bool :=
  match ty with
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128 => true
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128 => false

-- FIXME(chore): bulk prove them via macro?
instance : Fact (¬ ScalarTy.isSigned .Usize) where
  out := by decide

instance : Fact (¬ ScalarTy.isSigned .U8) where
  out := by decide

instance : Fact (¬ ScalarTy.isSigned .U16) where
  out := by decide

instance : Fact (¬ ScalarTy.isSigned .U32) where
  out := by decide

instance : Fact (¬ ScalarTy.isSigned .U64) where
  out := by decide

instance : Fact (¬ ScalarTy.isSigned .U128) where
  out := by decide


def Scalar.smin (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Isize.smin
  | .I8    => I8.smin
  | .I16   => I16.smin
  | .I32   => I32.smin
  | .I64   => I64.smin
  | .I128  => I128.smin
  | .Usize => Usize.smin
  | .U8    => U8.smin
  | .U16   => U16.smin
  | .U32   => U32.smin
  | .U64   => U64.smin
  | .U128  => U128.smin

def Scalar.smax (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Isize.smax
  | .I8    => I8.smax
  | .I16   => I16.smax
  | .I32   => I32.smax
  | .I64   => I64.smax
  | .I128  => I128.smax
  | .Usize => Usize.smax
  | .U8    => U8.smax
  | .U16   => U16.smax
  | .U32   => U32.smax
  | .U64   => U64.smax
  | .U128  => U128.smax

def Scalar.min (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Isize.min
  | .I8    => I8.min
  | .I16   => I16.min
  | .I32   => I32.min
  | .I64   => I64.min
  | .I128  => I128.min
  | .Usize => Usize.min
  | .U8    => U8.min
  | .U16   => U16.min
  | .U32   => U32.min
  | .U64   => U64.min
  | .U128  => U128.min

def Scalar.max (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Isize.max
  | .I8    => I8.max
  | .I16   => I16.max
  | .I32   => I32.max
  | .I64   => I64.max
  | .I128  => I128.max
  | .Usize => Usize.max
  | .U8    => U8.max
  | .U16   => U16.max
  | .U32   => U32.max
  | .U64   => U64.max
  | .U128  => U128.max

def Scalar.smin_eq (ty : ScalarTy) : Scalar.min ty = Scalar.smin ty := by
  cases ty <;> rfl

def Scalar.smax_eq (ty : ScalarTy) : Scalar.max ty = Scalar.smax ty := by
  cases ty <;> rfl

-- "Conservative" bounds
-- We use those because we can't compare to the isize bounds (which can't
-- reduce at compile-time). Whenever we perform an arithmetic operation like
-- addition we need to check that the result is in bounds: we first compare
-- to the conservative bounds, which reduce, then compare to the real bounds.
-- This is useful for the various #asserts that we want to reduce at
-- type-checking time.
def Scalar.cMin (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Scalar.min .I32
  | _ => Scalar.min ty

def Scalar.cMax (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => Scalar.max .I32
  | .Usize => Scalar.max .U32
  | _ => Scalar.max ty

theorem Scalar.min_lt_max (ty : ScalarTy) : Scalar.min ty < Scalar.max ty := by
  cases ty <;> simp [Scalar.min, Scalar.max] <;> try decide
  . simp [Isize.min, Isize.max]
    have h1 := Isize.refined_min.property
    have h2 := Isize.refined_max.property
    cases h1 <;> cases h2 <;> simp [*] <;> decide
  . simp [Usize.max]
    have h := Usize.refined_max.property
    cases h <;> simp [*] <;> decide

theorem Scalar.min_le_max (ty : ScalarTy) : Scalar.min ty ≤ Scalar.max ty := by
  have := Scalar.min_lt_max ty
  int_tac

theorem Scalar.cMin_bound ty : Scalar.min ty ≤ Scalar.cMin ty := by
  cases ty <;> (simp [Scalar.min, Scalar.max, Scalar.cMin, Scalar.cMax] at *; try decide)
  have h := Isize.refined_min.property
  cases h <;> simp [*, Isize.min]
  decide

theorem Scalar.cMax_bound ty : Scalar.cMax ty ≤ Scalar.max ty := by
  cases ty <;> (simp [Scalar.min, Scalar.max, Scalar.cMin, Scalar.cMax] at *; try decide)
  . have h := Isize.refined_max.property
    cases h <;> simp [*, Isize.max]; decide
  . have h := Usize.refined_max.property
    cases h <;> simp [*, Usize.max]; decide

theorem Scalar.cMin_suffices ty (h : Scalar.cMin ty ≤ x) : Scalar.min ty ≤ x := by
  have := Scalar.cMin_bound ty
  omega

theorem Scalar.cMax_suffices ty (h : x ≤ Scalar.cMax ty) : x ≤ Scalar.max ty := by
  have := Scalar.cMax_bound ty
  omega

/-- The scalar type.

    We could use a subtype, but it using a custom structure type allows us
    to have more control over the coercions and the simplifications (we tried
    using a subtype and it caused issues especially as we had to make the Scalar
    type non-reducible, so that we could have more control, but leading to
    some natural equalities not being obvious to the simplifier anymore).
 -/
structure Scalar (ty : ScalarTy) where
  val : Int
  hmin : Scalar.min ty ≤ val
  hmax : val ≤ Scalar.max ty
deriving Repr, BEq, DecidableEq

instance {ty} : BEq (Scalar ty) where
  beq a b := a.val = b.val

instance {ty} : LawfulBEq (Scalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp[BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance (ty : ScalarTy) : CoeOut (Scalar ty) Int where
  coe := λ v => v.val

/- Activate the ↑ notation -/
attribute [coe] Scalar.val

theorem Scalar.bound_suffices (ty : ScalarTy) (x : Int) :
  Scalar.cMin ty ≤ x ∧ x ≤ Scalar.cMax ty ->
  Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty
  :=
  λ h => by
  apply And.intro <;> have hmin := Scalar.cMin_bound ty <;> have hmax := Scalar.cMax_bound ty <;> omega

def Scalar.ofIntCore {ty : ScalarTy} (x : Int)
  (h : Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty) : Scalar ty :=
  { val := x, hmin := h.left, hmax := h.right }

@[reducible] def Scalar.ofInt {ty : ScalarTy} (x : Int)
  (hInBounds : Scalar.cMin ty ≤ x ∧ x ≤ Scalar.cMax ty := by decide) : Scalar ty :=
  Scalar.ofIntCore x (Scalar.bound_suffices ty x hInBounds)

@[simp] abbrev Scalar.in_bounds (ty : ScalarTy) (x : Int) : Prop :=
  Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty

@[simp] abbrev Scalar.check_bounds (ty : ScalarTy) (x : Int) : Bool :=
  (Scalar.cMin ty ≤ x || Scalar.min ty ≤ x) ∧ (x ≤ Scalar.cMax ty || x ≤ Scalar.max ty)

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

theorem Scalar.check_bounds_imp_in_bounds {ty : ScalarTy} {x : Int}
  (h: Scalar.check_bounds ty x) :
  Scalar.in_bounds ty x := by
  simp at *
  have ⟨ hmin, hmax ⟩ := h
  have hbmin := Scalar.cMin_bound ty
  have hbmax := Scalar.cMax_bound ty
  cases hmin <;> cases hmax <;> apply And.intro <;> omega

theorem Scalar.check_bounds_eq_in_bounds (ty : ScalarTy) (x : Int) :
  Scalar.check_bounds ty x ↔ Scalar.in_bounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_in_bounds h)
  . simp_all

-- Further thoughts: look at what has been done here:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Fin/Basic.lean
-- and
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/UInt.lean
-- which both contain a fair amount of reasoning already!
def Scalar.tryMkOpt (ty : ScalarTy) (x : Int) : Option (Scalar ty) :=
  if h:Scalar.check_bounds ty x then
    -- If we do:
    -- ```
    -- let ⟨ hmin, hmax ⟩ := (Scalar.check_bounds_imp_in_bounds h)
    -- Scalar.ofIntCore x hmin hmax
    -- ```
    -- then normalization blocks (for instance, some proofs which use reflexivity fail).
    -- However, the version below doesn't block reduction (TODO: investigate):
    some (Scalar.ofIntCore x (Scalar.check_bounds_imp_in_bounds h))
  else none

def Scalar.tryMk (ty : ScalarTy) (x : Int) : Result (Scalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow

theorem Scalar.tryMk_eq (ty : ScalarTy) (x : Int) :
  match tryMk ty x with
  | ok y => y.val = x ∧ in_bounds ty x
  | fail _ => ¬ (in_bounds ty x)
  | _ => False := by
  simp [tryMk, ofOption, tryMkOpt, ofIntCore]
  have h := check_bounds_eq_in_bounds ty x
  split_ifs <;> simp_all

@[simp] theorem Scalar.tryMk_eq_div (ty : ScalarTy) (x : Int) :
  tryMk ty x = div ↔ False := by
  simp [tryMk, ofOption, tryMkOpt]
  split_ifs <;> simp

@[simp] theorem zero_in_cbounds {ty : ScalarTy} : Scalar.cMin ty ≤ 0 ∧ 0 ≤ Scalar.cMax ty := by
  cases ty <;> simp [Scalar.cMax, Scalar.cMin, Scalar.max, Scalar.min] <;> decide

-- ofIntCore
-- TODO: typeclass?
def Isize.ofIntCore := @Scalar.ofIntCore .Isize
def I8.ofIntCore    := @Scalar.ofIntCore .I8
def I16.ofIntCore   := @Scalar.ofIntCore .I16
def I32.ofIntCore   := @Scalar.ofIntCore .I32
def I64.ofIntCore   := @Scalar.ofIntCore .I64
def I128.ofIntCore  := @Scalar.ofIntCore .I128
def Usize.ofIntCore := @Scalar.ofIntCore .Usize
def U8.ofIntCore    := @Scalar.ofIntCore .U8
def U16.ofIntCore   := @Scalar.ofIntCore .U16
def U32.ofIntCore   := @Scalar.ofIntCore .U32
def U64.ofIntCore   := @Scalar.ofIntCore .U64
def U128.ofIntCore  := @Scalar.ofIntCore .U128

--  ofInt
-- TODO: typeclass?
abbrev Isize.ofInt := @Scalar.ofInt .Isize
abbrev I8.ofInt    := @Scalar.ofInt .I8
abbrev I16.ofInt   := @Scalar.ofInt .I16
abbrev I32.ofInt   := @Scalar.ofInt .I32
abbrev I64.ofInt   := @Scalar.ofInt .I64
abbrev I128.ofInt  := @Scalar.ofInt .I128
abbrev Usize.ofInt := @Scalar.ofInt .Usize
abbrev U8.ofInt    := @Scalar.ofInt .U8
abbrev U16.ofInt   := @Scalar.ofInt .U16
abbrev U32.ofInt   := @Scalar.ofInt .U32
abbrev U64.ofInt   := @Scalar.ofInt .U64
abbrev U128.ofInt  := @Scalar.ofInt .U128

-- TODO: factor those lemmas out
@[simp] theorem Scalar.ofInt_val_eq {ty} (h : Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty) : (Scalar.ofIntCore x h).val = x := by
  simp [Scalar.ofInt, Scalar.ofIntCore]

@[simp] theorem Isize.ofInt_val_eq (h : Scalar.min ScalarTy.Isize ≤ x ∧ x ≤ Scalar.max ScalarTy.Isize) : (Isize.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem I8.ofInt_val_eq (h : Scalar.min ScalarTy.I8 ≤ x ∧ x ≤ Scalar.max ScalarTy.I8) : (I8.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem I16.ofInt_val_eq (h : Scalar.min ScalarTy.I16 ≤ x ∧ x ≤ Scalar.max ScalarTy.I16) : (I16.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem I32.ofInt_val_eq (h : Scalar.min ScalarTy.I32 ≤ x ∧ x ≤ Scalar.max ScalarTy.I32) : (I32.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem I64.ofInt_val_eq (h : Scalar.min ScalarTy.I64 ≤ x ∧ x ≤ Scalar.max ScalarTy.I64) : (I64.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem I128.ofInt_val_eq (h : Scalar.min ScalarTy.I128 ≤ x ∧ x ≤ Scalar.max ScalarTy.I128) : (I128.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem Usize.ofInt_val_eq (h : Scalar.min ScalarTy.Usize ≤ x ∧ x ≤ Scalar.max ScalarTy.Usize) : (Usize.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem U8.ofInt_val_eq (h : Scalar.min ScalarTy.U8 ≤ x ∧ x ≤ Scalar.max ScalarTy.U8) : (U8.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem U16.ofInt_val_eq (h : Scalar.min ScalarTy.U16 ≤ x ∧ x ≤ Scalar.max ScalarTy.U16) : (U16.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem U32.ofInt_val_eq (h : Scalar.min ScalarTy.U32 ≤ x ∧ x ≤ Scalar.max ScalarTy.U32) : (U32.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem U64.ofInt_val_eq (h : Scalar.min ScalarTy.U64 ≤ x ∧ x ≤ Scalar.max ScalarTy.U64) : (U64.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

@[simp] theorem U128.ofInt_val_eq (h : Scalar.min ScalarTy.U128 ≤ x ∧ x ≤ Scalar.max ScalarTy.U128) : (U128.ofIntCore x h).val = x := by
  apply Scalar.ofInt_val_eq h

-- The scalar types
-- We declare the definitions as reducible so that Lean can unfold them (useful
-- for type class resolution for instance).
@[reducible] def Isize := Scalar .Isize
@[reducible] def I8    := Scalar .I8
@[reducible] def I16   := Scalar .I16
@[reducible] def I32   := Scalar .I32
@[reducible] def I64   := Scalar .I64
@[reducible] def I128  := Scalar .I128
@[reducible] def Usize := Scalar .Usize
@[reducible] def U8    := Scalar .U8
@[reducible] def U16   := Scalar .U16
@[reducible] def U32   := Scalar .U32
@[reducible] def U64   := Scalar .U64
@[reducible] def U128  := Scalar .U128

instance (ty : ScalarTy) : Inhabited (Scalar ty) := by
  constructor; cases ty <;> apply (Scalar.ofInt 0)

-- TODO: reducible?
@[reducible] def core_isize_min : Isize := Scalar.ofIntCore Isize.min (by simp [Scalar.min, Scalar.max]; apply (Scalar.min_le_max .Isize))
@[reducible] def core_isize_max : Isize := Scalar.ofIntCore Isize.max (by simp [Scalar.min, Scalar.max]; apply (Scalar.min_le_max .Isize))
@[reducible] def core_i8_min : I8 := Scalar.ofInt I8.min
@[reducible] def core_i8_max : I8 := Scalar.ofInt I8.max
@[reducible] def core_i16_min : I16 := Scalar.ofInt I16.min
@[reducible] def core_i16_max : I16 := Scalar.ofInt I16.max
@[reducible] def core_i32_min : I32 := Scalar.ofInt I32.min
@[reducible] def core_i32_max : I32 := Scalar.ofInt I32.max
@[reducible] def core_i64_min : I64 := Scalar.ofInt I64.min
@[reducible] def core_i64_max : I64 := Scalar.ofInt I64.max
@[reducible] def core_i128_min : I128 := Scalar.ofInt I128.min
@[reducible] def core_i128_max : I128 := Scalar.ofInt I128.max

-- TODO: reducible?
@[reducible] def core_usize_min : Usize := Scalar.ofIntCore Usize.min (by simp [Scalar.min, Scalar.max]; apply (Scalar.min_le_max .Usize))
@[reducible] def core_usize_max : Usize := Scalar.ofIntCore Usize.max (by simp [Scalar.min, Scalar.max]; apply (Scalar.min_le_max .Usize))
@[reducible] def core_u8_min : U8 := Scalar.ofInt U8.min
@[reducible] def core_u8_max : U8 := Scalar.ofInt U8.max
@[reducible] def core_u16_min : U16 := Scalar.ofInt U16.min
@[reducible] def core_u16_max : U16 := Scalar.ofInt U16.max
@[reducible] def core_u32_min : U32 := Scalar.ofInt U32.min
@[reducible] def core_u32_max : U32 := Scalar.ofInt U32.max
@[reducible] def core_u64_min : U64 := Scalar.ofInt U64.min
@[reducible] def core_u64_max : U64 := Scalar.ofInt U64.max
@[reducible] def core_u128_min : U128 := Scalar.ofInt U128.min
@[reducible] def core_u128_max : U128 := Scalar.ofInt U128.max

-- Comparisons
instance {ty} : LT (Scalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (Scalar ty) where le a b := LE.le a.val b.val

-- Not marking this one with @[simp] on purpose: if we have `x = y` somewhere in the context,
-- we may want to use it to substitute `y` with `x` somewhere.
-- TODO: mark it as simp anyway?
theorem Scalar.eq_equiv {ty : ScalarTy} (x y : Scalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all

-- This is sometimes useful when rewriting the goal with the local assumptions
-- TODO: this doesn't get triggered
@[simp] theorem Scalar.eq_imp {ty : ScalarTy} (x y : Scalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

@[simp] theorem Scalar.lt_equiv {ty : ScalarTy} (x y : Scalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by simp [LT.lt]

@[simp] theorem Scalar.lt_imp {ty : ScalarTy} (x y : Scalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp] theorem Scalar.le_equiv {ty : ScalarTy} (x y : Scalar ty) :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by simp [LE.le]

@[simp] theorem Scalar.le_imp {ty : ScalarTy} (x y : Scalar ty) :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

instance Scalar.decLt {ty} (a b : Scalar ty) : Decidable (LT.lt a b) := Int.decLt ..
instance Scalar.decLe {ty} (a b : Scalar ty) : Decidable (LE.le a b) := Int.decLe ..

theorem Scalar.eq_of_val_eq {ty} : ∀ {i j : Scalar ty}, Eq i.val j.val → Eq i j
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem Scalar.val_eq_of_eq {ty} {i j : Scalar ty} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem Scalar.ne_of_val_ne {ty} {i j : Scalar ty} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance (ty : ScalarTy) : DecidableEq (Scalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Scalar.eq_of_val_eq h)
    | isFalse h => isFalse (Scalar.ne_of_val_ne h)

@[simp] theorem Scalar.neq_to_neq_val {ty} : ∀ {i j : Scalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

instance (ty: ScalarTy) : Preorder (Scalar ty) where
  le_refl := fun a => by simp
  le_trans := fun a b c => by
    intro Hab Hbc
    exact (le_trans ((Scalar.le_equiv _ _).1 Hab) ((Scalar.le_equiv _ _).1 Hbc))
  lt_iff_le_not_le := fun a b => by
    trans (a: Int) < (b: Int); exact (Scalar.lt_equiv _ _)
    trans (a: Int) ≤ (b: Int) ∧ ¬ (b: Int) ≤ (a: Int); exact lt_iff_le_not_le
    repeat rewrite [← Scalar.le_equiv]; rfl

instance (ty: ScalarTy) : PartialOrder (Scalar ty) where
  le_antisymm := fun a b Hab Hba => Scalar.eq_imp _ _ ((@le_antisymm Int _ _ _ ((Scalar.le_equiv a b).1 Hab) ((Scalar.le_equiv b a).1 Hba)))

instance ScalarDecidableLE (ty: ScalarTy) : DecidableRel (· ≤ · : Scalar ty -> Scalar ty -> Prop) := by
  simp [instLEScalar]
  -- Lift this to the decidability of the Int version.
  infer_instance

instance (ty: ScalarTy) : LinearOrder (Scalar ty) where
  le_total := fun a b => by
    rcases (Int.le_total a b) with H | H
    left; exact (Scalar.le_equiv _ _).2 H
    right; exact (Scalar.le_equiv _ _).2 H
  decidableLE := ScalarDecidableLE ty

-- Coercion theorems
-- This is helpful whenever you want to "push" casts to the innermost nodes
-- and make the cast normalization happen more magically.

@[simp, norm_cast]
theorem coe_max {ty: ScalarTy} (a b: Scalar ty): ↑(Max.max a b) = (Max.max (↑a) (↑b): ℤ) := by
  -- TODO: there should be a shorter way to prove this.
  rw [max_def, max_def]
  split_ifs <;> simp_all

-- Max theory
-- TODO: do the min theory later on.

theorem Scalar.zero_le_unsigned {ty} (s: ¬ ty.isSigned) (x: Scalar ty): Scalar.ofInt 0 (by simp) ≤ x := by
  apply (Scalar.le_equiv _ _).2
  convert x.hmin
  cases ty <;> simp [ScalarTy.isSigned] at s <;> simp [Scalar.min]

@[simp]
theorem Scalar.max_unsigned_left_zero_eq {ty} [s: Fact (¬ ty.isSigned)] (x: Scalar ty):
  Max.max (Scalar.ofInt 0 (by simp)) x = x := max_eq_right (Scalar.zero_le_unsigned s.out x)

@[simp]
theorem Scalar.max_unsigned_right_zero_eq {ty} [s: Fact (¬ ty.isSigned)] (x: Scalar ty):
  Max.max x (Scalar.ofInt 0 (by simp)) = x := max_eq_left (Scalar.zero_le_unsigned s.out x)

-- Some conversions
@[simp] abbrev Scalar.toNat {ty} (x : Scalar ty) : Nat := x.val.toNat
@[simp] abbrev U8.toNat    (x : U8) : Nat := x.val.toNat
@[simp] abbrev U16.toNat   (x : U16) : Nat := x.val.toNat
@[simp] abbrev U32.toNat   (x : U32) : Nat := x.val.toNat
@[simp] abbrev U64.toNat   (x : U64) : Nat := x.val.toNat
@[simp] abbrev U128.toNat  (x : U128) : Nat := x.val.toNat
@[simp] abbrev Usize.toNat (x : Usize) : Nat := x.val.toNat
@[simp] abbrev I8.toNat    (x : I8) : Nat := x.val.toNat
@[simp] abbrev I16.toNat   (x : I16) : Nat := x.val.toNat
@[simp] abbrev I32.toNat   (x : I32) : Nat := x.val.toNat
@[simp] abbrev I64.toNat   (x : I64) : Nat := x.val.toNat
@[simp] abbrev I128.toNat  (x : I128) : Nat := x.val.toNat
@[simp] abbrev Isize.toNat (x : Isize) : Nat := x.val.toNat

end Primitives
