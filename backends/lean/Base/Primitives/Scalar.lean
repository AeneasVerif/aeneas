import Lean
import Lean.Meta.Tactic.Simp
import Mathlib.Tactic.Linarith
import Base.Primitives.Base
import Base.Primitives.Core
import Base.Diverge.Base
import Base.Progress.Base
import Base.Arith.Int

namespace Primitives

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
  linarith

theorem Scalar.cMax_suffices ty (h : x ≤ Scalar.cMax ty) : x ≤ Scalar.max ty := by
  have := Scalar.cMax_bound ty
  linarith

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
deriving Repr

instance (ty : ScalarTy) : CoeOut (Scalar ty) Int where
  coe := λ v => v.val

/- Activate the ↑ notation -/
attribute [coe] Scalar.val

theorem Scalar.bound_suffices (ty : ScalarTy) (x : Int) :
  Scalar.cMin ty ≤ x ∧ x ≤ Scalar.cMax ty ->
  Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty
  :=
  λ h => by
  apply And.intro <;> have hmin := Scalar.cMin_bound ty <;> have hmax := Scalar.cMax_bound ty <;> linarith

/- [match_pattern] attribute: allows to us `Scalar.ofIntCore` inside of patterns.
   This is particularly useful once we introduce notations like `#u32` (which
   desugards to `Scalar.ofIntCore`) as it allows to write expressions like this:
   Example:
   ```
   match x with
   | 0#u32 => ...
   | 1#u32 => ...
   | ...
   ```
 -/
@[match_pattern] def Scalar.ofIntCore {ty : ScalarTy} (x : Int)
  (h : Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty) : Scalar ty :=
  { val := x, hmin := h.left, hmax := h.right }

-- The definitions below are used later to introduce nice syntax for constants,
-- like `1#u32`. We are reusing the technique described here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elaboration.20inside.2Foutside.20of.20match.20patterns/near/425455284

class InBounds (ty : ScalarTy) (x : Int) :=
  hInBounds : Scalar.cMin ty ≤ x ∧ x ≤ Scalar.cMax ty

-- This trick to trigger reduction for decidable propositions comes from
-- here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/instance.20with.20tactic.20autoparam/near/343495807
class Decide (p : Prop) [Decidable p] : Prop where
  isTrue : p
instance : @Decide p (.isTrue h) := @Decide.mk p (_) h

instance [Decide (Scalar.cMin ty ≤ v ∧ v ≤ Scalar.cMax ty)] : InBounds ty v where
  hInBounds := Decide.isTrue

@[reducible, match_pattern] def Scalar.ofInt {ty : ScalarTy} (x : Int) [InBounds ty x] : Scalar ty :=
  Scalar.ofIntCore x (Scalar.bound_suffices ty x InBounds.hInBounds)

@[simp] abbrev Scalar.in_bounds (ty : ScalarTy) (x : Int) : Prop :=
  Scalar.min ty ≤ x ∧ x ≤ Scalar.max ty

@[simp] abbrev Scalar.check_bounds (ty : ScalarTy) (x : Int) : Bool :=
  (Scalar.cMin ty ≤ x || Scalar.min ty ≤ x) ∧ (x ≤ Scalar.cMax ty || x ≤ Scalar.max ty)

theorem Scalar.check_bounds_imp_in_bounds {ty : ScalarTy} {x : Int}
  (h: Scalar.check_bounds ty x) :
  Scalar.in_bounds ty x := by
  simp at *
  have ⟨ hmin, hmax ⟩ := h
  have hbmin := Scalar.cMin_bound ty
  have hbmax := Scalar.cMax_bound ty
  cases hmin <;> cases hmax <;> apply And.intro <;> linarith

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

def Result.ofOption {a : Type u} (x : Option a) (e : Error) : Result a :=
  match x with
  | some x => ok x
  | none => fail e

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

def Scalar.neg {ty : ScalarTy} (x : Scalar ty) : Result (Scalar ty) := Scalar.tryMk ty (- x.val)

-- Our custom remainder operation, which satisfies the semantics of Rust
-- TODO: is there a better way?
def scalar_rem (x y : Int) : Int :=
  if 0 ≤ x then x % y
  else - (|x| % |y|)

@[simp]
def scalar_rem_nonneg {x y : Int} (hx : 0 ≤ x) : scalar_rem x y = x % y := by
  intros
  simp [*, scalar_rem]

-- Our custom division operation, which satisfies the semantics of Rust
-- TODO: is there a better way?
def scalar_div (x y : Int) : Int :=
  if 0 ≤ x && 0 ≤ y then x / y
  else if 0 ≤ x && y < 0 then - (|x| / |y|)
  else if x < 0 && 0 ≤ y then - (|x| / |y|)
  else |x| / |y|

@[simp]
def scalar_div_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) : scalar_div x y = x / y := by
  intros
  simp [*, scalar_div]

-- Checking that the remainder operation is correct
#assert scalar_rem 1 2 = 1
#assert scalar_rem (-1) 2 = -1
#assert scalar_rem 1 (-2) = 1
#assert scalar_rem (-1) (-2) = -1
#assert scalar_rem 7 3 = (1:Int)
#assert scalar_rem (-7) 3 = -1
#assert scalar_rem 7 (-3) = 1
#assert scalar_rem (-7) (-3) = -1

-- Checking that the division operation is correct
#assert scalar_div 3 2 = 1
#assert scalar_div (-3) 2 = -1
#assert scalar_div 3 (-2) = -1
#assert scalar_div (-3) (-2) = 1
#assert scalar_div 7 3 = 2
#assert scalar_div (-7) 3 = -2
#assert scalar_div 7 (-3) = -2
#assert scalar_div (-7) (-3) = 2

def Scalar.div {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  if y.val != 0 then Scalar.tryMk ty (scalar_div x.val y.val) else fail divisionByZero

def Scalar.rem {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  if y.val != 0 then Scalar.tryMk ty (scalar_rem x.val y.val) else fail divisionByZero

def Scalar.add {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val + y.val)

def Scalar.sub {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val - y.val)

def Scalar.mul {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val * y.val)

-- TODO: shift left
def Scalar.shiftl {ty0 ty1 : ScalarTy} (x : Scalar ty0) (y : Scalar ty1) : Result (Scalar ty0) :=
  sorry

-- TODO: shift right
def Scalar.shiftr {ty0 ty1 : ScalarTy} (x : Scalar ty0) (y : Scalar ty1) : Result (Scalar ty0) :=
  sorry

-- TODO: xor
def Scalar.xor {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Scalar ty :=
  sorry

-- TODO: and
def Scalar.and {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Scalar ty :=
  sorry

-- TODO: or
def Scalar.or {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Scalar ty :=
  sorry

-- Cast an integer from a [src_ty] to a [tgt_ty]
-- TODO: double-check the semantics of casts in Rust
def Scalar.cast {src_ty : ScalarTy} (tgt_ty : ScalarTy) (x : Scalar src_ty) : Result (Scalar tgt_ty) :=
  Scalar.tryMk tgt_ty x.val

-- This can't fail, but for now we make all casts faillible (easier for the translation)
def Scalar.cast_bool (tgt_ty : ScalarTy) (x : Bool) : Result (Scalar tgt_ty) :=
  Scalar.tryMk tgt_ty (if x then 1 else 0)

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

-- TODO: below: not sure this is the best way.
-- Should we rather overload operations like +, -, etc.?
-- Also, it is possible to automate the generation of those definitions
-- with macros (but would it be a good idea? It would be less easy to
-- read the file, which is not supposed to change a lot)

-- Negation

/--
Remark: there is no heterogeneous negation in the Lean prelude: we thus introduce
one here.

The notation typeclass for heterogeneous negation.
-/
class HNeg (α : Type u) (β : outParam (Type v)) where
  /-- `- a` computes the negation of `a`.
  The meaning of this notation is type-dependent. -/
  hNeg : α → β

/- Notation for heterogeneous negation.

   We initially used the notation "-" but it conflicted with the homogeneous
   negation too much. In particular, it made terms like `-10` ambiguous,
   and seemingly caused to backtracking in elaboration, leading to definitions
   like arrays of constants to take an unreasonable time to get elaborated
   and type-checked.

   TODO: PR to replace Neg with HNeg in Lean?
 -/
prefix:75  "-."   => HNeg.hNeg

/- We need this, otherwise we break pattern matching like in:

   ```
   def is_minus_one (x : Int) : Bool :=
     match x with
     | -1 => true
     | _ => false
   ```
-/
attribute [match_pattern] HNeg.hNeg

instance : HNeg Isize (Result Isize) where hNeg x := Scalar.neg x
instance : HNeg I8 (Result I8) where hNeg x := Scalar.neg x
instance : HNeg I16 (Result I16) where hNeg x := Scalar.neg x
instance : HNeg I32 (Result I32) where hNeg x := Scalar.neg x
instance : HNeg I64 (Result I64) where hNeg x := Scalar.neg x
instance : HNeg I128 (Result I128) where hNeg x := Scalar.neg x

-- Addition
instance {ty} : HAdd (Scalar ty) (Scalar ty) (Result (Scalar ty)) where
  hAdd x y := Scalar.add x y

-- Substraction
instance {ty} : HSub (Scalar ty) (Scalar ty) (Result (Scalar ty)) where
  hSub x y := Scalar.sub x y

-- Multiplication
instance {ty} : HMul (Scalar ty) (Scalar ty) (Result (Scalar ty)) where
  hMul x y := Scalar.mul x y

-- Division
instance {ty} : HDiv (Scalar ty) (Scalar ty) (Result (Scalar ty)) where
  hDiv x y := Scalar.div x y

-- Remainder
instance {ty} : HMod (Scalar ty) (Scalar ty) (Result (Scalar ty)) where
  hMod x y := Scalar.rem x y

-- Shift left
instance {ty0 ty1} : HShiftLeft (Scalar ty0) (Scalar ty1) (Result (Scalar ty0)) where
  hShiftLeft x y := Scalar.shiftl x y

-- Shift right
instance {ty0 ty1} : HShiftRight (Scalar ty0) (Scalar ty1) (Result (Scalar ty0)) where
  hShiftRight x y := Scalar.shiftr x y

-- Xor
instance {ty} : HXor (Scalar ty) (Scalar ty) (Scalar ty) where
  hXor x y := Scalar.xor x y

-- Or
instance {ty} : HOr (Scalar ty) (Scalar ty) (Scalar ty) where
  hOr x y := Scalar.or x y

-- And
instance {ty} : HAnd (Scalar ty) (Scalar ty) (Scalar ty) where
  hAnd x y := Scalar.and x y

-- core checked arithmetic operations

/- A helper function that converts failure to none and success to some
   TODO: move up to Base module? -/
def Option.ofResult {a : Type u} (x : Result a) :
  Option a :=
  match x with
  | ok x => some x
  | _ => none

/- [core::num::{T}::checked_add] -/
def core.num.checked_add (x y : Scalar ty) : Option (Scalar ty) :=
  Option.ofResult (x + y)

def U8.checked_add (x y : U8) : Option U8 := core.num.checked_add x y
def U16.checked_add (x y : U16) : Option U16 := core.num.checked_add x y
def U32.checked_add (x y : U32) : Option U32 := core.num.checked_add x y
def U64.checked_add (x y : U64) : Option U64 := core.num.checked_add x y
def U128.checked_add (x y : U128) : Option U128 := core.num.checked_add x y
def Usize.checked_add (x y : Usize) : Option Usize := core.num.checked_add x y
def I8.checked_add (x y : I8) : Option I8 := core.num.checked_add x y
def I16.checked_add (x y : I16) : Option I16 := core.num.checked_add x y
def I32.checked_add (x y : I32) : Option I32 := core.num.checked_add x y
def I64.checked_add (x y : I64) : Option I64 := core.num.checked_add x y
def I128.checked_add (x y : I128) : Option I128 := core.num.checked_add x y
def Isize.checked_add (x y : Isize) : Option Isize := core.num.checked_add x y

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub (x y : Scalar ty) : Option (Scalar ty) :=
  Option.ofResult (x - y)

def U8.checked_sub (x y : U8) : Option U8 := core.num.checked_sub x y
def U16.checked_sub (x y : U16) : Option U16 := core.num.checked_sub x y
def U32.checked_sub (x y : U32) : Option U32 := core.num.checked_sub x y
def U64.checked_sub (x y : U64) : Option U64 := core.num.checked_sub x y
def U128.checked_sub (x y : U128) : Option U128 := core.num.checked_sub x y
def Usize.checked_sub (x y : Usize) : Option Usize := core.num.checked_sub x y
def I8.checked_sub (x y : I8) : Option I8 := core.num.checked_sub x y
def I16.checked_sub (x y : I16) : Option I16 := core.num.checked_sub x y
def I32.checked_sub (x y : I32) : Option I32 := core.num.checked_sub x y
def I64.checked_sub (x y : I64) : Option I64 := core.num.checked_sub x y
def I128.checked_sub (x y : I128) : Option I128 := core.num.checked_sub x y
def Isize.checked_sub (x y : Isize) : Option Isize := core.num.checked_sub x y

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul (x y : Scalar ty) : Option (Scalar ty) :=
  Option.ofResult (x * y)

def U8.checked_mul (x y : U8) : Option U8 := core.num.checked_mul x y
def U16.checked_mul (x y : U16) : Option U16 := core.num.checked_mul x y
def U32.checked_mul (x y : U32) : Option U32 := core.num.checked_mul x y
def U64.checked_mul (x y : U64) : Option U64 := core.num.checked_mul x y
def U128.checked_mul (x y : U128) : Option U128 := core.num.checked_mul x y
def Usize.checked_mul (x y : Usize) : Option Usize := core.num.checked_mul x y
def I8.checked_mul (x y : I8) : Option I8 := core.num.checked_mul x y
def I16.checked_mul (x y : I16) : Option I16 := core.num.checked_mul x y
def I32.checked_mul (x y : I32) : Option I32 := core.num.checked_mul x y
def I64.checked_mul (x y : I64) : Option I64 := core.num.checked_mul x y
def I128.checked_mul (x y : I128) : Option I128 := core.num.checked_mul x y
def Isize.checked_mul (x y : Isize) : Option Isize := core.num.checked_mul x y

/- [core::num::{T}::checked_div] -/
def core.num.checked_div (x y : Scalar ty) : Option (Scalar ty) :=
  Option.ofResult (x / y)

def U8.checked_div (x y : U8) : Option U8 := core.num.checked_div x y
def U16.checked_div (x y : U16) : Option U16 := core.num.checked_div x y
def U32.checked_div (x y : U32) : Option U32 := core.num.checked_div x y
def U64.checked_div (x y : U64) : Option U64 := core.num.checked_div x y
def U128.checked_div (x y : U128) : Option U128 := core.num.checked_div x y
def Usize.checked_div (x y : Usize) : Option Usize := core.num.checked_div x y
def I8.checked_div (x y : I8) : Option I8 := core.num.checked_div x y
def I16.checked_div (x y : I16) : Option I16 := core.num.checked_div x y
def I32.checked_div (x y : I32) : Option I32 := core.num.checked_div x y
def I64.checked_div (x y : I64) : Option I64 := core.num.checked_div x y
def I128.checked_div (x y : I128) : Option I128 := core.num.checked_div x y
def Isize.checked_div (x y : Isize) : Option Isize := core.num.checked_div x y

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem (x y : Scalar ty) : Option (Scalar ty) :=
  Option.ofResult (x % y)

def U8.checked_rem (x y : U8) : Option U8 := core.num.checked_rem x y
def U16.checked_rem (x y : U16) : Option U16 := core.num.checked_rem x y
def U32.checked_rem (x y : U32) : Option U32 := core.num.checked_rem x y
def U64.checked_rem (x y : U64) : Option U64 := core.num.checked_rem x y
def U128.checked_rem (x y : U128) : Option U128 := core.num.checked_rem x y
def Usize.checked_rem (x y : Usize) : Option Usize := core.num.checked_rem x y
def I8.checked_rem (x y : I8) : Option I8 := core.num.checked_rem x y
def I16.checked_rem (x y : I16) : Option I16 := core.num.checked_rem x y
def I32.checked_rem (x y : I32) : Option I32 := core.num.checked_rem x y
def I64.checked_rem (x y : I64) : Option I64 := core.num.checked_rem x y
def I128.checked_rem (x y : I128) : Option I128 := core.num.checked_rem x y
def Isize.checked_rem (x y : Isize) : Option Isize := core.num.checked_rem x y

theorem Scalar.add_equiv {ty} {x y : Scalar ty} :
  match x + y with
  | ok z => Scalar.in_bounds ty (↑x + ↑y) ∧ (↑z : Int) = ↑x + ↑y
  | fail _ => ¬ (Scalar.in_bounds ty (↑x + ↑y))
  | _ => ⊥ := by
  -- Applying the unfoldings only inside the match
  conv in _ + _ => unfold HAdd.hAdd instHAddScalarResult; simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [in_bounds] at h
  split at h <;> simp_all [check_bounds_eq_in_bounds]

-- Generic theorem - shouldn't be used much
@[pspec]
theorem Scalar.add_spec {ty} {x y : Scalar ty}
  (hmin : Scalar.min ty ≤ ↑x + y.val)
  (hmax : ↑x + ↑y ≤ Scalar.max ty) :
  (∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y) := by
  have h := @add_equiv ty x y
  split at h <;> simp_all
  apply h

theorem Scalar.add_unsigned_spec {ty} (s: ¬ ty.isSigned) {x y : Scalar ty}
  (hmax : ↑x + ↑y ≤ Scalar.max ty) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  have hmin : Scalar.min ty ≤ ↑x + ↑y := by
    have hx := x.hmin
    have hy := y.hmin
    cases ty <;> simp [min, ScalarTy.isSigned] at * <;> linarith
  apply add_spec <;> assumption

/- Fine-grained theorems -/
@[pspec] theorem Usize.add_spec {x y : Usize} (hmax : ↑x + ↑y ≤ Usize.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem U8.add_spec {x y : U8} (hmax : ↑x + ↑y ≤ U8.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem U16.add_spec {x y : U16} (hmax : ↑x + ↑y ≤ U16.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem U32.add_spec {x y : U32} (hmax : ↑x + ↑y ≤ U32.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem U64.add_spec {x y : U64} (hmax : ↑x + ↑y ≤ U64.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem U128.add_spec {x y : U128} (hmax : ↑x + ↑y ≤ U128.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  apply Scalar.add_unsigned_spec <;> simp [ScalarTy.isSigned, Scalar.max, *]

@[pspec] theorem Isize.add_spec {x y : Isize}
  (hmin : Isize.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ Isize.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

@[pspec] theorem I8.add_spec {x y : I8}
  (hmin : I8.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ I8.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

@[pspec] theorem I16.add_spec {x y : I16}
  (hmin : I16.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ I16.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

@[pspec] theorem I32.add_spec {x y : I32}
  (hmin : I32.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ I32.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

@[pspec] theorem I64.add_spec {x y : I64}
  (hmin : I64.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ I64.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

@[pspec] theorem I128.add_spec {x y : I128}
  (hmin : I128.min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ I128.max) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y :=
  Scalar.add_spec hmin hmax

theorem core.num.checked_add_spec {ty} {x y : Scalar ty} :
  match core.num.checked_add x y with
  | some z => Scalar.in_bounds ty (↑x + ↑y) ∧ ↑z = (↑x + ↑y : Int)
  | none => ¬ (Scalar.in_bounds ty (↑x + ↑y)) := by
  have h := Scalar.tryMk_eq ty (↑x + ↑y)
  simp only [checked_add, Option.ofResult]
  cases heq: x + y <;> simp_all <;> simp [HAdd.hAdd, Scalar.add] at heq
  <;> simp [Add.add] at heq
  <;> simp_all

theorem Scalar.sub_equiv {ty} {x y : Scalar ty} :
  match x - y with
  | ok z => Scalar.in_bounds ty (↑x - ↑y) ∧ (↑z : Int) = ↑x - ↑y
  | fail _ => ¬ (Scalar.in_bounds ty (↑x - ↑y))
  | _ => ⊥ := by
  -- Applying the unfoldings only inside the match
  conv in _ - _ => unfold HSub.hSub instHSubScalarResult; simp [sub]
  have h := tryMk_eq ty (↑x - ↑y)
  simp [in_bounds] at h
  split at h <;> simp_all [check_bounds_eq_in_bounds]

-- Generic theorem - shouldn't be used much
@[pspec]
theorem Scalar.sub_spec {ty} {x y : Scalar ty}
  (hmin : Scalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ Scalar.max ty) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  apply h

theorem Scalar.sub_unsigned_spec {ty : ScalarTy} (s : ¬ ty.isSigned)
  {x y : Scalar ty} (hmin : Scalar.min ty ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  have : ↑x - ↑y ≤ Scalar.max ty := by
    have hx := x.hmin
    have hxm := x.hmax
    have hy := y.hmin
    cases ty <;> simp [min, max, ScalarTy.isSigned] at * <;> linarith
  intros
  apply sub_spec <;> assumption

/- Fine-grained theorems -/
@[pspec] theorem Usize.sub_spec {x y : Usize} (hmin : Usize.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem U8.sub_spec {x y : U8} (hmin : U8.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem U16.sub_spec {x y : U16} (hmin : U16.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem U32.sub_spec {x y : U32} (hmin : U32.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem U64.sub_spec {x y : U64} (hmin : U64.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem U128.sub_spec {x y : U128} (hmin : U128.min ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  apply Scalar.sub_unsigned_spec <;> simp_all [Scalar.min, ScalarTy.isSigned]

@[pspec] theorem Isize.sub_spec {x y : Isize} (hmin : Isize.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ Isize.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

@[pspec] theorem I8.sub_spec {x y : I8} (hmin : I8.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ I8.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

@[pspec] theorem I16.sub_spec {x y : I16} (hmin : I16.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ I16.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

@[pspec] theorem I32.sub_spec {x y : I32} (hmin : I32.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ I32.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

@[pspec] theorem I64.sub_spec {x y : I64} (hmin : I64.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ I64.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

@[pspec] theorem I128.sub_spec {x y : I128} (hmin : I128.min ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ I128.max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  Scalar.sub_spec hmin hmax

-- Generic theorem - shouldn't be used much
theorem Scalar.mul_spec {ty} {x y : Scalar ty}
  (hmin : Scalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ Scalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  conv => congr; ext; lhs; simp [HMul.hMul]
  simp [mul, tryMk, tryMkOpt, ofOption]
  split_ifs
  . simp [pure]
    rfl
  . tauto

theorem core.num.checked_sub_spec {ty} {x y : Scalar ty} :
  match core.num.checked_sub x y with
  | some z => Scalar.in_bounds ty (↑x - ↑y) ∧ ↑z = (↑x - ↑y : Int)
  | none => ¬ (Scalar.in_bounds ty (↑x - ↑y)) := by
  have h := Scalar.tryMk_eq ty (↑x - ↑y)
  simp only [checked_sub, Option.ofResult]
  have add_neg_eq : x.val + (-y.val) = x.val - y.val := by omega -- TODO: why do we need this??
  cases heq: x - y <;> simp_all <;> simp only [HSub.hSub, Scalar.sub, Sub.sub, Int.sub] at heq
  <;> simp_all

theorem Scalar.mul_equiv {ty} {x y : Scalar ty} :
  match x * y with
  | ok z => Scalar.in_bounds ty (↑x * ↑y) ∧ (↑z : Int) = ↑x * ↑y
  | fail _ => ¬ (Scalar.in_bounds ty (↑x * ↑y))
  | _ => ⊥ := by
  -- Applying the unfoldings only inside the match
  conv in _ * _ => unfold HMul.hMul instHMulScalarResult; simp [mul]
  have h := tryMk_eq ty (↑x * ↑y)
  simp [in_bounds] at h
  split at h <;> simp_all [check_bounds_eq_in_bounds]

theorem Scalar.mul_unsigned_spec {ty} (s: ¬ ty.isSigned) {x y : Scalar ty}
  (hmax : ↑x * ↑y ≤ Scalar.max ty) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  have : Scalar.min ty ≤ ↑x * ↑y := by
    have hx := x.hmin
    have hy := y.hmin
    cases ty <;> simp [ScalarTy.isSigned] at * <;> apply mul_nonneg hx hy
  apply mul_spec <;> assumption

/- Fine-grained theorems -/
@[pspec] theorem Usize.mul_spec {x y : Usize} (hmax : ↑x * ↑y ≤ Usize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem U8.mul_spec {x y : U8} (hmax : ↑x * ↑y ≤ U8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem U16.mul_spec {x y : U16} (hmax : ↑x * ↑y ≤ U16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem U32.mul_spec {x y : U32} (hmax : ↑x * ↑y ≤ U32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem U64.mul_spec {x y : U64} (hmax : ↑x * ↑y ≤ U64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem U128.mul_spec {x y : U128} (hmax : ↑x * ↑y ≤ U128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y := by
  apply Scalar.mul_unsigned_spec <;> simp_all [Scalar.max, ScalarTy.isSigned]

@[pspec] theorem Isize.mul_spec {x y : Isize} (hmin : Isize.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ Isize.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

@[pspec] theorem I8.mul_spec {x y : I8} (hmin : I8.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I8.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

@[pspec] theorem I16.mul_spec {x y : I16} (hmin : I16.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I16.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

@[pspec] theorem I32.mul_spec {x y : I32} (hmin : I32.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I32.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

@[pspec] theorem I64.mul_spec {x y : I64} (hmin : I64.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I64.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

@[pspec] theorem I128.mul_spec {x y : I128} (hmin : I128.min ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ I128.max) :
  ∃ z, x * y = ok z ∧ (↑z : Int) = ↑x * ↑y :=
  Scalar.mul_spec hmin hmax

theorem core.num.checked_mul_spec {ty} {x y : Scalar ty} :
  match core.num.checked_mul x y with
  | some z => Scalar.in_bounds ty (↑x * ↑y) ∧ ↑z = (↑x * ↑y : Int)
  | none => ¬ (Scalar.in_bounds ty (↑x * ↑y)) := by
  have h := Scalar.tryMk_eq ty (↑x * ↑y)
  simp only [checked_mul, Option.ofResult]
  have : Int.mul ↑x ↑y = ↑x * ↑y := by simp -- TODO: why do we need this??
  cases heq: x * y <;> simp_all <;> simp only [HMul.hMul, Scalar.mul, Mul.mul] at heq
  <;> simp_all

theorem Scalar.div_equiv {ty} {x y : Scalar ty} :
  match x / y with
  | ok z => y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_div ↑x ↑y) ∧ (↑z : Int) = scalar_div ↑x ↑y
  | fail _ => ¬ (y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_div ↑x ↑y))
  | _ => ⊥ := by
  -- Applying the unfoldings only inside the match
  conv in _ / _ => unfold HDiv.hDiv instHDivScalarResult; simp [div]
  have h := tryMk_eq ty (scalar_div ↑x ↑y)
  simp [in_bounds] at h
  split_ifs <;> simp <;>
  split at h <;> simp_all [check_bounds_eq_in_bounds]

-- Generic theorem - shouldn't be used much
@[pspec]
theorem Scalar.div_spec {ty} {x y : Scalar ty}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : Scalar.min ty ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ Scalar.max ty) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y := by
  simp [HDiv.hDiv, div, Div.div]
  simp [tryMk, tryMkOpt, ofOption, *]
  rfl

theorem Scalar.div_unsigned_spec {ty} (s: ¬ ty.isSigned) (x : Scalar ty) {y : Scalar ty}
  (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  have h : Scalar.min ty = 0 := by cases ty <;> simp [ScalarTy.isSigned, min] at *
  have hx := x.hmin
  have hy := y.hmin
  simp [h] at hx hy
  have hmin : 0 ≤ ↑x / ↑y := Int.ediv_nonneg hx hy
  have hmax : ↑x / ↑y ≤ Scalar.max ty := by
    have := Int.ediv_le_self ↑y hx
    have := x.hmax
    linarith
  have hs := @div_spec ty x y hnz
  simp [*] at hs
  apply hs

/- Fine-grained theorems -/
@[pspec] theorem Usize.div_spec (x : Usize) {y : Usize} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U8.div_spec (x : U8) {y : U8} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U16.div_spec (x : U16) {y : U16} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U32.div_spec (x : U32) {y : U32} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U64.div_spec (x : U64) {y : U64} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U128.div_spec (x : U128) {y : U128} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  apply Scalar.div_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem Isize.div_spec (x : Isize) {y : Isize}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : Isize.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ Isize.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

@[pspec] theorem I8.div_spec (x : I8) {y : I8}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I8.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ I8.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

@[pspec] theorem I16.div_spec (x : I16) {y : I16}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I16.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ I16.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

@[pspec] theorem I32.div_spec (x : I32) {y : I32}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I32.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ I32.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

@[pspec] theorem I64.div_spec (x : I64) {y : I64}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I64.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ I64.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

@[pspec] theorem I128.div_spec (x : I128) {y : I128}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I128.min ≤ scalar_div ↑x ↑y)
  (hmax : scalar_div ↑x ↑y ≤ I128.max):
  ∃ z, x / y = ok z ∧ (↑z : Int) = scalar_div ↑x ↑y :=
  Scalar.div_spec hnz hmin hmax

theorem core.num.checked_div_spec {ty} {x y : Scalar ty} :
  match core.num.checked_div x y with
  | some z => y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_div ↑x ↑y) ∧ ↑z = (scalar_div ↑x ↑y : Int)
  | none => ¬ (y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_div ↑x ↑y)) := by
  have h := Scalar.tryMk_eq ty (scalar_div ↑x ↑y)
  simp only [checked_div, Option.ofResult]
  cases heq0: (y.val = 0 : Bool) <;>
  cases heq1: x / y <;> simp_all <;> simp only [HDiv.hDiv, Scalar.div, Div.div] at heq1
  <;> simp_all

theorem Scalar.rem_equiv {ty} {x y : Scalar ty} :
  match x % y with
  | ok z => y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_rem ↑x ↑y) ∧ (↑z : Int) = scalar_rem ↑x ↑y
  | fail _ => ¬ (y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_rem ↑x ↑y))
  | _ => ⊥ := by
  -- Applying the unfoldings only inside the match
  conv in _ % _ => unfold HMod.hMod instHModScalarResult; simp [rem]
  have h := tryMk_eq ty (scalar_rem ↑x ↑y)
  simp [in_bounds] at h
  split_ifs <;> simp <;>
  split at h <;> simp_all [check_bounds_eq_in_bounds]

-- Generic theorem - shouldn't be used much
@[pspec]
theorem Scalar.rem_spec {ty} {x y : Scalar ty}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : Scalar.min ty ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ Scalar.max ty) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y := by
  simp [HMod.hMod, rem]
  simp [tryMk, tryMkOpt, ofOption, *]
  rfl

theorem Scalar.rem_unsigned_spec {ty} (s: ¬ ty.isSigned) (x : Scalar ty) {y : Scalar ty}
  (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  have h : Scalar.min ty = 0 := by cases ty <;> simp [ScalarTy.isSigned, min] at *
  have hx := x.hmin
  have hy := y.hmin
  simp [h] at hx hy
  have hmin : (0 : Int) ≤ x % y := Int.emod_nonneg ↑x hnz
  have hmax : ↑x % ↑y ≤ Scalar.max ty := by
    have h : (0 : Int) < y := by int_tac
    have h := Int.emod_lt_of_pos ↑x h
    have := y.hmax
    linarith
  have hs := @rem_spec ty x y hnz
  simp [*] at hs
  simp [*]

@[pspec] theorem Usize.rem_spec (x : Usize) {y : Usize} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U8.rem_spec (x : U8) {y : U8} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U16.rem_spec (x : U16) {y : U16} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U32.rem_spec (x : U32) {y : U32} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U64.rem_spec (x : U64) {y : U64} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem U128.rem_spec (x : U128) {y : U128} (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x % y = ok z ∧ (↑z : Int) = ↑x % ↑y := by
  apply Scalar.rem_unsigned_spec <;> simp [ScalarTy.isSigned, *]

@[pspec] theorem I8.rem_spec (x : I8) {y : I8}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I8.min ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ I8.max):
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y :=
  Scalar.rem_spec hnz hmin hmax

@[pspec] theorem I16.rem_spec (x : I16) {y : I16}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I16.min ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ I16.max):
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y :=
  Scalar.rem_spec hnz hmin hmax

@[pspec] theorem I32.rem_spec (x : I32) {y : I32}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I32.min ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ I32.max):
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y :=
  Scalar.rem_spec hnz hmin hmax

@[pspec] theorem I64.rem_spec (x : I64) {y : I64}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I64.min ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ I64.max):
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y :=
  Scalar.rem_spec hnz hmin hmax

@[pspec] theorem I128.rem_spec (x : I128) {y : I128}
  (hnz : ↑y ≠ (0 : Int))
  (hmin : I128.min ≤ scalar_rem ↑x ↑y)
  (hmax : scalar_rem ↑x ↑y ≤ I128.max):
  ∃ z, x % y = ok z ∧ (↑z : Int) = scalar_rem ↑x ↑y :=
  Scalar.rem_spec hnz hmin hmax

theorem core.num.checked_rem_spec {ty} {x y : Scalar ty} :
  match core.num.checked_rem x y with
  | some z => y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_rem ↑x ↑y) ∧ ↑z = (scalar_rem ↑x ↑y : Int)
  | none => ¬ (y.val ≠ 0 ∧ Scalar.in_bounds ty (scalar_rem ↑x ↑y)) := by
  have h := Scalar.tryMk_eq ty (scalar_rem ↑x ↑y)
  simp only [checked_rem, Option.ofResult]
  cases heq0: (y.val = 0 : Bool) <;>
  cases heq1: x % y <;> simp_all <;> simp only [HMod.hMod, Scalar.rem, Mod.mod] at heq1
  <;> simp_all

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
@[match_pattern] abbrev Isize.ofInt := @Scalar.ofInt .Isize
@[match_pattern] abbrev I8.ofInt    := @Scalar.ofInt .I8
@[match_pattern] abbrev I16.ofInt   := @Scalar.ofInt .I16
@[match_pattern] abbrev I32.ofInt   := @Scalar.ofInt .I32
@[match_pattern] abbrev I64.ofInt   := @Scalar.ofInt .I64
@[match_pattern] abbrev I128.ofInt  := @Scalar.ofInt .I128
@[match_pattern] abbrev Usize.ofInt := @Scalar.ofInt .Usize
@[match_pattern] abbrev U8.ofInt    := @Scalar.ofInt .U8
@[match_pattern] abbrev U16.ofInt   := @Scalar.ofInt .U16
@[match_pattern] abbrev U32.ofInt   := @Scalar.ofInt .U32
@[match_pattern] abbrev U64.ofInt   := @Scalar.ofInt .U64
@[match_pattern] abbrev U128.ofInt  := @Scalar.ofInt .U128

postfix:max "#isize" => Isize.ofInt
postfix:max "#i8"    => I8.ofInt
postfix:max "#i16"   => I16.ofInt
postfix:max "#i32"   => I32.ofInt
postfix:max "#i64"   => I64.ofInt
postfix:max "#i128"  => I128.ofInt
postfix:max "#usize" => Usize.ofInt
postfix:max "#u8"    => U8.ofInt
postfix:max "#u16"   => U16.ofInt
postfix:max "#u32"   => U32.ofInt
postfix:max "#u64"   => U64.ofInt
postfix:max "#u128"  => U128.ofInt

/- Testing the notations -/
example := 0#u32
example := 1#u32
example := 1#i32
example := 0#isize
example := (-1)#isize
example (x : U32) : Bool :=
  match x with
  | 0#u32 => true
  | _ => false

example (x : U32) : Bool :=
  match x with
  | 1#u32 => true
  | _ => false

example (x : I32) : Bool :=
  match x with
  | (-1)#i32 => true
  | _ => false

-- Notation for pattern matching
-- We make the precedence looser than the negation.
notation:70 a:70 "#scalar" => Scalar.mk (a) _ _

example {ty} (x : Scalar ty) : ℤ :=
  match x with
  | v#scalar => v

example {ty} (x : Scalar ty) : Bool :=
  match x with
  | 1#scalar => true
  | _ => false

example {ty} (x : Scalar ty) : Bool :=
  match x with
  | -(1 : Int)#scalar => true
  | _ => false

-- Testing the notations
example : Result Usize := 0#usize + 1#usize

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

-- Comparisons
instance {ty} : LT (Scalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (Scalar ty) where le a b := LE.le a.val b.val

-- Not marking this one with @[simp] on purpose
theorem Scalar.eq_equiv {ty : ScalarTy} (x y : Scalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all

-- This is sometimes useful when rewriting the goal with the local assumptions
@[simp] theorem Scalar.eq_imp {ty : ScalarTy} (x y : Scalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

theorem Scalar.lt_equiv {ty : ScalarTy} (x y : Scalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by simp [LT.lt]

@[simp] theorem Scalar.lt_imp {ty : ScalarTy} (x y : Scalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

theorem Scalar.le_equiv {ty : ScalarTy} (x y : Scalar ty) :
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

-- Leading zeros
def core.num.Usize.leading_zeros (x : Usize) : U32 := sorry
def core.num.U8.leading_zeros (x : U8) : U32 := sorry
def core.num.U16.leading_zeros (x : U16) : U32 := sorry
def core.num.U32.leading_zeros (x : U32) : U32 := sorry
def core.num.U64.leading_zeros (x : U64) : U32 := sorry
def core.num.U128.leading_zeros (x : U128) : U32 := sorry

def core.num.Isize.leading_zeros (x : Isize) : U32 := sorry
def core.num.I8.leading_zeros (x : I8) : U32 := sorry
def core.num.I16.leading_zeros (x : I16) : U32 := sorry
def core.num.I32.leading_zeros (x : I32) : U32 := sorry
def core.num.I64.leading_zeros (x : I64) : U32 := sorry
def core.num.I128.leading_zeros (x : I128) : U32 := sorry

-- Clone
def core.clone.impls.CloneUsize.clone (x : Usize) : Usize := x
def core.clone.impls.CloneU8.clone (x : U8) : U8 := x
def core.clone.impls.CloneU16.clone (x : U16) : U16 := x
def core.clone.impls.CloneU32.clone (x : U32) : U32 := x
def core.clone.impls.CloneU64.clone (x : U64) : U64 := x
def core.clone.impls.CloneU128.clone (x : U128) : U128 := x

def core.clone.impls.CloneIsize.clone (x : Isize) : Isize := x
def core.clone.impls.CloneI8.clone (x : I8) : I8 := x
def core.clone.impls.CloneI16.clone (x : I16) : I16 := x
def core.clone.impls.CloneI32.clone (x : I32) : I32 := x
def core.clone.impls.CloneI64.clone (x : I64) : I64 := x
def core.clone.impls.CloneI128.clone (x : I128) : I128 := x

def core.clone.CloneUsize : core.clone.Clone Usize := {
  clone := fun x => ok (core.clone.impls.CloneUsize.clone x)
}

def core.clone.CloneU8 : core.clone.Clone U8 := {
  clone := fun x => ok (core.clone.impls.CloneU8.clone x)
}

def core.clone.CloneU16 : core.clone.Clone U16 := {
  clone := fun x => ok (core.clone.impls.CloneU16.clone x)
}

def core.clone.CloneU32 : core.clone.Clone U32 := {
  clone := fun x => ok (core.clone.impls.CloneU32.clone x)
}

def core.clone.CloneU64 : core.clone.Clone U64 := {
  clone := fun x => ok (core.clone.impls.CloneU64.clone x)
}

def core.clone.CloneU128 : core.clone.Clone U128 := {
  clone := fun x => ok (core.clone.impls.CloneU128.clone x)
}

def core.clone.CloneIsize : core.clone.Clone Isize := {
  clone := fun x => ok (core.clone.impls.CloneIsize.clone x)
}

def core.clone.CloneI8 : core.clone.Clone I8 := {
  clone := fun x => ok (core.clone.impls.CloneI8.clone x)
}

def core.clone.CloneI16 : core.clone.Clone I16 := {
  clone := fun x => ok (core.clone.impls.CloneI16.clone x)
}

def core.clone.CloneI32 : core.clone.Clone I32 := {
  clone := fun x => ok (core.clone.impls.CloneI32.clone x)
}

def core.clone.CloneI64 : core.clone.Clone I64 := {
  clone := fun x => ok (core.clone.impls.CloneI64.clone x)
}

def core.clone.CloneI128 : core.clone.Clone I128 := {
  clone := fun x => ok (core.clone.impls.CloneI128.clone x)
}

end Primitives
