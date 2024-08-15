import Base.Primitives.ScalarBase
import Base.Arith.Scalar

namespace Primitives

open Result Error

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

/- ¬ x reverst the bits of x

   It has the following effect:
   - if x is unsigned, then it evaluates to Scalar.max - x
   - otherwise, it evalutes to -1 - x
-/
def Scalar.not {ty : ScalarTy} (x : Scalar ty) : Scalar ty :=
  match ty with
  -- Unsigned cases
  | .U8 => @Scalar.mk ScalarTy.U8 (U8.max - x.val) (by scalar_tac) (by scalar_tac)
  | .U16 => @Scalar.mk ScalarTy.U16 (U16.max - x.val) (by scalar_tac) (by scalar_tac)
  | .U32 => @Scalar.mk ScalarTy.U32 (U32.max - x.val) (by scalar_tac) (by scalar_tac)
  | .U64 => @Scalar.mk ScalarTy.U64 (U64.max - x.val) (by scalar_tac) (by scalar_tac)
  | .U128 => @Scalar.mk ScalarTy.U128 (U128.max - x.val) (by scalar_tac) (by scalar_tac)
  | .Usize => @Scalar.mk ScalarTy.Usize (Usize.max - x.val) (by scalar_tac) (by scalar_tac)
  -- Signed cases
  | .I8 => @Scalar.mk ScalarTy.I8 (-1 - x.val) (by scalar_tac) (by scalar_tac)
  | .I16 => @Scalar.mk ScalarTy.I16 (-1 - x.val) (by scalar_tac) (by scalar_tac)
  | .I32 => @Scalar.mk ScalarTy.I32 (-1 - x.val) (by scalar_tac) (by scalar_tac)
  | .I64 => @Scalar.mk ScalarTy.I64 (-1 - x.val) (by scalar_tac) (by scalar_tac)
  | .I128 => @Scalar.mk ScalarTy.I128 (-1 - x.val) (by scalar_tac) (by scalar_tac)
  | .Isize => @Scalar.mk ScalarTy.Isize (-1 - x.val)
      (by have := Isize.bounds_eq; scalar_tac)
      (by have := Isize.bounds_eq; scalar_tac)

-- Cast an integer from a [src_ty] to a [tgt_ty]
-- TODO: double-check the semantics of casts in Rust
def Scalar.cast {src_ty : ScalarTy} (tgt_ty : ScalarTy) (x : Scalar src_ty) : Result (Scalar tgt_ty) :=
  Scalar.tryMk tgt_ty x.val

-- This can't fail, but for now we make all casts faillible (easier for the translation)
def Scalar.cast_bool (tgt_ty : ScalarTy) (x : Bool) : Result (Scalar tgt_ty) :=
  Scalar.tryMk tgt_ty (if x then 1 else 0)

@[pspec]
theorem Scalar.cast_in_bounds_eq {src_ty tgt_ty : ScalarTy} (x : Scalar src_ty) (h_bounds: Scalar.in_bounds tgt_ty x): ∃ x', Scalar.cast tgt_ty x = .ok x' ∧ x'.val = x.val := by
  simp at h_bounds
  simp [cast, tryMk, tryMkOpt]
  split_ifs with h_nbounds
  . use (Scalar.ofIntCore x h_bounds); simp [ofOption, ofIntCore]
  . omega

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

-- Not
instance {ty} : HNot (Scalar ty) where
  hnot x := Scalar.not x

example (x : Scalar ty) : Scalar ty := ￢ x

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

theorem Scalar.add_unsigned_spec {ty} (s: ¬ ty.isSigned) {x y : Scalar ty}
  (hmax : ↑x + ↑y ≤ Scalar.max ty) :
  ∃ z, x + y = ok z ∧ (↑z : Int) = ↑x + ↑y := by
  have hmin : Scalar.min ty ≤ ↑x + ↑y := by
    have hx := x.hmin
    have hy := y.hmin
    cases ty <;> simp [min, ScalarTy.isSigned] at * <;> omega
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

theorem Scalar.sub_unsigned_spec {ty : ScalarTy} (s : ¬ ty.isSigned)
  {x y : Scalar ty} (hmin : Scalar.min ty ≤ ↑x - ↑y) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  have : ↑x - ↑y ≤ Scalar.max ty := by
    have hx := x.hmin
    have hxm := x.hmax
    have hy := y.hmin
    cases ty <;> simp [min, max, ScalarTy.isSigned] at * <;> omega
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

theorem Scalar.div_unsigned_spec {ty} (s: ¬ ty.isSigned) (x : Scalar ty) {y : Scalar ty}
  (hnz : ↑y ≠ (0 : Int)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = ↑x / ↑y := by
  have h : Scalar.min ty = 0 := by cases ty <;> simp [ScalarTy.isSigned, min] at *
  have hx := x.hmin
  have hy := y.hmin
  simp [h] at hx hy
  have hmin : 0 ≤ x.val / y.val := Int.ediv_nonneg hx hy
  have hmax : ↑x / ↑y ≤ Scalar.max ty := by
    have := Int.ediv_le_self ↑y hx
    have := x.hmax
    omega
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
    omega
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
