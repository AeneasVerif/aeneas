import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd

--------------------
-- ASSERT COMMAND --
--------------------

open Lean Elab Command Term Meta

syntax (name := assert) "#assert" term: command

@[command_elab assert]
unsafe
def assertImpl : CommandElab := fun (_stx: Syntax) => do
  runTermElabM (fun _ => do
    let r ← evalTerm Bool (mkConst ``Bool) _stx[1]
    if not r then
      logInfo "Assertion failed for: "
      logInfo _stx[1]
      logError "Expression reduced to false"
    pure ())

#eval 2 == 2
#assert (2 == 2)

-------------
-- PRELUDE --
-------------

-- Results & monadic combinators

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ret (v: α): Result α
  | fail (e: Error): Result α
deriving Repr, BEq

open Result

/- HELPERS -/

def ret? {α: Type} (r: Result α): Bool :=
  match r with
  | Result.ret _ => true
  | Result.fail _ => false

def massert (b:Bool) : Result Unit :=
  if b then .ret () else fail assertionFailure

def eval_global {α: Type} (x: Result α) (_: ret? x): α :=
  match x with
  | Result.fail _ => by contradiction
  | Result.ret x => x

/- DO-DSL SUPPORT -/

def bind (x: Result α) (f: α -> Result β) : Result β :=
  match x with
  | ret v  => f v 
  | fail v => fail v

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using return x in do-blocks
instance : Pure Result where
  pure := fun x => ret x

/- CUSTOM-DSL SUPPORT -/

-- Let-binding the Result of a monadic operation is oftentimes not sufficient,
-- because we may need a hypothesis for equational reasoning in the scope. We
-- rely on subtype, and a custom let-binding operator, in effect recreating our
-- own variant of the do-dsl

def Result.attach {α: Type} (o : Result α): Result { x : α // o = ret x } :=
  match o with
  | .ret x => .ret ⟨x, rfl⟩
  | .fail e => .fail e

macro "let" e:term " ⟵ " f:term : doElem =>
  `(doElem| let ⟨$e, h⟩ ← Result.attach $f)

-- TODO: any way to factorize both definitions?
macro "let" e:term " <-- " f:term : doElem =>
  `(doElem| let ⟨$e, h⟩ ← Result.attach $f)

-- We call the hypothesis `h`, in effect making it unavailable to the user
-- (because too much shadowing). But in practice, once can use the French single
-- quote notation (input with f< and f>), where `‹ h ›` finds a suitable
-- hypothesis in the context, this is equivalent to `have x: h := by assumption in x`
#eval do
  let y <-- .ret (0: Nat)
  let _: y = 0 := by cases ‹ ret 0 = ret y › ; decide
  let r: { x: Nat // x = 0 } := ⟨ y, by assumption ⟩
  .ret r

----------------------
-- MACHINE INTEGERS --
----------------------

-- NOTE: we reuse the fixed-width integer types from prelude.lean: UInt8, ...,
-- USize. They are generally defined in an idiomatic style, except that there is
-- not a single type class to rule them all (more on that below). The absence of
-- type class is intentional, and allows the Lean compiler to efficiently map
-- them to machine integers during compilation.

-- USize is designed properly: you cannot reduce `getNumBits` using the
-- simplifier, meaning that proofs do not depend on the compile-time value of
-- USize.size. (Lean assumes 32 or 64-bit platforms, and Rust doesn't really
-- support, at least officially, 16-bit microcontrollers, so this seems like a
-- fine design decision for now.)

-- Note from Chris Bailey: "If there's more than one salient property of your
-- definition then the subtyping strategy might get messy, and the property part
-- of a subtype is less discoverable by the simplifier or tactics like
-- library_search." So, we will not add refinements on the return values of the
-- operations defined on Primitives, but will rather rely on custom lemmas to
-- invert on possible return values of the primitive operations.

-- Machine integer constants, done via `ofNatCore`, which requires a proof that
-- the `Nat` fits within the desired integer type. We provide a custom tactic.

syntax "intlit" : tactic

macro_rules
  | `(tactic| intlit) => `(tactic|
    match USize.size, usize_size_eq with
    | _, Or.inl rfl => decide
    | _, Or.inr rfl => decide)

-- This is how the macro is expected to be used
#eval USize.ofNatCore 0 (by intlit)

-- Also works for other integer types (at the expense of a needless disjunction)
#eval UInt32.ofNatCore 0 (by intlit)

open System.Platform.getNumBits

-- TODO: is there a way of only importing System.Platform.getNumBits?
--
@[simp] def size_num_bits : Nat := (System.Platform.getNumBits ()).val

-- Remark: Lean seems to use < for the comparisons with the upper bounds by convention.
-- We keep the F* convention for now.
@[simp] def Isize.min : Int := - (HPow.hPow 2 (size_num_bits - 1))
@[simp] def Isize.max : Int := (HPow.hPow 2 (size_num_bits - 1)) - 1
@[simp] def I8.min    : Int := - (HPow.hPow 2 7)
@[simp] def I8.max    : Int := HPow.hPow 2 7 - 1
@[simp] def I16.min   : Int := - (HPow.hPow 2 15)
@[simp] def I16.max   : Int := HPow.hPow 2 15 - 1
@[simp] def I32.min   : Int := -(HPow.hPow 2 31)
@[simp] def I32.max   : Int := HPow.hPow 2 31 - 1
@[simp] def I64.min   : Int := -(HPow.hPow 2 63)
@[simp] def I64.max   : Int := HPow.hPow 2 63 - 1
@[simp] def I128.min  : Int := -(HPow.hPow 2 127)
@[simp] def I128.max  : Int := HPow.hPow 2 127 - 1
@[simp] def Usize.min : Int := 0
@[simp] def Usize.max : Int := HPow.hPow 2 size_num_bits - 1
@[simp] def U8.min    : Int := 0
@[simp] def U8.max    : Int := HPow.hPow 2 8 - 1
@[simp] def U16.min   : Int := 0
@[simp] def U16.max   : Int := HPow.hPow 2 16 - 1
@[simp] def U32.min   : Int := 0
@[simp] def U32.max   : Int := HPow.hPow 2 32 - 1
@[simp] def U64.min   : Int := 0
@[simp] def U64.max   : Int := HPow.hPow 2 64 - 1
@[simp] def U128.min  : Int := 0
@[simp] def U128.max  : Int := HPow.hPow 2 128 - 1

#assert (I8.min   == -128)
#assert (I8.max   == 127)
#assert (I16.min  == -32768)
#assert (I16.max  == 32767)
#assert (I32.min  == -2147483648)
#assert (I32.max  == 2147483647)
#assert (I64.min  == -9223372036854775808)
#assert (I64.max  == 9223372036854775807)
#assert (I128.min == -170141183460469231731687303715884105728)
#assert (I128.max == 170141183460469231731687303715884105727)
#assert (U8.min   == 0)
#assert (U8.max   == 255)
#assert (U16.min  == 0)
#assert (U16.max  == 65535)
#assert (U32.min  == 0)
#assert (U32.max  == 4294967295)
#assert (U64.min  == 0)
#assert (U64.max  == 18446744073709551615)
#assert (U128.min == 0)
#assert (U128.max == 340282366920938463463374607431768211455)

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

-- "Conservative" bounds
-- We use those because we can't compare to the isize bounds (which can't
-- reduce at compile-time). Whenever we perform an arithmetic operation like
-- addition we need to check that the result is in bounds: we first compare
-- to the conservative bounds, which reduce, then compare to the real bounds.
-- This is useful for the various #asserts that we want to reduce at
-- type-checking time.
def Scalar.cMin (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => I32.min
  | _ => Scalar.min ty

def Scalar.cMax (ty : ScalarTy) : Int :=
  match ty with
  | .Isize => I32.max
  | .Usize => U32.max
  | _ => Scalar.max ty

structure Scalar (ty : ScalarTy) where
  val : Int
  hmin : Scalar.min ty <= val
  hmax : val <= Scalar.max ty

def Scalar.ofIntCore {ty : ScalarTy} (x : Int)
  (hmin : Scalar.min ty <= x) (hmax : x <= Scalar.max ty) : Scalar ty :=
  { val := x, hmin := hmin, hmax := hmax }

def Scalar.ofInt {ty : ScalarTy} (x : Int)
  (h : Scalar.min ty <= x && x <= Scalar.max ty) : Scalar ty :=
  let hmin: Scalar.min ty <= x := by sorry
  let hmax: x <= Scalar.max ty := by sorry
  Scalar.ofIntCore x hmin hmax

-- Further thoughts: look at what has been done here:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Fin/Basic.lean
-- and
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/UInt.lean
-- which both contain a fair amount of reasoning already!
def Scalar.tryMk (ty : ScalarTy) (x : Int) : Result (Scalar ty) :=
  -- TODO: write this with only one if then else
  if hmin_cons: Scalar.cMin ty <= x || Scalar.min ty <= x then
    if hmax_cons: x <= Scalar.cMax ty || x <= Scalar.max ty then
      let hmin: Scalar.min ty <= x := by sorry
      let hmax: x <= Scalar.max ty := by sorry
      return Scalar.ofIntCore x hmin hmax
    else fail integerOverflow
  else fail integerOverflow

def Scalar.neg {ty : ScalarTy} (x : Scalar ty) : Result (Scalar ty) := Scalar.tryMk ty (- x.val)

def Scalar.div {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  if y.val != 0 then Scalar.tryMk ty (x.val / y.val) else fail divisionByZero

-- Checking that the % operation in Lean computes the same as the remainder operation in Rust
#assert 1 % 2 = (1:Int)
#assert (-1) % 2 = -1
#assert 1 % (-2) = 1
#assert (-1) % (-2) = -1

def Scalar.rem {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  if y.val != 0 then Scalar.tryMk ty (x.val % y.val) else fail divisionByZero

def Scalar.add {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val + y.val)

def Scalar.sub {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val - y.val)

def Scalar.mul {ty : ScalarTy} (x : Scalar ty) (y : Scalar ty) : Result (Scalar ty) :=
  Scalar.tryMk ty (x.val * y.val)

-- TODO: instances of +, -, * etc. for scalars

-- Cast an integer from a [src_ty] to a [tgt_ty]
-- TODO: check the semantics of casts in Rust
def Scalar.cast {src_ty : ScalarTy} (tgt_ty : ScalarTy) (x : Scalar src_ty) : Result (Scalar tgt_ty) :=
  Scalar.tryMk tgt_ty x.val

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

-- TODO: below: not sure this is the best way.
-- Should we rather overload operations like +, -, etc.?
-- Also, it is possible to automate the generation of those definitions
-- with macros (but would it be a good idea? It would be less easy to
-- read the file, which is not supposed to change a lot)

-- Negation

/--
Remark: there is no heterogeneous negation in the Lean prelude: we thus introduce
one here.

The notation typeclass for heterogeneous addition.
This enables the notation `- a : β` where `a : α`.
-/
class HNeg (α : Type u) (β : outParam (Type v)) where
  /-- `- a` computes the negation of `a`.
  The meaning of this notation is type-dependent. -/
  hNeg : α → β

prefix:75  "-"   => HNeg.hNeg

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
def Isize.ofInt := @Scalar.ofInt .Isize
def I8.ofInt    := @Scalar.ofInt .I8
def I16.ofInt   := @Scalar.ofInt .I16
def I32.ofInt   := @Scalar.ofInt .I32
def I64.ofInt   := @Scalar.ofInt .I64
def I128.ofInt  := @Scalar.ofInt .I128
def Usize.ofInt := @Scalar.ofInt .Usize
def U8.ofInt    := @Scalar.ofInt .U8
def U16.ofInt   := @Scalar.ofInt .U16
def U32.ofInt   := @Scalar.ofInt .U32
def U64.ofInt   := @Scalar.ofInt .U64
def U128.ofInt  := @Scalar.ofInt .U128

-- Comparisons
instance {ty} : LT (Scalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (Scalar ty) where le a b := LE.le a.val b.val

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

def Scalar.toInt {ty} (n : Scalar ty) : Int := n.val

-- -- We now define a type class that subsumes the various machine integer types, so
-- -- as to write a concise definition for scalar_cast, rather than exhaustively
-- -- enumerating all of the possible pairs. We remark that Rust has sane semantics
-- -- and fails if a cast operation would involve a truncation or modulo.

-- class MachineInteger (t: Type) where
--   size: Nat
--   val: t -> Fin size
--   ofNatCore: (n:Nat) -> LT.lt n size -> t

-- set_option hygiene false in
-- run_cmd
--   for typeName in [`UInt8, `UInt16, `UInt32, `UInt64, `USize].map Lean.mkIdent do
--   Lean.Elab.Command.elabCommand (← `(
--     namespace $typeName
--     instance: MachineInteger $typeName where
--       size := size
--       val := val
--       ofNatCore := ofNatCore
--     end $typeName
--   ))

-- -- Aeneas only instantiates the destination type (`src` is implicit). We rely on
-- -- Lean to infer `src`.

-- def scalar_cast { src: Type } (dst: Type) [ MachineInteger src ] [ MachineInteger dst ] (x: src): Result dst :=
--   if h: MachineInteger.val x < MachineInteger.size dst then
--     .ret (MachineInteger.ofNatCore (MachineInteger.val x).val h)
--   else
--     .fail integerOverflow

-------------
-- VECTORS --
-------------

def Vec (α : Type u) := { l : List α // List.length l <= Usize.max }

def vec_new (α : Type u): Vec α := ⟨ [], by sorry ⟩

def vec_len (α : Type u) (v : Vec α) : Usize :=
  let ⟨ v, l ⟩ := v
  Usize.ofIntCore (List.length v) (by sorry) l
 
def vec_push_fwd (α : Type u) (_ : Vec α) (_ : α) : Unit := ()

def vec_push_back (α : Type u) (v : Vec α) (x : α) : Result (Vec α)
  :=
  if h : List.length v.val <= U32.max || List.length v.val <= Usize.max then
    return ⟨ List.concat v.val x, by sorry ⟩
  else
    fail maximumSizeExceeded

def vec_insert_fwd (α : Type u) (v: Vec α) (i: USize) (_: α): Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def vec_insert_back (α : Type u) (v: Vec α) (i: USize) (x: α): Result (Vec α) :=
  if i.val < List.length v.val then
    .ret ⟨ List.set v.val i.val x, by
      have h: List.length v.val <= Usize.max := v.property
      rewrite [ List.length_set v.val i.val x ]
      assumption
    ⟩
  else
    .fail arrayOutOfBounds

def vec_index_fwd (α : Type u) (v: Vec α) (i: USize): Result α :=
  if h: i.val < List.length v.val then
    .ret (List.get v.val ⟨i.val, h⟩)
  else
    .fail arrayOutOfBounds

def vec_index_back (α : Type u) (v: Vec α) (i: USize) (_: α): Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def vec_index_mut_fwd (α : Type u) (v: Vec α) (i: USize): Result α :=
  if h: i.val < List.length v.val then
    .ret (List.get v.val ⟨i.val, h⟩)
  else
    .fail arrayOutOfBounds

def vec_index_mut_back (α : Type u) (v: Vec α) (i: USize) (x: α): Result (Vec α) :=
  if i.val < List.length v.val then
    .ret ⟨ List.set v.val i.val x, by
      have h: List.length v.val <= Usize.max := v.property
      rewrite [ List.length_set v.val i.val x ]
      assumption
    ⟩
  else
    .fail arrayOutOfBounds

----------
-- MISC --
----------

def mem_replace_fwd (a : Type) (x : a) (_ : a) : a :=
  x

def mem_replace_back (a : Type) (_ : a) (y : a) : a :=
  y

/-- Aeneas-translated function -- useful to reduce non-recursive definitions.
 Use with `simp [ aeneas ]` -/
register_simp_attr aeneas
