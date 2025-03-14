import Lean
import Lean.Meta.Tactic.Simp
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Ops.Add -- we need to use addition in some of the tests below
import Aeneas.ScalarTac

namespace Aeneas

namespace Std

open Lean Meta Elab Term PrettyPrinter

/- Something strange happens here: when we solve the goal with scalar_tac, it
   sometimes leaves meta-variables in place, which then causes issues when
   type-checking functions. For instance, it happens when we have const-generics
   in the translation: the constants contain meta-variables, which are then
   used in the types, which cause issues later. For this reason we first try
   solving the goal with `decide`, which often works in the cases which are
   problematic for `scalar_tac`, then we try with `scalar_tac`.
 -/
macro:max x:term:max noWs "#u8"    : term => `(U8.ofNat $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u16"   : term => `(U16.ofNat $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u32"   : term => `(U32.ofNat $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u64"   : term => `(U64.ofNat $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u128"  : term => `(U128.ofNat $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#usize" : term => `(Usize.ofNat $x (by first | decide | scalar_tac))

macro:max x:term:max noWs "#i8"    : term => `(I8.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i16"   : term => `(I16.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i32"   : term => `(I32.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i64"   : term => `(I64.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i128"  : term => `(I128.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#isize" : term => `(Isize.ofInt $x (by first | decide | scalar_tac))

-- Some pretty printing (for the goals)
@[app_unexpander U8.ofNat]
def unexpU8ofNat : Unexpander | `($_ $n $_) => `($n#u8) | _ => throw ()

@[app_unexpander U16.ofNat]
def unexpU16ofNat : Unexpander | `($_ $n $_) => `($n#u16) | _ => throw ()

@[app_unexpander U32.ofNat]
def unexpU32ofNat : Unexpander | `($_ $n $_) => `($n#u32) | _ => throw ()

@[app_unexpander U64.ofNat]
def unexpU64ofNat : Unexpander | `($_ $n $_) => `($n#u64) | _ => throw ()

@[app_unexpander U128.ofNat]
def unexpU128ofNat : Unexpander | `($_ $n $_) => `($n#u128) | _ => throw ()

@[app_unexpander Usize.ofNat]
def unexpUsizeofNat : Unexpander | `($_ $n $_) => `($n#usize) | _ => throw ()

@[app_unexpander I8.ofInt]
def unexpI8ofInt : Unexpander | `($_ $n $_) => `($n#i8) | _ => throw ()

@[app_unexpander I16.ofInt]
def unexpI16ofInt : Unexpander | `($_ $n $_) => `($n#i16) | _ => throw ()

@[app_unexpander I32.ofInt]
def unexpI32ofInt : Unexpander | `($_ $n $_) => `($n#i32) | _ => throw ()

@[app_unexpander I64.ofInt]
def unexpI64ofInt : Unexpander | `($_ $n $_) => `($n#i64) | _ => throw ()

@[app_unexpander I128.ofInt]
def unexpI128ofInt : Unexpander | `($_ $n $_) => `($n#i128) | _ => throw ()

@[app_unexpander Isize.ofInt]
def unexpIsizeofInt : Unexpander | `($_ $n $_) => `($n#isize) | _ => throw ()

-- Notation for pattern matching
-- We make the precedence looser than the negation.
notation:70 a:70 "#uscalar" => UScalar.mk (a)
notation:70 a:70 "#iscalar" => IScalar.mk (a)

/- Testing the notations -/
example := 0#u32
example := 1#u32
example := 1#i32
example := 0#isize
example := (-1)#isize

example := 1#u32

/-
-- This doesn't work anymore
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
-/

example (x : U32) : Bool :=
  match x with
  | 0#uscalar => true
  | _ => false

example (x : U32) : Bool :=
  match x with
  | 1#uscalar => true
  | _ => false

example (x : I32) : Bool :=
  match x with
  | (-1)#iscalar => true
  | _ => false

/-
-- FIXME
example {ty} (x : UScalar ty) : ℕ :=
  match x with
  | v#uscalar => v

example {ty} (x : IScalar ty) : ℤ :=
  match x with
  | v#iscalar => v
-/

/-
-- FIXME
example {ty} (x : UScalar ty) : Bool :=
  match x with
  | 1#uscalar => true
  | _ => false

example {ty} (x : IScalar ty) : Bool :=
  match x with
  | -(1 : Int)#iscalar => true
  | _ => false
-/

-- Testing the notations
example : Result Usize := 0#usize + 1#usize

-- More complex expressions
example (x y : Nat) (h : x + y ≤ 1000) : U32 := (x + y)#u32
example (x y : Int) (h : 0 ≤ x + y ∧ x + y ≤ 1000) : I32 := (x + y)#i32

namespace Scalar.Examples

  abbrev Array (a : Type) (len : U32) := { l : List a // l.length = len.val }

  -- Checking the syntax
  example : Array Int 0#u32 := ⟨ [], by simp ⟩

  /- The example below fails if we don't use `decide` in the elaboration
     of the scalar notation -/
  example (a : Array (Array Int 32#u32) 32#u32) := a

end Scalar.Examples

end Std

end Aeneas
