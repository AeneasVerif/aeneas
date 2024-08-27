import Lean
import Lean.Meta.Tactic.Simp
import Mathlib.Tactic.Linarith
import Base.Primitives.Scalar
import Base.Arith

namespace Primitives

open Lean Meta Elab Term PrettyPrinter

/- Something strange happens here: when we solve the goal with scalar_tac, it
   sometimes leaves meta-variables in place, which then causes issues when
   type-checking functions. For instance, it happens when we have const-generics
   in the translation: the constants contain meta-variables, which are then
   used in the types, which cause issues later. An example is given below:
 -/
macro:max x:term:max noWs "#isize" : term => `(Isize.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i8"    : term => `(I8.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i16"   : term => `(I16.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i32"   : term => `(I32.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i64"   : term => `(I64.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#i128"  : term => `(I128.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#usize" : term => `(Usize.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u8"    : term => `(U8.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u16"   : term => `(U16.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u32"   : term => `(U32.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u64"   : term => `(U64.ofInt $x (by first | decide | scalar_tac))
macro:max x:term:max noWs "#u128"  : term => `(U128.ofInt $x (by first | decide | scalar_tac))

-- Some pretty printing (for the goals)
@[app_unexpander U8.ofInt]
def unexpU8ofInt : Unexpander | `($_ $n $_) => `($n#u8) | _ => throw ()

@[app_unexpander U16.ofInt]
def unexpU16ofInt : Unexpander | `($_ $n $_) => `($n#u16) | _ => throw ()

@[app_unexpander U32.ofInt]
def unexpU32ofInt : Unexpander | `($_ $n $_) => `($n#u32) | _ => throw ()

@[app_unexpander U64.ofInt]
def unexpU64ofInt : Unexpander | `($_ $n $_) => `($n#u64) | _ => throw ()

@[app_unexpander U128.ofInt]
def unexpU128ofInt : Unexpander | `($_ $n $_) => `($n#u128) | _ => throw ()

@[app_unexpander Usize.ofInt]
def unexpUsizeofInt : Unexpander | `($_ $n $_) => `($n#usize) | _ => throw ()

@[app_unexpander I8.ofInt]
def unexpI8ofInt : Unexpander | `($_ $n $_) => `($n#u8) | _ => throw ()

@[app_unexpander I16.ofInt]
def unexpI16ofInt : Unexpander | `($_ $n $_) => `($n#u16) | _ => throw ()

@[app_unexpander I32.ofInt]
def unexpI32ofInt : Unexpander | `($_ $n $_) => `($n#u32) | _ => throw ()

@[app_unexpander I64.ofInt]
def unexpI64ofInt : Unexpander | `($_ $n $_) => `($n#u64) | _ => throw ()

@[app_unexpander I128.ofInt]
def unexpI128ofInt : Unexpander | `($_ $n $_) => `($n#u128) | _ => throw ()

@[app_unexpander Isize.ofInt]
def unexpIsizeofInt : Unexpander | `($_ $n $_) => `($n#usize) | _ => throw ()

-- Notation for pattern matching
-- We make the precedence looser than the negation.
notation:70 a:70 "#scalar" => Scalar.mk (a) _ _

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
  | 0#scalar => true
  | _ => false

example (x : U32) : Bool :=
  match x with
  | 1#scalar => true
  | _ => false

example (x : I32) : Bool :=
  match x with
  | (-1)#scalar => true
  | _ => false

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

-- More complex expressions
example (x y : Int) (h : 0 ≤ x + y ∧ x + y ≤ 1000) : U32 := (x + y)#u32

namespace Scalar.Examples

  abbrev Array (a : Type) (len : U32) := { l : List a // l.length = len.val }

  -- Checking the syntax
  example : Array Int 0#u32 := ⟨ [], by simp ⟩

  /- The example below fails if we don't use `decide` in the elaboration
     of the scalar notation -/
  example (a : Array (Array Int 32#u32) 32#u32) := a

end Scalar.Examples

end Primitives
