import Lean
import Lean.Meta.Tactic.Simp
import Mathlib.Tactic.Linarith
import Base.Primitives.Scalar
import Base.Arith

namespace Primitives

open Lean Meta Elab Term

macro:max x:term:max noWs "#isize" : term => `(Isize.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#i8"    : term => `(I8.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#i16"   : term => `(I16.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#i32"   : term => `(I32.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#i64"   : term => `(I64.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#i128"  : term => `(I128.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#usize" : term => `(Usize.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#u8"    : term => `(U8.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#u16"   : term => `(U16.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#u32"   : term => `(U32.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#u64"   : term => `(U64.ofInt $x (by scalar_tac))
macro:max x:term:max noWs "#u128"  : term => `(U128.ofInt $x (by scalar_tac))

-- Notation for pattern matching
-- We make the precedence looser than the negation.
notation:70 a:70 "#scalar" => Scalar.mk (a) _ _

/- Testing the notations -/
example := 0#u32
example := 1#u32
example := 1#i32
example := 0#isize
example := (-1)#isize

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

section Scalar.Examples
abbrev NList (a : Type) (x : U32) := { l : List a // l.length = x.val }

example : NList Int 0#u32 := ⟨ [], by simp ⟩

end Scalar.Examples

end Primitives
