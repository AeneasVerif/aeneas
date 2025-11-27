import Lean
import Aeneas.Std.Global
import Aeneas.Extract

namespace Aeneas

namespace Std

/-!
# Assert Command
-/

open Lean Elab Command Term Meta

syntax (name := assert) "#assert" term: command

@[command_elab assert]
unsafe
def assertImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    let r ← evalTerm Bool (mkConst ``Bool) stx[1]
    if not r then
      logInfo ("Assertion failed for:\n" ++ stx[1])
      throwError ("Expression reduced to false:\n"  ++ stx[1])
    pure ())

/--
info: true
-/
#guard_msgs in
#eval 2 == 2
#assert (2 == 2)

syntax (name := elabSyntax) "#elab" term: command

@[command_elab elabSyntax]
unsafe
def elabImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    /- Simply elaborate the syntax to check that it is correct -/
    let (_, _) ← Elab.Term.elabTerm stx[1] none |>.run
    pure ())

#elab 3

/-!
# Results and Monadic Combinators
-/

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/-!
# Helpers
-/

@[global_simps]
def ok? {α: Type u} (r: Result α): Bool :=
  match r with
  | ok _ => true
  | fail _ | div => false

def div? {α: Type u} (r: Result α): Bool :=
  match r with
  | div => true
  | ok _ | fail _ => false

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure

macro "prove_eval_global" : tactic => `(tactic| simp (failIfUnchanged := false) only [global_simps] <;> first | apply Eq.refl | decide)

@[global_simps]
def eval_global {α: Type u} (x: Result α) (_: ok? x := by prove_eval_global) : α :=
  match x with
  | fail _ | div => by contradiction
  | ok x => x

@[simp]
def Result.ofOption {a : Type u} (x : Option a) (e : Error) : Result a :=
  match x with
  | some x => ok x
  | none => fail e

@[simp] abbrev liftFun1 {α β} (f : α → β) : α → Result β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type} (f : α → β → γ) : α → β → Result γ := fun x y => ok (f x y)
@[simp] abbrev liftFun3 {α β γ δ} (f : α → β → γ → δ) : α → β → γ → Result δ := fun x y z => ok (f x y z)
@[simp] abbrev liftFun4 {α β γ δ ε} (f : α → β → γ → δ → ε) : α → β → γ → δ → Result ε := fun x y z a => ok (f x y z a)

/-!
# Do-DSL Support
-/

def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  match x with
  | ok v  => f v
  | fail v => fail v
  | div => div

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using pure x in do-blocks
instance : Pure Result where
  pure := fun x => ok x

@[simp] theorem bind_ok (x : α) (f : α → Result β) : bind (.ok x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]

@[simp] theorem bind_tc_ok (x : α) (f : α → Result β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, bind]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : Result a) (g :  a → Result b) (h : b → Result c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by
  simp [Bind.bind]
  cases e <;> simp

@[simp]
def bind_eq_iff (x : Result α) (y y' : α → Result β) :
  ((Bind.bind x y) = (Bind.bind x y')) ↔
  ∀ v, x = ok v → y v = y' v := by
  cases x <;> simp_all

instance : Monad Result where

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : PartialOrder (Result α) := inferInstanceAs (PartialOrder (FlatOrder .div))
noncomputable instance : CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder .div))
noncomputable instance : MonoBind Result where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Result _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl

end Order

/-!
# Lift
-/

/-- We use this to lift pure function calls to monadic calls.
    We don't mark this as reducible so that let-bindings don't get simplified away.

    In the generated code if regularly happens that we want to lift pure function calls so
    that `progress` can reason about them. For instance, `U32.wrapping_add` has type `U32 → U32 → U32`,
    but we provide a `progress` theorem with an informative post-condition, and which matches the pattern
    `toResult (wrapping_add x y)`. This theorem can only be looked up and appliced if the code is of the
    following shape:
    ```
    let z ← U32.wrapping_add x y
    ...
    ```
  -/
def toResult {α : Type u} (x : α) : Result α := Result.ok x

instance {α : Type u} : Coe α (Result α) where
  coe := toResult

attribute [coe] toResult

namespace Test
  /- Testing that our coercion from `α` to `Result α` works. -/
  example : Result Int := do
    let x0 ← ↑(0 : Int)
    let x1 ← ↑(x0 + 1 : Int)
    x1

  /- Testing that our coercion from `α` to `Result α` doesn't break other coercions. -/
  example (n : Nat) (i : Int) (_ : n < i) : True := by simp

  example : Result (BitVec 32) := do
    let x : BitVec 32 ← ↑(0#32)
    let y ← ↑(1#32)
    let z ← ↑(x + y)
    ok  z
end Test

/-!
# Misc
-/

abbrev Str := String

instance SubtypeBEq [BEq α] (p : α → Prop) : BEq (Subtype p) where
  beq v0 v1 := v0.val == v1.val

instance SubtypeLawfulBEq [BEq α] (p : α → Prop) [LawfulBEq α] : LawfulBEq (Subtype p) where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq]
  rfl := by intro a; cases a; simp [BEq.beq]

/- A helper function that converts failure to none and success to some
   TODO: move up to Core module? -/
def Option.ofResult {a : Type u} (x : Result a) :
  Option a :=
  match x with
  | ok x => some x
  | _ => none

/-!
# Misc Primitive Types
-/

-- We don't really use raw pointers for now
structure MutRawPtr (T : Type) where
  v : T

structure ConstRawPtr (T : Type) where
  v : T

end Std

end Aeneas
