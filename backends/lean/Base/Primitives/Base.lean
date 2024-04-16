import Lean

namespace Primitives

--------------------
-- ASSERT COMMAND --Std.
--------------------

open Lean Elab Command Term Meta

syntax (name := assert) "#assert" term: command

@[command_elab assert]
unsafe
def assertImpl : CommandElab := fun (_stx: Syntax) => do
  runTermElabM (fun _ => do
    let r ← evalTerm Bool (mkConst ``Bool) _stx[1]
    if not r then
      logInfo ("Assertion failed for:\n" ++ _stx[1])
      throwError ("Expression reduced to false:\n"  ++ _stx[1])
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
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/- HELPERS -/

def ok? {α: Type u} (r: Result α): Bool :=
  match r with
  | ok _ => true
  | fail _ | div => false

def div? {α: Type u} (r: Result α): Bool :=
  match r with
  | div => true
  | ok _ | fail _ => false

def massert (b:Bool) : Result Unit :=
  if b then ok () else fail assertionFailure

macro "prove_eval_global" : tactic => `(tactic| first | apply Eq.refl | decide)

def eval_global {α: Type u} (x: Result α) (_: ok? x := by prove_eval_global) : α :=
  match x with
  | fail _ | div => by contradiction
  | ok x => x

/- DO-DSL SUPPORT -/

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

/- CUSTOM-DSL SUPPORT -/

-- Let-binding the Result of a monadic operation is oftentimes not sufficient,
-- because we may need a hypothesis for equational reasoning in the scope. We
-- rely on subtype, and a custom let-binding operator, in effect recreating our
-- own variant of the do-dsl

def Result.attach {α: Type} (o : Result α): Result { x : α // o = ok x } :=
  match o with
  | ok x => ok ⟨x, rfl⟩
  | fail e => fail e
  | div => div

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

----------
-- MISC --
----------

@[simp] def core.mem.replace (a : Type) (x : a) (_ : a) : a × a := (x, x)
/- [core::option::Option::take] -/
@[simp] def Option.take (T: Type) (self: Option T): Option T × Option T := (self, .none)

/-- Aeneas-translated function -- useful to reduce non-recursive definitions.
 Use with `simp [ aeneas ]` -/
register_simp_attr aeneas

-- We don't really use raw pointers for now
structure MutRawPtr (T : Type) where
  v : T

structure ConstRawPtr (T : Type) where
  v : T

end Primitives
