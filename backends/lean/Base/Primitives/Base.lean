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
  | ret (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

open Result

instance Result_Inhabited (α : Type u) : Inhabited (Result α) :=
  Inhabited.mk (fail panic)

instance Result_Nonempty (α : Type u) : Nonempty (Result α) :=
  Nonempty.intro div

/- HELPERS -/

def ret? {α: Type u} (r: Result α): Bool :=
  match r with
  | ret _ => true
  | fail _ | div => false

def div? {α: Type u} (r: Result α): Bool :=
  match r with
  | div => true
  | ret _ | fail _ => false

def massert (b:Bool) : Result Unit :=
  if b then ret () else fail assertionFailure

def eval_global {α: Type u} (x: Result α) (_: ret? x): α :=
  match x with
  | fail _ | div => by contradiction
  | ret x => x

/- DO-DSL SUPPORT -/

def bind {α : Type u} {β : Type v} (x: Result α) (f: α → Result β) : Result β :=
  match x with
  | ret v  => f v 
  | fail v => fail v
  | div => div

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using return x in do-blocks
instance : Pure Result where
  pure := fun x => ret x

@[simp] theorem bind_ret (x : α) (f : α → Result β) : bind (.ret x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]

/- CUSTOM-DSL SUPPORT -/

-- Let-binding the Result of a monadic operation is oftentimes not sufficient,
-- because we may need a hypothesis for equational reasoning in the scope. We
-- rely on subtype, and a custom let-binding operator, in effect recreating our
-- own variant of the do-dsl

def Result.attach {α: Type} (o : Result α): Result { x : α // o = ret x } :=
  match o with
  | ret x => ret ⟨x, rfl⟩
  | fail e => fail e
  | div => div

@[simp] theorem bind_tc_ret (x : α) (f : α → Result β) :
  (do let y ← .ret x; f y) = f x := by simp [Bind.bind, bind]

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

-------------------------------
-- Tuple field access syntax --
-------------------------------
-- Declare new syntax `a.#i` for accessing the `i`-th term in a tuple
-- The `noWs` parser is used to ensure there is no whitespace.
syntax term noWs ".#" noWs num : term

open Lean Meta Elab Term

-- Auxliary function for computing the number of elements in a tuple (`Prod`) type.
def getArity (type : Expr) : Nat :=
  match type with
  | .app (.app (.const ``Prod _) _) as => getArity as + 1
  | _ => 1 -- It is not product

-- Given a `tuple` of size `n`, construct a term that for accessing the `i`-th element
def mkGetIdx (tuple : Expr) (n : Nat) (i : Nat) : MetaM Expr := do
  match i with
  | 0 => mkAppM ``Prod.fst #[tuple]
  | i+1 =>
    if n = 2 then
      -- If the tuple has only two elements and `i` is not `0`,
      -- we just return the second element.
      mkAppM ``Prod.snd #[tuple]
    else
      -- Otherwise, we continue with the rest of the tuple.
      let tuple ← mkAppM ``Prod.snd #[tuple]
      mkGetIdx tuple (n-1) i

-- Now, we define the elaboration function for the new syntax `a#i`
elab_rules : term
| `($a:term.#$i:num) => do
  -- Convert `i : Syntax` into a natural number
  let i := i.getNat
  -- Return error if it is 0.
  unless i ≥ 0 do
    throwError "tuple index must be greater or equal to 0"
  -- Convert `a : Syntax` into an `tuple : Expr` without providing expected type
  let tuple ← elabTerm a none
  let type ← inferType tuple
  -- Instantiate assigned metavariable occurring in `type`
  let type ← instantiateMVars type
  -- Ensure `tuple`'s type is a `Prod`uct.
  unless type.isAppOf ``Prod do
    throwError "tuple expected{indentExpr type}"
  let n := getArity type
  -- Ensure `i` is a valid index
  unless i < n do
    throwError "invalid tuple access at {i}, tuple has {n} elements"
  mkGetIdx tuple n i

----------
-- MISC --
----------

@[simp] def core.mem.replace (a : Type) (x : a) (_ : a) : a × a := (x, x)

/-- Aeneas-translated function -- useful to reduce non-recursive definitions.
 Use with `simp [ aeneas ]` -/
register_simp_attr aeneas

-- We don't really use raw pointers for now
structure MutRawPtr (T : Type) where
  v : T

structure ConstRawPtr (T : Type) where
  v : T

end Primitives
