import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd

-------------
-- PRELUDE --
-------------

-- Results & monadic combinators

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
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

@[inline]
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

@[inline]
def Result.attach {α: Type} (o : Result α): Result { x : α // o = ret x } :=
  match o with
  | .ret x => .ret ⟨x, rfl⟩
  | .fail e => .fail e

macro "let" e:term " ⟵ " f:term : doElem =>
  `(doElem| let ⟨$e, 𝒽⟩ ← Result.attach $f)

-- TODO: any way to factorize both definitions?
macro "let" e:term " <-- " f:term : doElem =>
  `(doElem| let ⟨$e, 𝒽⟩ ← Result.attach $f)

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

-- The machine integer operations (e.g. sub) are always total, which is not what
-- we want. We therefore define "checked" variants, below. Note that we add a
-- tiny bit of complexity for the USize variant: we first check whether the
-- result is < 2^32; if it is, we can compute the definition, rather than
-- returning a term that is computationally stuck (the comparison to USize.size
-- cannot reduce at compile-time, per the remark about regarding `getNumBits`).
-- This is useful for the various #asserts that we want to reduce at
-- type-checking time.

-- Further thoughts: look at what has been done here:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Fin/Basic.lean
-- and
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/UInt.lean
-- which both contain a fair amount of reasoning already!
def USize.checked_sub (n: USize) (m: USize): Result USize :=
  -- NOTE: the test USize.toNat n - m >= 0 seems to always succeed?
  if n >= m then
    let n' := USize.toNat n
    let m' := USize.toNat n
    let r := USize.ofNatCore (n' - m') (by
      have h: n' - m' <= n' := by
        apply Nat.sub_le_of_le_add
        case h => rewrite [ Nat.add_comm ]; apply Nat.le_add_left
      apply Nat.lt_of_le_of_lt h
      apply n.val.isLt
    )
    return r
  else
    fail integerOverflow

@[simp]
theorem usize_fits (n: Nat) (h: n <= 4294967295): n < USize.size :=
  match USize.size, usize_size_eq with
  | _, Or.inl rfl => Nat.lt_of_le_of_lt h (by decide)
  | _, Or.inr rfl => Nat.lt_of_le_of_lt h (by decide)

def USize.checked_add (n: USize) (m: USize): Result USize :=
  if h: n.val + m.val < USize.size then
    .ret ⟨ n.val + m.val, h ⟩
  else
    .fail integerOverflow

def USize.checked_rem (n: USize) (m: USize): Result USize :=
  if h: m > 0 then
    .ret ⟨ n.val % m.val, by
      have h1: ↑m.val < USize.size := m.val.isLt
      have h2: n.val.val % m.val.val < m.val.val := @Nat.mod_lt n.val m.val h
      apply Nat.lt_trans h2 h1
    ⟩
  else
    .fail integerOverflow

def USize.checked_mul (n: USize) (m: USize): Result USize :=
  if h: n.val * m.val < USize.size then
    .ret ⟨ n.val * m.val, h ⟩
  else
    .fail integerOverflow

def USize.checked_div (n: USize) (m: USize): Result USize :=
  if m > 0 then
    .ret ⟨ n.val / m.val, by
      have h1: ↑n.val < USize.size := n.val.isLt
      have h2: n.val.val / m.val.val <= n.val.val := @Nat.div_le_self n.val m.val
      apply Nat.lt_of_le_of_lt h2 h1
    ⟩
  else
    .fail integerOverflow

-- Test behavior...
#eval assert! USize.checked_sub 10 20 == fail integerOverflow; 0

#eval USize.checked_sub 20 10
-- NOTE: compare with concrete behavior here, which I do not think we want
#eval USize.sub 0 1
#eval UInt8.add 255 255

-- We now define a type class that subsumes the various machine integer types, so
-- as to write a concise definition for scalar_cast, rather than exhaustively
-- enumerating all of the possible pairs. We remark that Rust has sane semantics
-- and fails if a cast operation would involve a truncation or modulo.

class MachineInteger (t: Type) where
  size: Nat
  val: t -> Fin size
  ofNatCore: (n:Nat) -> LT.lt n size -> t

set_option hygiene false in
run_cmd
  for typeName in [`UInt8, `UInt16, `UInt32, `UInt64, `USize].map Lean.mkIdent do
  Lean.Elab.Command.elabCommand (← `(
    namespace $typeName
    instance: MachineInteger $typeName where
      size := size
      val := val
      ofNatCore := ofNatCore
    end $typeName
  ))

-- Aeneas only instantiates the destination type (`src` is implicit). We rely on
-- Lean to infer `src`.

def scalar_cast { src: Type } (dst: Type) [ MachineInteger src ] [ MachineInteger dst ] (x: src): Result dst :=
  if h: MachineInteger.val x < MachineInteger.size dst then
    .ret (MachineInteger.ofNatCore (MachineInteger.val x).val h)
  else
    .fail integerOverflow

-------------
-- VECTORS --
-------------

-- Note: unlike F*, Lean seems to use strict upper bounds (e.g. USize.size)
-- rather than maximum values (usize_max).
def Vec (α : Type u) := { l : List α // List.length l < USize.size }

def vec_new (α : Type u): Vec α := ⟨ [], by {
  match USize.size, usize_size_eq with
  | _, Or.inl rfl => simp
  | _, Or.inr rfl => simp
  } ⟩

#check vec_new

def vec_len (α : Type u) (v : Vec α) : USize :=
  let ⟨ v, l ⟩ := v
  USize.ofNatCore (List.length v) l

#eval vec_len Nat (vec_new Nat)
 
def vec_push_fwd (α : Type u) (_ : Vec α) (_ : α) : Unit := ()

-- NOTE: old version trying to use a subtype notation, but probably better to
-- leave Result elimination to auxiliary lemmas with suitable preconditions
-- TODO: I originally wrote `List.length v.val < USize.size - 1`; how can one
-- make the proof work in that case? Probably need to import tactics from
-- mathlib to deal with inequalities... would love to see an example.
def vec_push_back_old (α : Type u) (v : Vec α) (x : α) : { res: Result (Vec α) //
  match res with | fail _ => True | ret v' => List.length v'.val = List.length v.val + 1}
  :=
  if h : List.length v.val + 1 < USize.size then
    ⟨ return ⟨List.concat v.val x,
      by
        rw [List.length_concat]
        assumption
     ⟩, by simp ⟩
  else
    ⟨ fail maximumSizeExceeded, by simp ⟩

#eval do
  -- NOTE: the // notation is syntactic sugar for Subtype, a refinement with
  -- fields val and property. However, Lean's elaborator can automatically
  -- select the `val` field if the context provides a type annotation. We
  -- annotate `x`, which relieves us of having to write `.val` on the right-hand
  -- side of the monadic let.
  let v := vec_new Nat
  let x: Vec Nat ← (vec_push_back_old Nat v 1: Result (Vec Nat)) -- WHY do we need the type annotation here?
  -- TODO: strengthen post-condition above and do a demo to show that we can
  -- safely eliminate the `fail` case
  return (vec_len Nat x)

def vec_push_back (α : Type u) (v : Vec α) (x : α) : Result (Vec α)
  :=
  if h : List.length v.val + 1 <= 4294967295 then
    return ⟨ List.concat v.val x,
      by
        rw [List.length_concat]
        have h': 4294967295 < USize.size := by intlit
        apply Nat.lt_of_le_of_lt h h'
    ⟩
  else if h: List.length v.val + 1 < USize.size then
    return ⟨List.concat v.val x,
      by
        rw [List.length_concat]
        assumption
     ⟩
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
      have h: List.length v.val < USize.size := v.property
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
      have h: List.length v.val < USize.size := v.property
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

-------------------
-- SANITY CHECKS --
-------------------

-- TODO: add more once we have signed integers

#assert (USize.checked_rem 1 2 == .ret 1)
