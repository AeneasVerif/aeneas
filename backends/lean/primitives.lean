-------------
-- PRELUDE --
-------------

-- Results & monadic combinators

inductive error where
   | assertionFailure: error
   | integerOverflow: error
   | arrayOutOfBounds: error
   | maximumSizeExceeded: error
   | panic: error
deriving Repr

open error

inductive result (α : Type u) where
  | ret (v: α): result α
  | fail (e: error): result α 
deriving Repr

open result

-- TODO: is there automated syntax for these discriminators?
def is_ret {α: Type} (r: result α): Bool :=
  match r with
  | result.ret _ => true
  | result.fail _ => false

def eval_global {α: Type} (x: result α) (h: is_ret x): α :=
  match x with
  | result.fail _ => by contradiction
  | result.ret x => x

def bind (x: result α) (f: α -> result β) : result β :=
  match x with
  | ret v  => f v 
  | fail v => fail v

-- Allows using result in do-blocks
instance : Bind result where
  bind := bind

-- Allows using return x in do-blocks
instance : Pure result where
  pure := fun x => ret x

def massert (b:Bool) : result Unit :=
  if b then return () else fail assertionFailure

-- Machine integers

-- NOTE: we reuse the USize type from prelude.lean, because at least we know
-- it's defined in an idiomatic style that is going to make proofs easy (and
-- indeed, several proofs here are much shortened compared to Aymeric's earlier
-- attempt.) This is not stricto sensu the *correct* thing to do, because one
-- can query at run-time the value of USize, which we do *not* want to do (we
-- don't know what target we'll run on!), but when the day comes, we'll just
-- define our own USize.
-- ANOTHER NOTE: there is USize.sub but it has wraparound semantics, which is
-- not something we want to define (I think), so we use our own monadic sub (but
-- is it in line with the Rust behavior?)

-- TODO: I am somewhat under the impression that subtraction is defined as a
-- total function over nats...? the hypothesis in the if condition is not used
-- in the then-branch which confuses me quite a bit

-- TODO: add a refinement for the result (just like vec_push_back below) that
-- explains that the toNat of the result (in the case of success) is the sub of
-- the toNat of the arguments (i.e. intrinsic specification)
-- ... do we want intrinsic specifications for the builtins? that might require
-- some careful type annotations in the monadic notation for clients, but may
-- give us more "for free"

-- Note from Chris Bailey: "If there's more than one salient property of your
-- definition then the subtyping strategy might get messy, and the property part
-- of a subtype is less discoverable by the simplifier or tactics like
-- library_search." Try to settle this with a Lean expert on what is the most
-- productive way to go about this?

-- Further thoughts: look at what has been done here:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Fin/Basic.lean
-- and
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/UInt.lean
-- which both contain a fair amount of reasoning already!
def USize.checked_sub (n: USize) (m: USize): result USize :=
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

-- TODO: settle the style for usize_sub before we write these
def USize.checked_add (n: USize) (m: USize): result USize := sorry
def USize.checked_rem (n: USize) (m: USize): result USize := sorry
def USize.checked_mul (n: USize) (m: USize): result USize := sorry
def USize.checked_div (n: USize) (m: USize): result USize := sorry

-- One needs to perform a little bit of reasoning in order to successfully
-- inject constants into USize, so we provide a general-purpose macro

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

-- Test behavior...
#eval USize.checked_sub 10 20
#eval USize.checked_sub 20 10
-- NOTE: compare with concrete behavior here, which I do not think we want
#eval USize.sub 0 1
#eval UInt8.add 255 255

-- Vectors

def vec (α : Type u) := { l : List α // List.length l < USize.size }

def vec_new (α : Type u): result (vec α) := return ⟨ [], by {
  match USize.size, usize_size_eq with
  | _, Or.inl rfl => simp
  | _, Or.inr rfl => simp
  } ⟩

#check vec_new

def vec_len (α : Type u) (v : vec α) : USize :=
  let ⟨ v, l ⟩ := v
  USize.ofNatCore (List.length v) l

#eval do
  return (vec_len Nat (<- vec_new Nat))
 
def vec_push_fwd (α : Type u) (_ : vec α) (_ : α) : Unit := ()

-- TODO: more precise error condition here for the fail case
-- TODO: I originally wrote `List.length v.val < USize.size - 1`; how can one
-- make the proof work in that case? Probably need to import tactics from
-- mathlib to deal with inequalities... would love to see an example.
def vec_push_back (α : Type u) (v : vec α) (x : α) : { res: result (vec α) //
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
  let x: vec Nat ← vec_push_back Nat (<- vec_new Nat) 1
  -- TODO: strengthen post-condition above and do a demo to show that we can
  -- safely eliminate the `fail` case
  return (vec_len Nat x)
