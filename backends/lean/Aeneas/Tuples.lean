import Lean
import AeneasMeta.Utils

namespace Aeneas

namespace Std

-------------------------------
-- Tuple field access syntax --
-------------------------------
-- Declare new syntax `a.#i` for accessing the `i`-th term in a tuple
-- The `noWs` parser is used to ensure there is no whitespace.
-- We use the maximum precedence to make the syntax work with function calls.
-- Ex.: `f (0, 1).#0`
syntax:max term noWs ".#" noWs num : term

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
  /- In case we are indexing into a type abbreviation, we need to unfold the type.

     TODO: we have to be careful about not unfolding too much,
     for instance because of the following code:
     ```
     def Pair T U := T × U
     def Tuple T U V := T × Pair U V
     ```
     We have to make sure that, given `x : Tuple T U V`, `x.1` evaluates
     to the pair (an element of type `Pair T U`), not to the first field
     of the pair (an element of type `T`).

     We have a similar issue below if we generate code from the following Rust definition:
     ```
     struct Tuple(u32, (u32, u32));
     ```
     The issue is that in Rust, field 1 of `Tuple` is a pair `(u32, u32)`, but
     in Lean there is no difference between `A × B × C` and `A × (B × C)`.

     In case such situations happen we probably need to resort to chaining
     the pair projectors, like in: `x.snd.fst`.
   -/
  let type ← whnf type
  -- Ensure `tuple`'s type is a `Prod`uct.
  unless type.isAppOf ``Prod do
    throwError "tuple expected{indentExpr type}"
  let n := getArity type
  -- Ensure `i` is a valid index
  unless i < n do
    throwError "invalid tuple access at {i}, tuple has {n} elements"
  mkGetIdx tuple n i

end Std

end Aeneas
