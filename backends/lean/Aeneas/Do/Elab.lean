import Lean
import Aeneas.Do.Init

open Lean Elab Term

@[term_elab «do»]
def Aeneas.elabDo : TermElab :=fun stx expectedType? => do
  if ← getBoolOption ``newDoElab then
    return mkNatLit 1
  else
    Term.elabDo stx expectedType?

set_option Aeneas.newDoElab true
def add (a b : Nat) : Option Nat := do
  return a + b

def test (a :  Nat) : Option Nat := do
  let x ← add a 1
  let y ← add x x
  let z ← if x > 1 then add y y else add x x
  return z
