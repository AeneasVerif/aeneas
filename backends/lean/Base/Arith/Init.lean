import Base.Extensions
open Lean

/-!
# Scalar tac rules sets

This module defines several Aesop rule sets and options which are used by the
`scalar_tac` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

namespace Arith

declare_aesop_rule_sets [Aeneas.ScalarTac, Aeneas.ScalarTacNonLin]

#check Lean.Option.register
register_option scalarTac.nonLin : Bool := {
  defValue := false
  group := ""
  descr := "Activate the use of a set of lemmas to reason about non-linear arithmetic by `scalar_tac`"
}

-- The sets of rules that `scalar_tac` should use
open Extensions in
initialize scalarTacRuleSets : ListDeclarationExtension Name ← do
  mkListDeclarationExtension `scalarTacRuleSetsList

def scalarTacRuleSets.get : MetaM (List Name) := do
  pure (scalarTacRuleSets.getState (← getEnv))

-- Note that the changes are not persistent
def scalarTacRuleSets.set (names : List Name) : MetaM Unit := do
  let _ := scalarTacRuleSets.setState (← getEnv) names

-- Note that the changes are not persistent
def scalarTacRuleSets.add (name : Name) : MetaM Unit := do
  let _ := scalarTacRuleSets.modifyState (← getEnv) (fun ls => name :: ls)

end Arith
