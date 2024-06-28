import Aesop

/-!
# ScalarTac rule set

This module defines the `ScalarTac` Aesop rule set which is used by the
`scalar_tac` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Aeneas.ScalarTac]
