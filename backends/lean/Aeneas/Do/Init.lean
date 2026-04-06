import Lean

open Lean Elab Term

register_option Aeneas.newDoElab : Bool := {
    defValue := false
    descr  := "Use the custom Aeneas `do` elaborator"
  }

