import Aeneas.GrindSimpTac.GrindSimpTac
import Aeneas.SimpLists.Init
import Aeneas.SimpLists.SimpLists
import Aeneas.SimpBoolProp.SimpBoolProp
import Aeneas.ScalarTac.Init
import Aeneas.Grind.Init

/-!
# `gsimp_lists`: like `simp_lists` but using `grind` as a discharger

Built on top of `grindSimpTac`.
-/

namespace Aeneas.GrindSimpTac.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Aeneas.GrindSimpTac

syntax (name := gsimp_lists) "gsimp_lists" "only"? simpArgs (location)? : tactic
syntax (name := gsimp_lists?) "gsimp_lists?" "only"? simpArgs (location)? : tactic

private def gsimpListsElab (qmark : Bool)
  (onlyTk : Option Syntax)
  (simpArgsStx : Option (TSyntax ``simpArgs))
  (loc : Option (TSyntax `Lean.Parser.Tactic.location))
  (stx : stx)
  : TacticM Unit := do
  withMainContext do
  let loc ← Utils.parseOptLocation loc
  let «only» := onlyTk.isSome
  let simpThms ← SimpLists.simpListsSimpExt.getTheorems
  let simprocs ← SimpLists.simpListsSimprocExt.getSimprocs
  let hypsSimpThms ← SimpLists.simpListsHypsSimpExt.getTheorems
  let hypsSimprocs ← SimpLists.simpListsHypsSimprocExt.getSimprocs
  standardGrindSimpTac loc «only» (simpThms, simprocs)
    (hypsSimpThms, hypsSimprocs) simpArgsStx

elab_rules : tactic
  | `(tactic| gsimp_lists $[only%$onlyTk]? $args $[$loc:location]?) => do
    gsimpListsElab false onlyTk args loc (← getRef)
  | `(tactic| gsimp_lists? $[only%$onlyTk]? $args $[$loc:location]?) => do
    gsimpListsElab true onlyTk args loc (← getRef)

end Aeneas.GrindSimpTac.SimpLists
