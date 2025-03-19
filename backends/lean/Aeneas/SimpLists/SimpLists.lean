import Aeneas.SimpLists.Init
import Aeneas.ScalarTac.CondSimpTac
import Aeneas.List.List

/-!
# `simp_lists` tactic

The `simp_lists` tactic is used to simplify expressions using lists, such as nested
List `get` and `set`.
-/

namespace Aeneas.SimpLists

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
def simpListsTac (loc : Utils.Location) : TacticM Unit := do
  let addSimpThms : TacticM (Array FVarId) := pure #[]
  ScalarTac.condSimpTac "simp_lists" #[← simpListsSimpExt.getTheorems] #[← simpListsSimprocExt.getSimprocs] addSimpThms false loc

syntax (name := simp_lists) "simp_lists" (location)? : tactic

def parseSimpLists : TSyntax ``simp_lists -> TacticM Utils.Location
| `(tactic| simp_lists) => do
  pure (Utils.Location.targets #[] true)
| `(tactic| simp_lists $[$loc:location]?) => do
  let loc ← Utils.parseOptLocation loc
  pure loc
| _ => Lean.Elab.throwUnsupportedSyntax

elab stx:simp_lists : tactic => do
  let loc ← parseSimpLists stx
  simpListsTac loc

example [Inhabited α] (l : List α) (x : α) (i j : Nat) (hj : i ≠ j) : (l.set j x)[i]! = l[i]! := by
  simp_lists

example [Inhabited α] (l : List α) (x : α) (i : Nat) (hi : i < l.length) : (l.set i x)[i]! = x := by
  simp_lists

/-- We use this lemma to "normalize" successive calls to `List.set` -/
@[simp_lists_simps]
theorem List.set_comm_lt (a b : α) (n m : Nat) (l : List α) (h : n < m) :
  (l.set m a).set n b = (l.set n b).set m a := by
  rw [List.set_comm]
  omega

example [Inhabited α] (l : List α) (x y : α) (i j : Nat) (hj : i < j) : (l.set i x).set j y = (l.set j y).set i x := by
  simp_lists

end Aeneas.SimpLists
